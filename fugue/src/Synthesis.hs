{-# LANGUAGE StrictData #-}
{-# LANGUAGE InstanceSigs #-}

module Synthesis
  ( Context (..)
  , Function (..)
  , Functions (..)
  , SynthFunction (..)
  , SynthFunctions (..)
  , SynthResult (..)
  , Arg (..)
  , Example (..)
  , SynthState (..)
  , Synth (..)
  , ClosedTerm (..)

  , synthesise
  , synthesiseInEnvironment
  , assemble
  , toVal
  , toVal'
  , toClosed
  , toClosed'
  , simplify
  ) where

import Data.Maybe
import Data.List
import Data.Functor
import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans.RWS.CPS
import qualified Control.Monad.State.Strict as S
import Debug.Trace

import Parser
import Compiler
import Types
import Env ( fromEnvironment, Environment(types) )
import Infer
import Text.Read
import Control.Applicative
import Data.Bifunctor (bimap, second, first)

data Context = Context
  { examples :: [Example]
  , depth :: Int
  , env :: Env
  , dataTypes :: DataTypes
  , fns :: SynthFunctions
  , mayUseHomoRule :: Bool
  , homoAvoidance :: Int
  , noEgsAvoidance :: Int }

data SynthState = SynthState
  { newNames :: [Ident]
  , maxDepth :: Int }
  deriving Show

data SynthFunction = Fn
  { args :: [(Ident, ArgInfo)]
  , ret :: Type
  , body :: Body
  , egs :: [Example] }
  deriving Show

data ArgInfo = ArgInfo
  { argType :: Type
  , maySplitArg :: Bool }

instance Show ArgInfo where
  show a = show (argType a)

instance Eq ArgInfo where
  (==) :: ArgInfo -> ArgInfo -> Bool
  a == b = argType a == argType b

instance Eq SynthFunction where
  (Fn args _ body _) == (Fn args' _ body' _) = args == args' && body == body'

data Body
  = SynthVar Ident

  | SynthLiteral ClosedTerm

  -- constrName [(fnName, [fnArgs...])]
  | SynthConstr Ident [(Ident, [Ident])]

  -- splitArg [(constrName, [conArgs...], fnName, [fnArgs...])]
  | SynthCase Ident [(Ident, [Ident], Ident, [Ident])]

  -- recurseArg [(constrName, [conArgs...], recursivePart, bodyName, [bodyArgs...])]
  | SynthRecurse Ident [(Ident, [Ident], RecursivePart, Ident, [Ident])]

  -- fnName [fnArgs...]
  | SynthCall Ident [Ident]

  -- a hole
  | SynthHole
  deriving (Show, Eq)

data RecursivePart
  -- recursiveBinding, recFnName, [recArgs...]
  = Recurse Ident Ident [Ident]

  -- no recursion
  | NoRecurse
  deriving (Show, Eq)

type SynthFunctions = [(Ident, SynthFunction)]

data Thunk
  = ThunkConstr Ident [Thunk] -- a constructor call
  | ThunkCall Ident [ClosedTerm] -- a (maybe recursive) function call
  | ThunkRecLet Thunk [Ident] Ident [ClosedTerm]-- let x = <th | deps> in f' a' b' c' {x}
  | ThunkTerm ClosedTerm

-- a ClosedTerm is similar to a Term, but is always a fully-evaluated value.
-- furthermore, it contains only values that can be used as synthesis examples,
-- and so doesn't allow abstractions, etc. it can always be represented as
-- the application of some constructor to zero or more arguments, also closed terms.
data ClosedTerm = ConstrApp Ident [ClosedTerm]
  deriving Eq

-- an Arg represents an argument of an example, and is either a fully-evaluated term Val,
-- or a thunk. If it is a thunk, it is a partially-evaluated term. A thunk
-- will also track which functions it is being blocked by (i.e. waiting for).
data Arg = Val ClosedTerm | Thunk Thunk [Ident]

instance Show Arg where
  show (Val t) = show t
  show (Thunk t is) = "<" ++ show t ++ "|" ++ unwords is ++ ">"

data Example = Eg
  { ins :: [Arg]
  , out :: ClosedTerm }
  deriving Show

data SynthResult = SynthResult
  { root :: Ident
  , functions :: Functions
  , depthUsed :: Int }

instance Eq SynthResult where
  (SynthResult root fns _) == (SynthResult root' fns' _) = root == root' && fns == fns'

type Synth = RWST Context SynthFunctions SynthState []

type SynthImpl = [(Ident, ArgInfo)] -> Type -> Ident -> Synth SynthFunction

synthesiseInEnvironment ::
     Environment
  -> Ident
  -> Type
  -> [Example]
  -> [SynthResult]
synthesiseInEnvironment e = synthesise (fromEnvironment e) (types e)

synthesise ::
     Env
  -> DataTypes
  -> Ident
  -> Type
  -> [Example]
  -> [SynthResult]
synthesise env dts fnName goal egs = do
  (fn, st, synFns) <- runSynth defaultState ctx problem
  let fns = map (second assembleFn) synFns
      fns' = [ (fnName, simplifyFn fn) | (fnName, fn) <- fns ]
      fns'' = removeFnsUnusedBy fnName (windFrom fnName fns')
  return $ SynthResult fnName fns'' (maxDepth st)
  where ctx = Context { examples = egs, depth = 0, env = env, fns = [], dataTypes = dts
                      , mayUseHomoRule = False, homoAvoidance = 3, noEgsAvoidance = 1 }
        defaultState = SynthState { newNames = filter (/= fnName) allVars, maxDepth = 0 }
        (goalArgs, goalRet) = unfoldFnTy goal
        problem = (upToDepth 16 ... synth fnName) [ ArgInfo t True | t <- goalArgs ] goalRet

runSynth :: SynthState -> Context -> Synth a -> [(a, SynthState, SynthFunctions)]
runSynth s c p = runRWST p c s

upToDepth :: Int -> Synth a -> Synth a
upToDepth toDepth f = do
  each [ synthWithMaxDepth d | d <- [1..toDepth] ]
  where synthWithMaxDepth d = do
          modify $ \s -> s { maxDepth = d }
          debug $ "## synthesising with max depth " ++ show d ++ " ##"
          f

-- synthesises a function of the given argument and return types, and
-- defines it in the Writer under a given identifier. also returns the
-- function for convenience
synth :: Ident -> [ArgInfo] -> Type -> Synth SynthFunction
synth name argTypes ret = do
  d <- asks depth
  dMax <- gets maxDepth
  egs <- asks examples
  fns <- asks fns
  canHomo <- asks mayUseHomoRule
  avoid <- asks noEgsAvoidance

  debug $ "* synthesising " ++ name ++ " : "
    ++ intercalate " -> " (map (show . argType) argTypes)
    ++ " -> " ++ show ret ++ " with fns: " ++ unwords (map fst fns)
    ++ " and " ++ show (length egs) ++ " examples:"

  -- continue if either we are at least one away from reaching the max depth, or
  -- if there are a non-zero amount of examples.
  -- 
  -- this means that the null-examples rule only applies if we are at least one
  -- away from the max depth, which helps prune the tree a bit.
  guard $ d + avoid < dMax || not (null egs)

  if d < dMax then do
    fnArgs <- forM argTypes $ \t -> do
      name <- fresh
      return (name, t)

    f <- local (\c -> c { depth = d + 1 }) $ do
      egs' <- updateExamplesFully egs

      forM_ egs' $ \(Eg ins out) ->
        debug $ "  { " ++ intercalate ", " (map show ins) ++ " -> " ++ show out ++ " }"

      withExamples egs' $
        if null egs then
          synthNoEgs fnArgs ret name
        else noHomo (each [ synthUnify fnArgs ret name
                          , synthTrivial fnArgs ret name
                          , synthCommonConstr fnArgs ret name
                          , synthRecurse fnArgs ret name
                          , synthSplit fnArgs ret name ])
            `orElse` synthAllSame fnArgs ret name

    emitFunction name f

    return f
  else do
    debug "  : failed: out of depth"
    fail "out of depth"

  where noHomo = local (\c -> c { mayUseHomoRule = False })

synthNoEgs :: SynthImpl
synthNoEgs args retType _ = do
  debug ": trying synth no egs"

  egs <- asks examples

  if null egs then do
    debug "done: synth no egs"
    return $ Fn { args = args
                , ret = retType
                , body = SynthHole
                , egs = [] }
  else
    fail "there are examples so this rule doesn't apply"

synthTrivial :: SynthImpl
synthTrivial = eachArg "trivial" $ \i args retType fnName -> do
  egs <- asks examples

  guard $ all (\(Eg egArgs egRes) -> egArgs !! i `hasVal` egRes) egs

  -- synth trivial only applies when the type of the argument under inspection
  -- can be unified with the required return type.
  let (argName, ArgInfo argTy _) = args !! i
  guard $ argTy <= retType

  debug "done: synth trivial"

  return $ Fn { args = args
              , ret = retType
              , body = SynthVar argName
              , egs = egs }

synthAllSame :: SynthImpl
synthAllSame args retType _ = do
  debug ": trying synth all same"

  egs <- asks examples
  canUse <- asks mayUseHomoRule
  dMax <- gets maxDepth
  d <- asks depth
  avoid <- asks homoAvoidance

  guard $ canUse && d + avoid < dMax && not (null egs)

  case egs of
    [] -> fail "doesn't apply"
    (Eg _ o:egs) -> do
      if all ((== o) . out) egs then do
        debug $ "done: all same (o = " ++ show o ++ ")"
        return Fn { args = args
                  , ret = retType
                  , body = SynthLiteral o
                  , egs = egs }
      else
        fail "doesn't apply; not all same output"

synthCommonConstr :: SynthImpl
synthCommonConstr args retType fnName = do
  debug ": trying common constr"

  egs <- asks examples
  guard $ not (null egs)

  case sharedConstr egs of
    Nothing -> fail "the constructor is not shared"
    Just con -> do
      egs <- asks examples

      Just (Forall _ conTy) <- lookupType con
      let (conArgTys, _) = unfoldFnTy (specialiseConstructor conTy retType)
          (conArgs, apps) = unzip [ (args, deconstruct' o) | Eg args o <- egs ]
          (cons, argsByCon) = unzip apps
          argsByIndex = transpose argsByCon
          conEgs = [ zipWith Eg conArgs d | d <- argsByIndex ]
          (argNames, argTypes) = unzip args

      -- construct the function - the output of this synthesis.
      -- the sub-functions need not be synthesised yet, since only
      -- their names need to be known at this point.
      names <- forM conArgTys (const fresh)
      let fn = Fn { args = args
                  , ret = retType
                  , body = SynthConstr con [ (n, argNames) | n <- names ]
                  , egs = egs }

      -- actually synthesise the sub-functions
      withFunction fnName fn $
        traverseContinuation (zip3 names conArgTys conEgs) $ \(fnName', conArgTy, egs) c -> do
          f <- withExamples egs $ synth fnName' argTypes conArgTy
          withFunction fnName' f c

      debug "done: common constr"
      return fn

synthSplit :: SynthImpl
synthSplit = eachArg "case split" $ \splitOn args retType fnName -> do
  egs <- asks examples
  dts <- asks dataTypes

  -- we cannot split on an argument which is not fully evaluated
  guard (not (argIsThunk splitOn egs))

  let (splitArg, ArgInfo splitTy maySplit) = args !! splitOn
  guard maySplit
  case splitTy of
    TyConstr dtName dtArgs -> case lookup dtName dts of
      Just (DataType tyArgs dtConstrs) -> do
        let s = zip tyArgs dtArgs :: Subst
            concreteConstructors = [ DataConstructor i (map (sub s) ts)
                                   | DataConstructor i ts <- dtConstrs ]

        -- for each constructor in the datatype
        cases <- forM concreteConstructors $ \(DataConstructor con constructorArgTypes) -> do
          constructorArgs <- forM constructorArgTypes $ \ty -> do
            name <- fresh
            return (name, ty)

          -- find the examples which use the appropriate constructor for this branch,
          -- and update them (give them the deconstructed arguments as well as their
          -- existing parameters)
          let allArgs = args ++ [ (i, ArgInfo t True) | (i, t) <- constructorArgs ]

          -- make a new function name to synthesise this case inside
          caseFnName <- fresh

          return ( con
                 , map fst constructorArgs
                 , caseFnName
                 , allArgs )

        let fnBody = SynthCase splitArg [ (con, conArgs, caseFn, map fst allArgs)
                                        | (con, conArgs, caseFn, allArgs) <- cases ]
        let fn = Fn { args = args
                    , ret = retType
                    , body = fnBody
                    , egs = egs }

        withFunction fnName fn $
          traverseContinuation cases $ \(con, conArgs, caseFn, allArgs) c -> do
            let examples =
                  [ Eg (ins ++ map Val conArgs') out
                  | Eg ins out <- egs
                  , let (con', conArgs') = deconstruct' (fromVal (ins !! splitOn))
                  , con == con']

            fn <- withExamples examples $ synth caseFn (map snd allArgs) retType
            withFunction caseFn fn c

        debug $ "done: split on arg " ++ show splitOn

        return fn

      Nothing -> fail "non-datatype or undefined"
    _ -> fail "can't split on non-ADT"

synthRecurse :: SynthImpl
synthRecurse = eachArg "recurse" $ \splitOn args retType fnName -> do
  egs <- asks examples
  dts <- asks dataTypes
  fs <- asks fns
  d <- asks depth
  m <- gets maxDepth

  -- we cannot split on an argument which is not fully evaluated. all example arguments
  -- must be fully evaluated values, for simplicity. strictly speaking, only the argument
  -- being split on needs to be a non-thunk, but in most cases it won't be useful to
  -- split when there is already a thunk so we ignore these cases.
  guard $ not (egHasThunk egs)

  debug $ "trying recurse on arg: " ++ show splitOn

  -- the possible functions to recurse on are:
  --  * the current function being synthesised
  --  * plus, the previous x functions that were defined
  --    (where x = remaining_depth - 1)
  --    i.e. if depth = 4 and maxDepth = 5, no other functions will be considered
  let possibleRecFns = [fnName]-- : take (m - d - 1) (map fst fs)

  let (splitArg, ArgInfo splitTy maySplit) = args !! splitOn
  guard maySplit

  case splitTy of
    TyConstr dtName dtArgs -> case lookup dtName dts of
      Just (DataType tyArgs dtConstrs) -> do
        let s = zip tyArgs dtArgs :: Subst
            concreteConstructors = [ DataConstructor i (map (sub s) ts)
                                   | DataConstructor i ts <- dtConstrs ]

        guard $ not (null concreteConstructors)

        debug $ fnName ++ ": recursion will be attempted on: " ++ show possibleRecFns
        -- attempt to recurse on this function, as well as all previously defined functions.
        -- TODO: various things need to be updated to account for this, for example retType in
        -- possibleRecursiveArgs.
        forEach possibleRecFns $ \f -> do
          debug $ "attempting recursion on: " ++ f
          -- for each constructor in the datatype, see if we can find recursive arguments
          -- consisting of parts of the constructor. either way, keep track of whether or
          -- not we want to recurse for this case, and store all relevant info/names for
          -- later synthesis.
          possibleCases <- forM concreteConstructors $ \(DataConstructor con constructorArgTypes) -> do
            constructorArgs <- forM constructorArgTypes $ \ty -> do
              name <- fresh
              return (name, ty)

            caseFnName <- fresh
            recursiveCallName <- fresh

            let possibleRecArgs = forM args $ \(_, ArgInfo t _) ->
                  possibleRecursiveArgs t constructorArgs

            debug $ "for " ++ con ++ ", possibleRecArgs = " ++ show possibleRecArgs

            -- let recursiveArgs = forM args $ \(_, ArgInfo t _) -> chooseRecursiveArg t constructorArgs
            let args' = [ (n, ArgInfo t (i /= splitOn && sp))
                        | (i, (n, ArgInfo t sp)) <- zip [0..] args ]
                allArgs = args' ++ [ (i, ArgInfo t True) | (i, t) <- constructorArgs ]
                constructorParams = map fst constructorArgs

            let r = case possibleRecArgs of
                  [] -> [(NoRecurse, allArgs)]
                  possibleRecursiveArgs -> possibleRecursiveArgs <&> \recursiveArgs ->
                    let allArgs' = allArgs ++ [(recursiveCallName, ArgInfo retType False)]
                    in (Recurse recursiveCallName f recursiveArgs, allArgs')

            return [ (caseFnName, allArgs, recursivePart, con, constructorParams, bodyArgs)
                   | (recursivePart, bodyArgs) <- r ]

          debug $ "all possible cases:" ++ show (zip concreteConstructors possibleCases)

          forEach (transpose possibleCases) $ \cases -> do
            debug $ "trying cases: " ++ show cases
            -- the body of the entire recursive function being synthesised here is a case
            -- split, where each case either performs a recursive call or doesn't.
            let fnBody = SynthRecurse splitArg
                  [ (constrName, conArgs, recursivePart, caseFnName, map fst bodyArgs)
                  | (caseFnName, allArgs, recursivePart, constrName, conArgs, bodyArgs) <- cases
                  , let fnArgs = map fst bodyArgs ]

            let fn = Fn { args = args
                        , ret = retType
                        , body = fnBody
                        , egs = egs }

            debug $ "recursive body = " ++ show fnBody

            -- with this function (the recursive one being defined - "fnName") temporarily added
            -- to the namespace, we synthesise each case in turn.
            withFunction fnName fn $
              traverseContinuation cases $ \(caseFnName, allArgs, recursivePart, con, conParams, _) c -> do
                e <- asks env

                fn <- case recursivePart of
                  Recurse recCall recFnName recParams -> do
                    -- when a recursive call is made, we need to construct a thunk to pass as
                    -- an example to the sub-function.
                    let fnType = finalise $ foldr (-->) retType (map (argType . snd) allArgs ++ [retType])
                        lookupArg args name = fromJust $ lookup name args
                        examples = [ Eg (ins ++ map Val conArgs ++ [thunk]) out
                                   | Eg ins out <- egs
                                   , let (con', conArgs) = deconstruct' (fromVal (ins !! splitOn))
                                   , con == con'
                                   , let recArgs = map (lookupArg (zip conParams conArgs)) recParams
                                   , let thunk = Thunk (ThunkCall recFnName recArgs) [recFnName] ]

                    withExamples examples $ synth caseFnName (map snd allArgs ++ [ArgInfo retType False]) retType

                  NoRecurse -> do
                    let examples = [ Eg (ins ++ map Val conArgs) out
                                  | Eg ins out <- egs
                                  , let (con', conArgs) = deconstruct' (fromVal (ins !! splitOn))
                                  , con == con' ]

                    local (\c -> c { mayUseHomoRule = True }) $
                      withExamples examples $ synth caseFnName (map snd allArgs) retType

                withFunction caseFnName fn c

            debug $ "done: recurse on arg " ++ show splitOn
            return fn

      Nothing -> fail "non-datatype or undefined"
    _nonADT -> fail "can't recurse on non-ADT"

chooseRecursiveArg :: Type -> [(Ident, Type)] -> Maybe Ident
chooseRecursiveArg t consArgs = fst <$> find (\(_, t') -> t == t') consArgs

possibleRecursiveArgs :: Type -> [(Ident, Type)] -> [Ident]
possibleRecursiveArgs t args = fst <$> filter (\(_, t') -> t == t') args

synthUnify :: SynthImpl
synthUnify = eachArg "unify" $ \i args retType fnName -> do
  egs <- asks examples

  let insAt_i = transpose (map ins egs) !! i
      outs = map out egs

  case concat <$> zipWithM (unifyArg fnName) outs insAt_i of
    Just unifyEgs@(x:_) -> do
      debug $ " - can unify: " ++ show unifyEgs
      -- unifyEgs at this point is the set of examples we should add.
      -- we also need to update the existing examples, replacing the thunks with
      -- their proper values.
      let egs' = [ updateThunkCall fnName o' eg
                 | (eg, Eg _ o') <- zip egs unifyEgs ]
                 ++ unifyEgs -- ?

      fnName' <- fresh

      let fn = Fn { args = args
                  , ret = retType
                  , body = SynthCall fnName' (map fst args)
                  , egs = egs }

      withExamples egs' $ synth fnName' (map snd args) retType
    _ -> fail "couldn't unify"

eachArg :: String -> (Int -> SynthImpl) -> SynthImpl
eachArg name f args retType fnName = do
  debug $ ": trying " ++ name

  egs <- asks examples
  guard $ not (null egs)

  each [ f i args retType fnName | i <- [0..length args - 1] ]

-- e.g. <2 :: (2 :: h [2] 2 [] [])> unifies with 2 :: (2 :: []),
-- providing the example: h [2] 2 [] [] => [].
--
-- FOR NOW, we assume that there is only one instance of each
-- function, although if functions are allowed to be reused in the
-- future then this would break.
-- TODO: improve this
--
-- returns Just [egs...] if the given egs would unify the thunk 
-- with the term, and Nothing if the two are inconsolable.
-- 
-- it will only unify thunk function calls of the fnName provided.
-- e.g. in the example above, fnName would have to be "h".
unifyThunk :: Ident -> ClosedTerm -> Thunk -> Maybe [Example]
unifyThunk fnName (ConstrApp con' conArgs') (ThunkConstr con conArgs)
  | con == con' = do
      egs <- zipWithM (unifyThunk fnName) conArgs' conArgs
      return $ concat egs
unifyThunk fnName t (ThunkCall f fArgs)
  | fnName == f = Just [Eg (map Val fArgs) t]
unifyThunk fnName t (ThunkTerm t')
  | t == t' = Just []
unifyThunk _ _ _ = Nothing

unifyArg :: Ident -> ClosedTerm -> Arg -> Maybe [Example]
unifyArg i t (Thunk th deps) = unifyThunk i t th
unifyArg i _ _ = Just [] -- TODO: should this be Just [] ?

updateThunkCall :: Ident -> ClosedTerm -> Example -> Example
updateThunkCall i t (Eg ins out) = Eg (map goArg ins) out
  where goArg (Thunk th deps) = Thunk (replaceThunkCall i t th) (deps \\\ [i])
        goArg (Val v) = Val v

replaceThunkCall :: Ident -> ClosedTerm -> Thunk -> Thunk
replaceThunkCall f t (ThunkConstr con ths) = ThunkConstr con (map (replaceThunkCall f t) ths)
replaceThunkCall f t (ThunkCall f' args)
  | f == f' = ThunkTerm t
  | otherwise = ThunkCall f' args
replaceThunkCall f t (ThunkRecLet th deps fn fnArgs) = error "replaceThunkCall not implemented for ThunkRecLet"
replaceThunkCall f t (ThunkTerm t') = ThunkTerm t'

debug :: String -> Synth ()
debug _ = return ()
-- debug s = do
--   d <- asks depth
--   let prefix = concat (replicate d "* ")
--   traceM $ prefix ++ s

hasVal :: Arg -> ClosedTerm -> Bool
hasVal (Val v) t = v == t
hasVal (Thunk _ _) t = False

fromVal :: Arg -> ClosedTerm
fromVal (Val v) = v
fromVal _ = error "fromVal on non-val (i.e. thunk) argument"

isThunk :: Arg -> Bool
isThunk (Val _) = False
isThunk (Thunk _ _) = True

insToVals :: Example -> [ClosedTerm]
insToVals (Eg ins _) = map fromVal ins

argIsThunk :: Int -> [Example] -> Bool
argIsThunk n [] = False
argIsThunk n ((Eg args _):rest) = isThunk (args !! n) || argIsThunk n rest

egHasThunk :: [Example] -> Bool
egHasThunk [] = False
egHasThunk ((Eg args _):rest) = any isThunk args || egHasThunk rest

withSynth :: Ident -> [ArgInfo] -> Type -> Synth a -> Synth a
withSynth name args ret s = do
  fn <- synth name args ret
  withFunction name fn s

-- defines a function into the Writer output of the synthesiser.
-- this means that the function will be emitted (if this branch
-- succeeds), but will not be visible to the synthesis of any
-- further functions.
-- use withFunction if it's required that this function can be
-- used later on in another function.
emitFunction :: Ident -> SynthFunction -> Synth ()
emitFunction name fn = tell [(name, fn)]

-- like defineFunction, but also exposes the function to a further
-- synthesis problem to be (potentially) called in its d1efinition.
-- essentially "wraps" a synthesiser in some extra context.
withFunction :: Ident -> SynthFunction -> Synth a -> Synth a
withFunction name f s = do
  e <- asks env
  withFunctionInEnv name f e s

withFunctionInEnv :: Ident -> SynthFunction -> Env -> Synth a -> Synth a
withFunctionInEnv name f e =
  local (\c -> c
      { env = insertKV name (getType f, Local) (env c)
      , fns = (name, f) : fns c })

each :: (MonadFail m, Alternative m, Monoid w) => [RWST r w s m a] -> RWST r w s m a
each [] = fail "exhausted all possibilities"
each (x:xs) = rwsT $ \r s -> runRWST x r s <|> runRWST (each xs) r s

forEach :: (MonadFail m, Alternative m, Monoid w) => [a] -> (a -> RWST r w s m b) -> RWST r w s m b
forEach xs f = each (fmap f xs)

orElse :: Monoid w => RWST r w s [] a -> RWST r w s [] a -> RWST r w s [] a
orElse first alt = rwsT $ \r s -> case runRWST first r s of
  [] -> runRWST alt r s
  v -> v

assembleBody :: Body -> Expr
assembleBody (SynthVar x) = Var x
assembleBody (SynthLiteral v) = assembleTerm v
assembleBody (SynthConstr con fns) =
  applyMany $ Var con : [ applyManyIdents (n : args)
                        | (n, args) <- fns ]
assembleBody (SynthCase x cases) =
  Case (Var x)
       [ (con, conArgs, b)
       | (con, conArgs, fn, fnArgs) <- cases
       , let b = applyManyIdents (fn : fnArgs) ]
assembleBody (SynthRecurse x cases) =
  Case (Var x)
       [ (con, conArgs, b)
       | (con, conArgs, rp, fn, fnArgs) <- cases
       , let b = assembleRecursiveBody rp (applyManyIdents (fn : fnArgs)) ]
assembleBody (SynthCall f args) =
  applyMany $ map Var (f : args)
assembleBody SynthHole = Hole 0

assembleTerm :: ClosedTerm -> Expr
assembleTerm (ConstrApp c args) = applyMany $ Var c : map assembleTerm args

assembleRecursiveBody :: RecursivePart -> Expr -> Expr
assembleRecursiveBody (Recurse b recFn recArgs) body
  = Let b (applyManyIdents (recFn : recArgs)) body
assembleRecursiveBody NoRecurse body = body

assemble :: SynthFunction -> Expr
assemble (Fn args _ body _) = foldr (Abs . fst) (assembleBody body) args

assembleFn :: SynthFunction -> Function
assembleFn (Fn args ret body egs) =
  Function [ (i, t) | (i, ArgInfo t _) <- args] ret (assembleBody body) egs

getType :: SynthFunction -> Scheme
getType (Fn args ret _ _) =
  let argTypes = map (argType . snd) args
  in finalise $ foldr (-->) ret argTypes

fresh :: Synth Ident
fresh = do
  name <- gets (head . newNames)
  modify $ \s@SynthState { newNames = (n:ns) } -> s { newNames = ns }
  return name

specialiseConstructor :: Type -> Type -> Type
specialiseConstructor conTy ret = case runExcept (runUnify u) of
  Left err -> error "unexpected error specialising constructor"
  Right s -> sub s genTy'
  where (argTys, conRetTy) = unfoldFnTy conTy
        varNames = take (length argTys) [ "*temp" ++ show i | i <- [0..] ]
        genTy = foldr ((-->) . TyVar) ret varNames
        (conTy', genTy') = renameToDistinct conTy genTy
        u = unify genTy' conTy'

lookupType :: Ident -> Synth (Maybe Scheme)
lookupType x = do
  ts <- asks env
  return $ fmap fst (lookup x ts)

lookupType' :: Ident -> Synth Scheme
lookupType' x = do
  t <- lookupType x
  case t of
    Nothing -> error $ "synth: couldn't find type: " ++ x
    Just t -> return t

lookupFn :: Ident -> Synth (Maybe SynthFunction)
lookupFn x = do
  fns <- asks fns
  return $ lookup x fns

withExamples :: [Example] -> Synth a -> Synth a
withExamples egs = local (\l -> l { examples = egs })

-- TODO: I need to *always* be able to provide a SynthFunction to the
-- subfunctions being synthesised, so they can update their examples.
-- updateExamplesWith :: Ident -> SynthFunction -> Synth ()
-- ... or do i?
-- inefficiently, i can just check for all thunks if they can be updated
-- before each synth i guess?

updateExamplesFully :: [Example] -> Synth [Example]
updateExamplesFully egs = do
  (egs', changed) <- updateExamples egs
  if changed then updateExamplesFully egs' else return egs'

updateExamples :: [Example] -> Synth ([Example], Bool)
updateExamples egs = do
  fns <- asks fns

  let (ins, rets) = unzip [ (i, ret) | Eg i ret <- egs ]
      insT = transpose ins
      has = map fst fns

  r <- forM insT $ \c -> do
     let updatable = nub $ canUpdateAny c has
     notHoles <- filterM (fmap (maybe True (not . isHole)) . lookupFn) updatable
     case notHoles of
      [] -> return (c, False)
      updatable -> do
        new <- updateThunks updatable c
        return (new, True)

  let (ins'T, didUpdate) = unzip r
      ins' = transpose ins'T

  return ([ Eg i ret | (i, ret) <- zip ins' rets ], or didUpdate)

  where canUpdateAny [] _ = []
        canUpdateAny (Thunk t []:xs) has = "*finalise thunk*" : canUpdateAny xs has
        canUpdateAny (Thunk t fs:xs) has = fs `intersect` has ++ canUpdateAny xs has
        canUpdateAny (_:xs) has = canUpdateAny xs has

        updateThunks :: [Ident] -> [Arg] -> Synth [Arg]
        updateThunks updatable [] = return []
        updateThunks updatable (Thunk t []:xs) = case thunkToTerm t of
          Just term -> (Val term :) <$> updateThunks updatable xs
          Nothing -> error $ "thunkToTerm wasn't able to make a term from: " ++ show t
        updateThunks updatable (Thunk t fs:xs) = do
          let (fsUpdatable, fsNonupdatable) = fs `disjoint` updatable
          (t', fs') <- updateThunk t (fs `intersect` fsUpdatable)
          let fs'' = fs' ++ fsNonupdatable
          rest <- updateThunks updatable xs
          return (Thunk t' fs'' : rest)
        updateThunks updatable (x:xs) = (x:) <$> updateThunks updatable xs

        isHole :: SynthFunction -> Bool
        isHole Fn{ body = SynthHole } = True
        isHole _ = False

-- applies a function body with named arguments (names provided) to some
-- arguments, also provided. returns a set of function names which the
-- thunk is now dependent upon.
applyBody :: [Ident] -> Body -> [ClosedTerm] -> (Thunk, [Ident])
applyBody params body args = case body of
    SynthVar x ->
      (ThunkTerm $ get x, [])

    SynthLiteral v ->
      (ThunkTerm v, [])

    SynthConstr con calls ->
      let th = ThunkConstr con [ ThunkCall name (map get args) | (name, args) <- calls ]
      in (th, map fst calls)

    SynthCase x cases ->
      let (con, conArgs) = deconstruct' (get x)
          (_, conParams, fnName, fnArgs) =
            fromJust $ find (\(con', _, _, _) -> con == con') cases
          allArgs = zip (params ++ conParams) (args ++ conArgs)
          fnArgVals = map (getIn allArgs) fnArgs
          th = ThunkCall fnName fnArgVals
      in (th, [fnName])

    SynthRecurse x cases ->
      let (con, conArgs) = deconstruct' (get x)
          (_, conParams, recPart, fnName, fnArgs) =
            case find (\ (con', _, _, _, _) -> con == con') cases of
              Nothing -> error $ "couldn't find case " ++ con ++ " in cases: " ++ show cases
              Just x -> x
          allArgs = zip (params ++ conParams) (args ++ conArgs)
      in case recPart of
        Recurse recBinding recCall recArgs ->
          let allArgs' = allArgs ++ zip conParams conArgs
              recArgVals = map (getIn allArgs') recArgs
              fnArgVals = map (getIn allArgs') (init fnArgs)
              th = ThunkRecLet (ThunkCall recCall recArgVals) [recCall] fnName fnArgVals
          in (th, [recCall])
        NoRecurse ->
          let fnArgVals = map (getIn allArgs) fnArgs
          in (ThunkCall fnName fnArgVals, [fnName])

    SynthCall f args ->
      (ThunkCall f (map get args), [f])

    SynthHole -> error "attempted to apply a function which is undefined (i.e. a hole)"
  where getIn as x = case lookup x as of
          Just v -> v
          Nothing -> error $ "getIn (" ++ show body ++ "): couldn't find " ++ x ++ " in " ++ show as
        get = getIn (zip params args)
        call f xs = ThunkCall f (map get xs)

-- updates a thunk by applying a provided function where applicable.
-- the new thunk is returned along with the new list of dependencies introduced.
updateThunkWith :: Ident -> SynthFunction -> Thunk -> (Thunk, [Ident])
updateThunkWith fnName fn@(Fn args _ body _) th = case th of
  ThunkConstr s ths ->
    let (thunks, deps) = unzip (map (updateThunkWith fnName fn) ths)
    in (ThunkConstr s thunks, nub $ concat deps)

  ThunkCall callFn callArgs ->
    if callFn == fnName then case body of
      SynthHole -> (th, [callFn])
      body -> applyBody (map fst args) body callArgs
    else
      (th, [callFn])

  ThunkTerm t -> (th, [])

  ThunkRecLet th' deps callFn callArgs ->
    if fnName `elem` deps then
      case updateThunkWith fnName fn th' of
        (nonThunk, []) -> (ThunkCall callFn (callArgs ++ [thunkToTerm' nonThunk]), [callFn])
        (th'', deps') -> (ThunkRecLet th'' deps' callFn callArgs, deps')
    else
      (th, deps)

updateThunk :: Thunk -> [Ident] -> Synth (Thunk, [Ident])
updateThunk th deps = do
  fns <- asks fns
  depFns <- mapM lookupFn deps
  case sequence depFns of
    Nothing -> error "updateThunk called with insufficient functions"
    Just sfs -> return $
      foldr
        (\(fnName, fn) (th, ds) ->
          let (th', ds') = updateThunkWith fnName fn th
          in (th', ds' ++ ds))
        (th, []) (zip deps sfs)

thunkToTerm :: Thunk -> Maybe ClosedTerm
thunkToTerm (ThunkConstr i ts) = do
  ts' <- mapM thunkToTerm ts
  return $ ConstrApp i ts'
thunkToTerm (ThunkTerm t) = return t
thunkToTerm _ = Nothing

thunkToTerm' :: Thunk -> ClosedTerm
thunkToTerm' th = case thunkToTerm th of
  Just t -> t
  Nothing -> error $ "thunk " ++ show th ++ " is not a closed term"

deconstruct :: ClosedTerm -> Maybe (Ident, [ClosedTerm])
deconstruct (ConstrApp i args) = Just (i, args)

deconstruct' :: ClosedTerm -> (Ident, [ClosedTerm])
deconstruct' = fromJust . deconstruct

intToSucs :: Int -> Term
intToSucs 0 = CConstr "Zero"
intToSucs n = CApp (CConstr "Suc") (intToSucs (n - 1))

deconstructToClosed :: Term -> Maybe (Ident, [ClosedTerm])
deconstructToClosed (CConstr i) = Just (i, [])
deconstructToClosed (CApp l r) = do
  (i, ts) <- deconstructToClosed l
  r' <- toClosed r
  return (i, ts ++ [r'])
deconstructToClosed (CInt n) = deconstructToClosed (intToSucs n)
deconstructToClosed _ = Nothing

toClosed :: Term -> Maybe ClosedTerm
toClosed t = do
  (i, cs) <- deconstructToClosed t
  return $ ConstrApp i cs

sharedConstr :: [Example] -> Maybe Ident
sharedConstr [] = Nothing
sharedConstr xs = do
  let outputs = [ o | Eg _ o <- xs ]
  (y:ys) <- forM outputs (fmap fst . deconstruct)
  if all (== y) ys then
    return y
  else
    Nothing

applyMany :: [Expr] -> Expr
applyMany = foldl1 App

applyManyIdents :: [Ident] -> Expr
applyManyIdents = applyMany . map Var

unfoldApp :: Expr -> (Expr, [Expr])
unfoldApp (App f x) =
  let (f', args) = unfoldApp f
  in (f', args ++ [x])
unfoldApp e = (e, [])

data Function = Function
  { fnArgs :: [(Ident, Type)]
  , fnRetType :: Type
  , fnBody :: Expr
  , fnExamples :: [Example] }
  deriving Show

instance Eq Function where
  (Function args _ body _) == (Function args' _ body' _) = args == args' && body == body'

type Functions = [(Ident, Function)]

type Wind = S.State Functions

windFrom :: Ident -> Functions -> Functions
windFrom x = S.execState (windFn x)

windFn :: Ident -> Wind ()
windFn f = do
  Function args ret body egs <- lookupU' f
  body' <- wind body
  S.modify (insertFn f (Function args ret body' egs))

wind :: Expr -> Wind Expr
wind (Var x) = do
  fn <- lookupU x
  case fn of
    Just Function{ fnBody = body, fnArgs = [] } -> do
      windFn x
      wind body
    _ -> return $ Var x
wind app@(App e1 e2) = case unfoldApp app of
    (Var x, args) -> do
      fn <- lookupU x
      case fn of
        Just fn -> if canInline x fn then inline x args else app'
        Nothing -> app'
    _ -> app'
  where app' = App <$> wind e1 <*> wind e2
wind (Abs x e) = Abs x <$> wind e
wind (Let x e1 e2) = Let x <$> wind e1 <*> wind e2
wind (LetRec x e1 e2) = LetRec x <$> wind e1 <*> wind e2
wind (If e1 e2 e3) = If <$> wind e1 <*> wind e2 <*> wind e3
wind (Case e cases) = do
  cases' <- forM cases $ \(x, xs, b) -> do
    b' <- wind b
    return (x, xs, b')

  Case <$> wind e <*> return cases'
wind (LitInt n) = return $ LitInt n
wind (LitList xs) = LitList <$> mapM wind xs
wind (LitTuple xs) = LitTuple <$> mapM wind xs
wind (LitChar c) = return $ LitChar c
wind (TypeSpec e t) = TypeSpec <$> wind e <*> return t
wind (Hole n) = return $ Hole n

inline :: Ident -> [Expr] -> Wind Expr
inline f args = do
  windFn f
  Function fnArgs _ fnBody _ <- lookupU' f
  let arguments = zip (map fst fnArgs) args
  return $ subExpr arguments fnBody

lookupU :: Ident -> Wind (Maybe Function)
lookupU f = fmap (lookup f) S.get

lookupU' :: Ident -> Wind Function
lookupU' f = fmap fromJust (lookupU f)

canInline :: Ident -> Function -> Bool
canInline fnName Function{ fnBody = body } = not (body `calls` fnName)

insertFn :: Ident -> Function -> Functions -> Functions
insertFn x fn [] = []
insertFn x fn ((x', fn'):xs)
  | x == x' = (x, fn) : xs
  | otherwise = (x', fn') : insertFn x fn xs

calledBy :: Expr -> [Ident]
calledBy app@(App _ _) = case unfoldApp app of
  (Var x, xs) -> x : concatMap calledBy xs
  (f, xs) -> calledBy f ++ concatMap calledBy xs
calledBy (Abs _ a) = calledBy a
calledBy (Let _ a b) = calledBy a ++ calledBy b
calledBy (LetRec _ a b) = calledBy a ++ calledBy b
calledBy (If a b c) = calledBy a ++ calledBy b ++ calledBy c
calledBy (Case a cs) = calledBy a ++ concatMap (\(_,_,b) -> calledBy b) cs
calledBy (LitList xs) = concatMap calledBy xs
calledBy (LitTuple xs) = concatMap calledBy xs
calledBy (TypeSpec a _) = calledBy a
calledBy _ = []

allFunctionsUsedBy :: Ident -> Functions -> [Ident]
allFunctionsUsedBy x fns = go x fns []
  where go :: Ident -> Functions -> [Ident] -> [Ident]
        go x fns visited
          | x `elem` visited = visited
          | otherwise = x : case lookup x fns of
              Nothing -> []
              Just Function{ fnBody = body } ->
                let newCalls = calledBy body \\\ (x : visited)
                in foldl' (\vs call -> go call fns vs) visited newCalls

removeFnsUnusedBy :: Ident -> Functions -> Functions
removeFnsUnusedBy x fns = filter ((`elem` used) . fst) fns
  where used = allFunctionsUsedBy x fns

simplifyFn :: Function -> Function
simplifyFn (Function args ret body egs)
  = Function args ret (simplify body) egs

simplify :: Expr -> Expr
simplify (App e1 e2) = App (simplify e1) (simplify e2)
simplify (Abs x b) = Abs x (simplify b)
simplify (Let i v b)
  | refs == 0 = b'
  | refs == 1 = simplify (subExpr [(i, v')] b')
  | otherwise = Let i v' b'
  where (v', b') = (simplify v, simplify b)
        refs = references i b'
simplify (LetRec i v b)
  | refs == 0 = b'
  | refs == 1 = simplify (subExpr [(i, v')] b')
  | otherwise = LetRec i v' b'
  where (v', b') = (simplify v, simplify b)
        refs = references i b'
simplify (If c b1 b2) = If (simplify c) (simplify b1) (simplify b2)
simplify (Case c cases) =
  let bodies' = [ simplify b | (_, _, b) <- cases ]
  in Case c [ (con, conArgs, b') | ((con, conArgs, _), b') <- zip cases bodies' ]
simplify (LitList es) = LitList (map simplify es)
simplify (LitTuple es) = LitTuple (map simplify es)
simplify (TypeSpec e t) = TypeSpec (simplify e) t
simplify old = old

-- counts references of an ident in an expr
references :: Ident -> Expr -> Int
references i = foldExpr (+) f 0
  where f (Var v) = if v == i then 1 else 0
        f _ = 0

calls :: Expr -> Ident -> Bool
calls e i = i `elem` calledBy e

toVal :: Value a => a -> Maybe Arg
toVal v = do
  c <- toClosed (toTerm v)
  return $ Val c

toVal' :: Value a => a -> Arg
toVal' = fromJust . toVal

toClosed' :: Value a => a -> ClosedTerm
toClosed' = fromJust . toClosed . toTerm

(...) :: (b -> c) -> (a1 -> a2 -> b) -> a1 -> a2 -> c
(...) = (.) . (.)

insertKV :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
insertKV k v [] = [(k, v)]
insertKV k v ((k', v'):xs)
  | k == k' = (k, v) : xs
  | otherwise = (k', v') : insertKV k v xs

deleteKV :: Eq a => a -> [(a, b)] -> [(a, b)]
deleteKV k [] = []
deleteKV k ((k', v'):xs)
  | k == k' = xs
  | otherwise = (k', v') : deleteKV k xs

(\\\) :: Eq a => [a] -> [a] -> [a]
xs \\\ [] = xs
xs \\\ (y:ys) = [ x | x <- xs, x /= y ] \\\ ys

-- disjoint xs ys = (xs `intersect` ys, xs \\\ (xs `intersect` ys))
-- TODO: this can surely be implemented better
disjoint :: Eq a => [a] -> [a] -> ([a], [a])
disjoint xs ys = (xs `intersect` ys, xs \\\ ys)

traverseContinuation :: Monad m => [a] -> (a -> m [b] -> m [b]) -> m [b]
traverseContinuation xs f = foldr f (return []) xs

instance Show Thunk where
  show (ThunkConstr "Zero" []) = "0"
  show (ThunkConstr "Suc" [t]) = case readMaybe (show t) :: Maybe Int of
    Just n -> show (1 + n)
    Nothing -> "(Suc " ++ show t ++ ")"
  show (ThunkConstr "Nil" []) = "[]"
  show (ThunkConstr "Cons" [l, r]) = "(" ++ show l ++ " :: " ++ show r ++ ")"
  show (ThunkConstr con []) = con
  show (ThunkConstr con ts) = "(" ++ con ++ " " ++ unwords (map show ts) ++ ")"

  show (ThunkCall f ts) = "(" ++ f ++ " " ++ unwords (map show ts) ++ ")"
  show (ThunkTerm t) = show t
  show (ThunkRecLet th deps callFn callArgs) =
    "let <x> = <" ++ show th ++ " | " ++ unwords deps ++ "> in " ++
    callFn ++ " " ++ unwords (map show callArgs) ++ " <x>"

instance Show ClosedTerm where
  show (ConstrApp "Zero" []) = "0"
  show (ConstrApp "Suc" [t]) = case readMaybe (show t) :: Maybe Int of
    Just n -> show (1 + n)
    Nothing -> "(Suc " ++ show t ++ ")"
  show (ConstrApp "Nil" []) = "[]"
  show (ConstrApp "Cons" [l, r]) = "(" ++ show l ++ " :: " ++ show r ++ ")"
  show (ConstrApp i []) = i
  show (ConstrApp i ts) = "(" ++ i ++ " " ++ unwords (map show ts) ++ ")"