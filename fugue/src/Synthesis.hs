{-# LANGUAGE StrictData #-}

module Synthesis
  ( Context (..)
  , Function (..)
  , Functions (..)
  , SynthFunction (..)
  , SynthFunctions (..)
  , Arg (..)
  , Example (..)
  , SynthState (..)
  , Synth (..)
  , ClosedTerm (..)

  , synthesise
  , removeRedundant
  , unwindFrom

  , test
  , testStutter
  , Thunk (..)
  , Body (..)
  , applyBody
  , unifyThunk
  ) where

import Data.Maybe
import Data.List
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

data Context = Context
  { examples :: [Example]
  , depth :: Int
  , env :: Env
  , dataTypes :: DataTypes
  , fns :: SynthFunctions }

data SynthFunction = Fn
       { args :: [(Ident, Type)]
       , ret :: Type
       , body :: Body
       , egs :: [Example] }
  deriving Show

data Body
  = SynthVar Ident

  -- constrName [(fnName, [fnArgs...])]
  | SynthConstr Ident [(Ident, [Ident])]

  -- splitArg [(constrName, [conArgs...], fnName, [fnArgs...])]
  | SynthCase Ident [(Ident, [Ident], Ident, [Ident])]

  -- recurseArg [(constrName, [conArgs...], recursivePart, bodyName, [bodyArgs...])]
  | SynthRecurse Ident [(Ident, [Ident], RecursivePart, Ident, [Ident])]

  -- a hole
  | SynthHole
  deriving Show

data RecursivePart
  -- recursiveBinding, recFnName, [recArgs...]
  = Recurse Ident Ident [Ident]

  -- no recursion
  | NoRecurse
  deriving Show

type SynthFunctions = [(Ident, SynthFunction)]

data Thunk
  = ThunkConstr Ident [Thunk] -- a constructor call
  | ThunkCall Ident [ClosedTerm] -- a (maybe recursive) function call
  | ThunkRecLet Thunk [Ident] Ident [ClosedTerm]-- let x = <th | deps> in f' a' b' c' {x}
  | ThunkTerm ClosedTerm

instance Show Thunk where
  show (ThunkConstr "Zero" []) = "0"
  show (ThunkConstr "Suc" [t]) = case readMaybe (show t) :: Maybe Int of
    Just n -> show (1 + n)
    Nothing -> "(Suc " ++ show t ++ ")"
  show (ThunkConstr con []) = con
  show (ThunkConstr con ts) = "(" ++ con ++ " " ++ unwords (map show ts) ++ ")"
  show (ThunkCall f ts) = "(" ++ f ++ " " ++ unwords (map show ts) ++ ")"
  show (ThunkTerm t) = show t
  show (ThunkRecLet th deps callFn callArgs) =
    "let <x> = <" ++ show th ++ " | " ++ unwords deps ++ "> in " ++
    callFn ++ " " ++ unwords (map show callArgs) ++ " <x>"

-- a ClosedTerm is similar to a Term, but is always a fully-evaluated value.
-- furthermore, it contains only values that can be used as synthesis examples,
-- and so doesn't allow abstractions, etc. it can always be represented as
-- the application of some constructor to zero or more arguments, also closed terms.
data ClosedTerm = ConstrApp Ident [ClosedTerm]
  deriving Eq

instance Show ClosedTerm where
  show (ConstrApp "Zero" []) = "0"
  show (ConstrApp "Suc" [t]) = case readMaybe (show t) :: Maybe Int of
    Just n -> show (1 + n)
    Nothing -> "(Suc " ++ show t ++ ")"
  show (ConstrApp "Nil" []) = "[]"
  show (ConstrApp "Cons" [l, r]) = "(" ++ show l ++ " :: " ++ show r ++ ")"
  show (ConstrApp i []) = i
  show (ConstrApp i ts) = "(" ++ i ++ " " ++ unwords (map show ts) ++ ")"

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

data SynthState = SynthState
  { newNames :: [Ident]
  , maxDepth :: Int }
  deriving Show

type Synth = RWST Context SynthFunctions SynthState Maybe

type SynthImpl = [(Ident, Type)] -> Type -> Ident -> Synth SynthFunction

synthesiseInEnvironment ::
     Environment
  -> Ident
  -> Type
  -> [Example]
  -> Maybe (Ident, Function, Functions)
synthesiseInEnvironment e = synthesise (fromEnvironment e) (types e)

synthesise ::
     Env
  -> DataTypes
  -> Ident
  -> Type
  -> [Example]
  -> Maybe (Ident, Function, Functions)
synthesise env dts fnName goal egs = case runSynth defaultState ctx problem of
  Nothing -> Nothing
  Just (fn, fns) ->
    let fn' = assembleFn fn
        fns' = removeRedundant fnName (unwindFrom fnName fns)
    in Just (fnName, fn', fns')
  where ctx = Context {
          examples = egs
        , depth = 0
        , env = env
        , fns = []
        , dataTypes = dts }
        defaultState = SynthState {
          newNames = allVars
        , maxDepth = 0 }
        problem = uncurry (upToDepth 8 ... synth fnName) (unfoldFnTy goal)

runSynth :: SynthState -> Context -> Synth a -> Maybe (a, SynthFunctions)
runSynth s c p = case runRWST p c s of
  Nothing -> Nothing
  Just (a, _, fns) -> Just (a, fns)

upToDepth :: Int -> Synth a -> Synth a
upToDepth toDepth f = do
  try [ synthWithMaxDepth d | d <- [1..toDepth] ]
  where synthWithMaxDepth d = do
          modify $ \s -> s { maxDepth = d }
          debug $ "## synthesising with max depth " ++ show d ++ " ##"
          f

-- synthesises a function of the given argument and return types, and
-- defines it in the Writer under a given identifier. also returns the
-- function for convenience
synth :: Ident -> [Type] -> Type -> Synth SynthFunction
synth name argTypes ret = do
  d <- asks depth
  dMax <- gets maxDepth
  egs <- asks examples
  fns <- asks fns

  debug $ "* synthesising " ++ name ++ " : " ++ intercalate " -> " (map show argTypes) ++ " -> " ++ show ret ++ " with fns: " ++ unwords (map fst fns)

  -- TODO: so, generating holes is really useful obviously, but it has a few
  -- issues. most notably, it often leads to less efficient solutions because
  -- the synthesiser gets "lazy" (not in that way).
  --
  -- possible solutions:
  --  * generate multiple solutions; select the "best" one
  --     - type Synth a = RWST Context SynthFunctions SynthState (MaybeT [a])?
  --  * give a penalty for using holes
  --     - this would be ~equivalent to "holding" a hole solution for a few
  --       depth iterations, and if nothing is found in n iterations the hole
  --       solution is accepted.
  --  * disallow holes / make them a user option
  guard $ not (null egs)

  if d < dMax then do
    fnArgs <- forM argTypes $ \t -> do
      name <- fresh
      return (name, t)

    f <- local (\c -> c { depth = d + 1 }) $ do
      egs' <- updateExamplesFully egs

      forM_ egs' $ \(Eg ins out) ->
        debug $ "  { " ++ intercalate ", " (map show ins) ++ " -> " ++ show out ++ " }"

      withExamples egs' $ try
          [ --synthNoEgs args ret name
            synthUnify fnArgs ret name
          , synthTrivial fnArgs ret name
          , synthRecurse fnArgs ret name
          , synthCommonConstr fnArgs ret name
          , synthSplit fnArgs ret name ]

    emitFunction name f
    debug $ "synthesis complete for " ++ name ++ " " ++ unwords (map fst (args f)) ++ ": " ++ show (body f)

    return f
  else do
    debug "  : failed: out of depth"
    fail "out of depth"

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
synthTrivial args retType _ = do
  debug ": trying synth trivial"

  egs <- asks examples

  go egs 0
  where go egs n
          | n >= length args = fail "none of the arguments matched"
          | all (\(Eg egArgs egRes) -> egArgs !! n `hasVal` egRes) egs = do
            debug "done: synth trivial"
            return $ Fn { args = args
                        , ret = retType
                        , body = SynthVar (fst $ args !! n)
                        , egs = egs }
          | otherwise = go egs (n + 1)

{-
In theory, could give visibility to the parent function in the sub-syntheses in
  other problems too (including common constr, case-splits, etc). It may be best
  to limit it to just the explicit recursion introductions though.
-}
synthCommonConstr :: SynthImpl
synthCommonConstr args retType fnName = do
  debug ": trying common constr"

  egs <- asks examples

  case sharedConstr egs of
    Nothing -> fail "the constructor is not shared"
    Just con -> do
      egs <- asks examples

      Forall _ conTy <- lookupType' con
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
synthSplit args retType name = do
  debug ": trying case split"

  try [ synthSplitOn i args retType name
      | i <- [0..length args - 1] ]

synthSplitOn :: Int -> SynthImpl
synthSplitOn splitOn args retType fnName = do
  debug $ "- trying split on arg " ++ show splitOn
  egs <- asks examples
  dts <- asks dataTypes

  -- we cannot split on an argument which is not fully evaluated
  guard (not (argIsThunk splitOn egs))

  let (splitArg, splitTy) = args !! splitOn
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
          let allArgs = args ++ constructorArgs

          -- make a new function name to synthesise this case inside
          caseFnName <- fresh

          return ( con
                 , map fst constructorArgs
                 , caseFnName
                 , allArgs )

        let body = SynthCase splitArg [ (con, conArgs, caseFn, map fst allArgs)
                                      | (con, conArgs, caseFn, allArgs) <- cases ]
        let fn = Fn { args = args
                    , ret = retType
                    , body = body
                    , egs = egs }

        withFunction fnName fn $ traverseContinuation cases $ \(con, conArgs, caseFn, allArgs) c -> do
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
synthRecurse args retType name = do
  debug ": trying recursion split"

  try [ synthRecurseOn i args retType name
      | i <- [0..length args - 1] ]

synthRecurseOn :: Int -> SynthImpl
synthRecurseOn splitOn args retType fnName = do
  egs <- asks examples
  dts <- asks dataTypes

  -- we cannot split on an argument which is not fully evaluated. all example arguments
  -- must be fully evaluated values, for simplicity. strictly speaking, only the argument
  -- being split on needs to be a non-thunk, but in most cases it won't be useful to
  -- split when there is already a thunk so we ignore these cases.
  guard $ not (egHasThunk egs)

  let (splitArg, splitTy) = args !! splitOn
  case splitTy of
    TyConstr dtName dtArgs -> case lookup dtName dts of
      Just (DataType tyArgs dtConstrs) -> do
        let s = zip tyArgs dtArgs :: Subst
            concreteConstructors = [ DataConstructor i (map (sub s) ts)
                                   | DataConstructor i ts <- dtConstrs ]

        -- for each constructor in the datatype, see if we can find recursive arguments
        -- consisting of parts of the constructor. either way, keep track of whether or
        -- not we want to recurse for this case, and store all relevant info/names for
        -- later synthesis.
        cases <- forM concreteConstructors $ \(DataConstructor con constructorArgTypes) -> do
          constructorArgs <- forM constructorArgTypes $ \ty -> do
            name <- fresh
            return (name, ty)

          caseFnName <- fresh
          recursiveCallName <- fresh

          -- right now, the first usable constructor argument is selected. this is not
          -- always optimal (e.g. in the case of trees), so this should be changed in
          -- the future to attempt synthesis on each one in turn.
          let recursiveArgs = forM args $ \(_, t) -> chooseRecursiveArg t constructorArgs
              allArgs = args ++ constructorArgs
              constructorParams = map fst constructorArgs

          let (recursivePart, bodyArgs) =
                case recursiveArgs of
                  Nothing -> (NoRecurse, allArgs)
                  Just recursiveArgs ->
                    let allArgs' = allArgs ++ [(recursiveCallName, retType)]
                    in (Recurse recursiveCallName fnName recursiveArgs, allArgs')

          return (caseFnName, allArgs, recursivePart, con, constructorParams, bodyArgs)

        -- the body of the entire recursive function being synthesised here is a case
        -- split, where each case either performs a recursive call or doesn't.
        let body = SynthRecurse splitArg
              [ (constrName, conArgs, recursivePart, caseFnName, map fst bodyArgs)
              | (caseFnName, allArgs, recursivePart, constrName, conArgs, bodyArgs) <- cases
              , let fnArgs = map fst bodyArgs ]

        let fn = Fn { args = args
                    , ret = retType
                    , body = body
                    , egs = egs }

        debug $ "recursive body = " ++ show body

        -- with this function (the recursive one being defined - "fnName") temporarily added
        -- to the namespace, we synthesise each case in turn.
        withFunction fnName fn $
          traverseContinuation cases $ \(caseFnName, allArgs, recursivePart, con, conParams, _) c -> do
            e <- asks env

            fn <- case recursivePart of
              Recurse recCall fnName recParams -> do
                -- when a recursive call is made, we need to construct a thunk to pass as
                -- an example to the sub-function.
                let fnType = finalise $ foldr (-->) retType (map snd allArgs ++ [retType])
                    lookupArg args name = fromJust $ lookup name args
                    examples = [ Eg (ins ++ map Val conArgs ++ [thunk]) out
                               | Eg ins out <- egs
                               , let (con', conArgs) = deconstruct' (fromVal (ins !! splitOn))
                               , con == con'
                               , let recArgs = map (lookupArg (zip conParams conArgs)) recParams
                               , let thunk = Thunk (ThunkCall fnName recArgs) [fnName] ]

                withExamples examples $ synth caseFnName (map snd allArgs ++ [retType]) retType

              NoRecurse -> do
                let examples = [ Eg (ins ++ map Val conArgs) out
                                | Eg ins out <- egs
                                , let (con', conArgs) = deconstruct' (fromVal (ins !! splitOn))
                                , con == con' ]

                withExamples examples $ synth caseFnName (map snd allArgs) retType

            withFunction caseFnName fn c

        debug $ "done: recurse on arg " ++ show splitOn
        return fn

      Nothing -> fail "non-datatype or undefined"
    _nonADT -> fail "can't recurse on non-ADT"

chooseRecursiveArg :: Type -> [(Ident, Type)] -> Maybe Ident
chooseRecursiveArg t consArgs = fst <$> find (\(_, t') -> t == t') consArgs

synthUnify :: SynthImpl
synthUnify args retType fnName = do
  debug ": trying synth unify"

  try [ synthUnifyOn i args retType fnName
      | i <- [0..length args - 1] ]

synthUnifyOn :: Int -> SynthImpl
synthUnifyOn i args retType fnName = do
  egs <- asks examples

  let insAt_i = transpose (map ins egs) !! i
      outs = map out egs

  debug $ " - trying unify on " ++ show i ++ "; insAt_i = " ++ show insAt_i ++ "; outs = " ++ show outs

  case concat <$> zipWithM (unifyArg fnName) outs insAt_i of
    Just unifyEgs -> do
      debug $ " - can unify: " ++ show unifyEgs
      -- unifyEgs at this point is the set of examples we should add.
      -- we also need to update the existing examples, replacing the thunks with
      -- their proper values.
      let egs' = [ updateThunkCall fnName o' eg
                 | (eg, Eg _ o') <- zip egs unifyEgs ]
                 ++ unifyEgs -- ?

      withExamples egs' $ synth fnName (map snd args) retType
    Nothing -> fail "couldn't unify"

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
unifyArg i _ _ = Nothing -- TODO: should this be Just [] ?

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
debug s = do
  d <- asks depth
  let prefix = concat (replicate d "* ")
  traceM $ prefix ++ s

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
argIsThunk n ((Eg args _):_) = isThunk (args !! n)

egHasThunk :: [Example] -> Bool
egHasThunk [] = False
egHasThunk ((Eg args _):_) = any isThunk args

withSynth :: Ident -> [Type] -> Type -> Synth a -> Synth a
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

try :: Monoid w => [RWST r w s Maybe a] -> RWST r w s Maybe a
try [] = fail "exhausted all possibilities"
try (x:xs) = rwsT $ \r s -> case runRWST x r s of
  Nothing -> runRWST (try xs) r s
  Just (a, s', w') -> Just (a, s', w')

assembleBody :: Body -> Expr
assembleBody (SynthVar x) = Var x
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
assembleBody SynthHole = Hole 0

assembleRecursiveBody :: RecursivePart -> Expr -> Expr
assembleRecursiveBody (Recurse b recFn recArgs) body
  = Let b (applyManyIdents (recFn : recArgs)) body
assembleRecursiveBody NoRecurse body = body

assemble :: SynthFunction -> Expr
assemble (Fn args _ body _) = foldr (Abs . fst) (assembleBody body) args

assembleFn :: SynthFunction -> Function
assembleFn (Fn args ret body egs) = Function args ret (assembleBody body) egs

getType :: SynthFunction -> Scheme
getType (Fn args ret _ _) =
  let argTypes = map snd args
  in finalise $ foldr (-->) ret argTypes

collapse :: SynthFunctions -> Expr -> Expr
collapse fns app@(App f x) = case unfoldApp app of
  (Var f', xs') -> case lookup f' fns of
    Nothing -> App (collapse fns f) (collapse fns x)
    Just fn -> app
  _ -> app
collapse _ _ = error "not yet implemented collapse for this expression"

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
lookupType' x = fromJust <$> lookupType x

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

  r <- forM insT $ \c -> case canUpdateAny c has of
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
        updateThunks updatable (Thunk t []:xs) = (Val (thunkToTerm' t) :) <$> updateThunks updatable xs
        updateThunks updatable (Thunk t fs:xs) = do
          (t', fs') <- updateThunk t (fs `intersect` updatable)
          rest <- updateThunks updatable xs
          return (Thunk t' fs' : rest)
        updateThunks updatable (x:xs) = (x:) <$> updateThunks updatable xs

applyBody :: [Ident] -> Body -> [ClosedTerm] -> (Thunk, [Ident])
applyBody params body args = case body of
    SynthVar x ->
      (ThunkTerm $ get x, [])

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
            fromJust $ find (\(con', _, _, _, _) -> con == con') cases
          allArgs = zip (params ++ conParams) (args ++ conArgs)
      in case recPart of
        Recurse recBinding recCall recArgs ->
          let recArgVals = map (getIn allArgs) recArgs
              fnArgVals = map (getIn allArgs) (init fnArgs)
              th = ThunkRecLet (ThunkCall recCall recArgVals) [recCall] fnName fnArgVals
          in (th, [recCall])
        NoRecurse ->
          let fnArgVals = map (getIn allArgs) fnArgs
          in (ThunkCall fnName fnArgVals, [fnName])

    SynthHole -> undefined
  where getIn as x = case lookup x as of
          Just v -> v
          Nothing -> error $ "getIn: couldn't find " ++ x ++ " in " ++ show (map fst as)
        get = getIn (zip params args)
        call f xs = ThunkCall f (map get xs)

updateThunkWith :: Ident -> SynthFunction -> Thunk -> (Thunk, [Ident])
updateThunkWith fnName fn@(Fn args _ body _) th = case th of
  ThunkConstr s ths ->
    let (thunks, deps) = unzip (map (updateThunkWith fnName fn) ths)
    in (ThunkConstr s thunks, nub $ concat deps)

  ThunkCall callFn callArgs ->
    if callFn == fnName then
      applyBody (map fst args) body callArgs
    else
      (th, [callFn])

  ThunkTerm t -> (th, [])

  ThunkRecLet th' deps callFn callArgs ->
    if fnName `elem` deps then
      case updateThunkWith fnName fn th' of
        (nonThunk, []) -> (ThunkCall callFn (callArgs ++ [thunkToTerm' nonThunk]), [callFn])
        (th'', deps') -> (ThunkRecLet th'' deps' callFn callArgs, deps')
      -- this should end up in one of two cases:
      --  * the application results in a thunk which can be turned into a closed term,
      --    in which case we can return a ThunkCall and move onto the inner call of callFn
      --  * further evaluation is required to reach this point
    else
      (th, deps)

updateThunk :: Thunk -> [Ident] -> Synth (Thunk, [Ident])
updateThunk th deps = do
  fns <- asks fns
  depFns <- mapM lookupFn deps
  case sequence depFns of
    Nothing -> error "updateThunk called with insufficient functions"
    Just sfs -> return $
      foldr (\(fnName, fn) (th, ds) -> updateThunkWith fnName fn th)
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

unfoldFnTy :: Type -> ([Type], Type)
unfoldFnTy (TyConstr "->" [a, b]) =
  let (rest, ret) = unfoldFnTy b
  in (a : rest, ret)
unfoldFnTy t = ([], t)

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

type Functions = [(Ident, Function)]

type Unwind = S.State Functions

unwindFrom :: Ident -> SynthFunctions -> Functions
unwindFrom x fns = S.execState (unwindFn x) fns'
  where fns' = [ (name, assembleFn fn) | (name, fn) <- fns ]

unwindFn :: Ident -> Unwind ()
unwindFn f = do
  Function args ret body egs <- lookupU' f
  body' <- unwind body
  S.modify (insertFn f (Function args ret body' egs))

unwind :: Expr -> Unwind Expr
unwind (Var x) = do
  fn <- lookupU x
  case fn of
    Just Function{ fnBody = body, fnArgs = [] } -> unwind body
    _ -> return $ Var x
unwind app@(App e1 e2) = case unfoldApp app of
    (Var x, args) -> do
      fn <- lookupU x
      case fn of
        Just fn -> if canInline x fn then inline x args else app'
        Nothing -> app'
    _ -> app'
  where app' = App <$> unwind e1 <*> unwind e2
unwind (Abs x e) = Abs x <$> unwind e
unwind (Let x e1 e2) = Let x <$> unwind e1 <*> unwind e2
unwind (LetRec x e1 e2) = LetRec x <$> unwind e1 <*> unwind e2
unwind (If e1 e2 e3) = If <$> unwind e1 <*> unwind e2 <*> unwind e3
unwind (Case e cases) = do
  cases' <- forM cases $ \(x, xs, b) -> do
    b' <- unwind b
    return (x, xs, b')

  Case <$> unwind e <*> return cases'
unwind (LitInt n) = return $ LitInt n
unwind (LitList xs) = LitList <$> mapM unwind xs
unwind (LitTuple xs) = LitTuple <$> mapM unwind xs
unwind (LitChar c) = return $ LitChar c
unwind (TypeSpec e t) = TypeSpec <$> unwind e <*> return t
unwind (Hole n) = return $ Hole n

inline :: Ident -> [Expr] -> Unwind Expr
inline f args = do
  unwindFn f
  Function fnArgs _ fnBody _ <- lookupU' f
  let arguments = zip (map fst fnArgs) args
  return $ subExpr arguments fnBody

lookupU :: Ident -> Unwind (Maybe Function)
lookupU f = fmap (lookup f) S.get

lookupU' :: Ident -> Unwind Function
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

removeRedundant :: Ident -> Functions -> Functions
removeRedundant x fns = filter ((`elem` used) . fst) fns
  where used = allFunctionsUsedBy x fns

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

traverseContinuation :: Monad m => [a] -> (a -> m [b] -> m [b]) -> m [b]
traverseContinuation xs f = foldr f (return []) xs

test'' env = synthesiseInEnvironment env "head" (tyList tyInt --> tyInt)
  [ Eg [toVal' ([1, 2] :: [Int])] (toClosed' (1 :: Int))
  , Eg [toVal' ([0, 2, 3] :: [Int])] (toClosed' (0 :: Int)) ]

test' env = synthesiseInEnvironment env "double" (tyInt --> tyList tyInt --> tyList tyInt)
  [ Eg [toVal' (0 :: Int), toVal' ([1] :: [Int])] (toClosed' ([0, 0, 1] :: [Int]))
  , Eg [toVal' (2 :: Int), toVal' ([] :: [Int])] (toClosed' ([2, 2] :: [Int])) ]

test env = synthesiseInEnvironment env "is_one" (tyInt --> tyBool)
  [ Eg [toVal' (0 :: Int)] (toClosed' False)
  , Eg [toVal' (1 :: Int)] (toClosed' True)
  , Eg [toVal' (2 :: Int)] (toClosed' False) ]

testStutter env = synthesiseInEnvironment env "stutter" (tyList tyInt --> tyList tyInt)
  [ Eg [toVal' ([] :: [Int])] (toClosed' ([] :: [Int]))
  --, Eg [toVal' ([1] :: [Int])] (toClosed' ([1, 1] :: [Int]))
  , Eg [toVal' ([1, 2] :: [Int])] (toClosed' ([1, 1, 2, 2] :: [Int])) ]
