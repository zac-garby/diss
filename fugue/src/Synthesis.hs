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
import Env
import Infer

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

data RecursivePart =
  -- recursiveBinding, recFnName, [recArgs...]
  Recurse Ident Ident [Ident]

  -- no recursion
  | NoRecurse
  deriving Show

type SynthFunctions = [(Ident, SynthFunction)]

data Thunk
  = ThunkConstr Ident [Thunk] -- a constructor call
  | ThunkRecurse Ident [ClosedTerm] -- a (recursive) function call
  deriving Show

-- a ClosedTerm is similar to a Term, but is always a fully-evaluated value.
-- furthermore, it contains only values that can be used as synthesis examples,
-- and so doesn't allow abstractions, etc. it can always be represented as
-- the application of some constructor to zero or more arguments, also closed terms.
data ClosedTerm = ConstrApp Ident [ClosedTerm]
  deriving (Show, Eq)

-- an Arg represents an argument of an example, and is either a fully-evaluated term Val,
-- or a thunk. If it is a thunk, it is a partially-evaluated term, along
-- with the name of the function whose definition the evaluation is blocked by.
data Arg = Val ClosedTerm | Thunk Thunk Ident

instance Show Arg where
  show (Val t) = show t
  show (Thunk t i) = "<" ++ i ++ " | " ++ show t ++ ">"

data Example = Eg [Arg] ClosedTerm
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
        -- fns' = [ (name, assembleFn fn) | (name, fn) <- fns ]
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
        problem = uncurry (upToDepth 16 ... synth fnName) (unfoldFnTy goal)

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

  debug $ "* synthesising " ++ name ++ " : " ++ intercalate " -> " (map show argTypes) ++ " -> " ++ show ret

  egs <- asks examples
  forM_ egs $ \(Eg ins out) -> debug $ "  { " ++ unwords (map show ins) ++ " -> " ++ show out ++ " }"

  guard $ not (null egs)

  if d < dMax then do
    args <- forM argTypes $ \t -> do
      name <- fresh
      return (name, t)

    f <- local (\c -> c { depth = d + 1 }) $
      try [ synthTrivial args ret name
          , synthRecurse args ret name
          , synthCommonConstr args ret name
          , synthSplit args ret name ]

    defineFunction name f

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
    -- return $ Function args retType (Hole 0) []
    return $ Fn { args = args
                , ret = retType
                , body = SynthHole
                , egs = [] }
  else
    fail "there are examples so this rule doesn't apply"

-- synthOne :: SynthCase
-- synthOne args retType _ = do
--   debug ": trying synth one eg"

--   egs <- asks examples
--   case egs of
--     [ Eg _ out ] -> do
--       debug "done: synth one eg"
--       return $ Function args retType _ []
--     _doesNotApply -> fail "there are either no examples or more than one"

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
synthCommonConstr args retType _ = do
  debug ": trying common constr"

  egs <- asks examples

  case sharedConstr egs of
    Nothing -> fail "the constructor is not shared"
    Just con -> do
      egs <- asks examples

      Forall _ conTy <- lookupType' con
      let (conArgTys, _) = unfoldFnTy (specialiseConstructor conTy retType)
          (conArgs, d) = unzip [ (args, deconstruct' o) | Eg args o <- egs ]
          (cons, d') = unzip d
          d'T = transpose d'
          conEgs = [ zipWith Eg conArgs d | d <- d'T ]
          (argNames, argTypes) = unzip args

      names <- forM (zip conArgTys conEgs) $ \(conArgTy, egs) -> do
        fnName <- fresh
        f <- withExamples egs (synth fnName argTypes conArgTy)
        return (fnName, f)

      debug "done: common constr"
      return $ Fn { args = args
                        , ret = retType
                        , body = SynthConstr con [ (n, argNames) | (n, _) <- names ]
                        , egs = egs }

synthSplit :: [(Ident, Type)] -> Type -> Ident -> Synth SynthFunction
synthSplit args retType name = do
  debug ": trying case split"

  try [ synthSplitOn i args retType name
      | i <- [0..length args - 1] ]

synthSplitOn :: Int -> [(Ident, Type)] -> Type -> Ident -> Synth SynthFunction
synthSplitOn splitOn args retType _ = do
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
              examples =
                     [ Eg (ins ++ map Val conArgs') out
                     | Eg ins out <- egs
                     , let (con', conArgs') = deconstruct' (fromVal (ins !! splitOn))
                     , con == con']

          -- make a new function name to synthesise this case inside
          caseFnName <- fresh
          withExamples examples (synth caseFnName (map snd allArgs) retType)

          return ( con
                 , map fst constructorArgs
                 , caseFnName
                 , map fst allArgs )

        let body = SynthCase splitArg cases
        debug $ "done: split on arg " ++ show splitOn
        return $ Fn { args = args
                          , ret = retType
                          , body = body
                          , egs = egs }

      Nothing -> fail "non-datatype or undefined"
    _ -> fail "can't split on non-ADT"

synthRecurse :: [(Ident, Type)] -> Type -> Ident -> Synth SynthFunction
synthRecurse args retType name = do
  debug ": trying case split"

  try [ synthRecurseOn i args retType name
      | i <- [0..length args - 1] ]

synthRecurseOn :: Int -> [(Ident, Type)] -> Type -> Ident -> Synth SynthFunction
synthRecurseOn splitOn args retType fnName = do
  debug $ "- trying recurse on arg " ++ show splitOn ++ "; fnName = " ++ fnName
  egs <- asks examples
  dts <- asks dataTypes

  -- we cannot split on an argument which is not fully evaluated. all example arguments
  -- must be fully evaluated values
  guard $ not (egHasThunk egs)

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

          caseFnName <- fresh
          recursiveCallName <- fresh

          let recursiveArgs = forM args $ \(_, t) -> chooseRecursiveArg t constructorArgs
              allArgs = args ++ constructorArgs
              constructorParams = map fst constructorArgs

          let (recursivePart, bodyArgs) =
                case recursiveArgs of
                  Nothing -> (NoRecurse, allArgs)
                  Just recursiveArgs ->
                    let allArgs' = allArgs ++ [(recursiveCallName, retType)]
                    in (Recurse recursiveCallName fnName recursiveArgs, allArgs')

          -- make a new function name to synthesise this case inside
          return ( (caseFnName, allArgs, recursivePart)
                 , (con, constructorParams, bodyArgs) )

        -- let body = Case (Var splitArg) (map snd cases)
        let body = SynthRecurse splitArg
              [ (constrName, conArgs, recursivePart, caseFnName, map fst bodyArgs)
              | ((caseFnName, allArgs, recursivePart), (constrName, conArgs, bodyArgs)) <- cases
              , let fnArgs = map fst bodyArgs ]

        let fn = Fn { args = args
                    , ret = retType
                    , body = body
                    , egs = egs }

        -- attempt to actually synthesise the auxiliary functions
        -- TODO: 'withFunction fnName fn' needs to be able to see
        withFunction fnName fn $ forM_ cases $ \((caseFnName, allArgs, recursivePart), (con,conParams,_)) -> do
          e <- asks env

          case recursivePart of
            Recurse recCall fnName recParams -> do
              let fnType = finalise $ foldr (-->) retType (map snd allArgs ++ [retType])
                  lookupArg args name = fromJust $ lookup name args
                  --thunk = Thunk (ThunkRecurse fnName recParams) fnName
                  examples = [ Eg (ins ++ map Val conArgs ++ [thunk]) out
                             | Eg ins out <- egs
                             , let (con', conArgs) = deconstruct' (fromVal (ins !! splitOn))
                             , con == con'
                             , let recArgs = map (lookupArg (zip conParams conArgs)) recParams
                             , let thunk = Thunk (ThunkRecurse fnName recArgs) fnName ]

              withExamples examples $ synth caseFnName (map snd allArgs ++ [retType]) retType

            NoRecurse -> do
              let examples = [ Eg (ins ++ map Val conArgs) out
                              | Eg ins out <- egs
                              , let (con', conArgs) = deconstruct' (fromVal (ins !! splitOn))
                              , con == con' ]

              withExamples examples $ synth caseFnName (map snd allArgs) retType

        debug $ "done: recurse on arg " ++ show splitOn
        return fn

      Nothing -> fail "non-datatype or undefined"
    _nonADT -> fail "can't recurse on non-ADT"

chooseRecursiveArg :: Type -> [(Ident, Type)] -> Maybe Ident
chooseRecursiveArg t consArgs = fst <$> find (\(_, t') -> t == t') consArgs

debug :: String -> Synth ()
--debug _ = return ()
debug s = do
  d <- asks depth
  let prefix = concat (replicate d "* ")
  traceM $ prefix ++ s

replace :: Int -> a -> [a] -> [a]
replace 0 x (y:ys) = x:ys
replace n x (y:ys) = y : replace (n-1) x ys
replace _ _ [] = undefined

hasVal :: Arg -> ClosedTerm -> Bool
hasVal (Val v) t = v == t
hasVal (Thunk _ _) t = False

fromVal :: Arg -> ClosedTerm
fromVal (Val v) = v
fromVal _ = undefined

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
defineFunction :: Ident -> SynthFunction -> Synth ()
defineFunction name fn = tell [(name, fn)]

-- like defineFunction, but also exposes the function to a further
-- synthesis problem to be (potentially) called in its definition.
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

{-
try' ::  Monad m => [MaybeT m a] -> MaybeT m a
try' [] = fail "exhausted all possibilities"
try' (x:xs) = let x' = runMaybeT x in MaybeT $ do
  m <- x'
  case m of
    Nothing -> runMaybeT (try xs)
    Just r -> return (Just r)
-}

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

withExamples :: [Example] -> Synth a -> Synth a
withExamples egs = local (\l -> l { examples = egs })

updateThunk :: Ident -> SynthFunction -> Thunk -> Thunk
updateThunk i fn (ThunkConstr n ts) = ThunkConstr n (map (updateThunk i fn) ts)
updateThunk i fn th@(ThunkRecurse n args)
  | i == n = undefined
  | otherwise = th

applyBody :: SynthFunction -> [Thunk] -> Thunk
applyBody (Fn arguments _ body _) args = case body of
  SynthVar x -> get x
  SynthConstr s x0 -> undefined
  SynthCase s x0 -> undefined
  SynthRecurse s x0 -> undefined
  SynthHole -> undefined
  where params = map fst arguments
        get x = fromJust $ lookup x (zip params args)

fnNames = [ "fn" ++ show i | i <- [0..] ]

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

allCalledBy :: Ident -> Functions -> [Ident]
allCalledBy x fns = go x fns []
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
  where used = allCalledBy x fns

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
  , Eg [toVal' ([1] :: [Int])] (toClosed' ([1, 1] :: [Int]))
  , Eg [toVal' ([1, 2] :: [Int])] (toClosed' ([1, 1, 2, 2] :: [Int])) ]
