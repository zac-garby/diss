module Synthesis where

import Data.Maybe
import Data.List
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Control.Monad.Trans.Maybe
import Debug.Trace

import Parser
import Compiler
import Types
import Env
import Infer

data Context = Context
  { env :: Environment
  , examples :: [Example] }

data Function = Function
  { args :: [(Ident, Type)]
  , ret :: Type
  , body :: Expr
  , egs :: [Example] }
  deriving Show

type Functions = [(Ident, Function)]

-- an Arg represents an argument of an example, and is either a fully-evaluated term Val,
-- or a thunk. If it is a thunk, it is a partially-evaluated term, along
-- with the name of the function whose definition the evaluation is blocked by.
data Arg = Val Term | Thunk Term Ident

instance Show Arg where
  show (Val t) = show t
  show (Thunk t i) = "<" ++ i ++ " | " ++ show t ++ ">"

data Example = Eg [Arg] Term
  deriving Show

data SynthState = SynthState
  { newNames :: [Ident]
  , functions :: Functions
  , depth :: Int }
  deriving Show

type Synth = MaybeT (StateT SynthState (Reader Context))

synthesise :: Environment -> Type -> [Example] -> Maybe (Ident, Functions)
synthesise env goal egs =
  let r = runReader (runStateT (runMaybeT (uncurry synth (unfoldFnTy goal)))
                                (SynthState allVars [] 16)) ctx
  in case r of
    (Nothing, _) -> Nothing
    (Just i, SynthState { functions = fns }) -> Just (i, fns)
  where ctx = Context { env = env
                      , examples = egs }

synth :: [Type] -> Type -> Synth Ident
synth argTypes ret = do
  d <- gets depth
  guard $ d > 0
  modify $ \s -> s { depth = depth s - 1 }

  egs <- asks examples

  args <- forM argTypes $ \t -> do
    name <- fresh
    return (name, t)

  try [ synthNoEgs args ret
      , synthTrivial args ret
      , synthRecurse args ret
      , synthCommonConstr args ret
      , synthSplit args ret ]

synthNoEgs :: [(Ident, Type)] -> Type -> Synth Ident
synthNoEgs args retType = do
  egs <- asks examples

  if null egs then
    defineFunction $ Function args retType (Hole 0) []
  else
    exit

synthTrivial :: [(Ident, Type)] -> Type -> Synth Ident
synthTrivial args retType = do
  egs <- asks examples
  go egs 0
  where go egs n
          | n >= length args = exit
          | all (\(Eg egArgs egRes) -> egArgs !! n `hasVal` egRes) egs =
            defineFunction $ Function { args = args
                                      , ret = retType
                                      , body = Var (fst $ args !! n)
                                      , egs = egs }
          | otherwise = go egs (n + 1)

synthCommonConstr :: [(Ident, Type)] -> Type -> Synth Ident
synthCommonConstr args retType = do
  egs <- asks examples

  case sharedConstr egs of
    Nothing -> exit
    Just con -> do
      egs <- asks examples
      ts <- asks (terms . env)

      Forall _ conTy <- lookupType' con
      let (conArgTys, _) = unfoldFnTy (specialiseConstructor conTy retType)
          (conArgs, d) = unzip [ (args, deconstruct' o) | Eg args o <- egs ]
          (cons, d') = unzip d
          d'T = transpose d'
          conEgs = [ zipWith Eg conArgs d | d <- d'T ]
          (argNames, argTypes) = unzip args

      fns <- forM (zip conArgTys conEgs) $ \(conArgTy, egs) -> do
        withExamples egs (synth argTypes conArgTy)

      let body = applyMany $ Var con
                 : [ applyMany $ Var fn : map Var argNames | fn <- fns ]

      defineFunction $ Function { args = args
                                , ret = retType
                                , body = body
                                , egs = egs }

synthSplit :: [(Ident, Type)] -> Type -> Synth Ident
synthSplit args retType = try [ synthSplitOn i args retType
                              | i <- [0..length args - 1] ]

synthSplitOn :: Int -> [(Ident, Type)] -> Type -> Synth Ident
synthSplitOn splitOn args retType = do
  egs <- asks examples
  e <- asks env

  guard (not (argIsThunk splitOn egs))
  let (splitArg, splitTy) = args !! splitOn

  case splitTy of
    TyConstr dtName dtArgs -> case lookupDataType dtName e of
      Just (DataType tyArgs dtConstrs) -> do
        let s = zip tyArgs dtArgs :: Subst
            dtConstrs' = [ DataConstructor i (map (sub s) ts)
                         | DataConstructor i ts <- dtConstrs ]

        cases <- forM dtConstrs' $ \(DataConstructor con conArgTys) -> do
          conArgs <- forM conArgTys $ \ty -> do
            name <- fresh
            return (name, ty)

          let allArgs = args ++ conArgs
              egs' = [ Eg (ins ++ map Val conArgs') out
                     | Eg ins out <- egs
                     , let (con', conArgs') = deconstruct' (fromVal (ins !! splitOn))
                     , con == con']

          g <- withExamples egs' (synth (map snd allArgs) retType)
          return (con, map fst conArgs, applyMany (map Var (g : map fst allArgs)))

        let body = Case (Var splitArg) cases
        defineFunction $ Function { args = args
                                  , ret = retType
                                  , body = body
                                  , egs = egs }

      Nothing -> fail "non-datatype or undefined"
    _ -> fail "can't split on non-ADT"

synthRecurse :: [(Ident, Type)] -> Type -> Synth Ident
synthRecurse args retType = try [ synthRecurseOn i args retType
                                | i <- [0..length args - 1] ]

synthRecurseOn :: Int -> [(Ident, Type)] -> Type -> Synth Ident
synthRecurseOn splitOn args retType = do
  egs <- asks examples
  e <- asks env

  guard (not (argIsThunk splitOn egs))
  let (splitArg, splitTy) = args !! splitOn

  fnName <- fresh

  case splitTy of
    TyConstr dtName dtArgs -> case lookupDataType dtName e of
      Just (DataType tyArgs dtConstrs) -> do
        let s = zip tyArgs dtArgs :: Subst
            dtConstrs' = [ DataConstructor i (map (sub s) ts)
                         | DataConstructor i ts <- dtConstrs ]

        cases <- forM dtConstrs' $ \(DataConstructor con conArgTys) -> do
          conArgs <- forM conArgTys $ \ty -> do
            name <- fresh
            return (name, ty)

          let allArgs = args ++ conArgs
              egs' = [ Eg (ins ++ map Val conArgs') out
                     | Eg ins out <- egs
                     , let (con', conArgs') = deconstruct' (fromVal (ins !! splitOn))
                     , con == con']
              recursiveCalls = [ applyMany (map Var (fnName : map fst recArgs))
                               | (i, (argName, argTy)) <- zip [0..] conArgs,
                                 argTy == splitTy,
                                 let recArgs = replace i (argName, splitTy) args ]

          g <- withExamples egs' (synth (map snd allArgs) retType)

          let app = applyMany (map Var (g : map fst allArgs) ++ recursiveCalls)

          return (con, map fst conArgs, app)

        let body = Case (Var splitArg) cases
        defineFunctionNamed fnName $
          Function { args = args
                   , ret = retType
                   , body = body
                   , egs = egs }

      Nothing -> fail "non-datatype or undefined"
    _ -> fail "can't split on non-ADT"

replace :: Int -> a -> [a] -> [a]
replace 0 x (y:ys) = x:ys
replace n x (y:ys) = y : replace (n-1) x ys
replace _ _ [] = undefined

hasVal :: Arg -> Term -> Bool
hasVal (Val v) t = v == t
hasVal (Thunk _ _) t = False

fromVal :: Arg -> Term
fromVal (Val v) = v
fromVal _ = undefined

isThunk :: Arg -> Bool
isThunk (Val _) = False
isThunk (Thunk _ _) = True

argIsThunk :: Int -> [Example] -> Bool
argIsThunk n [] = False
argIsThunk n ((Eg args _):_) = isThunk (args !! n)

defineFunction :: Function -> Synth Ident
defineFunction f = do
  name <- fresh
  defineFunctionNamed name f

defineFunctionNamed :: Ident -> Function -> Synth Ident
defineFunctionNamed n f = do
  modify $ \s@SynthState { functions = fns } -> s { functions = (n, f) : fns }
  return n

exit :: Monad m => MaybeT m a
exit = fail "ignored"

try ::  Monad m => [MaybeT m a] -> MaybeT m a
try [] = fail "exhausted all possibilities"
try (x:xs) = let x' = runMaybeT x in MaybeT $ do
  m <- x'
  case m of
    Nothing -> runMaybeT (try xs)
    Just r -> return (Just r)

assemble :: Function -> Expr
assemble (Function args _ body _) = foldr (Abs . fst) body args

collapse :: Functions -> Expr -> Expr
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
  ts <- asks (terms . env)
  return $ fmap fst (lookup x ts)

lookupType' :: Ident -> Synth Scheme
lookupType' x = fromJust <$> lookupType x

withExamples :: [Example] -> Synth a -> Synth a
withExamples egs = local (\l -> l { examples = egs })

fnNames = [ "fn" ++ show i | i <- [0..] ]

deconstruct :: Term -> Maybe (Ident, [Term])
deconstruct (CConstr i) = Just (i, [])
deconstruct (CApp l r) = do
  (i, ts) <- deconstruct l
  return (i, ts ++ [r])
deconstruct (CInt n) = deconstruct (intToSucs n)
deconstruct t = Nothing

deconstruct' :: Term -> (Ident, [Term])
deconstruct' = fromJust . deconstruct

intToSucs :: Int -> Term
intToSucs 0 = CConstr "Zero"
intToSucs n = CApp (CConstr "Suc") (intToSucs (n - 1))

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

type Unwind = State Functions

unwindFrom :: Ident -> Functions -> Functions
unwindFrom x = execState (unwindFn x)

unwindFn :: Ident -> Unwind ()
unwindFn f = do
  Function args ret body egs <- lookupU' f
  body' <- unwind body
  modify (insertFn f (Function args ret body' egs))

unwind :: Expr -> Unwind Expr
unwind (Var x) = do
  fn <- lookupU x
  case fn of
    Just Function{ body = body, args = [] } -> unwind body
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
lookupU f = fmap (lookup f) get

lookupU' :: Ident -> Unwind Function
lookupU' f = fmap fromJust (lookupU f)

canInline :: Ident -> Function -> Bool
canInline fnName Function{ body = body } = not (body `calls` fnName)

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
              Just Function{ body = body } ->
                let newCalls = calledBy body \\ (x : visited)
                in foldl' (\vs call -> go call fns vs) visited newCalls

removeRedundant :: Ident -> Functions -> Functions
removeRedundant x fns = filter ((`elem` used) . fst) fns
  where used = allCalledBy x fns

calls :: Expr -> Ident -> Bool
calls e i = i `elem` calledBy e

toVal :: Value a => a -> Arg
toVal = Val . toTerm

test' env = synthesise env (tyList tyInt --> tyInt)
  [ Eg [toVal ([1, 2] :: [Int])] (toTerm (1 :: Int))
  , Eg [toVal ([0, 2, 3] :: [Int])] (toTerm (0 :: Int)) ]

test env = synthesise env (tyInt --> tyList tyInt --> tyList tyInt)
  [ Eg [toVal (0 :: Int), toVal ([1] :: [Int])] (toTerm ([0, 0, 1] :: [Int]))
  , Eg [toVal (2 :: Int), toVal ([] :: [Int])] (toTerm ([2, 2] :: [Int])) ]

test'' env = synthesise env (tyInt --> tyBool)
  [ Eg [toVal (0 :: Int)] (toTerm False)
  , Eg [toVal (1 :: Int)] (toTerm True) ]

testStutter env = synthesise env (tyList tyInt --> tyList tyInt)
  [ Eg [toVal ([] :: [Int])] (toTerm ([] :: [Int]))
  , Eg [toVal ([1, 2] :: [Int])] (toTerm ([1, 1, 2, 2] :: [Int])) ]
