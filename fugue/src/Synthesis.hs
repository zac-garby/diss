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

data Example = Eg [Term] Term
  deriving Show

type Synth = MaybeT (StateT ([Ident], Functions) (Reader Context))

synthesise :: Environment -> Type -> [Example] -> Maybe (Ident, Functions)
synthesise env goal egs =
  let r = runReader (runStateT (runMaybeT (uncurry synth (unfoldFnTy goal)))
                                (allVars, [])) ctx
  in case r of
    (Nothing, _) -> Nothing
    (Just i, (_, fns)) -> Just (i, fns)
  where ctx = Context { env = env
                      , examples = egs }

synth :: [Type] -> Type -> Synth Ident
synth argTypes ret = do
  fns <- gets snd
  egs <- asks examples

  traceM $ "synth: " ++ intercalate " -> " (map show argTypes) ++ " -> " ++ show ret
  
  args <- forM argTypes $ \t -> do
    name <- fresh
    return (name, t)

  try [ synthNoEgs args ret
      , synthTrivial args ret
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
          | all (\(Eg egArgs egRes) -> egArgs !! n == egRes) egs =
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

      let body = applyMany $ (Var con)
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
              egs' = [ Eg (ins ++ conArgs') out
                     | Eg ins out <- egs
                     , let (con', conArgs') = deconstruct' (ins !! splitOn)
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

defineFunction :: Function -> Synth Ident
defineFunction f = do
  name <- fresh
  modify $ \(ns, fs) -> (ns, (name, f) : fs)
  return name

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
assemble (Function args _ body _) = foldr Abs body (map fst args)

collapse :: Functions -> Expr -> Expr
collapse fns app@(App f x) = case unfoldApp app of
  (Var f', xs') -> case lookup f' fns of
    Nothing -> App (collapse fns f) (collapse fns x)
    Just fn -> app
  _ -> app

fresh :: Synth Ident
fresh = do
  name <- gets (head . fst)
  modify $ \(n:ns, fs) -> (ns, fs)
  return name

specialiseConstructor :: Type -> Type -> Type
specialiseConstructor conTy ret = case runExcept (runUnify u) of
  Left err -> error "unexpected error specialising constructor"
  Right s -> sub s genTy'
  where (argTys, conRetTy) = unfoldFnTy conTy
        varNames = take (length argTys) [ "*temp" ++ show i | i <- [0..] ]
        genTy = foldr (-->) ret (map TyVar varNames)
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
--deconstruct (CInt n) = deconstruct (intToSucs n)
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
  (y:ys) <- forM outputs (\o -> fmap fst (deconstruct o))
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

unwind :: Functions -> Expr -> Expr
unwind fns (Var x) = case lookup x fns of -- inline zero-arity functions but no others
    Just (Function { body = body }) -> unwind fns body
    _ -> Var x
unwind fns app@(App e1 e2) = case unfoldApp app of
    (Var x, args) -> case lookup x fns of
      Just fn -> if canInline x fn then inline fn args fns else app'
      Nothing -> app'
    _ -> app'
  where app' = App (unwind fns e1) (unwind fns e2)
unwind fns (Abs x e) = Abs x (unwind fns e)
unwind fns (Let x e1 e2) = Let x (unwind fns e1) (unwind fns e2)
unwind fns (LetRec x e1 e2) = LetRec x (unwind fns e1) (unwind fns e2)
unwind fns (If e1 e2 e3) = If (unwind fns e1) (unwind fns e2) (unwind fns e3)
unwind fns (Case e cases) = Case (unwind fns e)
                                 [ (x, xs, unwind fns b)
                                 | (x, xs, b) <- cases ]
unwind fns (LitInt n) = LitInt n
unwind fns (LitList xs) = LitList (map (unwind fns) xs)
unwind fns (LitTuple xs) = LitTuple (map (unwind fns) xs)
unwind fns (LitChar c) = LitChar c
unwind fns (TypeSpec e t) = TypeSpec (unwind fns e) t
unwind fns (Hole n) = Hole n

inline :: Function -> [Expr] -> Functions -> Expr
inline (Function { args = fnArgs, body = fnBody }) args fns =
  let fnBody' = unwind fns fnBody
      arguments = zip (map fst fnArgs) args
  in subExpr arguments fnBody'

canInline :: Ident -> Function -> Bool
canInline fnName (Function { body = body }) = not (body `calls` fnName)

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

calls :: Expr -> Ident -> Bool
calls e i = i `elem` calledBy e

test env = synthesise env (tyList tyInt --> tyInt)
  [ Eg [toTerm ([1, 2] :: [Int])] (toTerm (1 :: Int))
  , Eg [toTerm ([1, 2, 3] :: [Int])] (toTerm (1 :: Int)) ]

test' env = synthesise env (tyInt --> tyList tyInt --> tyList tyInt)
  [ Eg [toTerm (0 :: Int), toTerm ([1] :: [Int])] (toTerm ([1] :: [Int]))
  , Eg [toTerm (2 :: Int), toTerm ([] :: [Int])] (toTerm ([] :: [Int])) ]
