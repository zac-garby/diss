module Synthesis where

import Data.Maybe
import Data.List
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Lazy
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

type Synth = StateT ([Ident], Functions) (Reader Context)

synthesise :: Environment -> Type -> [Example] -> (Expr, Functions)
synthesise env goal egs =
  let (i, (_, fns)) = runReader (runStateT (uncurry synth (unfoldFn goal))
                                (allVars, [])) ctx
      fn = fromJust (lookup i fns)
  in (assemble fn, fns)
  where ctx = Context { env = env
                      , examples = egs }

synth :: [Type] -> Type -> Synth Ident
synth argTypes ret = do
  egs <- asks examples
  
  args <- forM argTypes $ \t -> do
    name <- fresh
    return (name, t)

  begin
    `orElse` synthTrivial args ret
    `orElse` synthCommonConstr args ret
    `orElse` defineFunction (Function args ret (Hole 0) egs)

synthTrivial :: [(Ident, Type)] -> Type -> Synth (Maybe Ident)
synthTrivial args retType = do
  egs <- asks examples
  go egs 0
  where go egs n
          | n >= length args = return Nothing
          | all (\(Eg egArgs egRes) -> egArgs !! n == egRes) egs = do
            f <- defineFunction $ Function { args = args
                                          , ret = retType
                                          , body = Var (fst $ args !! n)
                                          , egs = egs }
            return $ Just f
          | otherwise = go egs (n + 1)

synthCommonConstr :: [(Ident, Type)] -> Type -> Synth (Maybe Ident)
synthCommonConstr args retType = do
  egs <- asks examples
  
  case sharedConstr egs of
    Nothing -> return Nothing
    Just con -> do
      egs <- asks examples
      ts <- asks (terms . env)
  
      Forall _ conTy <- lookupType' con
      let (conArgTys, _) = unfoldFn (specialiseConstructor conTy retType)
          (conArgs, d) = unzip [ (args, deconstruct o) | Eg args o <- egs ]
          (cons, d') = unzip d
          d'T = transpose d'
          conEgs = [ zipWith Eg conArgs d | d <- d'T ]
          (argNames, argTypes) = unzip args

      fns <- forM (zip conArgTys conEgs) $ \(conArgTy, egs) -> do
        withExamples egs (synth argTypes conArgTy)

      let body = applyMany $ (Var con)
                 : [ applyMany $ Var fn : map Var argNames | fn <- fns ]
  
      f <- defineFunction $ Function { args = args
                                    , ret = retType
                                    , body = body
                                    , egs = egs }
      return $ Just f

defineFunction :: Function -> Synth Ident
defineFunction f = do
  name <- fresh
  modify $ \(ns, fs) -> (ns, (name, f) : fs)
  return name

infixr `orElse`
orElse :: Synth (Maybe Ident) -> Synth Ident -> Synth Ident
orElse a b = do
  i <- a
  case i of
    Nothing -> b
    Just x -> return x

begin = return Nothing
 
assemble :: Function -> Expr
assemble (Function args _ body _) = foldr Abs body (map fst args)

fresh :: Synth Ident
fresh = do
  name <- gets (head . fst)
  modify $ \(n:ns, fs) -> (ns, fs)
  return name

specialiseConstructor :: Type -> Type -> Type
specialiseConstructor conTy ret = case runExcept (runUnify u) of
  Left err -> error "unexpected error specialising constructor"
  Right s -> sub s genTy'
  where (argTys, conRetTy) = unfoldFn conTy
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

deconstruct :: Term -> (Ident, [Term])
deconstruct (CConstr i) = (i, [])
deconstruct (CApp l r) = let (i, ts) = deconstruct l
                         in (i, ts ++ [r])
deconstruct (CInt n) = deconstruct (intToSucs n)
deconstruct t = error $ "cannot deconstruct term: " ++ show t

intToSucs :: Int -> Term
intToSucs 0 = CConstr "Zero"
intToSucs n = CApp (CConstr "Suc") (intToSucs (n - 1))

sharedConstr :: [Example] -> Maybe Ident
sharedConstr [] = Nothing
sharedConstr xs = if all (== y) ys then Just y else Nothing
  where outputs = [ o | Eg _ o <- xs ]
        (y:ys) = [ i | (i, _) <- map deconstruct outputs ]

applyMany :: [Expr] -> Expr
applyMany = foldl1 App

unfoldFn :: Type -> ([Type], Type)
unfoldFn (TyConstr "->" [a, b]) =
  let (rest, ret) = unfoldFn b
  in (a : rest, ret)
unfoldFn t = ([], t)

test env = synthesise env (tyInt --> tyList tyInt --> tyList tyInt)
  [ Eg [toTerm (0 :: Int), toTerm ([1] :: [Int])] (toTerm ([0, 0, 1] :: [Int]))
  , Eg [toTerm (2 :: Int), toTerm ([] :: [Int])] (toTerm ([2, 2] :: [Int])) ]

test' env = synthesise env (tyInt --> tyList tyInt --> tyList tyInt)
  [ Eg [toTerm (0 :: Int), toTerm ([1] :: [Int])] (toTerm ([1] :: [Int]))
  , Eg [toTerm (2 :: Int), toTerm ([] :: [Int])] (toTerm ([] :: [Int])) ]
