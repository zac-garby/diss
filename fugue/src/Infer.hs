{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Infer ( TypeError (..)
             , BoundHole (..)
             , typecheck ) where

import qualified Control.Monad.State.Lazy as S
import qualified Control.Monad.Writer as W

import Data.List
import Data.Maybe
import Control.Monad.Except
import Control.Monad.RWS.Lazy
import Control.Monad.State.Lazy (StateT, State)
import Debug.Trace

import Types
import Holes
import Parser

type Constraint = (Type, Type)

instance Sub Constraint where
  sub s (t1, t2) = (sub s t1, sub s t2)

data TypeError = UnifyInfiniteError Ident Type
               | UnifyConstructorsError Type Type
               | TypeSpecMismatch Scheme Scheme
               | UnboundVariableError Ident
               | FoundHoles Scheme [BoundHole]

typecheck :: Env -> Expr -> Except TypeError Scheme
typecheck e expr = do
  (sch, cs) <- runInfer e (inferScheme expr)
  return sch

type Infer = RWST
  Env                -- typing environment
  [Constraint]       -- constraints accumulator
  [Ident]            -- fresh variable names
  (Except TypeError) -- errors

infer :: Expr -> Infer Type

infer (Var x) = do
  env <- ask
  case lookup x env of
    Nothing -> throwError $ UnboundVariableError x
    Just (t, _) -> instantiate t

infer (Abs x e) = do
  tv <- fresh
  te <- with (x, Forall [] tv) (infer e)
  
  return $ tv --> te

infer (App f x) = do
  tf <- infer f
  tx <- infer x
  tv <- fresh
  
  tf ~~ tx --> tv
  
  return tv

infer (Let x e b) = do
  (te, cs) <- listen $ infer e
  s <- lift $ runUnify (solve cs)
  sch <- local (sub s) (generalise (sub s te))
  with (x, sch) (infer b)

infer (LetRec x e b) = do
  tv <- fresh
  te <- with (x, Forall [] tv) (infer e)
  
  te ~~ tv

  with (x, Forall [] tv) (infer b)

infer (If cond t f) = do
  tc <- infer cond
  tt <- infer t
  tf <- infer f
  
  tc ~~ tyBool
  tt ~~ tf

  return tt

infer (LitInt _) = return tyInt
infer (LitBool _) = return tyBool
infer (LitChar _) = return tyChar

infer (LitList xs) = do
  t <- fresh
  forM_ xs $ \x -> do
    tx <- infer x
    t ~~ tx
  return $ tyList t

infer (LitTuple xs) = do
  ts <- forM xs infer
  return $ tyTuple ts

infer (TypeSpec e t) = do
  (te, cs) <- listen $ infer e
  s <- lift $ runUnify (solve cs)
  sch <- local (sub s) (generalise (sub s te))
  t' <- local (sub s) (generalise t)
  if sch <= t'
    then return t
    else throwError $ TypeSpecMismatch sch t'

infer (Hole i) = return $ TyHole i

runInfer :: Env -> Infer a -> Except TypeError (a, [Constraint])
runInfer env i = evalRWST i env tempVars

instantiate :: Scheme -> Infer Type
instantiate (Forall vs t) = do
  s <- zip vs <$> mapM (const fresh) vs
  return $ sub s t

generalise :: Type -> Infer Scheme
generalise t = do
  env <- ask
  return $ Forall (freeVars t \\ freeVars env) t

freshName :: Infer Ident
freshName = do
  name <- gets head
  modify tail
  return name

fresh :: Infer Type
fresh = fmap TyVar freshName

tempVars :: [Ident]
tempVars = [ i ++ "'" | i <- allVars ]

infixl 1 ~~
(~~) :: Type -> Type -> Infer ()
(~~) a b = tell [(a, b)]

with :: MonadReader Env m => (Ident, Scheme) -> m a -> m a
with (i, sch) = local ((i, (sch, Local)) :)

type Unify = StateT Subst (Except TypeError)

runUnify :: Unify a -> Except TypeError Subst
runUnify u = S.execStateT u []

withConstraints :: Sub a => Infer a -> ([Constraint] -> Unify b) -> Infer (a, Subst)
withConstraints i u = do
  (t, cs) <- listen i
  s <- lift $ runUnify (u cs)
  return (sub s t, s)

unify :: Type -> Type -> Unify ()
unify t1 t2 | t1 == t2 = return ()
unify t (TyVar v) = v `extend` t
unify (TyVar v) t = v `extend` t
unify t h@(TyHole _) = show h `extend` t
unify h@(TyHole _) t = show h `extend` t
unify a@(TyConstr c1 ts1) b@(TyConstr c2 ts2)
  | c1 /= c2 || a1 /= a2 = throwError $ UnifyConstructorsError a b
  | otherwise = unifyPairs (zip ts1 ts2)
  where a1 = length ts1
        a2 = length ts2

unifyPairs :: [(Type, Type)] -> Unify ()
unifyPairs [] = return ()
unifyPairs ((t1, t2):rest) = do
  unify t1 t2
  s <- S.get
  unifyPairs [ (sub s t1, sub s t2) | (t1, t2) <- rest ]

solve :: [Constraint] -> Unify ()
solve cs = forM_ cs $ \(t1, t2) -> do
  s <- S.get
  unify (sub s t1) (sub s t2)

extend :: Ident -> Type -> Unify ()
v `extend` t | t == TyVar v = return ()
             | v `elem` freeVars t = throwError $ UnifyInfiniteError v t
             | otherwise = S.modify (compose [(v, t)])

compose :: Subst -> Subst -> Subst
compose s1 s2 = map (fmap (sub s1)) s2 ++ s1

inferScheme :: Expr -> Infer Scheme
inferScheme expr = do
  (t, s) <- withConstraints (infer expr) solve
  case isComplete expr of
    True  -> return $ finalise t
    False -> do
      (t', holes) <- typeHoles expr t
      let (sch, holes') = finaliseHoles t' holes
      throwError $ FoundHoles sch holes'

finaliseHoles :: Type -> [BoundHole] -> (Scheme, [BoundHole])
finaliseHoles t hs =
  let r = makeRenamer t
      t' = sub r t
      hs' = map (sub r) hs
  in (Forall (nub $ freeVars t') t', hs')

typeHoles :: Expr -> Type -> Infer (Type, [BoundHole])
typeHoles expr t = do
  (hs, cs) <- listen $ W.execWriterT (typeAs expr t)
  s <- lift $ runUnify (solve cs)
  return (sub s t, map (sub s) hs)

-- types an expression, assuming it's already consistent with a given type.
-- this means that holes can infer their types from context.
typeAs :: Expr -> Type -> W.WriterT [BoundHole] Infer ()

typeAs (Var x) t = lift $ do
  env <- ask
  case lookup x env of
    Nothing -> throwError $ UnboundVariableError x
    Just (sch, _) -> do
      t' <- instantiate sch
      t ~~ t'
  
typeAs (LitInt n) t = lift $ tyInt ~~ t
typeAs (LitBool b) t = lift $ tyBool ~~ t
typeAs (LitChar c) t = lift $ tyChar ~~ t

typeAs (LitList xs) t = do
  tv <- lift fresh
  lift $ t ~~ tyList tv
  forM_ xs $ \x -> do
    typeAs x tv

typeAs (LitTuple xs) t = do
  ts <- forM xs $ \x -> do
    tv <- lift fresh
    typeAs x tv
    return tv
    
  lift $ tyTuple ts ~~ t

typeAs (App f x) t = do
  tx <- lift fresh
  typeAs f (tx --> t)
  typeAs x tx

typeAs (Abs x b) (TyConstr "->" [t1, t2]) = do
  with (x, Forall [] t1) $ typeAs b t2

typeAs (Abs x b) t = do
  t1 <- lift fresh
  t2 <- lift fresh
  with (x, Forall [] t1) $ typeAs (Abs x b) (t1 --> t2)
  lift $ t ~~ t1 --> t2

typeAs (Let x v b) t = do
  tv <- lift fresh
  typeAs v tv
  with (x, Forall [] tv) $ typeAs b t

typeAs (LetRec x v b) t = do
  tx <- lift fresh
  tv <- lift fresh
  with (x, Forall [] tx) $ typeAs v tv

  lift $ tx ~~ tv

  with (x, Forall [] tx) $ typeAs b t

typeAs (If c true false) t = do
  typeAs c tyBool
  typeAs true t
  typeAs false t

typeAs (TypeSpec e t) t' = do
  lift $ t ~~ t'
  typeAs e t'

typeAs (Hole n) t = do
  env <- lift ask
  lift $ TyHole n ~~ t
  tell $ [BoundHole n t env]

