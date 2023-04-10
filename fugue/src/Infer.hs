{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Infer ( TypeError (..)
             , BoundHole (..)
             , typecheck
             , unify
             , runUnify ) where

import qualified Control.Monad.State.Lazy as S
import qualified Control.Monad.Writer as W

import Data.List
import Data.Maybe
import Control.Monad
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
               | MissingCases [DataConstructor]
               | UnknownConstructor Ident

typecheck :: Env -> DataTypes -> Expr -> Except TypeError Scheme
typecheck e dts expr = do
  (sch, cs) <- runInfer e dts (inferScheme expr)
  return sch

data InferContext = Context
  { env :: Env
  , types :: DataTypes }

type Infer = RWST
  InferContext       -- typing environment and defined types
  [Constraint]       -- constraints accumulator
  [Ident]            -- fresh variable names
  (Except TypeError) -- errors

infer :: Expr -> Infer Type

infer (Var x) = do
  env <- asks env
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
  sch <- withSolved e generalise
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

infer (Case t []) = undefined

infer (Case t cases) = do
  tt <- infer t
  tb <- fresh
  env <- ask

  let (con1, _, _) = head cases
  dt <- dataTypeWithCon con1

  case dt of
    Just (DataType dtParams dtCons) -> case missingCases dtCons cases of
      [] -> do
        forM_ cases $ \(constr, args, body) -> do
          tArgs <- mapM (const fresh) args
          let schArgs = zipWith (\arg ty -> (arg, Forall [] ty)) args tArgs

          (tb', tt') <- withMany schArgs $ do
            tb' <- infer body
            tt' <- infer $ foldl App (Var constr) (map Var args)
            return (tb', tt')

          tb ~~ tb'
          tt ~~ tt'

        return tb
      missing -> throwError $ MissingCases missing
    Nothing -> throwError $ UnknownConstructor con1

infer (LitInt _) = return tyInt
infer (LitChar _) = return tyChar

infer (LitList xs) = do
  t <- fresh
  forM_ xs $ \x -> do
    tx <- infer x
    t ~~ tx
  return $ tyList t

infer (LitTuple xs) = do
  ts <- forM xs infer
  case ts of
    [] -> return tyUnit
    [a, b] -> return $ tyPair ts
    _ -> error "only units and 2-tuples are supported"

infer (TypeSpec e t) = do
  (te, cs) <- listen $ infer e
  s <- lift $ runUnify (solve cs)

  (sch, t') <- withSolved e $ \te -> do
    sch <- generalise te
    t' <- generalise t
    return (sch, t')

  if sch <= t'
    then return t
    else throwError $ TypeSpecMismatch sch t'

infer (Hole i) = return $ TyHole i

missingCases :: [DataConstructor] -> [(Ident, [Ident], Expr)] -> [DataConstructor]
missingCases dtCons cases = filter (\(DataConstructor name _) -> not (covered name)) dtCons
  where covered name = any (\(name', _, _) -> name == name') cases

withSolved :: Expr -> (Type -> Infer a) -> Infer a
withSolved e body = do
  (te, cs) <- listen $ infer e
  s <- lift $ runUnify (solve cs)
  local (\c -> c { env = sub s (env c) }) (body (sub s te))

runInfer :: Env -> DataTypes -> Infer a -> Except TypeError (a, [Constraint])
runInfer env dts i = evalRWST i (Context env dts) tempVars

dataTypeWithCon :: Ident -> Infer (Maybe DataType)
dataTypeWithCon name = do
  dts <- asks types
  return $ find (\(DataType _ cons) ->
                   any (\(DataConstructor n _) -> n == name) cons)
    (map snd dts)

instantiate :: Scheme -> Infer Type
instantiate (Forall vs t) = do
  s <- zip vs <$> mapM (const fresh) vs
  return $ sub s t

generalise :: Type -> Infer Scheme
generalise t = do
  env <- asks env
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

with :: MonadReader InferContext m => (Ident, Scheme) -> m a -> m a
with (i, sch) = local $ \ c -> c { env = (i, (sch, Local)) : env c }

withMany :: MonadReader InferContext m => [(Ident, Scheme)] -> m a -> m a
withMany is b = foldr with b is

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
  if isComplete expr then return $ finalise t else (do
    (t', holes) <- typeHoles expr t
    let (sch, holes') = finaliseHoles t' holes
    throwError $ FoundHoles sch holes')

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
  env <- asks env
  case lookup x env of
    Nothing -> throwError $ UnboundVariableError x
    Just (sch, _) -> do
      t' <- instantiate sch
      t ~~ t'

typeAs (LitInt n) t = lift $ tyInt ~~ t
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

  lift $ case ts of
    [] -> tyUnit ~~ t
    [a, b] -> tyPair [a, b] ~~ t
    _ -> error "only units and 2-tuples are supported"

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

typeAs (Case c cases) t = do
  tc <- lift fresh
  typeAs c tc

  forM_ cases $ \(constr, args, body) -> do
    tyArgs <- mapM (const (lift fresh)) args
    let schArgs = zipWith (\arg ty -> (arg, Forall [] ty)) args tyArgs

    withMany schArgs $ do
      typeAs body t
      typeAs (foldl App (Var constr) (map Var args)) tc

typeAs (TypeSpec e t) t' = do
  lift $ t ~~ t'
  typeAs e t'

typeAs (Hole n) t = do
  env <- lift (asks env)
  lift $ TyHole n ~~ t
  tell [BoundHole n t env]

