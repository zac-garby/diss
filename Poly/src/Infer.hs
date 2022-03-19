{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}

module Infer ( TypeError (..)
             , Infer
             , typecheck
             , finalise ) where

import qualified Control.Monad.State.Lazy as S
import qualified Control.Monad.Writer as W

import Data.List
import Data.Maybe
import Control.Monad.Except
import Control.Monad.RWS.Lazy
import Control.Monad.State.Lazy (StateT, State)
import Debug.Trace

import Types
import Parser

type Constraint = (Type, Type)

instance Sub Constraint where
  sub s (t1, t2) = (sub s t1, sub s t2)

data TypeError = UnifyInfiniteError Ident Type
               | UnifyConstructorsError Ident Ident
               | UnifyConstructorArityMismatch Ident Int Int
               | UnboundVariableError Ident
               | FoundHoles Scheme [BoundHole]

instance Show TypeError where
  show (UnifyInfiniteError v t) = "could not construct infinite type " ++ v ++ " ~ " ++ show t
  show (UnifyConstructorsError c1 c2) = "could not unify different constructors " ++ c1 ++ " and " ++ c2
  show (UnifyConstructorArityMismatch c a1 a2) = "constructor arity mismatch for " ++ c ++ ": " ++ show a1 ++ " vs " ++ show a2
  show (UnboundVariableError v) = "unbound variable: " ++ v
  show (FoundHoles sch hs) = "found holes in " ++ show sch ++ ":\n"
                             ++ intercalate "\n" (map show hs)

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
  sch <- generalise (sub s te) -- fixed bug: let two = (\n -> add n 1) 1 in two
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

infer (TypeSpec e t) = do
  te <- infer e
  te ~~ t
  return t

infer (Hole i) = return $ TyHole i

runInfer :: Env -> Infer a -> Except TypeError (a, [Constraint])
runInfer env i = evalRWST i env tempVars

instantiate :: Scheme -> Infer Type
instantiate (Forall vs t) = do
  vs' <- zip vs <$> mapM (const freshName) vs
  return $ fmap (\v -> fromMaybe v (lookup v vs')) t

generalise :: Type -> Infer Scheme
generalise t = do
  env <- ask
  let freeEnv = concat [ freeVars ty | (_, (ty, _)) <- env ]
  return $ Forall (freeVars t \\ freeEnv) t

freshName :: Infer Ident
freshName = do
  name <- gets head
  modify tail
  return name

fresh :: Infer Type
fresh = fmap TyVar freshName

tempVars :: [Ident]
tempVars = [ i ++ "'" | i <- allVars ]

allVars :: [Ident]
allVars = allVars' 0
  where allVars' 0 = map pure letters ++ allVars' 1
        allVars' n = map (:show n) letters ++ allVars' (n + 1)
        letters = ['a'..'z']

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
unify (TyConstr c1 ts1) (TyConstr c2 ts2)
  | c1 /= c2 = throwError $ UnifyConstructorsError c1 c2
  | a1 /= a2 = throwError $ UnifyConstructorArityMismatch c1 a1 a2
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

typecheck :: Env -> Expr -> Except TypeError Scheme
typecheck e expr = do
  (sch, cs) <- runInfer e (inferScheme expr)
  return sch

inferScheme :: Expr -> Infer Scheme
inferScheme expr = do
  (t, s) <- withConstraints (infer expr) solve
  case isComplete expr of
    True  -> return $ finalise t
    False -> do
      (t', holes) <- typeHoles expr t
      let (sch, holes') = finaliseHoles t' holes
      throwError $ FoundHoles sch holes'

finalise :: Type -> Scheme
finalise t = let t' = rename t
             in Forall (nub $ freeVars t') t'

finaliseHoles :: Type -> [BoundHole] -> (Scheme, [BoundHole])
finaliseHoles t hs =
  let r = makeRenamer t
      t' = sub r t
      hs' = map (sub r) hs
  in (Forall (nub $ freeVars t') t', hs')

rename :: Type -> Type
rename t = sub (makeRenamer t) t

makeRenamer :: Type -> Subst
makeRenamer t = snd $ S.execState (traverse mk t) (allVars, [])
  where mk :: Ident -> S.State ([Ident], Subst) ()
        mk v = do
          state <- S.get
          let ((new:rest), existing) = state
          case lookup v existing of
            Just n -> return ()
            Nothing -> S.put (rest, (v, TyVar new) : existing)


data BoundHole = BoundHole HoleIndex Type Env

instance Sub BoundHole where
  sub s (BoundHole i t e) = BoundHole i (sub s t) (sub s e)

instance Show BoundHole where
  show (BoundHole i ty env)
    | null relevant = "    ?" ++ show i ++ " : " ++ show ty
                   ++ "\n      no relevant bindings"
    | otherwise = "    ?" ++ show i ++ " : " ++ show ty
                   ++ "\n      relevant bindings include:\n"
                   ++ intercalate "\n" [ "        " ++ pprintIdent ops id ++ " : " ++ show t
                                      | (id, (t, l)) <- relevant ]

    where relevant = reverse $ nubBy (\(i, _) (j, _) -> i == j)
                     [ (id, (t, l)) | (id, (t, l)) <- env, l == Local ]

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

typeAs (App f x) t = do
  tx <- lift fresh
  typeAs f (tx --> t)
  typeAs x tx

typeAs (Abs x b) (TyConstr "→" [t1, t2]) = do
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

isComplete :: Expr -> Bool
isComplete = null . holesIn

holesIn :: Expr -> [HoleIndex]
holesIn = foldExpr (++) f []
  where f (Hole i) = [i]
        f _ = []
