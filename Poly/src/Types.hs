{-# LANGUAGE FlexibleInstances, DeriveTraversable #-}

module Types ( GenericType (..)
             , Scheme (..)
             , TypeError (..)
             , Type
             , Env
             , typecheck
             , finalise
             , tyInt
             , tyBool
             , (-->) ) where

import qualified Control.Monad.State.Lazy as S
import qualified Control.Monad.Writer as W

import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Except
import Control.Monad.RWS.Lazy
import Control.Monad.State.Lazy (StateT, State)
import Debug.Trace

import Parser

class Vars a where
  freeVars :: a -> [Ident]

class Sub a where
  sub :: Subst -> a -> a

data GenericType a = TyVar a
                   | TyConstr Ident [GenericType a]
                   deriving (Eq, Ord, Traversable)

instance Show (GenericType String) where
  show (TyVar v) = v
  show (TyConstr "->" [l,r]) = bracketType l ++ " → " ++ show r
  show (TyConstr c []) = c
  show (TyConstr c ts) = c ++ " " ++ intercalate " " (map bracketType ts)
  
bracketType :: Type -> String
bracketType (TyConstr c []) = c
bracketType t@(TyConstr _ _) = "(" ++ show t ++ ")"
bracketType t = show t

instance Functor GenericType where
  fmap f (TyVar v) = TyVar (f v)
  fmap f (TyConstr c ts) = TyConstr c [ fmap f t | t <- ts ]

instance Foldable GenericType where
  foldr f s (TyVar v) = f v s
  foldr f s (TyConstr c ts) = foldr (\t b -> foldr f b t) s ts

type Type = GenericType Ident
type Env = [(Ident, Scheme)]

data Scheme = Forall [Ident] Type

instance Show Scheme where
  show (Forall [] t) = show t
  show (Forall vs t) = "∀ " ++ intercalate " " vs ++ " . " ++ show t

instance Vars Type where
  freeVars = foldr (:) []

instance Vars Scheme where
  freeVars (Forall vs t) = freeVars t \\ vs

tyInt :: Type
tyInt = TyConstr "int" []

tyBool :: Type
tyBool = TyConstr "bool" []

infixr -->  
(-->) :: Type -> Type -> Type
a --> b = TyConstr "->" [a, b]

allVars :: [Ident]
allVars = allVars' 0
  where allVars' 0 = map pure letters ++ allVars' 1
        allVars' n = map (:show n) letters ++ allVars' (n + 1)
        letters = ['a'..'z']

type Subst = [(Ident, Type)]

instance Sub Type where
  sub s t@(TyVar v) = fromMaybe t (lookup v s)
  sub s (TyConstr c ts) = TyConstr c (map (sub s) ts)

instance Sub Scheme where
  sub s (Forall vs t) = Forall vs (sub s t)

instance Sub Env where
  sub s e = [ (id, sub s sch) | (id, sch) <- e ]

type Constraint = (Type, Type)

data TypeError = UnifyInfiniteError Ident Type
               | UnifyConstructorsError Ident Ident
               | UnifyConstructorArityMismatch Ident Int Int
               | UnboundVariableError Ident
               | HasHoles Type [BoundHole]

instance Show TypeError where
  show (UnifyInfiniteError v t) = "could not construct infinite type " ++ v ++ " ~ " ++ show t
  show (UnifyConstructorsError c1 c2) = "could not unify different constructors " ++ c1 ++ " and " ++ c2
  show (UnifyConstructorArityMismatch c a1 a2) = "constructor arity mismatch for " ++ c ++ ": " ++ show a1 ++ " vs " ++ show a2
  show (UnboundVariableError v) = "unbound variable: " ++ v
  show (HasHoles ty hs) = "found holes in term of type : " ++ show ty ++ "\n" ++ intercalate "\n" (map show hs)

data BoundHole = BoundHole Type Env

instance Show BoundHole where
  show (BoundHole ty env)
    | null env' = "    hole : " ++ show ty ++ "\n      no relevant bindings"
    | otherwise = "    hole : " ++ show ty ++ "\n      relevant bindings include:\n"
                            ++ intercalate "\n" [ "        " ++ id ++ " : " ++ show t | (id, t) <- env' ]
    where env' = takeWhile (\(id, _) -> head id /= '?') env

type Infer = RWST
  Env                         -- typing environment
  ([Constraint], [BoundHole]) -- (constraints accumulator, bound holes)
  [Ident]                     -- fresh variable names
  (Except TypeError)          -- errors

infer :: Expr -> Infer Type

infer (Var x) = do
  env <- ask
  case lookup x env of
    Nothing -> throwError $ UnboundVariableError x
    Just t -> instantiate t

infer (Hole n) = do
  env <- ask
  case lookup ("?" ++ show n) env of
    Nothing -> error "hole variable not defined in the env - this shouldn't happen"
    Just t -> do
      ty <- instantiate t
      tell ([], [BoundHole ty env])
      return ty

infer (Abs x e) = do
  tv <- fresh
  te <- with (x, Forall [] tv) (infer e)
  
  return $ tv --> te

infer (App f x) = do
  tf <- infer f
  tx <- infer x
  tv <- fresh
  
  tf ~~ (tx --> tv)
  
  return tv

infer (Let x e b) = do
  (te, (cs, _)) <- listen $ infer e
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

runInfer :: Env -> Infer a -> Except TypeError (a, ([Constraint], [BoundHole]))
runInfer env i = evalRWST i env allVars

instantiate :: Scheme -> Infer Type
instantiate (Forall vs t) = do
  vs' <- zip vs <$> mapM (const freshName) vs
  return $ fmap (\v -> fromMaybe v (lookup v vs')) t

generalise :: Type -> Infer Scheme
generalise t = do
  env <- ask
  let freeEnv = concat [ freeVars t | (_, t) <- env ]
  return $ Forall (freeVars t \\ freeEnv) t

freshName :: Infer Ident
freshName = do
  name <- gets head
  modify tail
  return name

fresh :: Infer Type
fresh = fmap TyVar freshName

(~~) :: Type -> Type -> Infer ()
(~~) a b = tell ([(a, b)], [])

with :: (Ident, Scheme) -> Infer a -> Infer a
with p = local (p :)

type Unify = StateT Subst (Except TypeError)

runUnify :: Unify a -> Except TypeError Subst
runUnify u = S.execStateT u []

unify :: Type -> Type -> Unify ()
unify t1 t2 | t1 == t2 = return ()
unify t (TyVar v) = v `extend` t

unify (TyVar v) t = v `extend` t
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

holesIn :: Expr -> [Int]
holesIn e = snd (W.runWriter (traverseExpr he e))
  where he :: Expr -> W.Writer [Int] ()
        he (Hole n) = tell [n]
        he t = return ()

withHoles :: Expr -> Infer a -> Infer a
withHoles e i = join $ S.evalStateT (w e i) 0
  where w h@(Hole _) i = do
          n <- S.get
          modify succ
          tv <- lift fresh
          lift $ return $ with (show h, Forall [] $ tv) i
        w (App f x) i = w f i >>= w x
        w (Abs _ t) i = w t i
        w (Let _ val body) i = w val i >>= w body
        w (LetRec _ val body) i = w val i >>= w body
        w (If cond t f) i = w cond i >>= w t >>= w f
        w _ i = return i

typecheck :: Env -> Expr -> Except TypeError Scheme
typecheck e t = do
  (t, (cs, hs)) <- runInfer e (withHoles t $ infer t)
  s <- runUnify (solve cs)
  case hs of
    [] -> return $ finalise (sub s t)
    holes -> do
      let r = makeRenamer t `compose` s
      throwError $ HasHoles (sub r t) [ BoundHole (sub r th) (sub r env)
                                      | (BoundHole th env) <- holes ]

finalise :: Type -> Scheme
finalise t = let t' = rename t
             in Forall (nub $ freeVars t') t'

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
