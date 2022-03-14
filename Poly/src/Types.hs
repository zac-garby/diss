{-# LANGUAGE FlexibleInstances, DeriveTraversable #-}

module Types ( GenericType (..)
             , Scheme (..)
             , TypeError (..)
             , HoleIndex
             , Type
             , Env
             , Subst
             , Constraint
             , typecheck
             , finalise
             , tyInt
             , tyBool
             , tyList
             , (-->) )where

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

type HoleIndex = Int

data GenericType a = TyVar a
                   | TyConstr Ident [GenericType a]
                   | TyHole HoleIndex
                   deriving (Eq, Ord, Traversable)

instance Show (GenericType String) where
  show (TyVar v) = v
  show (TyConstr "→" [l,r]) = bracketType l ++ " → " ++ show r
  show (TyConstr c []) = c
  show (TyConstr c ts) = c ++ " " ++ intercalate " " (map bracketType ts)
  show (TyHole i) = "¿" ++ show i ++ "?"
  
bracketType :: Type -> String
bracketType t@(TyConstr "→" _) = "(" ++ show t ++ ")"
bracketType t = show t

instance Functor GenericType where
  fmap f (TyVar v) = TyVar (f v)
  fmap f (TyConstr c ts) = TyConstr c [ fmap f t | t <- ts ]
  fmap _ (TyHole i) = TyHole i

instance Foldable GenericType where
  foldr f s (TyVar v) = f v s
  foldr f s (TyConstr c ts) = foldr (\t b -> foldr f b t) s ts
  foldr _ s (TyHole _) = s

type Type = GenericType Ident
type Env = [(Ident, Scheme)]

data Scheme = Forall [Ident] Type

instance Show Scheme where
  show (Forall [] t) = show t
  show (Forall vs t) = "∀ " ++ intercalate " " vs ++ " . " ++ show t

instance Vars Type where
  freeVars = foldr (:) []

instance Vars Scheme where
  freeVars (Forall vs t) = nub (freeVars t) \\ vs

tyInt :: Type
tyInt = TyConstr "Int" []

tyBool :: Type
tyBool = TyConstr "Bool" []

tyList :: Type -> Type
tyList t = TyConstr "List" [t]

infixr 2 -->
(-->) :: Type -> Type -> Type
a --> b = TyConstr "→" [a, b]

allVars :: [Ident]
allVars = allVars' 0
  where allVars' 0 = map pure letters ++ allVars' 1
        allVars' n = map (:show n) letters ++ allVars' (n + 1)
        letters = ['a'..'z']

type Subst = [(Ident, Type)]

instance Sub Type where
  sub s t@(TyVar v) = fromMaybe t (lookup v s)
  sub s (TyConstr c ts) = TyConstr c (map (sub s) ts)
  sub s (TyHole i) = TyHole i

instance Sub Scheme where
  sub s (Forall vs t) = Forall vs (sub s t)

instance Sub Env where
  sub s e = [ (id, sub s sch) | (id, sch) <- e ]

instance Sub Constraint where
  sub s (t1, t2) = (sub s t1, sub s t2)

instance Sub BoundHole where
  sub s (BoundHole i t e) = BoundHole i (sub s t) (sub s e)

type Constraint = (Type, Type)

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

type Infer c = RWST
  Env                -- typing environment
  [c]                -- constraints accumulator
  [Ident]            -- fresh variable names
  (Except TypeError) -- errors

infer :: Expr -> Infer Constraint Type

infer (Var x) = do
  env <- ask
  case lookup x env of
    Nothing -> throwError $ UnboundVariableError x
    Just t -> instantiate t

infer (Hole i) = return $ TyHole i

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

infer (LitList xs) = do
  t <- fresh
  forM_ xs $ \x -> do
    tx <- infer x
    t ~~ tx
  return $ tyList t

infer (LitCons hd tl) = do
  thd <- infer hd
  ttl <- infer tl
  tyList thd ~~ ttl
  return $ tyList thd

runInfer :: Env -> Infer c a -> Except TypeError (a, [c])
runInfer env i = evalRWST i env allVars

instantiate :: Scheme -> Infer c Type
instantiate (Forall vs t) = do
  vs' <- zip vs <$> mapM (const freshName) vs
  return $ fmap (\v -> fromMaybe v (lookup v vs')) t

generalise :: Type -> Infer c Scheme
generalise t = do
  env <- ask
  let freeEnv = concat [ freeVars ty | (_, ty) <- env ]
  return $ Forall (freeVars t \\ freeEnv) t

freshName :: Infer c Ident
freshName = do
  name <- gets head
  modify tail
  return name

fresh :: Infer c Type
fresh = fmap TyVar freshName

infixl 1 ~~
(~~) :: Type -> Type -> Infer Constraint ()
(~~) a b = tell [(a, b)]

with :: (Ident, Scheme) -> Infer c a -> Infer c a
with p = local (p :)

type Unify = StateT Subst (Except TypeError)

runUnify :: Unify a -> Except TypeError Subst
runUnify u = S.execStateT u []

withConstraints :: Sub a => Infer Constraint a -> ([Constraint] -> Unify b) -> Infer Constraint (a, Subst)
withConstraints i u = do
  (t, cs) <- listen i
  s <- lift $ runUnify (u cs)
  return (sub s t, s)

unify :: Type -> Type -> Unify ()
unify t1 t2 | t1 == t2 = return ()
unify t (TyVar v) = v `extend` t
unify (TyVar v) t = v `extend` t
unify t h@(TyHole _) = return ()
unify h@(TyHole _) t = return ()
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

inferScheme :: Expr -> Infer Constraint Scheme
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

instance Show BoundHole where
  show (BoundHole i ty env)
    | null env' = "    ?" ++ show i ++ " : " ++ show ty
                  ++ "\n      no relevant bindings"
    | otherwise = "    ?" ++ show i ++ " : " ++ show ty
                  ++ "\n      relevant bindings include:\n"
                  ++ intercalate "\n" [ "        " ++ id ++ " : " ++ show t
                                      | (id, t) <- env' ]

    where env' = reverse $ takeWhile (\(id, _) -> head id /= '?') env

typeHoles :: Expr -> Type -> Infer Constraint (Type, [BoundHole])
typeHoles expr t = do
  (_, cs) <- listen $ typeAs expr t
  s <- lift $ runUnify (solve cs)
  return $ (sub s t, (holeTypes $ map (sub s) cs))

holeTypes :: [Constraint] -> [BoundHole]
holeTypes [] = []
holeTypes ((TyHole i, t):cs) = (BoundHole i t []) : holeTypes cs
holeTypes ((t, TyHole i):cs) = (BoundHole i t []) : holeTypes cs
holeTypes (_:cs) = holeTypes cs

-- types an expression, assuming it's already consistent with a given type.
-- this means that holes can infer their types from context.
typeAs :: Expr -> Type -> Infer Constraint ()

typeAs (Var x) t = do
  env <- ask
  case lookup x env of
    Nothing -> throwError $ UnboundVariableError x
    Just sch -> do
      t' <- instantiate sch
      t ~~ t'
  
typeAs (LitInt n) t = tyInt ~~ t
typeAs (LitBool b) t = tyBool ~~ t
typeAs (LitList xs) t = return ()
typeAs (LitCons hd tl) t = return ()

typeAs (App f x) t = do
  tx <- fresh
  typeAs f (tx --> t)
  typeAs x tx

typeAs (Abs x b) (TyConstr "→" [t1, t2]) = do
  with (x, Forall [] t1) $ typeAs b t2

typeAs (Abs x b) t = do
  t1 <- fresh
  t2 <- fresh
  with (x, Forall [] t1) $ typeAs (Abs x b) (t1 --> t2)
  t ~~ t1 --> t2

typeAs (Let x v b) t = do
  tv <- fresh
  typeAs v tv
  {-(_, cs) <- listen $ typeAs v tv
  s <- lift $ runUnify (solve cs)
  -- sch <- generalise (sub s tv)-}
  with (x, Forall [] tv) $ typeAs b t

{-
infer (LetRec x e b) = do
  tv <- fresh
  te <- with (x, Forall [] tv) (infer e)
  
  te ~~ tv

  with (x, Forall [] tv) (infer b)
-}
typeAs (LetRec x v b) t = do
  tx <- fresh
  tv <- fresh
  with (x, Forall [] tx) (typeAs v tv)

  tx ~~ tv

  with (x, Forall [] tx) (typeAs b t)

typeAs (If c true false) t = do
  typeAs c tyBool
  typeAs true t
  typeAs false t

typeAs (Hole n) t = TyHole n ~~ t

isComplete :: Expr -> Bool
isComplete = null . holesIn

holesIn :: Expr -> [HoleIndex]
holesIn = foldExpr (++) f []
  where f (Hole i) = [i]
        f _ = []
