{-# LANGUAGE DeriveTraversable, FlexibleInstances #-}

module Types ( GenericType (..)
             , DataType (..)
             , DataConstructor (..)
             , DataTypes
             , Scheme (..)
             , BindingLocality (..)
             , HoleIndex
             , Type
             , Env
             , Subst
             , Sub (..)
             , Vars (..)
             , tyInt
             , tyBool
             , tyChar
             , tyList
             , tyPair
             , tyUnit
             , tyString
             , (-->)
             , finalise
             , allVars
             , rename
             , makeRenamer
             , renameToDistinct
             , unfoldFnTy ) where

import Control.Monad.State.Lazy
import Data.List
import Data.Maybe

type HoleIndex = Int
type Ident = String

data GenericType a = TyVar a
                   | TyConstr Ident [GenericType a]
                   | TyHole HoleIndex
                   deriving (Eq, Traversable)

type Type = GenericType Ident

data Scheme = Forall [Ident] Type
  deriving Eq

data DataType = DataType [Ident] [DataConstructor]
  deriving Show

data DataConstructor = DataConstructor Ident [Type]
  deriving Show

type DataTypes = [(Ident, DataType)]

tyInt :: Type
tyInt = TyConstr "Int" []

tyBool :: Type
tyBool = TyConstr "Bool" []

tyChar :: Type
tyChar = TyConstr "Char" []

tyList :: Type -> Type
tyList t = TyConstr "List" [t]

tyPair :: [Type] -> Type
tyPair = TyConstr "Pair"

tyUnit :: Type
tyUnit = TyConstr "Unit" []

tyString :: Type
tyString = tyList tyChar

infixr 2 -->
(-->) :: Type -> Type -> Type
a --> b = TyConstr "->" [a, b]

instance Ord Scheme where
  Forall vs1 t1 <= Forall vs2 t2 = sub (subst t1 t2) t1 == t2
    where subst (TyVar a) t2
            | a `elem` vs1 = [(a, t2)]
          subst (TyConstr c1 ts1) (TyConstr c2 ts2)
            | c1 == c2 = concat [ subst t1 t2 | (t1, t2) <- zip ts1 ts2 ]
          subst h@(TyHole i) t2 = [(show h, t2)]
          subst _ _ = []

  a < b = a <= b && not (b <= a)
  a > b = b < a

instance Ord Type where
  t1 <= t2 = finalise t1 <= finalise t2

instance Functor GenericType where
  fmap f (TyVar v) = TyVar (f v)
  fmap f (TyConstr c ts) = TyConstr c [ fmap f t | t <- ts ]
  fmap _ (TyHole i) = TyHole i

instance Foldable GenericType where
  foldr f s (TyVar v) = f v s
  foldr f s (TyConstr c ts) = foldr (flip (foldr f)) s ts
  foldr _ s (TyHole _) = s

instance Show (GenericType String) where
  show (TyVar v) = v
  show (TyConstr "->" [l,r]) = bracketType l ++ " → " ++ show r
  show (TyConstr "List" [t]) = "[" ++ show t ++ "]"
  show (TyConstr "Tuple" xs) = "(" ++ intercalate ", " (map show xs) ++ ")"
  show (TyConstr c []) = c
  show (TyConstr c ts) = c ++ " " ++ unwords (map bracketType ts)
  show (TyHole i) = "¿" ++ show i ++ "?"

bracketType :: Type -> String
bracketType t@(TyConstr "->" _) = "(" ++ show t ++ ")"
bracketType t = show t

data BindingLocality = Local | Global
  deriving (Show, Eq, Ord)

type Env = [(Ident, (Scheme, BindingLocality))]

instance Show Scheme where
  show (Forall [] t) = show t
  show (Forall vs t) = "∀ " ++ unwords vs ++ " . " ++ show t

class Vars a where
  freeVars :: a -> [Ident]

instance Vars Type where
  freeVars = nub . foldr (:) []

instance Vars Scheme where
  freeVars (Forall vs t) = nub (freeVars t) \\ vs

instance Vars Env where
  freeVars env = nub (concat [ freeVars sch | (_, (sch, _)) <- env ])

type Subst = [(Ident, Type)]

class Sub a where
  sub :: Subst -> a -> a

instance Sub Type where
  sub s t@(TyVar v) = fromMaybe t (lookup v s)
  sub s (TyConstr c ts) = TyConstr c (map (sub s) ts)
  sub s t@(TyHole i) = fromMaybe t (lookup (show t) s)

instance Sub Scheme where
  sub s (Forall vs t) = Forall vs (sub s' t)
    where s' = [ (i, t) | (i, t) <- s, i `notElem` vs ]

instance Sub Env where
  sub s e = [ (id, (sub s sch, l)) | (id, (sch, l)) <- e ]

allVars :: [Ident]
allVars = allVars' 0
  where allVars' 0 = map pure letters ++ allVars' 1
        allVars' n = map (:show n) letters ++ allVars' (n + 1)
        letters = ['a'..'z']

finalise :: Type -> Scheme
finalise t = let t' = rename t
             in Forall (nub $ freeVars t') t'

rename :: Type -> Type
rename t = sub (makeRenamer t) t

makeRenamer :: Type -> Subst
makeRenamer t = snd $ execState (traverse mk t) (allVars, [])
  where mk :: Ident -> State ([Ident], Subst) ()
        mk v = do
          state <- get
          let (new:rest, existing) = state
          case lookup v existing of
            Just n -> return ()
            Nothing -> put (rest, (v, TyVar new) : existing)

renameToDistinct :: Type -> Type -> (Type, Type)
renameToDistinct t1 t2
  | null inCommon = (t1, t2)
  | otherwise = renameToDistinct (sub s t1) t2
  where fv1 = freeVars t1
        fv2 = freeVars t2
        inCommon = fv1 `intersect` fv2
        s = [(v, TyVar (v ++ "'")) | v <- inCommon]

unfoldFnTy :: Type -> ([Type], Type)
unfoldFnTy (TyConstr "->" [a, b]) =
  let (rest, ret) = unfoldFnTy b
  in (a : rest, ret)
unfoldFnTy t = ([], t)