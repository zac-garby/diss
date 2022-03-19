{-# LANGUAGE DeriveTraversable, FlexibleInstances #-}

module Types ( GenericType (..)
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
             , tyString
             , (-->) )where

import Data.List
import Data.Maybe

type HoleIndex = Int
type Ident = String

data GenericType a = TyVar a
                   | TyConstr Ident [GenericType a]
                   | TyHole HoleIndex
                   deriving (Eq, Ord, Traversable)

type Type = GenericType Ident

data Scheme = Forall [Ident] Type

tyInt :: Type
tyInt = TyConstr "Int" []

tyBool :: Type
tyBool = TyConstr "Bool" []

tyChar :: Type
tyChar = TyConstr "Char" []

tyList :: Type -> Type
tyList t = TyConstr "List" [t]

tyString :: Type
tyString = tyList tyChar

infixr 2 -->
(-->) :: Type -> Type -> Type
a --> b = TyConstr "→" [a, b]

instance Functor GenericType where
  fmap f (TyVar v) = TyVar (f v)
  fmap f (TyConstr c ts) = TyConstr c [ fmap f t | t <- ts ]
  fmap _ (TyHole i) = TyHole i

instance Foldable GenericType where
  foldr f s (TyVar v) = f v s
  foldr f s (TyConstr c ts) = foldr (\t b -> foldr f b t) s ts
  foldr _ s (TyHole _) = s

instance Show (GenericType String) where
  show (TyVar v) = v
  show (TyConstr "→" [l,r]) = bracketType l ++ " → " ++ show r
  show (TyConstr "List" [t]) = "[" ++ show t ++ "]"
  show (TyConstr c []) = c
  show (TyConstr c ts) = c ++ " " ++ intercalate " " (map bracketType ts)
  show (TyHole i) = "¿" ++ show i ++ "?"
  
bracketType :: Type -> String
bracketType t@(TyConstr "→" _) = "(" ++ show t ++ ")"
bracketType t = show t

data BindingLocality = Local | Global
  deriving (Show, Eq, Ord)

type Env = [(Ident, (Scheme, BindingLocality))]

instance Show Scheme where
  show (Forall [] t) = show t
  show (Forall vs t) = "∀ " ++ intercalate " " vs ++ " . " ++ show t

class Vars a where
  freeVars :: a -> [Ident]

instance Vars Type where
  freeVars = foldr (:) []

instance Vars Scheme where
  freeVars (Forall vs t) = nub (freeVars t) \\ vs

type Subst = [(Ident, Type)]

class Sub a where
  sub :: Subst -> a -> a
  
instance Sub Type where
  sub s t@(TyVar v) = fromMaybe t (lookup v s)
  sub s (TyConstr c ts) = TyConstr c (map (sub s) ts)
  sub s t@(TyHole i) = fromMaybe t (lookup (show t) s)

instance Sub Scheme where
  sub s (Forall vs t) = Forall vs (sub s t)

instance Sub Env where
  sub s e = [ (id, (sub s sch, l)) | (id, (sch, l)) <- e ]

