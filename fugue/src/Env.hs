module Env ( Environment (..)
           , defaultEnv
           , defineTerm
           , defineDataType
           , lookupTerm
           , lookupDataType ) where

import Data.Char

import Types
import Infer
import Compiler

data Environment = Environment
  { terms :: [(String, (Scheme, Term))]
  , types :: DataTypes }
  deriving Show

defineTerm :: String -> Scheme -> Term -> Environment -> Environment
defineTerm name sch val (Environment terms types) =
  Environment (insertKV name (sch, val) terms) types

defineDataType :: String -> DataType -> Environment -> Environment
defineDataType name dt (Environment terms types) =
  Environment terms (insertKV name dt types)

lookupTerm :: String -> Environment -> Maybe (Scheme, Term)
lookupTerm name (Environment terms _) = lookup name terms

lookupDataType :: String -> Environment -> Maybe DataType
lookupDataType name (Environment _ types) = lookup name types

a = TyVar "a"
b = TyVar "b"
c = TyVar "c"

defaultEnv :: Environment
defaultEnv = Environment
  [ ("__add", intBinOp (+))
  , ("__sub", intBinOp (-))
  , ("__mul", intBinOp (*))
  , ("__div", intBinOp div)
  , ("__mod", intBinOp mod)
  , ("__eq", ( finalise $ a --> a --> tyBool
             , CBuiltin Full $ \x ->
                 CBuiltin Full $ \y -> toTerm (x == y)))
  , ("__lt", intCompOp (<))
  , ("__gt", intCompOp (>))
  , ("__lte", intCompOp (<=))
  , ("__gte", intCompOp (>=))
  , ("chr", ( finalise $ tyInt --> tyChar
            , toTerm chr ))
  , ("ord", ( finalise $ tyChar --> tyInt
            , toTerm ord ))
  , ("fst", ( finalise $ tyTuple [a, b] --> a
            , CBuiltin WHNF $ \(CTuple [t, _]) -> t ))
  , ("snd", ( finalise $ tyTuple [a, b] --> b
            , CBuiltin WHNF $ \(CTuple [_, t]) -> t ))
  , ("fst3", ( finalise $ tyTuple [a, b, c] --> a
             , CBuiltin WHNF $ \(CTuple [t,_,_]) -> t))
  , ("snd3", ( finalise $ tyTuple [a, b, c] --> b
             , CBuiltin WHNF $ \(CTuple [_,t,_]) -> t))
  , ("trd3", ( finalise $ tyTuple [a, b, c] --> c
             , CBuiltin WHNF $ \(CTuple [_,_,t]) -> t)) ]

  []

intBinOp :: (Int -> Int -> Int) -> (Scheme, Term)
intBinOp f = ( finalise $ tyInt --> tyInt --> tyInt
             , toTerm f )

intCompOp :: (Int -> Int -> Bool) -> (Scheme, Term)
intCompOp f = ( finalise $ tyInt --> tyInt --> tyBool
              , toTerm f )

intFn :: (Int -> Term) -> Term
intFn f = CBuiltin Full $ \(CInt n) -> f n

listFn :: ([Term] -> Term) -> Term
listFn f = CBuiltin Full $ \t -> case clist2list t of
  Just xs -> f xs
  Nothing -> error "this shouldn't happen"

insertKV :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
insertKV k v [] = [(k, v)]
insertKV k v ((k', v'):xs)
  | k == k' = (k, v) : xs
  | otherwise = (k', v') : insertKV k v xs
