module Env ( Environment (..)
           , defaultEnv
           , defineTerm
           , undefineTerm
           , defineDataType
           , lookupTerm
           , lookupDataType
           , fromEnvironment
           , envTerms ) where

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

undefineTerm :: String -> Environment -> Environment
undefineTerm name (Environment terms types) =
  Environment (deleteKV name terms) types

defineDataType :: String -> DataType -> Environment -> Environment
defineDataType name dt (Environment terms types) =
  Environment terms (insertKV name dt types)

lookupTerm :: String -> Environment -> Maybe (Scheme, Term)
lookupTerm name (Environment terms _) = lookup name terms

lookupDataType :: String -> Environment -> Maybe DataType
lookupDataType name (Environment _ types) = lookup name types

fromEnvironment :: Environment -> Env
fromEnvironment emt = [ (n, (sch, Global)) | (n, (sch, _)) <- terms emt ]

envTerms :: Environment -> [Term]
envTerms emt = [ t | (_, (_, t)) <- terms emt ]

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
  , ("Zero", ( finalise tyInt
             , CConstr "Zero") )
  , ("Suc", ( finalise $ tyInt --> tyInt
            , CConstr "Suc" )) ]

  [ ("Int", DataType []
            [ DataConstructor "Zero" []
            , DataConstructor "Suc" [tyInt]]) ]

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

deleteKV :: Eq a => a -> [(a, b)] -> [(a, b)]
deleteKV k [] = []
deleteKV k ((k', v'):xs)
  | k == k' = xs
  | otherwise = (k', v') : deleteKV k xs