module Env ( Environment
           , defaultEnv ) where

import Data.Char

import Types
import Infer
import Compiler

type Environment = [(String, (Scheme, Term))]

a = TyVar "a"
b = TyVar "b"

defaultEnv :: Environment
defaultEnv = [ ("__add", intBinOp (+))
             , ("__sub", intBinOp (-))
             , ("__mul", intBinOp (*))
             , ("__div", intBinOp div)
             , ("__eq", intCompOp (==))
             , ("__lt", intCompOp (<))
             , ("__gt", intCompOp (>))
             , ("__lte", intCompOp (<=))
             , ("__gte", intCompOp (>=))
             , ("head", ( finalise $ tyList a --> a
                        , CBuiltin WHNF headFn ))
             , ("tail", ( finalise $ tyList a --> tyList a
                        , CBuiltin WHNF tailFn ))
             , ("null", ( finalise $ tyList a --> tyBool
                        , CBuiltin WHNF nullFn ))
             , ("__cons", ( finalise $ a --> tyList a --> tyList a
                        , CBuiltin None $ \h ->
                            CBuiltin None $ \t -> CCons h t ))
             , ("chr", ( finalise $ tyInt --> tyChar
                       , toTerm chr ))
             , ("ord", ( finalise $ tyChar --> tyInt
                       , toTerm ord )) ]

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

headFn :: Term -> Term
headFn (CCons hd _) = hd
headFn CNil = error "the empty list doesn't have a head"

tailFn :: Term -> Term
tailFn (CCons _ tl) = tl
tailFn CNil = error "the empty list doesn't have a tail"

nullFn :: Term -> Term
nullFn (CCons _ _) = toTerm False
nullFn CNil = toTerm True
