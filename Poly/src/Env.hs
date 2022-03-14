module Env ( Environment
           , defaultEnv ) where

import Types
import Compiler

type Environment = [(String, (Scheme, Term))]

a = TyVar "a"
b = TyVar "b"

defaultEnv :: Environment
defaultEnv = [ ("add", intBinOp (+))
             , ("sub", intBinOp (-))
             , ("mul", intBinOp (*))
             , ("div", intBinOp div)
             , ("eq", ( finalise $ tyInt --> tyInt --> tyBool
                      , intFn $ \m -> intFn $ \n -> CLitBool (m == n) ))
             , ("head", listOp head)
             , ("tail", listOp (list2clist . tail))
             , ("cons", ( finalise $ a --> tyList a --> tyList a
                        , CBuiltin $ \h -> listFn (list2clist . (h:)))) ]

intBinOp :: (Int -> Int -> Int) -> (Scheme, Term)
intBinOp f = (ty, t)
  where ty = finalise (tyInt --> tyInt --> tyInt)
        t = intFn $ \m -> intFn $ \n -> CLitInt (f m n)

listOp :: ([Term] -> Term) -> (Scheme, Term)
listOp f = (ty, listFn f)
  where ty = finalise (tyList a --> tyList a)

intFn :: (Int -> Term) -> Term
intFn f = CBuiltin $ \(CLitInt n) -> f n

listFn :: ([Term] -> Term) -> Term
listFn f = CBuiltin $ \t -> case clist2list t of
  Just xs -> f xs
  Nothing -> error "this shouldn't happen"
