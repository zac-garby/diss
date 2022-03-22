module Env ( Environment
           , defaultEnv ) where

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
                            CBuiltin None $ \t -> CLitCons h t )) ]

intBinOp :: (Int -> Int -> Int) -> (Scheme, Term)
intBinOp f = ( finalise $ tyInt --> tyInt --> tyInt
             , toTerm f )

intCompOp :: (Int -> Int -> Bool) -> (Scheme, Term)
intCompOp f = ( finalise $ tyInt --> tyInt --> tyBool
              , toTerm f )

intFn :: (Int -> Term) -> Term
intFn f = CBuiltin Full $ \(CLitInt n) -> f n

listFn :: ([Term] -> Term) -> Term
listFn f = CBuiltin Full $ \t -> case clist2list t of
  Just xs -> f xs
  Nothing -> error "this shouldn't happen"

headFn :: Term -> Term
headFn (CLitCons hd _) = hd
headFn CLitNil = error "the empty list doesn't have a head"

tailFn :: Term -> Term
tailFn (CLitCons _ tl) = tl
tailFn CLitNil = error "the empty list doesn't have a tail"

nullFn :: Term -> Term
nullFn (CLitCons _ _) = toTerm False
nullFn CLitNil = toTerm True
