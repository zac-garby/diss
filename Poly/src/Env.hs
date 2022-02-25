module Env ( Environment
           , defaultEnv ) where

import Types
import Compiler

type Environment = [(String, (Scheme, Term))]

defaultEnv :: Environment
defaultEnv = [ ("add", intBinOp (+))
             , ("sub", intBinOp (-))
             , ("mul", intBinOp (*))
             , ("div", intBinOp div)
             , ("eq", ( finalise $ tyInt --> tyInt --> tyBool
                      , intFn $ \m -> intFn $ \n -> CLitBool (m == n) )) ]

intBinOp :: (Int -> Int -> Int) -> (Scheme, Term)
intBinOp f = (ty, t)
  where ty = finalise (tyInt --> tyInt --> tyInt)
        t = intFn $ \m -> intFn $ \n -> CLitInt (f m n)

intFn :: (Int -> Term) -> Term
intFn f = CBuiltin $ \(CLitInt n) -> f n
