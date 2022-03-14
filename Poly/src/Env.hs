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
                      , toTerm ((==) :: Int -> Int -> Bool) ))
             , ("head", ( finalise $ tyList a --> a
                        , listFn head ))
             , ("tail", ( finalise $ tyList a --> tyList a
                        , listFn $ list2clist . tail))
             , ("cons", ( finalise $ a --> tyList a --> tyList a
                        , CBuiltin $ \h -> listFn (list2clist . (h:)))) ]

intBinOp :: (Int -> Int -> Int) -> (Scheme, Term)
intBinOp f = ( finalise $ tyInt --> tyInt --> tyInt
             , toTerm f)

intFn :: (Int -> Term) -> Term
intFn f = CBuiltin $ \(CLitInt n) -> f n

listFn :: ([Term] -> Term) -> Term
listFn f = CBuiltin $ \t -> case clist2list t of
  Just xs -> f xs
  Nothing -> error "this shouldn't happen"
