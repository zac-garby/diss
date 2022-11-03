module Synthesis where

import Control.Monad.Reader
import Control.Monad.State.Lazy

import Parser
import Compiler
import Types
import Env

data Context = Context
  { env :: Environment
  , examples :: [Example]
  , functions :: [(Ident, (Scheme, [Example]))] }

data Example = Eg [Term] Term

type Synth = StateT [Ident] (Reader Context)

synthesise :: Environment -> Type -> [Example] -> Expr
synthesise env goal egs = undefined
  where ctx = Context { env = env
                      , examples = egs
                      , functions = [("f", (finalise goal, egs))] }

synth :: Type -> Synth Expr
synth t@(TyConstr "->" [a, b]) = undefined

fresh :: Synth Ident
fresh = do
  name <- gets head
  modify tail
  return name

