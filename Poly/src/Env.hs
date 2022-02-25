module Env ( Environment
           , defaultEnv ) where

import Types
import Compiler

type Environment = [(String, (Scheme, Term))]

defaultEnv :: Environment
defaultEnv = [ ("one", (Forall [] tyInt, CLitInt 1)) ]
