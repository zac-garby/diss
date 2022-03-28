module Holes ( BoundHole (..)
             , relevant ) where

import Data.List

import Parser
import Types

data BoundHole = BoundHole HoleIndex Type Env
  deriving Show

instance Sub BoundHole where
  sub s (BoundHole i t e) = BoundHole i (sub s t) (sub s e)

relevant :: BoundHole -> Env
relevant (BoundHole _ _ env) = reverse $ nubBy (\(i, _) (j, _) -> i == j)
           [ (id, (t, l)) | (id, (t, l)) <- env, l == Local ]
