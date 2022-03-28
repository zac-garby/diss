module Holes ( BoundHole (..)
             , relevant
             , possibleFits ) where

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

possibleFits :: BoundHole -> (Env, Env)
possibleFits (BoundHole _ t env) = (unique best, unique viable)
  where sch = finalise t
        best = filter (\(_, (sch', _)) -> sch' <= sch) env
        
        -- these fits would involve specialising the type of the hole
        -- which is not always desirable
        viable = filter (\(i, (sch', _)) -> sch < sch') env

        unique = nubBy (\(i, _) (j, _) -> i == j)

