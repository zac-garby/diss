module Holes ( BoundHole (..)
             , Fit (..)
             , relevant
             , viableFits ) where

import Data.List
import Debug.Trace

import Parser
import Types

data BoundHole = BoundHole HoleIndex Type Env
  deriving Show

instance Sub BoundHole where
  sub s (BoundHole i t e) = BoundHole i (sub s t) (sub s e)

relevant :: BoundHole -> Env
relevant (BoundHole _ _ env) = reverse $ nubBy (\(i, _) (j, _) -> i == j)
           [ (id, (t, l)) | (id, (t, l)) <- env, l == Local ]

data Fit = Fit { id :: Ident
               , args :: [Type]
               , scheme :: Scheme }
           deriving (Eq, Show)

viableFits :: BoundHole -> [Fit]
viableFits (BoundHole _ t env) = map snd $ sortOn fst $ map specialise $ unique fits
  where sch = Forall [] t
        fs = partials env
        
        fits = filter (\(Fit i args sch') -> sch' <= sch) fs
        unique = nubBy (\(Fit i xs _) (Fit j ys _) -> i == j && length xs == length ys)

        specialise :: Fit -> (Int, Fit)
        specialise (Fit i args sch') = (complexity s, Fit i (map (sub s) args) sch)
          where s = mkSubst sch' sch

        complexity :: Subst -> Int
        complexity [] = 0
        complexity ((v, t):rest) = c t + complexity rest
          where c (TyVar _) = 1
                c (TyConstr _ ts) = 1 + sum (map c ts)
                c (TyHole _) = 1

        mkSubst (Forall vs1 t1) (Forall vs2 t2) = subst t1 t2
          where subst (TyVar a) t2
                  | a `elem` vs1 = [(a, t2)]
                subst (TyConstr c1 ts1) (TyConstr c2 ts2)
                  | c1 == c2 = concat [ subst t1 t2 | (t1, t2) <- zip ts1 ts2 ]
                subst h@(TyHole i) t2 = [(show h, t2)]
                subst _ _ = []

        partials :: Env -> [Fit]
        partials env = go [ Fit i [] t | (i, (t, _)) <- env ]
          where go ps = case ps >>= app of
                  [] -> ps
                  ps' -> ps ++ go ps'
  
                app (Fit i as (Forall vs (TyConstr "->" [a, b])))
                  = [Fit i (as ++ [a]) (Forall vs b)]
                app _ = []
