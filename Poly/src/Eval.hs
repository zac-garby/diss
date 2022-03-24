module Eval ( eval
            , subEnv ) where

import Data.Foldable
import Data.Maybe
import Control.Applicative
import Debug.Trace

import Compiler

eval :: Term -> Term
eval t = eval' $! t

eval' :: Term -> Term
eval' t = case evalStep $! t of
  Just t' -> eval' $! t'
  Nothing -> t

subEnv :: [Term] -> Term -> Term
subEnv vs = foldr (.) id (zipWith (-->) [0..] vs)

evalStep :: Term -> Maybe Term
evalStep (CApp (CAbs t12) v2) | isValue v2 = return $! shift (-1) ((0 --> shift 1 v2) t12)
evalStep (CApp (CBuiltin t f) v) | isProper t v = return $! f v
evalStep (CApp t1 t2) = case evalStep $! t1 of
  Just t1' -> return $! CApp t1' t2
  Nothing -> do
    t2' <- evalStep $! t2
    return $ CApp t1 t2'
evalStep f@(CFix (CAbs t)) = return $ (0 --> f) t
evalStep (CFix t) = do
  t' <- evalStep t
  return $! CFix t'
evalStep (CIf (CLitBool True) t _) = return $! t
evalStep (CIf (CLitBool False) _ f) = return $! f
evalStep (CIf cond t f) = do
  cond' <- evalStep $! cond
  return $ CIf cond' t f
evalStep (CLitCons h t) = case evalStep $! h of
  Just h' -> return $! CLitCons h' t
  Nothing -> do
    t' <- evalStep $! t
    return $ CLitCons h t'
evalStep (CLitTuple (x:xs)) = case evalStep $! x of
  Just x' -> return $! CLitTuple (x' : xs)
  Nothing -> do
    rest <- evalStep $! CLitTuple xs
    let (CLitTuple xs') = rest
    return $ CLitTuple (x : xs')
evalStep _ = Nothing

isProper :: EvalType -> Term -> Bool
isProper Full = isValue
isProper WHNF = isWHNF
isProper None = const True

isValue :: Term -> Bool
isValue (CVar _) = True
isValue (CAbs _) = True
isValue (CApp (CAbs _) _) = False
isValue (CApp (CBuiltin _ _) _) = False
isValue (CApp a b) = isValue a && isValue b
isValue (CFix t) = False
isValue (CIf _ _ _) = False
isValue (CLitInt _) = True
isValue (CLitBool _) = True
isValue (CLitChar _) = True
isValue CLitNil = True
isValue (CLitCons a b) = isValue a && isValue b
isValue (CLitTuple xs) = all isValue xs
isValue (CBuiltin _ _) = True

isWHNF :: Term -> Bool
isWHNF (CLitCons h _) = isValue h
isWHNF t = isValue t

shift :: Int -> Term -> Term
shift d = shift' d 0

shift' :: Int -> Int -> Term -> Term
shift' d c (CVar n) | n < c = CVar n
                    | otherwise = CVar (n + d)
shift' d c (CAbs t) = CAbs (shift' d (c + 1) t)
shift' d c (CApp f x) = CApp (shift' d c f) (shift' d c x)
shift' d c (CFix t) = CFix (shift' d c t)
shift' d c (CIf cond t f) = CIf (shift' d c cond) (shift' d c t) (shift' d c f)
shift' d c (CLitInt i) = CLitInt i
shift' d c (CLitBool b) = CLitBool b
shift' d c (CLitChar ch) = CLitChar ch
shift' d c (CLitNil) = CLitNil
shift' d c (CLitCons a b) = CLitCons (shift' d c a) (shift' d c b)
shift' d c (CLitTuple xs) = CLitTuple (map (shift' d c) xs)
shift' d c (CBuiltin t f) = CBuiltin t f

(-->) :: Int -> Term -> Term -> Term
(j --> s) (CVar n) | j == n = s
                   | otherwise = CVar n
(j --> s) (CAbs t) = CAbs $! ((j+1) --> (shift 1 s)) t
(j --> s) (CApp f x) = (CApp $! (j --> s) f) $! ((j --> s) x)
(j --> s) (CFix t) = CFix $! (j --> s) t
(j --> s) (CIf cond t f) = CIf ((j --> s) cond) ((j --> s) t) ((j --> s) f)
(j --> s) (CLitInt i) = CLitInt i
(j --> s) (CLitBool b) = CLitBool b
(j --> s) (CLitChar c) = CLitChar c
(j --> s) (CLitNil) = CLitNil
(j --> s) (CLitCons a b) = CLitCons ((j --> s) a) ((j --> s) b)
(j --> s) (CLitTuple xs) = CLitTuple (map (j --> s) xs)
(j --> s) (CBuiltin t f) = CBuiltin t f
