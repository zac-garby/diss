module Eval where

import Data.Foldable

import Compiler

eval :: Term -> Term
eval t = case evalStep t of
  Just t' -> eval t'
  Nothing -> t

evalStep :: Term -> Maybe Term
evalStep t = asum $ map ($t) [ evalAppAbs
                             , evalApp1
                             , evalApp2
                             , evalIf
                             , evalFix ]

evalApp1 :: Term -> Maybe Term
evalApp1 (CApp t1 t2) = do
  t1' <- evalStep t1
  return $ CApp t1' t2
evalApp1 _ = Nothing

evalApp2 :: Term -> Maybe Term
evalApp2 (CApp t1 t2) = do
  t2' <- evalStep t2
  return $ CApp t1 t2'
evalApp2 _ = Nothing

evalAppAbs :: Term -> Maybe Term
evalAppAbs (CApp (CAbs t12) v2) = return $ shift (-1) ((0 --> shift 1 v2) t12)
evalAppAbs _ = Nothing

evalFix :: Term -> Maybe Term
evalFix (CFix t) = return $ CApp t (CFix t)
evalFix _ = Nothing

evalIf :: Term -> Maybe Term
evalIf (CIf (CLitBool True) t _) = return t
evalIf (CIf (CLitBool False) _ f) = return f
evalIf (CIf cond t f) = do
  cond' <- evalStep cond
  return $ CIf cond' t f
evalIf _ = Nothing

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

(-->) :: Int -> Term -> Term -> Term
(j --> s) (CVar n) | j == n = s
                   | otherwise = CVar n
(j --> s) (CAbs t) = CAbs $ ((j+1) --> (shift 1 s)) t
(j --> s) (CApp f x) = CApp ((j --> s) f) ((j --> s) x)
(j --> s) (CFix t) = CFix ((j --> s) t)
(j --> s) (CIf cond t f) = CIf ((j --> s) cond) ((j --> s) t) ((j --> s) f)
(j --> s) (CLitInt i) = CLitInt i
(j --> s) (CLitBool b) = CLitBool b
