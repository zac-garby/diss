{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use record patterns" #-}
module Eval ( eval
            , subEnv ) where

import Data.Foldable
import Data.Maybe
import Control.Applicative
import Debug.Trace

import Compiler

eval :: Term -> Term
eval t = case evalStep $! t of
  Just t' -> eval $! t'
  Nothing -> t

subEnv :: [Term] -> Term -> Term
subEnv vs = foldr (.) id (zipWith (-->) [0..] vs)

evalStep :: Term -> Maybe Term
evalStep t = evalAppAbs t
         <|> evalApp1 t
         <|> evalApp2 t
         <|> evalFix t
         <|> evalIf t
         <|> evalCase t
         <|> evalTuple t
         <|> evalInt t

evalAppAbs :: Term -> Maybe Term
evalAppAbs (CAbs t12 :$ v2) | isValue v2 = return $ shift (-1) ((0 --> shift 1 v2) t12)
evalAppAbs (CBuiltin t f :$ v) | isProper t v = return $ f v
evalAppAbs _ = Nothing

evalApp1 :: Term -> Maybe Term
evalApp1 (t1 :$ t2) = do
  t1' <- evalStep t1
  return $ t1' :$ t2
evalApp1 _ = Nothing

evalApp2 :: Term -> Maybe Term
evalApp2 (t1 :$ t2) = do
  t2' <- evalStep t2
  return $ t1 :$ t2'
evalApp2 _ = Nothing

evalFix :: Term -> Maybe Term
evalFix f@(CFix (CAbs t)) = return $ (0 --> f) t
evalFix (CFix t) = do
  t' <- evalStep t
  return $! CFix t'
evalFix _ = Nothing

evalIf :: Term -> Maybe Term
evalIf (CIf CTrue t _) = return t
evalIf (CIf CFalse _ f) = return f
evalIf (CIf cond t f) = do
  cond' <- evalStep cond
  return $ CIf cond' t f
evalIf _ = Nothing

evalCase :: Term -> Maybe Term
evalCase (CCase _ []) = undefined
evalCase (CCase t cs'@((con, body) : cs))
  | isValue t = case match con t body of
      Just args -> return $ foldl CApp body args
      Nothing -> return $ CCase t cs
  | otherwise = do
      t' <- evalStep t
      return $ CCase t cs'
evalCase _ = Nothing

evalTuple :: Term -> Maybe Term
evalTuple (CPair x y) = case evalStep x of
  Just x' -> return $ CPair x' y
  Nothing -> do
    y' <- evalStep y
    return $ CPair x y'
evalTuple _ = Nothing

evalInt :: Term -> Maybe Term
evalInt CZero = return $ CInt 0
evalInt (CSuc (CInt n)) = return $ CInt (1 + n)
evalInt _ = Nothing

match :: String -> Term -> Term -> Maybe [Term]
match con (f :$ x) (CAbs b) = do
  args <- match con f b
  return $ args ++ [x]
match con (CConstr con') b | con == con' = return []
match "Zero" (CInt 0) b = return []
match "Suc" (CInt n) b | n > 0 = return [CInt (n - 1)]
match _ _ _ = Nothing

isProper :: EvalType -> Term -> Bool
isProper Full = isValue
isProper WHNF = isWHNF
isProper None = const True

isValue :: Term -> Bool
isValue (CVar _) = True
isValue (CAbs _) = True
isValue ((CAbs _) :$ _) = False
isValue ((CBuiltin _ _) :$ _) = False
isValue (a :$ b) = isValue a && isValue b
isValue (CFix t) = False
isValue (CIf _ _ _) = False
isValue (CCase _ _) = False
isValue (CInt _) = True
isValue (CChar _) = True
isValue CZero = False
isValue (CConstr "Suc") = False
isValue (CConstr _) = True
isValue (CPair a b) = isValue a && isValue b
isValue (CBuiltin _ _) = True

isWHNF :: Term -> Bool
isWHNF (CConstr _ :$ a) = True
isWHNF (a :$ b) = isWHNF a
isWHNF t = isValue t

shift :: Int -> Term -> Term
shift d = shift' d 0

shift' :: Int -> Int -> Term -> Term
shift' d c (CVar n) | n < c = CVar n
                    | otherwise = CVar (n + d)
shift' d c (CAbs t) = CAbs (shift' d (c + 1) t)
shift' d c (f :$ x) = CApp (shift' d c f) (shift' d c x)
shift' d c (CFix t) = CFix (shift' d c t)
shift' d c (CIf cond t f) = CIf (shift' d c cond) (shift' d c t) (shift' d c f)
shift' d c (CCase t cs) = CCase (shift' d c t) [ (con, shift' d c b) | (con, b) <- cs ]
shift' d c (CInt i) = CInt i
shift' d c (CChar ch) = CChar ch
shift' d c (CConstr con) = CConstr con
shift' d c (CPair x y) = CPair (shift' d c x) (shift' d c y)
shift' d c (CBuiltin t f) = CBuiltin t f

(-->) :: Int -> Term -> Term -> Term
(j --> s) (CVar n) | j == n = s
                   | otherwise = CVar n
(j --> s) (CAbs t) = CAbs $! ((j+1) --> shift 1 s) t
(j --> s) (f :$ x) = (j --> s) f :$ (j --> s) x
(j --> s) (CFix t) = CFix $! (j --> s) t
(j --> s) (CIf cond t f) = CIf ((j --> s) cond) ((j --> s) t) ((j --> s) f)
(j --> s) (CCase t cs) = CCase ((j --> s) t) [ (con, (j --> s) b) | (con, b) <- cs ]
(j --> s) (CInt i) = CInt i
(j --> s) (CChar c) = CChar c
(j --> s) (CConstr c) = CConstr c
(j --> s) (CPair x y) = CPair ((j --> s) x) ((j --> s) y)
(j --> s) (CBuiltin t f) = CBuiltin t f
