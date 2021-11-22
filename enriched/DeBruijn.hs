module DeBruijn where

import Control.Applicative
import Control.Monad
import Data.List
import Data.Maybe

import qualified Named

type Index = Int
type Name = String

data Term = Var Index
          | Abs Name Term
          | App Term Term
          | Let Name Term Term
          deriving Eq

type Names = [String]

app :: [Term] -> Term
app = foldl1 App

showTerm :: Names -> Term -> String
showTerm ns t = showTerm' ns False t

showTerm' :: Names -> Bool -> Term -> String
showTerm' ns b (Var i) = ns !! i
showTerm' ns b (Abs n t) = bracket b $ "λ" ++ n ++ "." ++ showTerm' (n : ns) False t
showTerm' ns b (App f x) = bracket b (showTerm' ns True f ++ " " ++ showTerm' ns True x)

bracket :: Bool -> String -> String
bracket True s = "(" ++ s ++ ")"
bracket False s = s

instance Show Term where
  show (Var i) = show i
  show (Abs n t) = "λ" ++ n ++ "." ++ show t
  show (App f x) = "(" ++ show f ++ " " ++ show x ++ ")"

-- issue: (λf.λx.f x) x -> λx.x x, but the two x's there are distinct
fromNamed :: Named.Term -> (Term, Names)
fromNamed = fromNamed' []

fromNamed' :: Names -> Named.Term -> (Term, Names)
fromNamed' ns (Named.Var n) = case elemIndex n ns of
  Just i -> (Var i, ns)
  Nothing -> (Var (length ns), ns ++ [n])
fromNamed' ns (Named.Abs n t) = (Abs n t', tail ns')
  where (t', ns') = fromNamed' (n : ns) t
fromNamed' ns (Named.App f x) =
  let (f', ns') = fromNamed' ns f
      (x', ns'') = fromNamed' ns' x
  in (App f' x', ns'')

parseTerm :: String -> Maybe (Term, Names)
parseTerm x = do
  t <- Named.parseTerm x
  return $ fromNamed t

parseTerm1 = fromJust . parseTerm

eval :: Term -> Term
eval t = case evalStep t of
  Just t' -> eval t'
  Nothing -> t

evalStep :: Term -> Maybe Term
evalStep t = evalAppAbs t <|> evalApp1 t <|> evalApp2 t

evalApp1 :: Term -> Maybe Term
evalApp1 (App t1 t2) = do
  t1' <- evalStep t1
  return $ App t1' t2
evalApp1 _ = Nothing

evalApp2 :: Term -> Maybe Term
evalApp2 (App v1 t2) | isValue v1 = do
  t2' <- evalStep t2
  return $ App v1 t2'
evalApp2 _ = Nothing

evalAppAbs :: Term -> Maybe Term
evalAppAbs (App (Abs _ t12) v2) = return $ shift (-1) ((0 --> shift 1 v2) t12)
evalAppAbs _ = Nothing

isValue :: Term -> Bool
isValue (Abs _ _) = True
isValue _ = False

shift :: Int -> Term -> Term
shift d = shift' d 0

shift' :: Int -> Int -> Term -> Term
shift' d c (Var n) | n < c = Var n
                   | otherwise = Var (n + d)
shift' d c (Abs n t) = Abs n (shift' d (c + 1) t)
shift' d c (App f x) = App (shift' d c f) (shift' d c x)

(-->) :: Int -> Term -> Term -> Term
(j --> s) (Var n) | j == n = s
                  | otherwise = Var n
(j --> s) (Abs n t) = Abs n $ ((j+1) --> (shift 1 s)) t
(j --> s) (App f x) = App ((j --> s) f) ((j --> s) x)
