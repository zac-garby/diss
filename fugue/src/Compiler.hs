module Compiler ( Term (..)
                , EvalType (..)
                , CompilerError (..)
                , Value (..)
                , Index
                , list2clist
                , clist2list
                , compile ) where

import Data.List
import Control.Monad.Reader
import Control.Monad.Except
import Debug.Trace

import Parser
import Types

type Index = Int

data EvalType = Full | WHNF | None
  deriving (Show, Eq)

data Term = CVar Index
          | CAbs Term
          | CApp Term Term
          | CFix Term
          | CIf Term Term Term
          | CInt Int
          | CBool Bool
          | CChar Char
          | CConstr Ident
          | CNil
          | CCons Term Term
          | CTuple [Term]
          | CBuiltin EvalType (Term -> Term)

instance Show Term where
  show (CVar i) = show i
  show (CAbs t) = "λ." ++ show t
  show (CApp f x) = bracket (show f) ++ bracket (show x)
  show (CFix t) = "fix " ++ show t
  show (CIf cond t f) = "if " ++ show cond ++ " then " ++ show t ++ " else " ++ show f
  show (CInt i) = "#" ++ show i
  show (CBool b) = show b
  show (CChar c) = show c
  show (CConstr id) = id
  show (CNil) = "[]"
  show (CCons h t) = bracket (show h) ++ " :: " ++ bracket (show t)
  show (CTuple xs) = "(" ++ intercalate ", " (map show xs) ++ ")"
  show (CBuiltin Full f) = "<builtin>"
  show (CBuiltin WHNF f) = "<builtin (to WHNF)>"
  show (CBuiltin None f) = "<builtin (no eval)>"

instance Eq Term where
  (CInt x) == (CInt y) = x == y
  (CBool x) == (CBool y) = x == y
  (CChar x) == (CChar y) = x == y
  CNil == CNil = True
  (CCons x xs) == (CCons y ys) = x == y && xs == ys
  (CTuple xs) == (CTuple ys) = and $ zipWith (==) xs ys
  _ == _ = False

bracket :: String -> String
bracket s = "(" ++ s ++ ")"

data CompilerError = UndefinedVariable Ident
                   | FoundHole

type Compiler = ReaderT [Ident] (Except CompilerError)

compile :: Env -> Expr -> Except CompilerError Term
compile env e = runReaderT (fromExpr e) names
  where names = map fst env

fromExpr :: Expr -> Compiler Term

fromExpr (Var v) = do
  ns <- ask
  case elemIndex v ns of
    Just i -> return $ CVar i
    Nothing -> throwError $ UndefinedVariable v
    
fromExpr (App f x) = do
  f' <- fromExpr f
  x' <- fromExpr x
  return $ CApp f' x'
  
fromExpr (Abs v t) = do
  t' <- with v $ fromExpr t
  return $ CAbs t'

fromExpr (Let v val body) = fromExpr $ App (Abs v body) val

fromExpr (LetRec v val body) = do
  body' <- with v $ fromExpr body
  val' <- with v $ fromExpr val
  return $ CApp (CAbs body') (CFix $ CAbs val')

fromExpr (If cond t f) = do
  cond' <- fromExpr cond
  t' <- fromExpr t
  f' <- fromExpr f
  return $ CIf cond' t' f'

fromExpr (LitInt n) = return $ CInt n
fromExpr (LitBool b) = return $ CBool b
fromExpr (LitChar c) = return $ CChar c

fromExpr (LitList xs) = do
  xs' <- mapM fromExpr xs
  return $ foldr CCons CNil xs'

fromExpr (LitTuple xs) = do
  xs' <- mapM fromExpr xs
  return $ CTuple xs'

fromExpr (TypeSpec e _) = fromExpr e

fromExpr (Hole i) = throwError FoundHole

with :: Ident -> Compiler a -> Compiler a
with i = local (i:)

list2clist :: [Term] -> Term
list2clist = foldr CCons CNil

clist2list :: Term -> Maybe [Term]
clist2list (CCons h t) = do
  rest <- clist2list t
  return $ h : rest
clist2list CNil = return []
clist2list _ = Nothing

class Value a where
  toTerm :: a -> Term
  fromTerm :: Term -> a

instance Value Int where
  toTerm n = CInt n
  fromTerm (CInt n) = n

instance Value Bool where
  toTerm b = CBool b
  fromTerm (CBool b) = b

instance Value Char where
  toTerm c = CChar c
  fromTerm (CChar c) = c

instance Value a => Value [a] where
  toTerm xs = foldr CCons CNil (map toTerm xs)

  fromTerm (CCons h t) = fromTerm h : fromTerm t
  fromTerm CNil = []

instance (Value a, Value b) => Value (a -> b) where
  toTerm f = CBuiltin Full $ \t -> toTerm (f (fromTerm t))
  fromTerm (CBuiltin _ f) = \a -> fromTerm (f (toTerm a))

instance Value () where
  toTerm () = CTuple []
  fromTerm _ = ()

instance (Value a, Value b) => Value (a, b) where
  toTerm (a, b) = CTuple [toTerm a, toTerm b]
  fromTerm (CTuple [a, b]) = (fromTerm a, fromTerm b)

-- ...
