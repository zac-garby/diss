module Compiler ( Term (..)
                , EvalType (..)
                , CompilerError (..)
                , Value (..)
                , Index
                , list2clist
                , clist2list
                , outputShow
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
          | CLitInt Int
          | CLitBool Bool
          | CLitChar Char
          | CLitNil
          | CLitCons Term Term
          | CBuiltin EvalType (Term -> Term)

instance Show Term where
  show (CVar i) = show i
  show (CAbs t) = "λ." ++ show t
  show (CApp f x) = bracket (show f) ++ bracket (show x)
  show (CFix t) = "fix " ++ show t
  show (CIf cond t f) = "if " ++ show cond ++ " then " ++ show t ++ " else " ++ show f
  show (CLitInt i) = "#" ++ show i
  show (CLitBool b) = show b
  show (CLitChar c) = show c
  show (CLitNil) = "[]"
  show (CLitCons h t) = bracket (show h) ++ " :: " ++ bracket (show t)
  show (CBuiltin Full f) = "<builtin>"
  show (CBuiltin WHNF f) = "<builtin (to WHNF)>"
  show (CBuiltin None f) = "<builtin (no eval)>"

outputShow :: Term -> Maybe String
outputShow (CLitInt i) = Just $ show i
outputShow (CLitBool b) = Just $ show b
outputShow (CLitChar c) = Just $ show c
outputShow (CLitNil) = Just "[]"
outputShow c@(CLitCons (CLitChar _) _) = do
  cs <- clist2list c
  return $ "\"" ++ map (\(CLitChar c) -> c) cs ++ "\""
outputShow c@(CLitCons h t) = do
  ts <- clist2list c
  strings <- mapM outputShow ts
  return $ "[" ++ intercalate ", " strings ++ "]"
outputShow _ = Nothing

bracket :: String -> String
bracket s = "(" ++ s ++ ")"

data CompilerError = UndefinedVariable Ident
                   | FoundHole

instance Show CompilerError where
  show (UndefinedVariable v) = "undeclared variable: " ++ v
  show FoundHole = "attempted to compile an incomplete expression containing a hole"

type Compiler = ReaderT [Ident] (Except CompilerError)

compile :: Env -> Expr -> Except CompilerError Term
compile env e = runReaderT (fromExpr e) names
  where names = map fst env

runCompiler :: Compiler a -> Either CompilerError a
runCompiler c = runExcept (runReaderT c [])

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

fromExpr (LitInt n) = return $ CLitInt n
fromExpr (LitBool b) = return $ CLitBool b
fromExpr (LitChar c) = return $ CLitChar c
fromExpr (LitList xs) = do
  xs' <- mapM fromExpr xs
  return $ foldr CLitCons CLitNil xs'

fromExpr (TypeSpec e _) = fromExpr e

fromExpr (Hole i) = throwError FoundHole

with :: Ident -> Compiler a -> Compiler a
with i = local (i:)

list2clist :: [Term] -> Term
list2clist = foldr CLitCons CLitNil

clist2list :: Term -> Maybe [Term]
clist2list (CLitCons h t) = do
  rest <- clist2list t
  return $ h : rest
clist2list CLitNil = return []
clist2list _ = Nothing

class Value a where
  toTerm :: a -> Term
  fromTerm :: Term -> a

instance Value Int where
  toTerm n = CLitInt n
  fromTerm (CLitInt n) = n

instance Value Bool where
  toTerm b = CLitBool b
  fromTerm (CLitBool b) = b

instance Value Char where
  toTerm c = CLitChar c
  fromTerm (CLitChar c) = c

instance Value a => Value [a] where
  toTerm xs = foldr CLitCons CLitNil (map toTerm xs)

  fromTerm (CLitCons h t) = fromTerm h : fromTerm t
  fromTerm CLitNil = []

instance (Value a, Value b) => Value (a -> b) where
  toTerm f = CBuiltin Full $ \t -> toTerm (f (fromTerm t))
  fromTerm (CBuiltin _ f) = \a -> fromTerm (f (toTerm a))
