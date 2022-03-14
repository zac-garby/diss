module Compiler ( Term (..)
                , CompilerError (..)
                , Index
                , outputShow
                , clist2list
                , list2clist
                , compile ) where

import Data.List
import Control.Monad.Reader
import Control.Monad.Except
import Debug.Trace

import Parser
import Types

type Index = Int

data Term = CVar Index
          | CAbs Term
          | CApp Term Term
          | CFix Term
          | CIf Term Term Term
          | CLitInt Int
          | CLitBool Bool
          | CLitNil
          | CLitCons Term Term
          | CBuiltin (Term -> Term)

instance Show Term where
  show (CVar i) = show i
  show (CAbs t) = "λ." ++ show t
  show (CApp f x) = bracket (show f) ++ bracket (show x)
  show (CFix t) = "fix " ++ show t
  show (CIf cond t f) = "if " ++ show cond ++ " then " ++ show t ++ " else " ++ show f
  show (CLitInt i) = "#" ++ show i
  show (CLitBool b) = show b
  show (CLitNil) = "[]"
  show (CLitCons h t) = bracket (show h) ++ " :: " ++ bracket (show t)
  show (CBuiltin f) = "<builtin>"

outputShow :: Term -> Maybe String
outputShow (CLitInt i) = Just $ show i
outputShow (CLitBool b) = Just $ show b
outputShow (CLitNil) = Just "[]"
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
fromExpr (LitList xs) = do
  xs' <- mapM fromExpr xs
  return $ list2clist xs'
fromExpr (Hole i) = throwError FoundHole

with :: Ident -> Compiler a -> Compiler a
with i = local (i:)
  
clist2list :: Term -> Maybe [Term]
clist2list (CLitCons h t) = do
  rest <- clist2list t
  return $ h : rest
clist2list CLitNil = return []
clist2list _ = Nothing

list2clist :: [Term] -> Term
list2clist = foldr CLitCons CLitNil
