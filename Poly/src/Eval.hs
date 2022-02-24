module Eval where

import Control.Monad.Reader
import Control.Monad.Except

import Parser

type Index = Int

data Term = CVar Index
          | CAbs Term
          | CApp Term Term
          | CFix Term
          | CLitInt Int
          | CLitBool Bool
          deriving (Eq, Show)

data CompilerError = UndefinedVariable Ident
  deriving (Eq, Show)

type Compiler = ReaderT [Ident] (Except CompilerError)

compile :: Expr -> Either CompilerError Term
compile = runCompiler . fromExpr

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

fromExpr (LitInt n) = return $ CLitInt n
fromExpr (LitBool b) = return $ CLitBool b

with :: Ident -> Compiler a -> Compiler a
with i = local (i:)
  
elemIndex :: Eq a => a -> [a] -> Maybe Int
elemIndex x [] = Nothing
elemIndex x (y:ys)
  | x == y = return 0
  | otherwise = (1+) <$> elemIndex x ys
