module Main where

import System.IO
import Data.List
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict

import Parser
import Types

data Error = TypeErr TypeError
           | SyntaxErr FilePath

type Interactive = ExceptT Error (StateT Env IO)

instance Show Error where
  show (TypeErr te) = show te
  show (SyntaxErr fp) = "syntax error in " ++ fp

main :: IO ()
main = void $ evalStateT (runExceptT repl) []

repl :: Interactive ()
repl = do
  liftIO $ putStr "☛ "
  liftIO $ hFlush stdout
  l <- liftIO $ getLine

  case l of
    "" -> repl
    ':':'l':rest -> loadFiles (words rest)
    ':':'b':rest -> browse
    ':':'h':rest -> help
    s -> handleExpr s

  liftIO $ putStrLn ""
  repl

handleExpr :: String -> Interactive ()
handleExpr s = case parseTerm s of
  Just t -> typecheckTerm t
  Nothing -> liftIO $ putStrLn "parse error"

typecheckTerm :: Term -> Interactive ()
typecheckTerm t = do
  env <- get
  liftIO $ case typecheck env t of
    Left err -> putStrLn $ show err
    Right (Forall [] ty) -> putStrLn $ " : " ++ show ty
    Right (Forall vars ty) -> do
      putStrLn $ " : ∀ " ++ intercalate " " vars
      putStrLn $ "      " ++ show ty

loadFiles :: [String] -> Interactive ()
loadFiles fs = do
  forM_ fs $ \file -> do
    oldEnv <- get
    loadFile file `catchError` \err -> do
      liftIO $ putStrLn $ "error loading " ++ file ++ ":"
      liftIO $ putStrLn $ "  " ++ show err
      put oldEnv

  browse

loadFile :: String -> Interactive ()
loadFile file = do
  s <- liftIO $ readFile file
  case parseProgram s of
    Just p -> typecheckProgram p
    Nothing -> throwError $ SyntaxErr file

typecheckProgram :: Program -> Interactive ()
typecheckProgram defs = forM_ defs $ \(Definition name t) -> do
  env <- get
  case typecheck env (LetRec name t (Var name)) of
    Left err -> throwError $ TypeErr err
    Right sch -> modify (insertKV name sch)

browse :: Interactive ()
browse = do
  env <- get
  forM_ env $ \(name, sch) ->
    liftIO $ putStrLn $ " " ++ name ++ " : " ++ show sch

help :: Interactive ()
help = liftIO $ do
  putStrLn " Usage"
  putStrLn "   :l  load files"
  putStrLn "   :b  browse loaded globals"
  putStrLn "   :h  show this help message"

insertKV :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
insertKV k v [] = [(k, v)]
insertKV k v ((k', v'):xs)
  | k == k' = (k, v) : xs
  | otherwise = (k', v') : insertKV k v xs
