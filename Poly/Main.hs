module Main where

import System.IO
import Data.List
import Control.Monad
import Control.Monad.State.Strict

import Parser
import Types

type Interactive = StateT Env IO

main :: IO ()
main = evalStateT repl []

repl :: Interactive ()
repl = do
  liftIO $ putStr "☛ "
  liftIO $ hFlush stdout
  l <- liftIO $ getLine

  case l of
    "" -> repl
    ':':'l':rest -> loadFiles (words rest)
    ':':'b':rest -> browse
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
loadFiles fs = forM_ fs $ \file -> do
  s <- liftIO $ readFile file
  case parseProgram s of
    Just p -> typecheckProgram p
    Nothing -> liftIO $ putStrLn $ "syntax error in " ++ file

typecheckProgram :: Program -> Interactive ()
typecheckProgram defs = forM_ defs $ \(Definition name t) -> do
  env <- get
  case typecheck env t of
    Left err -> liftIO $ putStrLn $ name ++ " error: " ++ show err
    Right sch -> do
      liftIO $ putStrLn $ " " ++ name ++ " : " ++ show sch
      modify (insertKV name sch)

browse :: Interactive ()
browse = do
  env <- get
  forM_ env $ \(name, sch) ->
    liftIO $ putStrLn $ " " ++ name ++ " : " ++ show sch

insertKV :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
insertKV k v [] = [(k, v)]
insertKV k v ((k', v'):xs)
  | k == k' = (k, v) : xs
  | otherwise = (k', v') : insertKV k v xs
