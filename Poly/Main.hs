module Main where

import System.IO
import Data.List
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict

import Parser
import Types
import Compiler

data Error = TypeErr TypeError
           | SyntaxErr FilePath
           | CompileErr CompilerError

type Interactive = ExceptT Error (StateT Env IO)

instance Show Error where
  show (TypeErr te) = show te
  show (SyntaxErr fp) = "syntax error in " ++ fp

main :: IO ()
main = void $ evalStateT (runExceptT repl) []

repl :: Interactive ()
repl = forever $ do
  liftIO $ putStr "☛ "
  liftIO $ hFlush stdout
  l <- liftIO $ getLine

  oldEnv <- get
  handleCommand l `catchError` restore oldEnv

  liftIO $ putStrLn ""

handleCommand :: String -> Interactive ()
handleCommand "" = repl
handleCommand (':':'l':rest) = loadFiles (words rest)
handleCommand (':':'b':rest) = browse
handleCommand (':':'h':rest) = help
handleCommand s = handleInput s

restore :: Env -> Error -> Interactive ()
restore oldEnv err = do
  liftIO $ putStrLn "error:"
  liftIO $ putStrLn $ "  " ++ show err
  put oldEnv

handleInput :: String -> Interactive ()
handleInput s = case parseExpr s of
  Just t -> do
    typecheckTerm t
    case compile t of
      Left e -> throwError $ CompileErr e
      Right term -> liftIO $ print term
  Nothing -> throwError $ SyntaxErr "<repl>"

typecheckTerm :: Expr -> Interactive ()
typecheckTerm t = do
  env <- get
  case typecheck env t of
    Left err -> throwError $ TypeErr err
    Right (Forall [] ty) -> liftIO $ putStrLn $ " : " ++ show ty
    Right (Forall vars ty) -> liftIO $ do
      putStrLn $ " : ∀ " ++ intercalate " " vars
      putStrLn $ "      " ++ show ty

loadFiles :: [String] -> Interactive ()
loadFiles fs = do
  forM_ fs loadFile
  liftIO $ putStrLn $ "loaded " ++ show (length fs) ++ " file(s)"

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
