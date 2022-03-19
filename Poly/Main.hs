module Main where

import System.IO
import Data.List
import Text.Parsec (ParseError)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict

import Parser
import Types
import Infer
import Compiler
import Eval
import Env

type Interactive = ExceptT Error (StateT Environment IO)

data Error = TypeErr TypeError
           | SyntaxErr ParseError
           | CompileErr CompilerError

instance Show Error where
  show (TypeErr te) = show te
  show (SyntaxErr fp) = show fp
  show (CompileErr ce) = show ce

main :: IO ()
main = void $ evalStateT (runExceptT repl) defaultEnv

repl :: Interactive ()
repl = forever $ do
  liftIO $ putStr "► "
  liftIO $ hFlush stdout
  l <- liftIO $ getLine

  oldEnv <- get
  handleCommand l `catchError` restore oldEnv

  liftIO $ putStrLn ""

handleCommand :: String -> Interactive ()
handleCommand "" = repl
handleCommand (':':'l':rest) = loadFiles (words rest)
handleCommand (':':'b':rest) = browse
handleCommand (':':'t':rest) = checkType rest
handleCommand (':':'h':rest) = help
handleCommand s = handleInput s

handleInput :: String -> Interactive ()
handleInput s = do
  t <- parseExpr "<repl>" s ?? SyntaxErr
  sch <- typecheckTerm t
  env <- get
  term <- compile (fromEnvironment env) t ?? CompileErr
  
  liftIO $ do
    printTerm $ eval (subEnv (envTerms env) term)
    putStrLn $ "  : " ++ show sch

loadFiles :: [String] -> Interactive ()
loadFiles fs = do
  forM_ fs loadFile
  liftIO $ putStrLn $ "  loaded " ++ show (length fs) ++ " file(s)"

browse :: Interactive ()
browse = do
  env <- get
  forM_ env $ \(name, (sch, t)) ->
    liftIO $ putStrLn $ "  " ++ pprintIdent ops name ++ " : " ++ show sch

checkType :: String -> Interactive ()
checkType s = do
  t <- parseExpr "<repl>" s ?? SyntaxErr
  sch <- typecheckTerm t
  liftIO $ putStrLn $ "  : " ++ show sch

help :: Interactive ()
help = liftIO $ do
  putStrLn "  Usage"
  putStrLn "    :l  load file(s)"
  putStrLn "    :b  browse loaded globals"
  putStrLn "    :t  derive the type of a term without evaluating"
  putStrLn "    :h  show this help message"

typecheckTerm :: Expr -> Interactive Scheme
typecheckTerm t = do
  env <- gets fromEnvironment
  typecheck env t ?? TypeErr

loadFile :: String -> Interactive ()
loadFile file = do
  s <- liftIO $ readFile file
  p <- parseProgram file s ?? SyntaxErr
  typecheckProgram p

typecheckProgram :: Program -> Interactive ()
typecheckProgram defs = forM_ defs $ \(Definition name t) -> do
  env <- gets fromEnvironment
  let t' = LetRec name t (Var name)
  sch <- typecheck env t' ?? TypeErr
  term <- compile env t' ?? CompileErr
  modify (insertKV name (sch, term))

restore :: Environment -> Error -> Interactive ()
restore oldEnv err = do
  liftIO $ putStrLn "  error:"
  liftIO $ putStrLn $ "  • " ++ show err
  put oldEnv

printTerm :: Term -> IO ()
printTerm t = case outputShow t of
                Just s -> putStrLn $ "  = " ++ s
                Nothing -> return ()

insertKV :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
insertKV k v [] = [(k, v)]
insertKV k v ((k', v'):xs)
  | k == k' = (k, v) : xs
  | otherwise = (k', v') : insertKV k v xs

fromEnvironment :: Environment -> Env
fromEnvironment emt = [ (n, (sch, Global)) | (n, (sch, _)) <- emt ]

envTerms :: Environment -> [Term]
envTerms emt = [ t | (_, (_, t)) <- emt ]

(??) :: Except a b -> (a -> Error) -> Interactive b
e ?? f = case runExcept e of
  Left err -> throwError (f err)
  Right val -> return val
