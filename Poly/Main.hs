module Main where

import System.IO
import Data.List
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict

import Parser
import Types
import Compiler
import Eval
import Env

type Interactive = ExceptT Error (StateT Environment IO)

data Error = TypeErr TypeError
           | SyntaxErr FilePath
           | CompileErr CompilerError

instance Show Error where
  show (TypeErr te) = show te
  show (SyntaxErr fp) = "syntax error in " ++ fp
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
handleCommand (':':'h':rest) = help
handleCommand s = handleInput s

handleInput :: String -> Interactive ()
handleInput s = do
  t <- parseExpr "<repl>" s ?? SyntaxErr
  (Forall _ ty) <- typecheckTerm t
  env <- get
  term <- compile (fromEnvironment env) t ?? CompileErr
  
  liftIO $ do
    printTerm $ eval (subEnv (envTerms env) term)
    putStrLn $ "  : " ++ show ty

loadFiles :: [String] -> Interactive ()
loadFiles fs = do
  forM_ fs loadFile
  liftIO $ putStrLn $ "  loaded " ++ show (length fs) ++ " file(s)"

browse :: Interactive ()
browse = do
  env <- get
  forM_ env $ \(name, (sch, t)) ->
    liftIO $ putStrLn $ "  " ++ name ++ " : " ++ show sch

help :: Interactive ()
help = liftIO $ do
  putStrLn " Usage"
  putStrLn "   :l  load file(s)"
  putStrLn "   :b  browse loaded globals"
  putStrLn "   :h  show this help message"

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
printTerm (CLitInt n) = putStrLn $ "  = " ++ show n
printTerm (CLitBool b) = putStrLn $ "  = " ++ show b
printTerm _ = return ()

insertKV :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
insertKV k v [] = [(k, v)]
insertKV k v ((k', v'):xs)
  | k == k' = (k, v) : xs
  | otherwise = (k', v') : insertKV k v xs

fromEnvironment :: Environment -> Env
fromEnvironment emt = [ (n, sch) | (n, (sch, _)) <- emt ]

envTerms :: Environment -> [Term]
envTerms emt = [ t | (_, (_, t)) <- emt ]

(??) :: Except a b -> (a -> Error) -> Interactive b
e ?? f = case runExcept e of
  Left err -> throwError (f err)
  Right val -> return val
