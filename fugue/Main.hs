module Main where

import System.IO
import System.Directory
import Data.List
import Data.Time.Clock
import Text.Parsec (ParseError)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Graphics.Vty hiding (Cursor)

import Parser
import Types
import Infer
import Compiler
import Eval
import Env
import Pretty
import Editor

type Interactive = ExceptT Error (StateT Environment IO)
type Editor = ExceptT Error (StateT Location IO)

data Error = TypeErr TypeError
           | SyntaxErr ParseError
           | CompileErr CompilerError
           | FileErr FilePath

instance Show Error where
  show (TypeErr te) = show te
  show (SyntaxErr fp) = show fp
  show (CompileErr ce) = show ce
  show (FileErr fp) = "file '" ++ fp ++ "' does not exist"

main :: IO ()
main = interactive

interactive :: IO ()
interactive = do
  cfg <- standardIOConfig
  vty <- mkVty cfg
  evalStateT (runExceptT (loop vty)) (edit e2)
  shutdown vty

loop :: Vty -> Editor ()
loop vty = do
  s <- get
  
  let img = render s
      pic = picForImage img
      
  e <- liftIO $ do
    update vty pic
    nextEvent vty
    
  case e of
    EvKey KEsc _ -> return ()
    EvKey (KChar 'q') _ -> return ()
    EvKey k ms -> do
      case k of
        KDown -> send down
        KUp -> if MShift `elem` ms then send top else send up
        KRight -> send next
        KLeft -> send prev
        KChar '\t' -> send next
        KChar ' ' -> send insertNext
        KBS -> send remove
        _ -> return ()
      loop vty

send :: (Location -> Maybe Location) -> Editor ()
send f = do
  s <- get
  case f s of
    Nothing -> return ()
    Just s' -> put s'

{-
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
handleCommand (':':'p':rest) = perf rest
handleCommand (':':'l':rest) = loadFiles (words rest)
handleCommand (':':'b':[])   = search "t"
handleCommand (':':'b':rest) = search rest
handleCommand (':':'t':rest) = checkType rest
handleCommand (':':'h':rest) = help
handleCommand s = handleInput s

handleInput :: String -> Interactive ()
handleInput s = do
  t <- parseRepl "<repl>" s ?? SyntaxErr
  case t of
    ReplExpr e -> handleExpr e
    ReplDef d -> typecheckProgram [d]

handleExpr :: Expr -> Interactive ()
handleExpr t = do
  sch <- typecheckTerm t
  env <- get
  term <- compile (fromEnvironment env) t ?? CompileErr
  
  liftIO $ do
    printTerm $ eval (subEnv (envTerms env) term)
    putStrLn $ "  : " ++ prettyScheme sch

perf :: String -> Interactive ()
perf s = do
  start <- liftIO $ getCurrentTime
  handleInput s
  end <- liftIO $ getCurrentTime
  liftIO $ putStrLn $ "  (finished in " ++ show (diffUTCTime end start) ++ ")"

loadFiles :: [String] -> Interactive ()
loadFiles fs = do
  forM_ fs $ \f -> do
    let fn = f ++ ".fugue"
    exist <- liftIO $ doesFileExist fn
    if exist then
      loadFile fn
    else
      throwError fn ?? FileErr

  liftIO $ putStrLn $ "  loaded " ++ show (length fs) ++ " file(s)"

search :: String -> Interactive ()
search s = do
  ty <- parseType "<repl>" s ?? SyntaxErr
  let sch = finalise ty
  env <- get
  let matches = filter (\(name, (sch', _)) -> sch <= sch' || sch' <= sch) env

  liftIO $ case matches of
    [] -> putStrLn $ "  no matches found for " ++ prettyScheme sch
    matches -> putStrLn $ prettyEnv matches

checkType :: String -> Interactive ()
checkType s = do
  t <- parseExpr "<repl>" s ?? SyntaxErr
  sch <- typecheckTerm t
  liftIO $ putStrLn $ "  : " ++ prettyScheme sch

help :: Interactive ()
help = liftIO $ do
  putStrLn "  Usage"
  putStrLn "    :l <file1> <file2> ...  load file(s)"
  putStrLn "    :b                      browse entire environment"
  putStrLn "    :b <type>               search the environment"
  putStrLn "    :t                      derive the type of a term"
  putStrLn "    :p                      time an evaluation"
  putStrLn "    :h                      show this help message"

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
typecheckProgram prog = do
  let (types, defs) = programParts prog
  forM_ defs $ \(name, t) -> do
    env <- gets fromEnvironment
    let t' = case lookup name types of
               Just ty -> TypeSpec (LetRec name t (Var name)) ty
               Nothing -> LetRec name t (Var name)
    sch <- typecheck env t' ?? TypeErr
    term <- compile env t' ?? CompileErr
    modify (insertKV name (sch, term))

-- splits a program into (all type defs, all term defs)
programParts :: Program -> ([(Ident, Type)], [(Ident, Expr)])
programParts [] = ([], [])
programParts (d@(Definition n t):ds) = ([], [(n, t)]) `mappend` programParts ds
programParts (d@(TypeDefinition n t):ds) = ([(n, t)], []) `mappend` programParts ds

restore :: Environment -> Error -> Interactive ()
restore oldEnv err = do
  liftIO $ putStrLn "  error:"
  liftIO $ putStrLn $ "  • " ++ show err
  put oldEnv

printTerm :: Term -> IO ()
printTerm t = case prettyTerm t of
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
-}
