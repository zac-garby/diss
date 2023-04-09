{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use list literal pattern" #-}

module Main where

import System.IO
import System.Directory
import Data.List
import Data.Time.Clock
import Text.Parsec (ParseError)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Debug.Trace

import Parser
import Types
import Infer
import Compiler
import Eval
import Env
import Pretty
import Synthesis

type Interactive = ExceptT Error (StateT Environment IO)

data Error = TypeErr TypeError
           | SyntaxErr ParseError
           | CompileErr CompilerError
           | FileErr FilePath
           | DefinedErr Ident

instance Show Error where
  show (TypeErr te) = show te
  show (SyntaxErr fp) = show fp
  show (CompileErr ce) = show ce
  show (FileErr fp) = "file '" ++ fp ++ "' does not exist"
  show (DefinedErr id) = "identifier '" ++ id ++ "' is defined twice"

main :: IO ()
main = do
  putStrLn "fugue v2.0"
  putStrLn "type :h for available commands"
  evalStateT (runExceptT repl) defaultEnv
  return ()

repl :: Interactive ()
repl = forever $ do
  liftIO $ putStr "► "
  liftIO $ hFlush stdout
  l <- liftIO getLine

  oldEnv <- get
  handleCommand l `catchError` restore oldEnv

  liftIO $ putStrLn ""

handleCommand :: String -> Interactive ()
handleCommand "" = repl
handleCommand (':':'p':rest) = perf rest
handleCommand (':':'l':rest) = loadFiles (words rest)
handleCommand (':':'b':[])   = search "t"
handleCommand (':':'b':rest) = search rest
handleCommand (':':'i':[])   = info
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
  let matches = filter (\(name, (sch', _)) -> sch <= sch' || sch' <= sch) (terms env)

  liftIO $ case matches of
    [] -> putStrLn $ "  no matches found for " ++ prettyScheme sch
    matches -> putStrLn $ prettyTypes matches

info :: Interactive ()
info = do
  env <- get
  liftIO $ case types env of
    [] -> putStrLn $ "  no datatypes defined"
    dts -> putStrLn $ prettyDataTypes (types env)

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
  putStrLn "    :i                      list information about defined types"
  putStrLn "    :t                      derive the type of a term"
  putStrLn "    :p                      time an evaluation"
  putStrLn "    :h                      show this help message"

typecheckTerm :: Expr -> Interactive Scheme
typecheckTerm t = do
  env <- gets fromEnvironment
  dts <- gets types
  typecheck env dts t ?? TypeErr

testHead env = synthesiseInEnvironment env "head" (tyList tyInt --> tyInt)
  [ Eg [toVal' ([1, 2] :: [Int])] (toClosed' (1 :: Int))
  , Eg [toVal' ([0, 2, 3] :: [Int])] (toClosed' (0 :: Int)) ]

testDouble env = synthesiseInEnvironment env "double" (tyInt --> tyList tyInt --> tyList tyInt)
  [ Eg [toVal' (0 :: Int), toVal' ([1] :: [Int])] (toClosed' ([0, 0, 1] :: [Int]))
  , Eg [toVal' (2 :: Int), toVal' ([] :: [Int])] (toClosed' ([2, 2] :: [Int])) ]

testIsOne env = synthesiseInEnvironment env "is_one" (tyInt --> tyBool)
  [ Eg [toVal' (0 :: Int)] (toClosed' False)
  , Eg [toVal' (1 :: Int)] (toClosed' True)
  , Eg [toVal' (2 :: Int)] (toClosed' False) ]

testLength env = synthesiseInEnvironment env "length" (tyList (TyVar "a") --> tyInt)
  [ Eg [toVal' ([] :: [Int])] (toClosed' (0 :: Int))
  , Eg [toVal' ([1] :: [Int])] (toClosed' (1 :: Int))
  , Eg [toVal' ([3, 2, 1] :: [Int])] (toClosed' (3 :: Int)) ]

testStutter env = synthesiseInEnvironment env "stutter" (tyList (TyVar "a") --> tyList (TyVar "a"))
  [ Eg [toVal' ([] :: [Int])] (toClosed' ([] :: [Int]))
  --, Eg [toVal' ([1] :: [Int])] (toClosed' ([1, 1] :: [Int]))
  , Eg [toVal' ([1, 2] :: [Int])] (toClosed' ([1, 1, 2, 2] :: [Int])) ]

loadFile :: String -> Interactive ()
loadFile file = do
  s <- liftIO $ readFile file
  p <- parseProgram file s ?? SyntaxErr
  typecheckProgram p
  
  env <- get
  case testLength env of
    [] -> liftIO $ putStrLn "synthesis failed! :("
    xs -> do
      --liftIO $ putStrLn $ "synthesised " ++ show (length (take 5 xs)) ++ " functions"
      forM_ (zip [1..5] (nub xs)) $ \(num, SynthResult i fns d) -> liftIO $ do
        putStrLn $ "attempt #" ++ show num ++ ", reached depth = " ++ show d ++ ":"
        putStrLn $ "synthesised " ++ show (length fns) ++ " function(s)"
        putStrLn $ intercalate "\n\n" (map (uncurry prettyFunction) fns)
        putStrLn ""
        --term <- compile (fromEnvironment env) (assemble fn) ?? CompileErr
        --putStrLn $ "compiled = " ++ show term

typecheckProgram :: Program -> Interactive ()
typecheckProgram prog = do
  let (typeDecls, defs, datas) = programParts prog

  forM_ datas $ \(name, dt) -> do
    insertDataType name dt
    insertConstructors name dt
  
  forM_ defs $ \(name, t) -> do
    env <- gets fromEnvironment
    dts <- gets types
    let t' = case lookup name typeDecls of
               Just ty -> TypeSpec (LetRec name t (Var name)) ty
               Nothing -> LetRec name t (Var name)
    sch <- typecheck env dts t' ?? TypeErr
    term <- compile env t' ?? CompileErr
    insertTerm name sch term

-- splits a program into (all type decls., all term defs, all data defs.)
programParts :: Program -> ([(Ident, Type)], [(Ident, Expr)], [(Ident, DataType)])
programParts [] = ([], [], [])
programParts (d@(Definition n t):ds) = ([], [(n, t)], []) `mappend` programParts ds
programParts (d@(TypeDefinition n t):ds) = ([(n, t)], [], []) `mappend` programParts ds
programParts (d@(DataDefinition n dt):ds) = ([], [], [(n, dt)]) `mappend` programParts ds

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

insertTerm :: Ident -> Scheme -> Term -> Interactive ()
insertTerm name sch val = modify $ defineTerm name sch val

insertDataType :: Ident -> DataType -> Interactive ()
insertDataType name dt = modify $ defineDataType name dt

insertConstructors :: Ident -> DataType -> Interactive ()
insertConstructors name (DataType tyArgs constrs) = forM_ constrs $ \(DataConstructor id args) -> do
  let sch = finalise $ foldr (-->) (TyConstr name (map TyVar tyArgs)) args
  insertTerm id sch (CConstr id)

(??) :: Except a b -> (a -> Error) -> Interactive b
e ?? f = case runExcept e of
  Left err -> throwError (f err)
  Right val -> return val
