{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use list literal pattern" #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import qualified Graphics.Vty as V

import System.IO
import System.Directory
import Data.List
import Data.Ord
import Data.Time.Clock
import Data.Maybe (fromMaybe, catMaybes)
import Text.Parsec (ParseError)
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Debug.Trace

import Graphics.Vty ((<|>))

import Parser
import Types
import Infer
import Compiler
import Eval
import Env
import Pretty
import Synthesis
import Data.Functor

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
handleCommand (':':'s':rest) = synthesiseTypeSpec rest
handleCommand s = handleInput s

handleInput :: String -> Interactive ()
handleInput s = do
  t <- parseRepl "<repl>" s ?? SyntaxErr
  case t of
    ReplExpr e -> do
      t <- handleExpr e
      liftIO $ printTerm t
    ReplDef d -> typecheckProgram [d]

handleExpr :: Expr -> Interactive Term
handleExpr t = do
  sch <- typecheckTerm t
  env <- get
  term <- compile (fromEnvironment env) t ?? CompileErr
  return $ eval (subEnv (envTerms env) term)

perf :: String -> Interactive ()
perf s = do
  start <- liftIO getCurrentTime
  handleInput s
  end <- liftIO getCurrentTime
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
    [] -> putStrLn "  no datatypes defined"
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
  putStrLn "    :s f : t1 -> ... -> tn  synthesise the function f with given type "

typecheckTerm :: Expr -> Interactive Scheme
typecheckTerm t = do
  env <- gets fromEnvironment
  dts <- gets types
  typecheck env dts t ?? TypeErr

synthesiseTypeSpec :: String -> Interactive ()
synthesiseTypeSpec s = do
  e <- parseExpr "<repl>" s ?? SyntaxErr
  case e of
    TypeSpec (Var f) t -> beginSynthesis f t
    _ -> error "not a type spec"

data SynthesiserState = SynthesiserState
  { fnName :: Ident
  , ty :: Type
  , egStrings :: [([String], String)]
  , egParsed :: [([Maybe Term], Maybe Term)]
  , egsActual :: [Example]
  , rowEg :: Int
  , colEg :: Int
  , numIns :: Int
  , results :: [SynthResult]
  , numResults :: Int
  , vty :: V.Vty }

beginSynthesis :: Ident -> Type -> Interactive ()
beginSynthesis f t = do
  let (argTys, retTy) = unfoldFnTy t
  let len = length argTys

  vty <- liftIO $ do
    cfg <- V.standardIOConfig
    V.mkVty cfg

  (res, st) <- runStateT runSynthesiser
    (SynthesiserState f t [ (replicate len "", "") ] [ (replicate len Nothing, Nothing) ] [] 0 0 len [] 1 vty)

  liftIO $ do
    V.shutdown vty
    putStrLn "synthesis finished."

runSynthesiser :: StateT SynthesiserState Interactive ()
runSynthesiser = do
  v <- gets vty
  pic <- renderSynthesiser
  ev <- liftIO $ do
    V.update v pic
    V.nextEvent v
  repeat <- updateSynthesiser ev
  when repeat runSynthesiser

updateSynthesiser :: V.Event -> StateT SynthesiserState Interactive Bool
updateSynthesiser ev = do
  SynthesiserState f t egStrs parsed _ row col numIns _ numRes _ <- get

  case ev of
    V.EvKey (V.KChar 'c') [V.MCtrl] -> return False
    V.EvKey V.KEsc mods -> return False

    V.EvKey (V.KChar '\t') [] -> synthsiserMove 1 0 >> return True
    V.EvKey V.KUp [V.MShift] -> synthsiserMove 0 (-1) >> return True
    V.EvKey V.KRight [V.MShift] -> synthsiserMove 1 0 >> return True
    V.EvKey V.KDown [V.MShift] -> synthsiserMove 0 1 >> return True
    V.EvKey V.KLeft [V.MShift] -> synthsiserMove (-1) 0 >> return True
    V.EvKey V.KEnter [] -> do
      modify $ \st -> st { egStrings = egStrings st ++ [ (replicate numIns "", "") ]
                         , egParsed = egParsed st ++ [ (replicate numIns Nothing, Nothing) ] }
      synthsiserMove 0 1
      modify $ \st -> st { colEg = 0 }
      return True

    V.EvKey (V.KChar ch) [] -> synthesiserUpdateSelected (++ [ch]) >> return True
    V.EvKey V.KBS [] -> synthesiserUpdateSelected init' >> return True
    _ -> return True
    where init' [] = []
          init' xs = init xs

renderSynthesiser :: StateT SynthesiserState Interactive V.Picture
renderSynthesiser = do
  SynthesiserState f t egs parsed egsActual row col numIns res _ _ <- get
  let maxWidths = map (length . maximumBy (comparing length)) (transpose (map fst egs))
      theLines
            = header
           ++ [ green f <|> white " : " <|> white (show t) ]
           ++ [ grey start <|> V.horizCat (intersperse inSep ins') <|> arrow <|> out' <|> grey end
              | (j, (ins, out), (insP, outP)) <- zip3 [0..] egs parsed
              , let ins' = [ pad (if (i, j) == (col, row) then inputSel inp else maybe (inputNoParse inp) (inputBox . fromMaybe "..." . prettyTerm) inpP) l
                           | (i, inp, inpP, l) <- zip4 [0..] ins insP maxWidths ]
              , let out' = if (j, col) == (row, numIns) then inputSel out else maybe (inputNoParse out) (inputBox . fromMaybe "..." . prettyTerm) outP
              , let start = if j == 0 then "{ " else ", "
              , let end = if j + 1 == length egs then " }" else "" ]
           ++ [ white (replicate 32 '━') ]
           ++ [ green $ "synthesised " ++ show (length res) ++ " results" ]
           ++ [ green $ "  (using " ++ show (length egsActual) ++ " examples)" ]
           ++ map (white . prettyExample) egsActual
           ++ case res of
                [] -> [ red "could not synthesise" ]
                res -> 
                  [ V.vertCat fns'
                  | SynthResult root fns depthUsed <- res
                  , let fns' = concatMap (map white . lines . uncurry prettyFunction) fns ]
      pic = V.picForImage (V.pad 8 4 8 4 $ V.vertCat theLines)

  return pic

  where white = V.string (V.defAttr `V.withForeColor` V.brightWhite)
        grey = V.string (V.defAttr `V.withForeColor` V.white)
        green = V.string (V.defAttr `V.withForeColor` V.brightGreen)
        red = V.string (V.defAttr `V.withForeColor` V.brightRed)
        inputBox xs = V.string (V.defAttr `V.withForeColor` V.brightWhite `V.withBackColor` V.black) (fillOut xs)
        inputSel xs = V.string (V.defAttr `V.withForeColor` V.black `V.withBackColor` V.brightWhite `V.withStyle` V.bold) (fillOut xs)
        inputNoParse xs = V.string (V.defAttr `V.withForeColor` V.brightWhite `V.withBackColor` V.red `V.withStyle` V.bold) (fillOut xs)
        inSep = grey " "
        arrow = grey " → "
        fillOut xs = if null xs then " " else xs
        pad p l = let diff = l - V.imageWidth p
                  in if diff <= 0 then p else p <|> white (replicate diff ' ')
        header = map green [ " __       ____          __           _     "
                           , " \\ \\     / __/__ ____  / /____ ____ (_)__ _"
                           , " /\\ \\   / _// _ `/ _ \\/ __/ _ `(_-</ / _ `/"
                           , "/_/\\_\\ /_/  \\_,_/_//_/\\__/\\_,_/___/_/\\_,_/ "
                           , "                                   & Fugue"
                           , ""
                           , "         [ESC] or [C-c] to exit"
                           , "       [RET] to add a new example"
                           , " [TAB] or [Shift + Arrows] to move around"
                           , "" ]

synthsiserMove :: Int -> Int -> StateT SynthesiserState Interactive ()
synthsiserMove x y = do
  synthesiserUpdateSelected id
  modify $ \st ->
    st { colEg = (colEg st + x) `mod` (numIns st + 1)
       , rowEg = (rowEg st + y) `mod` length (egStrings st) }

synthesiserUpdateSelected :: (String -> String) -> StateT SynthesiserState Interactive ()
synthesiserUpdateSelected f = do
  SynthesiserState _ t egs parsed _ row col numIns _ _ _ <- get
  let txt = if col == numIns then snd (egs !! row) else fst (egs !! row) !! col

  v <- case parseMaybe (f txt) of
    Nothing -> return Nothing
    Just ex -> do
      t <- lift $ handleExpr ex
      return $ Just t

  modify $ \st ->
    st { egStrings = [ (ins', out')
                     | (j, (ins, out)) <- zip [0..] egs
                     , let ins' = [ if (i, j) == (col, row) then f inp else inp
                                  | (i, inp) <- zip [0..] ins ]
                     , let out' = if (j, col) == (row, numIns) then f out else out ]
       , egParsed = [ (ins', out')
                    | (j, (ins, out), (insP, outP)) <- zip3 [0..] egs parsed
                    , let ins' = [ if (i, j) == (col, row) then v else inpP
                                 | (i, inp, inpP) <- zip3 [0..] ins insP ]
                    , let out' = if (j, col) == (row, numIns) then v else outP ] }

  synthesiserDoSynthesis
  where parseMaybe s = case runExcept $ parseExpr "synth" s of
          Left pe -> Nothing
          Right ex -> Just ex

synthesiserDoSynthesis :: StateT SynthesiserState Interactive ()
synthesiserDoSynthesis = do
  SynthesiserState f t egStrings parsed _ row col numIns _ numRes _ <- get

  let egs = catMaybes $ parsed <&> \(ins, out) -> do
        ins' <- mapM (fmap (fmap Val . toClosed)) ins >>= sequence
        out' <- out >>= toClosed
        return $ Eg ins' out'

  e <- lift get
  let res = synthesiseInEnvironment e f t egs
  modify $ \st -> st { results = take numRes res, egsActual = egs }

testHead env = synthesiseInEnvironment env "head" (tyList (TyVar "a") --> TyVar "a")
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

testZip env = synthesiseInEnvironment env "zip"
  (tyList (TyVar "a") --> tyList (TyVar "b") --> tyList (tyPair [TyVar "a", TyVar "b"]))
  [ Eg [toVal' ([] :: [Int]), toVal' ([] :: [Int])] (toClosed' ([] :: [(Int, Int)]))
  , Eg [toVal' ([1] :: [Int]), toVal' ([] :: [Int])] (toClosed' ([] :: [(Int, Int)]))
  , Eg [toVal' ([1, 2] :: [Int]), toVal' ([2, 3] :: [Int])] (toClosed' ([(1, 2), (2, 3)] :: [(Int, Int)])) ]

testF env = synthesiseInEnvironment env "f"
  (tyList (TyVar "a") --> tyList (TyVar "a"))
  [ Eg [toVal' ([] :: [Int])] (toClosed' ([] :: [Int]))
  , Eg [toVal' ([1, 2] :: [Int])] (toClosed' ([1] :: [Int])) ]

loadFile :: String -> Interactive ()
loadFile file = do
  s <- liftIO $ readFile file
  p <- parseProgram file s ?? SyntaxErr
  typecheckProgram p

  env <- get
  case testF env of
    [] -> liftIO $ putStrLn "synthesis failed! :("
    xs -> do
      --liftIO $ putStrLn $ "synthesised " ++ show (length (take 5 xs)) ++ " functions"
      forM_ (zip [1..3] (nub xs)) $ \(num, SynthResult i fns d) -> liftIO $ do
        putStrLn $ "attempt #" ++ show num ++ ", reached depth = " ++ show d ++ ":"
        putStrLn $ "synthesised " ++ show (length fns) ++ " function(s)"
        putStrLn $ intercalate "\n\n" (map (uncurry prettyFunction) fns)

        putStr "   (press <return> for another try...)"
        hFlush stdout
        getLine
        putStrLn ""
        --term <- compile (fromEnvironment env) (assemble fn) ?? CompileErr
        --putStrLn $ "compiled = " ++ show term -}

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
