{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use list literal pattern" #-}

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

import Graphics.Vty ((<|>), (<->), defaultConfig)
import Graphics.Vty.Platform.Unix (mkVty)

import Parser
import Types
import Infer
import Compiler
import Eval
import Env
import Pretty
import Synthesis
import Data.Functor
import Text.Read (readMaybe)

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

  vty <- liftIO (mkVty V.defaultConfig)
--    cfg <- V.defaultConfig
   

  (res, st) <- runStateT runSynthesiser
    (SynthesiserState f t [ (replicate len "", "") ] [ (replicate len Nothing, Nothing) ] [] 0 0 len [] 3 vty)

  liftIO $ do
    V.shutdown vty
    putStrLn "synthesis finished."

  case res of
    Nothing -> liftIO $ putStrLn "  (result not saved)"
    Just SynthResult{ functions = functions } -> forM_ (reverse functions) $
      \(fnName, Function args ret body _) -> do
        e <- get
        let fnExpr = foldr (Abs . fst) body args
        let def = Definition fnName fnExpr
        typecheckProgram [def]
        liftIO $ putStrLn $ "  (defined function: " ++ fnName ++ ")"

runSynthesiser :: StateT SynthesiserState Interactive (Maybe SynthResult)
runSynthesiser = do
  v <- gets vty
  pic <- renderSynthesiser
  ev <- liftIO $ do
    V.update v pic
    V.nextEvent v
  repeat <- updateSynthesiser ev
  if repeat then runSynthesiser else chooseSynthesisResult

updateSynthesiser :: V.Event -> StateT SynthesiserState Interactive Bool
updateSynthesiser ev = do
  SynthesiserState f t egStrs parsed _ row col numIns _ numRes _ <- get

  case ev of
    V.EvKey (V.KChar 'c') [V.MCtrl] -> return False
    V.EvKey V.KEsc mods -> return False

    V.EvKey (V.KChar '\t') [] -> synthsiserMove 1 0 >> return True
    V.EvKey V.KUp mods -> when (V.MShift `elem` mods) (synthsiserMove 0 (-1)) >> return True
    V.EvKey V.KRight mods -> when (V.MShift `elem` mods) (synthsiserMove 1 0) >> return True
    V.EvKey V.KDown mods -> when (V.MShift `elem` mods) (synthsiserMove 0 1) >> return True
    V.EvKey V.KLeft mods -> when (V.MShift `elem` mods) (synthsiserMove (-1) 0) >> return True
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
  let theLines = header
           ++ [ green f <|> white " : " <|> white (show t) ]
           ++ [ grey start <|> V.horizCat (intersperse inSep ins') <|> arrow <|> out' <|> grey end
              | (j, (ins, out), (insP, outP)) <- zip3 [0..] egs parsed
              , let ins' = [ if (i, j) == (col, row) then
                               inputSel inp
                             else
                               maybe (inputNoParse inp) (inputBox . fromMaybe " !! " . prettyTermPlain) inpP
                           | (i, inp, inpP) <- zip3 [0..] ins insP ]
              , let out' = if (j, col) == (row, numIns) then
                             inputSel out
                           else
                             maybe (inputNoParse out) (inputBox . fromMaybe "!!" . prettyTermPlain) outP
                            --  maybe (inputNoParse out) (inputBox . show) outP
              , let start = if j == 0 then "{ " else ", "
              , let end = if j + 1 == length egs then " }" else "" ]
           ++ [ white (replicate 32 '━') ]
           ++ [ green $ "synthesised " ++ show (length res) ++ " results:",
                white $ replicate 64 ' ' ]
           ++ case res of
                [] -> [ red "could not synthesise" ]
                res ->
                  [ white ("result #" ++ show i) <-> V.translateX 2 fnsImg <-> white (replicate 64 ' ')
                  | (i, SynthResult root fns depthUsed) <- zip [1..] res
                  , let fnImgs = map (uncurry prettyFunctionImg) (reverse fns)
                  , let fnsImg = V.vertCat (intersperse inSep fnImgs) ]
      pic = V.picForImage (V.pad 8 4 8 4 $ V.vertCat theLines)

  return pic

  where white = V.string (V.defAttr `V.withForeColor` V.brightWhite)
        grey = V.string (V.defAttr `V.withForeColor` V.white)
        green = V.string (V.defAttr `V.withForeColor` V.brightGreen)
        red = V.string (V.defAttr `V.withForeColor` V.brightRed)
        inputBox xs = V.string (V.defAttr `V.withForeColor` V.brightWhite `V.withBackColor` V.black) (fillOut xs)
        inputSel xs = V.string (V.defAttr `V.withForeColor` V.black `V.withBackColor` V.brightWhite `V.withStyle` V.bold) (fillOut xs)
        inputNoParse xs = V.string (V.defAttr `V.withForeColor` V.brightWhite `V.withBackColor` V.red `V.withStyle` V.bold) (fillOut xs)
        inSep = grey ", "
        arrow = grey " → "
        fillOut xs = if null xs then " " else xs

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
      let (argTys, retTy) = unfoldFnTy t
          reqTy = if col == numIns then retTy else argTys !! col
      t <- lift . tryError $ do
        actualTy <- typecheckTerm ex
        if finalise reqTy <= actualTy || actualTy <= finalise reqTy then
          handleExpr ex
        else
          throwError $ TypeErr $ TypeSpecMismatch actualTy (finalise reqTy)
      return $ case t of
        Left er -> Nothing
        Right te -> Just te

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

  when (txt /= f txt) synthesiserDoSynthesis

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
  let res = nub (synthesiseInEnvironment e f t egs)
  modify $ \st -> st { results = take numRes res, egsActual = egs }

chooseSynthesisResult :: StateT SynthesiserState Interactive (Maybe SynthResult)
chooseSynthesisResult = do
  v <- gets vty
  pic <- renderChooser
  ev <- liftIO $ do
    V.update v pic
    V.nextEvent v
  updateChooser ev

renderChooser :: StateT SynthesiserState Interactive V.Picture
renderChooser = do
  SynthesiserState f t egs parsed egsActual row col numIns res _ _ <- get
  let maxWidths = map (length . maximumBy (comparing length)) (transpose (map fst egs))
      theLines
            = header
           ++ [ green f <|> white " : " <|> white (show t) ]
           ++ map white [ ""
                        , "  press the corresponding keys to pick a result,"
                        , "  press ESCAPE to quit without saving,"
                        , "  or press any other key to continue adding more examples."
                        , "" ]
           ++ case res of
                [] -> [ red "could not synthesise" ]
                res ->
                  [ white ("PRESS: [" ++ show i ++ "]") <-> V.translateX 2 fnsImg <-> white (replicate 64 ' ')
                  | (i, SynthResult root fns depthUsed) <- zip [1..] res
                  , let fnImgs = map (uncurry prettyFunctionImg) (reverse fns)
                  , let fnsImg = V.vertCat (intersperse inSep fnImgs) ]
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

updateChooser :: V.Event -> StateT SynthesiserState Interactive (Maybe SynthResult)
updateChooser ev = do
  SynthesiserState f t egStrs parsed _ row col numIns res numRes _ <- get

  case ev of
    V.EvKey (V.KChar 'c') [V.MCtrl] -> return Nothing
    V.EvKey V.KEsc mods -> return Nothing

    V.EvKey (V.KChar ch) [] -> case readMaybe (ch : "") :: Maybe Int of
      Nothing -> runSynthesiser
      Just n -> if n < numRes then return (Just $ res !! (n - 1)) else runSynthesiser

    _ -> runSynthesiser

loadFile :: String -> Interactive ()
loadFile file = do
  s <- liftIO $ readFile file
  p <- parseProgram file s ?? SyntaxErr
  typecheckProgram p

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

header :: [V.Image]
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
  where green = V.string (V.defAttr `V.withForeColor` V.brightGreen)
