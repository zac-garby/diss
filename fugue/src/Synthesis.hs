module Synthesis
  ( Context (..)
  , Function (..)
  , Functions (..)
  , Arg (..)
  , Example (..)
  , SynthState (..)
  , Synth (..)
  , synthesise
  , removeRedundant
  , unwindFrom
  , test
  ) where

import Data.Maybe
import Data.List
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Control.Monad.Trans.Maybe
import Debug.Trace

import Parser
import Compiler
import Types
import Env
import Infer
import System.IO (hFlush, stdout)
import System.IO.Unsafe (unsafePerformIO)

data Context = Context
  { examples :: [Example]
  , depth :: Int }

data Function = Function
  { args :: [(Ident, Type)]
  , ret :: Type
  , body :: Expr
  , egs :: [Example] }
  deriving Show

data RecursivePart = Recurse Expr
                   | NoRecurse
                   deriving Show

type Functions = [(Ident, Function)]

-- an Arg represents an argument of an example, and is either a fully-evaluated term Val,
-- or a thunk. If it is a thunk, it is a partially-evaluated term, along
-- with the name of the function whose definition the evaluation is blocked by.
data Arg = Val Term | Thunk Term Ident

instance Show Arg where
  show (Val t) = show t
  show (Thunk t i) = "<" ++ i ++ " | " ++ show t ++ ">"

data Example = Eg [Arg] Term
  deriving Show

data SynthState = SynthState
  { newNames :: [Ident]
  , functions :: Functions
  , maxDepth :: Int
  , env :: Environment }
  deriving Show

type Synth = MaybeT (StateT SynthState (Reader Context))

type SynthCase = [(Ident, Type)] -> Type -> Ident -> Synth Function

synthesise :: Environment -> Ident -> Type -> [Example] -> Maybe (Ident, Functions)
synthesise env fnName goal egs =
  let r = runSynth defaultState ctx problem
  in case r of
    (Nothing, _) -> Nothing
    (Just i, SynthState { functions = fns }) -> Just (i, fns)
  where ctx = Context {
          examples = egs
        , depth = 0 }
        defaultState = SynthState {
          newNames = allVars
        , functions = []
        , maxDepth = 0
        , env = env }
        problem = uncurry (upToDepth 16 ... synthDef "result") (unfoldFnTy goal)

runSynth :: SynthState -> Context -> Synth a -> (Maybe a, SynthState)
runSynth s c p = runReader (runStateT (runMaybeT p) s) c

upToDepth :: Int -> Synth a -> Synth a
upToDepth toDepth f = do
  try [ synthWithMaxDepth d | d <- [1..toDepth] ]
  where synthWithMaxDepth d = do
          modify $ \s -> s { maxDepth = d }
          f

synth :: [Type] -> Type -> Ident -> Synth Function
synth argTypes ret name = do
  d <- asks depth
  dMax <- gets maxDepth

  debug $ "* synthesising " ++ name ++ " : " ++ intercalate " -> " (map show argTypes) ++ " -> " ++ show ret
  
  if d < dMax then do
    egs <- asks examples

    forM_ egs $ \(Eg args t) -> do
      debug $ "* { (" ++ intercalate ", " (map show args) ++ ") => " ++ show t ++ " }"

    args <- forM argTypes $ \t -> do
      name <- fresh
      return (name, t)

    local (\c -> c { depth = d + 1 }) $
      try [ synthNoEgs args ret name
          , synthTrivial args ret name
          , synthRecurse args ret name
          , synthCommonConstr args ret name
          , synthSplit args ret name ]
  else do
    debug "* failed: out of depth"
    fail "out of depth"

synthNoEgs :: SynthCase
synthNoEgs args retType _ = do
  debug ": trying synth no egs"

  egs <- asks examples

  if null egs then do
    debug "done: synth no egs"
    return $ Function args retType (Hole 0) []
  else
    exit

synthTrivial :: SynthCase
synthTrivial args retType _ = do
  debug ": trying synth trivial"

  egs <- asks examples
  go egs 0
  where go egs n
          | n >= length args = exit
          | all (\(Eg egArgs egRes) -> egArgs !! n `hasVal` egRes) egs = do
            debug "done: synth trivial"
            return $ Function { args = args
                              , ret = retType
                              , body = Var (fst $ args !! n)
                              , egs = egs }
          | otherwise = go egs (n + 1)

{-
In theory, could give visibility to the parent function in the sub-syntheses in
  other problems too (including common constr, case-splits, etc). It may be best
  to limit it to just the explicit recursion introductions though.
-}
synthCommonConstr :: SynthCase
synthCommonConstr args retType _ = do
  debug ": trying common constr"

  egs <- asks examples

  case sharedConstr egs of
    Nothing -> exit
    Just con -> do
      egs <- asks examples
      ts <- gets (terms . env)

      Forall _ conTy <- lookupType' con
      let (conArgTys, _) = unfoldFnTy (specialiseConstructor conTy retType)
          (conArgs, d) = unzip [ (args, deconstruct' o) | Eg args o <- egs ]
          (cons, d') = unzip d
          d'T = transpose d'
          conEgs = [ zipWith Eg conArgs d | d <- d'T ]
          (argNames, argTypes) = unzip args

      names <- forM (zip conArgTys conEgs) $ \(conArgTy, egs) -> do
        fnName <- fresh
        withExamples egs (synthDef fnName argTypes conArgTy)

      let body = applyMany $ Var con
                 : [ applyMany $ Var n : map Var argNames | n <- names ]

      debug "done: common constr"
      return $ Function { args = args
                        , ret = retType
                        , body = body
                        , egs = egs }

synthSplit :: [(Ident, Type)] -> Type -> Ident -> Synth Function
synthSplit args retType name = do
  debug ": trying case split"

  try [ synthSplitOn i args retType name
      | i <- [0..length args - 1] ]

synthSplitOn :: Int -> [(Ident, Type)] -> Type -> Ident -> Synth Function
synthSplitOn splitOn args retType _ = do
  debug $ "- trying split on arg " ++ show splitOn
  egs <- asks examples
  e <- gets env

  -- we cannot split on an argument which is not fully evaluated
  guard (not (argIsThunk splitOn egs))

  let (splitArg, splitTy) = args !! splitOn
  case splitTy of
    TyConstr dtName dtArgs -> case lookupDataType dtName e of
      Just (DataType tyArgs dtConstrs) -> do
        let s = zip tyArgs dtArgs :: Subst
            concreteConstructors = [ DataConstructor i (map (sub s) ts)
                                   | DataConstructor i ts <- dtConstrs ]

        -- for each constructor in the datatype
        cases <- forM concreteConstructors $ \(DataConstructor con constructorArgTypes) -> do
          constructorArgs <- forM constructorArgTypes $ \ty -> do
            name <- fresh
            return (name, ty)

          -- find the examples which use the appropriate constructor for this branch,
          -- and update them (give them the deconstructed arguments as well as their
          -- existing parameters)
          let allArgs = args ++ constructorArgs
              examples =
                     [ Eg (ins ++ map Val conArgs') out
                     | Eg ins out <- egs
                     , let (con', conArgs') = deconstruct' (fromVal (ins !! splitOn))
                     , con == con']

          -- make a new function name to synthesise this case inside
          caseFnName <- fresh
          g <- withExamples examples (synthDef caseFnName (map snd allArgs) retType)

          return (con, map fst constructorArgs, applyMany (map Var (g : map fst allArgs)))

        let body = Case (Var splitArg) cases
        debug $ "done: split on arg " ++ show splitOn
        return $ Function { args = args
                          , ret = retType
                          , body = body
                          , egs = egs }

      Nothing -> fail "non-datatype or undefined"
    _ -> fail "can't split on non-ADT"

synthRecurse :: [(Ident, Type)] -> Type -> Ident -> Synth Function
synthRecurse args retType name = do
  debug ": trying case split"

  try [ synthRecurseOn i args retType name
      | i <- [0..length args - 1] ]

synthRecurseOn :: Int -> [(Ident, Type)] -> Type -> Ident -> Synth Function
synthRecurseOn splitOn args retType fnName = do
  debug $ "- trying recurse on arg " ++ show splitOn ++ "; fnName = " ++ fnName
  egs <- asks examples
  e <- gets env

  -- we cannot split on an argument which is not fully evaluated
  guard (not (argIsThunk splitOn egs))

  let (splitArg, splitTy) = args !! splitOn
  case splitTy of
    TyConstr dtName dtArgs -> case lookupDataType dtName e of
      Just (DataType tyArgs dtConstrs) -> do
        let s = zip tyArgs dtArgs :: Subst
            concreteConstructors = [ DataConstructor i (map (sub s) ts)
                                   | DataConstructor i ts <- dtConstrs ]

        -- for each constructor in the datatype
        cases <- forM concreteConstructors $ \(DataConstructor con constructorArgTypes) -> do
          constructorArgs <- forM constructorArgTypes $ \ty -> do
            name <- fresh
            return (name, ty)
          
          caseFnName <- fresh
          recursiveCallName <- fresh

          let recursiveArgs = forM args $ \(_, t) -> chooseRecursiveArg t constructorArgs
              allArgs = args ++ constructorArgs ++ [(recursiveCallName, retType)]
              constructorParams = map fst constructorArgs
              functionCall = applyMany $ map Var (caseFnName : map fst allArgs)

          -- TODO: simplify this code to be non-monadic?
          (recursivePart, body) <- case recursiveArgs of
            Nothing -> do
              debug $ "could not find suitable recursive argument from options: " ++ show constructorArgs ++ " so synthesising normally"

              return ( NoRecurse
                     , functionCall )
            Just recursiveArgs -> do
              let recursiveCall = applyMany $ map Var (fnName : recursiveArgs)
              
              return ( Recurse recursiveCall
                     , Let recursiveCallName recursiveCall functionCall )
          
          debug $ "body for " ++ con ++ " is: '" ++ show body 

          -- make a new function name to synthesise this case inside
          return ( (caseFnName, allArgs, recursivePart)
                 , (con, constructorParams, body) )

        let body = Case (Var splitArg) (map snd cases)
        let fn = Function { args = args
                          , ret = retType
                          , body = body
                          , egs = egs }

        -- attempt to actually synthesise the auxiliary functions
        withFunction fnName fn $ forM_ cases $ \((caseFnName, allArgs, recursivePart), (con,_,_)) -> do
          e <- gets env
          
          case recursivePart of
            Recurse ex -> do
              let fnType = finalise $ foldr (-->) retType (map snd allArgs ++ [retType])
                  en = fromEnvironment e ++ [(caseFnName, (fnType, Local))]
              -- define 'caseFnName : t1 -> t2 -> ...' in the environment
              case runExcept (compile en ex) of
                Left err -> do
                  debug $ "! could not compile recursive call: '" ++ show ex ++ "': " ++ show err
                  fail "compile error"
                Right recursiveCall -> do
                  -- the recursive call is currently being blocked by fnName not being defined
                  let thunk = Thunk recursiveCall fnName

                  -- find the examples which use the appropriate constructor for this branch,
                  -- and update them (give them the deconstructed arguments as well as their
                  -- existing parameters)
                  let examples = [ Eg (ins ++ map Val conArgs' ++ [thunk]) out
                                 | Eg ins out <- egs
                                 , let (con', conArgs') = deconstruct' (fromVal (ins !! splitOn))
                                 , con == con']

                  withExamples examples (synthDef caseFnName (map snd allArgs) retType)
            NoRecurse -> do
              let examples = [ Eg (ins ++ map Val conArgs') out
                             | Eg ins out <- egs
                             , let (con', conArgs') = deconstruct' (fromVal (ins !! splitOn))
                             , con == con' ]

              withExamples examples (synthDef caseFnName (map snd allArgs) retType)

        debug $ "done: recurse on arg " ++ show splitOn
        return fn

      Nothing -> fail "non-datatype or undefined"
    _nonADT -> fail "can't recurse on non-ADT"

chooseRecursiveArg :: Type -> [(Ident, Type)] -> Maybe Ident
chooseRecursiveArg t consArgs = fst <$> find (\(_, t') -> t == t') consArgs

debug :: String -> Synth ()
debug s = do
  d <- asks depth
  let prefix = concat (replicate d "* ")
  traceM $ prefix ++ s

replace :: Int -> a -> [a] -> [a]
replace 0 x (y:ys) = x:ys
replace n x (y:ys) = y : replace (n-1) x ys
replace _ _ [] = undefined

hasVal :: Arg -> Term -> Bool
hasVal (Val v) t = v == t
hasVal (Thunk _ _) t = False

fromVal :: Arg -> Term
fromVal (Val v) = v
fromVal _ = undefined

isThunk :: Arg -> Bool
isThunk (Val _) = False
isThunk (Thunk _ _) = True

argIsThunk :: Int -> [Example] -> Bool
argIsThunk n [] = False
argIsThunk n ((Eg args _):_) = isThunk (args !! n)

synthDef :: Ident -> [Type] -> Type -> Synth Ident
synthDef name args ret = do
  fn <- synth args ret name
  defineFunctionNamed name fn

defineFunctionNamed :: Ident -> Function -> Synth Ident
defineFunctionNamed n f = do
  e <- gets env

  let compiled = compile (fromEnvironment e) (assemble f)
  case runExcept compiled of
    Left err -> do
      debug $ "! could not compile function '" ++ n ++ "': " ++ show err
      debug $ "  (" ++ n ++ " := " ++ show (body f) ++ ")"
      fail "compile error"
    Right fnTerm -> do
      debug $ " : defined function '" ++ n ++ "': " ++ show fnTerm
      modify $ \s -> s { functions = (n, f) : functions s
                       , env = defineTerm n (getType f) fnTerm e }
      return n

undefineFunctionNamed :: Ident -> Synth ()
undefineFunctionNamed n = do
  modify $ \s -> s { functions = [ (n', f) | (n', f) <- functions s, n /= n' ]
                   , env = undefineTerm n (env s) }

withFunction :: Ident -> Function -> Synth a -> Synth a
withFunction name f s = do
  defineFunctionNamed name f
  r <- s
  undefineFunctionNamed name
  return r

exit :: Monad m => MaybeT m a
exit = fail "ignored"

try ::  Monad m => [MaybeT m a] -> MaybeT m a
try [] = fail "exhausted all possibilities"
try (x:xs) = let x' = runMaybeT x in MaybeT $ do
  m <- x'
  case m of
    Nothing -> runMaybeT (try xs)
    Just r -> return (Just r)

assemble :: Function -> Expr
assemble (Function args _ body _) = foldr (Abs . fst) body args

getType :: Function -> Scheme
getType (Function args ret _ _) = 
  let argTypes = map snd args
  in finalise $ foldr (-->) ret argTypes

collapse :: Functions -> Expr -> Expr
collapse fns app@(App f x) = case unfoldApp app of
  (Var f', xs') -> case lookup f' fns of
    Nothing -> App (collapse fns f) (collapse fns x)
    Just fn -> app
  _ -> app
collapse _ _ = error "not yet implemented collapse for this expression"

fresh :: Synth Ident
fresh = do
  name <- gets (head . newNames)
  modify $ \s@SynthState { newNames = (n:ns) } -> s { newNames = ns }
  return name

specialiseConstructor :: Type -> Type -> Type
specialiseConstructor conTy ret = case runExcept (runUnify u) of
  Left err -> error "unexpected error specialising constructor"
  Right s -> sub s genTy'
  where (argTys, conRetTy) = unfoldFnTy conTy
        varNames = take (length argTys) [ "*temp" ++ show i | i <- [0..] ]
        genTy = foldr ((-->) . TyVar) ret varNames
        (conTy', genTy') = renameToDistinct conTy genTy
        u = unify genTy' conTy'

lookupType :: Ident -> Synth (Maybe Scheme)
lookupType x = do
  ts <- gets (terms . env)
  return $ fmap fst (lookup x ts)

lookupType' :: Ident -> Synth Scheme
lookupType' x = fromJust <$> lookupType x

withExamples :: [Example] -> Synth a -> Synth a
withExamples egs = local (\l -> l { examples = egs })

fnNames = [ "fn" ++ show i | i <- [0..] ]

deconstruct :: Term -> Maybe (Ident, [Term])
deconstruct (CConstr i) = Just (i, [])
deconstruct (CApp l r) = do
  (i, ts) <- deconstruct l
  return (i, ts ++ [r])
deconstruct (CInt n) = deconstruct (intToSucs n)
deconstruct t = Nothing

deconstruct' :: Term -> (Ident, [Term])
deconstruct' = fromJust . deconstruct

intToSucs :: Int -> Term
intToSucs 0 = CConstr "Zero"
intToSucs n = CApp (CConstr "Suc") (intToSucs (n - 1))

sharedConstr :: [Example] -> Maybe Ident
sharedConstr [] = Nothing
sharedConstr xs = do
  let outputs = [ o | Eg _ o <- xs ]
  (y:ys) <- forM outputs (fmap fst . deconstruct)
  if all (== y) ys then
    return y
  else
    Nothing

applyMany :: [Expr] -> Expr
applyMany = foldl1 App

unfoldFnTy :: Type -> ([Type], Type)
unfoldFnTy (TyConstr "->" [a, b]) =
  let (rest, ret) = unfoldFnTy b
  in (a : rest, ret)
unfoldFnTy t = ([], t)

unfoldApp :: Expr -> (Expr, [Expr])
unfoldApp (App f x) =
  let (f', args) = unfoldApp f
  in (f', args ++ [x])
unfoldApp e = (e, [])

type Unwind = State Functions

unwindFrom :: Ident -> Functions -> Functions
unwindFrom x = execState (unwindFn x)

unwindFn :: Ident -> Unwind ()
unwindFn f = do
  Function args ret body egs <- lookupU' f
  body' <- unwind body
  modify (insertFn f (Function args ret body' egs))

unwind :: Expr -> Unwind Expr
unwind (Var x) = do
  fn <- lookupU x
  case fn of
    Just Function{ body = body, args = [] } -> unwind body
    _ -> return $ Var x
unwind app@(App e1 e2) = case unfoldApp app of
    (Var x, args) -> do
      fn <- lookupU x
      case fn of
        Just fn -> if canInline x fn then inline x args else app'
        Nothing -> app'
    _ -> app'
  where app' = App <$> unwind e1 <*> unwind e2
unwind (Abs x e) = Abs x <$> unwind e
unwind (Let x e1 e2) = Let x <$> unwind e1 <*> unwind e2
unwind (LetRec x e1 e2) = LetRec x <$> unwind e1 <*> unwind e2
unwind (If e1 e2 e3) = If <$> unwind e1 <*> unwind e2 <*> unwind e3
unwind (Case e cases) = do
  cases' <- forM cases $ \(x, xs, b) -> do
    b' <- unwind b
    return (x, xs, b')

  Case <$> unwind e <*> return cases'
unwind (LitInt n) = return $ LitInt n
unwind (LitList xs) = LitList <$> mapM unwind xs
unwind (LitTuple xs) = LitTuple <$> mapM unwind xs
unwind (LitChar c) = return $ LitChar c
unwind (TypeSpec e t) = TypeSpec <$> unwind e <*> return t
unwind (Hole n) = return $ Hole n

inline :: Ident -> [Expr] -> Unwind Expr
inline f args = do
  unwindFn f
  Function fnArgs _ fnBody _ <- lookupU' f
  let arguments = zip (map fst fnArgs) args
  return $ subExpr arguments fnBody

lookupU :: Ident -> Unwind (Maybe Function)
lookupU f = fmap (lookup f) get

lookupU' :: Ident -> Unwind Function
lookupU' f = fmap fromJust (lookupU f)

canInline :: Ident -> Function -> Bool
canInline fnName Function{ body = body } = not (body `calls` fnName)

insertFn :: Ident -> Function -> Functions -> Functions
insertFn x fn [] = []
insertFn x fn ((x', fn'):xs)
  | x == x' = (x, fn) : xs
  | otherwise = (x', fn') : insertFn x fn xs

calledBy :: Expr -> [Ident]
calledBy app@(App _ _) = case unfoldApp app of
  (Var x, xs) -> x : concatMap calledBy xs
  (f, xs) -> calledBy f ++ concatMap calledBy xs
calledBy (Abs _ a) = calledBy a
calledBy (Let _ a b) = calledBy a ++ calledBy b
calledBy (LetRec _ a b) = calledBy a ++ calledBy b
calledBy (If a b c) = calledBy a ++ calledBy b ++ calledBy c
calledBy (Case a cs) = calledBy a ++ concatMap (\(_,_,b) -> calledBy b) cs
calledBy (LitList xs) = concatMap calledBy xs
calledBy (LitTuple xs) = concatMap calledBy xs
calledBy (TypeSpec a _) = calledBy a
calledBy _ = []

allCalledBy :: Ident -> Functions -> [Ident]
allCalledBy x fns = go x fns []
  where go :: Ident -> Functions -> [Ident] -> [Ident]
        go x fns visited
          | x `elem` visited = visited
          | otherwise = x : case lookup x fns of
              Nothing -> []
              Just Function{ body = body } ->
                let newCalls = calledBy body \\ (x : visited)
                in foldl' (\vs call -> go call fns vs) visited newCalls

removeRedundant :: Ident -> Functions -> Functions
removeRedundant x fns = filter ((`elem` used) . fst) fns
  where used = allCalledBy x fns

calls :: Expr -> Ident -> Bool
calls e i = i `elem` calledBy e

toVal :: Value a => a -> Arg
toVal = Val . toTerm

(...) :: (b -> c) -> (a1 -> a2 -> b) -> a1 -> a2 -> c
(...) = (.) . (.)

test'' env = synthesise env "head" (tyList tyInt --> tyInt)
  [ Eg [toVal ([1, 2] :: [Int])] (toTerm (1 :: Int))
  , Eg [toVal ([0, 2, 3] :: [Int])] (toTerm (0 :: Int)) ]

test' env = synthesise env "double" (tyInt --> tyList tyInt --> tyList tyInt)
  [ Eg [toVal (0 :: Int), toVal ([1] :: [Int])] (toTerm ([0, 0, 1] :: [Int]))
  , Eg [toVal (2 :: Int), toVal ([] :: [Int])] (toTerm ([2, 2] :: [Int])) ]

test env = synthesise env "is_one" (tyInt --> tyBool)
  [ Eg [toVal (0 :: Int)] (toTerm False)
  , Eg [toVal (1 :: Int)] (toTerm True)
  , Eg [toVal (2 :: Int)] (toTerm False) ]

testStutter env = synthesise env "stutter" (tyList tyInt --> tyList tyInt)
  [ Eg [toVal ([] :: [Int])] (toTerm ([] :: [Int]))
  , Eg [toVal ([1, 2] :: [Int])] (toTerm ([1, 1, 2, 2] :: [Int])) ]
