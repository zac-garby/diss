module Editor where

import Control.Monad
import Data.Maybe
import Data.List
import Types
import Parser (Ident)
-- import Control.Monad.State

import qualified Parser as P

data Command = GotoAbsVar Int | GotoAbsBody
             | GotoLetArg Int | GotoLetVal | GotoLetBody
             | GotoIfCond | GotoIfTrue | GotoIfFalse
             | GotoIndex Int
             deriving (Eq, Ord, Show)

data Crumb = InApp [Expr] [Expr]
           | InAbsVar [Ident] [Ident] Expr | InAbsBody [Ident]
           | InLetArg [Ident] [Ident] Expr Expr | InLetVal [Ident] Expr | InLetBody [Ident] Expr
           | InLetRecArg [Ident] [Ident] Expr Expr | InLetRecVal [Ident] Expr | InLetRecBody [Ident] Expr
           | InIfCond Expr Expr | InIfTrue Expr Expr | InIfFalse Expr Expr
           | InList [Expr] [Expr]
           | InTuple [Expr] [Expr]
           deriving (Eq, Show)

data Expr = Var Ident
          | App [Expr]
          | Abs [Ident] Expr
          | Let [Ident] Expr Expr
          | LetRec [Ident] Expr Expr
          | If Expr Expr Expr
          | LitInt Int
          | LitBool Bool
          | LitList [Expr]
          | LitTuple [Expr]
          | LitString String
          | LitChar Char
          | TypeSpec Expr Type
          | Hole
          deriving (Show, Eq)

data Cursor = CExpr Expr
            | CName Ident
            deriving (Show, Eq)

data Location = At Cursor [Crumb]
            deriving Show

e1 = App [Abs ["x", "y", "z"] (Var "x"), LitInt 1, LitInt 2, LitInt 3]
e2 = LitList [LitInt 1, LitInt 2, LitInt 3]
e3 = LitTuple [LitInt 1, LitInt 2, LitInt 3]

edit :: Expr -> Location
edit e = At (CExpr e) []

top :: Location -> Maybe Expr
top (At (CExpr e) []) = return e
top (At (CName x) []) = Nothing
top e              = up e >>= top

goto :: Command -> Location -> Maybe Location
goto (GotoIndex i)  (At (CExpr (App es)) cs) | length es > i
  = return $ At (CExpr (es !! i)) (InApp (take i es) (drop (i + 1) es) : cs)
goto (GotoAbsVar i) (At (CExpr (Abs xs e)) cs) | length xs > i
  = return $ At (CName (xs !! i)) (InAbsVar (take i xs) (drop (i + 1) xs) e : cs)
goto GotoAbsBody    (At (CExpr (Abs xs e)) cs) = return $ At (CExpr e) (InAbsBody xs : cs)
goto (GotoLetArg i) (At (CExpr (Let args v b)) cs) | length args > i
  = return $ At (CName (args !! i)) (InLetArg (take i args) (drop (i + 1) args) v b : cs)
goto GotoLetVal     (At (CExpr (Let args v b)) cs) = return $ At (CExpr v) (InLetVal args b : cs)
goto GotoLetBody    (At (CExpr (Let args v b)) cs) = return $ At (CExpr b) (InLetBody args v : cs)
goto (GotoLetArg i) (At (CExpr (LetRec args v b)) cs) | length args > i
  = return $ At (CName (args !! i)) (InLetRecArg (take i args) (drop (i + 1) args) v b : cs)
goto GotoLetVal     (At (CExpr (LetRec args v b)) cs) = return $ At (CExpr v) (InLetRecVal args b : cs)
goto GotoLetBody    (At (CExpr (LetRec args v b)) cs) = return $ At (CExpr b) (InLetRecBody args v : cs)
goto GotoIfCond     (At (CExpr (If c t f)) cs) = return $ At (CExpr c) (InIfCond t f : cs)
goto GotoIfTrue     (At (CExpr (If c t f)) cs) = return $ At (CExpr t) (InIfTrue c f : cs)
goto GotoIfFalse    (At (CExpr (If c t f)) cs) = return $ At (CExpr f) (InIfFalse c t : cs)
goto (GotoIndex i)  (At (CExpr (LitList es)) cs) | length es > i
  = return $ At (CExpr (es !! i)) (InList (take i es) (drop (i + 1) es) : cs)
goto (GotoIndex i)  (At (CExpr (LitTuple es)) cs) | length es > i
  = return $ At (CExpr (es !! i)) (InTuple (take i es) (drop (i + 1) es) : cs)
goto _ _ = Nothing

up :: Location -> Maybe Location
up (At (CExpr e) (InApp p q : cs))        = return $ At (CExpr (App (p ++ [e] ++ q))) cs
up (At (CName x) (InAbsVar p q e : cs))   = return $ At (CExpr (Abs (p ++ [x] ++ q) e)) cs
up (At (CExpr e) (InAbsBody xs : cs))     = return $ At (CExpr (Abs xs e)) cs
up (At (CName x) (InLetArg pre post v b : cs)) = return $ At (CExpr (Let (pre ++ [x] ++ post) v b)) cs
up (At (CExpr v) (InLetVal x b : cs))     = return $ At (CExpr (Let x v b)) cs
up (At (CExpr b) (InLetBody x v : cs))    = return $ At (CExpr (Let x v b)) cs
up (At (CName x) (InLetRecArg pre post v b : cs))  = return $ At (CExpr (LetRec (pre ++ [x] ++ post) v b)) cs
up (At (CExpr v) (InLetRecVal x b : cs))  = return $ At (CExpr (LetRec x v b)) cs
up (At (CExpr b) (InLetRecBody x v : cs)) = return $ At (CExpr (LetRec x v b)) cs
up (At (CExpr c) (InIfCond t f : cs))     = return $ At (CExpr (If c t f)) cs
up (At (CExpr t) (InIfTrue c f : cs))     = return $ At (CExpr (If c t f)) cs
up (At (CExpr f) (InIfFalse c t : cs))    = return $ At (CExpr (If c t f)) cs
up (At (CExpr e) (InList pre post : cs))  = return $ At (CExpr (LitList (pre ++ [e] ++ post))) cs
up (At (CExpr e) (InTuple pre post : cs)) = return $ At (CExpr (LitTuple (pre ++ [e] ++ post))) cs
up _                                      = Nothing

down :: Location -> Maybe Location
down ed@(At (CExpr (App [])) cs) = Nothing
down ed@(At (CExpr (App es)) cs) = goto (GotoIndex 0) ed
down ed@(At (CExpr (Abs [] _)) cs) = Nothing
down ed@(At (CExpr (Abs _ _)) cs) = goto (GotoAbsVar 0) ed
down ed@(At (CExpr (Let [] _ _)) cs) = Nothing
down ed@(At (CExpr (Let _ _ _)) cs) = goto (GotoLetArg 0) ed
down ed@(At (CExpr (LetRec [] _ _)) cs) = Nothing
down ed@(At (CExpr (LetRec _ _ _)) cs) = goto (GotoLetArg 0) ed
down ed@(At (CExpr (If _ _ _)) cs) = goto GotoIfCond ed
down ed@(At (CExpr (LitList [])) cs) = Nothing
down ed@(At (CExpr (LitList _)) cs) = goto (GotoIndex 0) ed
down ed@(At (CExpr (LitTuple [])) cs) = Nothing
down ed@(At (CExpr (LitTuple _)) cs) = goto (GotoIndex 0) ed
down _ = Nothing

next :: Location -> Maybe Location
next (At _ []) = Nothing
next ed@(At _ (c : cs)) = up ed >>= goto (case c of
  InApp p []           -> GotoIndex 0
  InApp p q            -> GotoIndex (length p + 1)
  InAbsVar p [] _      -> GotoAbsBody
  InAbsVar p q _       -> GotoAbsVar (length p + 1)
  InAbsBody _          -> GotoAbsVar 0
  InLetArg p [] _ _    -> GotoLetVal
  InLetArg p q _ _     -> GotoLetArg (length p + 1)
  InLetVal _ _         -> GotoLetBody
  InLetBody _ _        -> GotoLetArg 0
  InLetRecArg p [] _ _ -> GotoLetVal
  InLetRecArg p q _ _  -> GotoLetArg (length p + 1) 
  InLetRecVal _ _      -> GotoLetBody
  InLetRecBody _ _     -> GotoLetArg 0
  InIfCond _ _         -> GotoIfTrue
  InIfTrue _ _         -> GotoIfFalse
  InIfFalse _ _        -> GotoIfCond
  InList pre []        -> GotoIndex 0
  InList pre post      -> GotoIndex (length pre + 1)
  InTuple pre []       -> GotoIndex 0
  InTuple pre post     -> GotoIndex (length pre + 1))

remove :: Location -> Maybe Location
remove = replace f g
  where f Hole = []
        f _ = [Hole]

        g "" = []
        g _ = [""]

replace :: (Expr -> [Expr]) -> (Ident -> [Ident]) -> Location -> Maybe Location
-- replace _ _ (At _ []) = Nothing
replace f _ ed@(At (CExpr e) cs) =
  case f e of
    []       -> deleteItem ed
    [e']     -> setExpr e' ed
    (e':es') -> do
      (c:cs) <- return cs
      c' <- case c of
        InApp ps qs -> return $ InApp ps (es' ++ qs)
        InList ps qs -> return $ InList ps (es' ++ qs)
        InTuple ps qs -> return $ InTuple ps (es' ++ qs)
        _ -> Nothing
      return $ At (CExpr e') (c' : cs)
replace _ g ed@(At (CName x) cs) =
  case g x of
    []       -> deleteItem ed
    [x']     -> setName x' ed
    (x':xs') -> do
      (c:cs) <- return cs
      c' <- case c of
        InAbsVar ps qs b -> return $ InAbsVar ps (xs' ++ qs) b
        InLetArg ps qs v b -> return $ InLetArg ps (xs' ++ qs) v b
        InLetRecArg ps qs v b -> return $ InLetRecArg ps (xs' ++ qs) v b
      return $ At (CName x') (c' : cs)

replaceExpr :: (Expr -> [Expr]) -> Location -> Maybe Location
replaceExpr f = replace f pure

replaceName :: (Ident -> [Ident]) -> Location -> Maybe Location
replaceName g = replace pure g

deleteItem :: Location -> Maybe Location
deleteItem ed@(At _ cs) = do
  (e', cs') <- go cs
  return $ At e' cs'
  where go :: [Crumb] -> Maybe (Cursor, [Crumb])
        go (InApp [] [] : cs)     = Nothing
        go (InApp [] (q:qs) : cs) = return $ (CExpr q, InApp [] qs : cs)
        go (InApp ps qs : cs)     = return $ (CExpr (last ps), InApp (init ps) qs : cs)

        go (InAbsVar [] [] b : cs)     = Nothing
        go (InAbsVar [] (q:qs) b : cs) = return $ (CName q, InAbsVar [] qs b : cs)
        go (InAbsVar ps qs b : cs)     = return $ (CName (last ps), InAbsVar (init ps) qs b : cs)

        go (InLetArg [] [] v b : cs)     = Nothing
        go (InLetArg [] (q:qs) v b : cs) = return $ (CName q, InLetArg [] qs v b : cs)
        go (InLetArg ps qs v b : cs)     = return $ (CName (last ps), InLetArg (init ps) qs v b : cs)
        
        go (InLetRecArg [] [] v b : cs)     = Nothing
        go (InLetRecArg [] (q:qs) v b : cs) = return $ (CName q, InLetRecArg [] qs v b : cs)
        go (InLetRecArg ps qs v b : cs)     = return $ (CName (last ps), InLetRecArg (init ps) qs v b : cs)
        
        go (InList [] [] : cs)     = return $ (CExpr (LitList []), cs)
        go (InList [] (q:qs) : cs) = return $ (CExpr q, InList [] qs : cs)
        go (InList ps qs : cs)     = return $ (CExpr (last ps), InTuple (init ps) qs : cs)
        
        go (InTuple [] [] : cs)     = return $ (CExpr (LitTuple []), cs)
        go (InTuple [] (q:qs) : cs) = return $ (CExpr q, InTuple [] qs : cs)
        go (InTuple ps qs : cs)     = return $ (CExpr (last ps), InTuple (init ps) qs : cs)
        
        go _ = Nothing

modify :: (Expr -> Expr) -> (Ident -> Ident) -> Location -> Maybe Location
modify f _ (At (CExpr e) cs) = return $ At (CExpr (f e)) cs
modify _ g (At (CName x) cs) = return $ At (CName (g x)) cs

setExpr :: Expr -> Location -> Maybe Location
setExpr e = modify (const e) id

setName :: Ident -> Location -> Maybe Location
setName x = modify id (const x)

render :: Location -> String
render (At (CExpr e) cs) = fst (foldl (uncurry renderIn) ("<" ++ showEx e ++ ">", False) cs)
render (At (CName x) cs) = fst (foldl (uncurry renderIn) ("<" ++ showEx (Var x) ++ ">", False) cs)

render' = Just . render

renderIn :: String -> Bool -> Crumb -> (String, Bool)
renderIn s b (InApp p q) = (betweenExprs " " p q (bracket b s), True)
renderIn s _ (InAbsVar p q b) = ("λ" ++ between " " p q s ++ " → " ++ showEx b, True)
renderIn s _ (InAbsBody xs) = ("λ" ++ intercalate " " xs ++ " → " ++ s, True)
renderIn s _ (InLetArg p q v b) = ("let " ++ between " " p q s ++ " = " ++ showEx v ++ " in " ++ showEx b, True)
renderIn s _ (InLetVal xs b) = ("let " ++ intercalate " " xs ++ " = " ++ s ++ " in " ++ showEx b, True)
renderIn s _ (InLetBody xs v) = ("let " ++ intercalate " " xs ++ " = " ++ showEx v ++ " in " ++ s, True)
renderIn s _ (InLetRecArg p q v b) = ("let rec " ++ between " " p q s ++ " = " ++ showEx v ++ " in " ++ showEx b, True)
renderIn s _ (InLetRecVal xs b) = ("let rec " ++ intercalate " " xs ++ " = " ++ s ++ " in " ++ showEx b, True)
renderIn s _ (InLetRecBody xs v) = ("let rec " ++ intercalate " " xs ++ " = " ++ showEx v ++ " in " ++ s, True)
renderIn s _ (InIfCond t f) = ("if " ++ s ++ " then " ++ showEx t ++ " else " ++ showEx f, True)
renderIn s _ (InIfTrue c f) = ("if " ++ showEx c ++ " then " ++ s ++ " else " ++ showEx f, True)
renderIn s _ (InIfFalse c t) = ("if " ++ showEx c ++ " then " ++ showEx t ++ " else " ++ s, True)
renderIn s _ (InList p q) = ("[" ++ betweenExprs ", " p q s ++ "]", False)
renderIn s _ (InTuple p q) = ("(" ++ betweenExprs ", " p q s ++ ")", False)

showEx :: Expr -> String
showEx (Var "") = "..."
showEx (Var x) = x
showEx (App es) = intercalate " " (map br es)
showEx (Abs xs e) = "λ" ++ intercalate " " xs ++ " → " ++ showEx e
showEx (Let xs v b) = "let " ++ intercalate " " xs ++ " = " ++ showEx v ++ " in " ++ showEx b
showEx (LetRec xs v b) = "let rec " ++ intercalate " " xs ++ " = " ++ showEx v ++ " in " ++ showEx b
showEx (If c t f) = "if " ++ showEx c ++ " then " ++ showEx t ++ " else " ++ showEx f
showEx (LitInt n) = show n
showEx (LitBool b) = show b
showEx (LitList xs) = "[" ++ intercalate ", " (map showEx xs) ++ "]"
showEx (LitTuple xs) = "(" ++ intercalate ", " (map showEx xs) ++ ")"
showEx (LitString s) = "\"" ++ s ++ "\""
showEx (LitChar c) = show c
showEx (TypeSpec e t) = showEx e ++ " : " ++ show t
showEx Hole = "_"

between :: String -> [String] -> [String] -> String -> String
between sep p q x = intercalate sep (p ++ [x] ++ q)

betweenExprs :: String -> [Expr] -> [Expr] -> String -> String
betweenExprs sep p q = between sep (map br p) (map br q)

bracket :: Bool -> String -> String
bracket True s = "(" ++ s ++ ")"
bracket False s = s

needsBracket :: Expr -> Bool
needsBracket e@(App _) = True
needsBracket e@(Abs _ _) = True
needsBracket e@(Let _ _ _) = True
needsBracket e@(LetRec _ _ _) = True
needsBracket e@(If _ _ _) = True
needsBracket e@(TypeSpec _ _) = True
needsBracket _ = False

br :: Expr -> String
br e = bracket (needsBracket e) (showEx e)

test :: Maybe Location -> IO ()
test l = putStrLn . fromMaybe "no result" $ l >>= render'
