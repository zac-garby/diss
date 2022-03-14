module Parser ( Expr (..)
              , Definition (..)
              , Ident
              , Program
              , parseProgram
              , parseExpr
              , foldExpr ) where

import qualified Control.Monad.State.Lazy as S

import Text.ParserCombinators.ReadP
import Data.Char
import Data.List
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Lazy
import Control.Applicative hiding (many)
import Debug.Trace

type Ident = String
data Definition = Definition Ident Expr
type Program = [Definition]

data Expr = Var Ident
          | App Expr Expr
          | Abs Ident Expr
          | Let Ident Expr Expr
          | LetRec Ident Expr Expr
          | If Expr Expr Expr
          | LitInt Int
          | LitBool Bool
          | LitList [Expr]
          | LitChar Char
          | Hole Int
          deriving (Eq, Ord)

parseProgram = parseWrapper program
parseExpr = parseWrapper (numberHoles <$> expr)

parseWrapper :: ReadP a -> FilePath -> String -> Except FilePath a
parseWrapper p f s = case readP_to_S (space *> p <* space <* eof) s of
  ((a, _):_) -> return a
  _ -> throwError f

program :: ReadP Program
program = sepBy (def <* space <* char '.') space

def :: ReadP Definition
def = do
  name <- ident             <* space
  args <- sepBy ident space <* space
  char '='                  <* space
  body <- expr
  return $ Definition name (foldr Abs body args)

expr :: ReadP Expr
expr = choice [ app
              , abstr
              , letRecExpr
              , letExpr
              , ifExpr ]

atom :: ReadP Expr
atom = choice [var, hole, bracket, litInt, litBool, litChar, litList]

app :: ReadP Expr
app = chainl1 atom (space >> return App)

var :: ReadP Expr
var = Var <$> ident

hole :: ReadP Expr
hole = do
  string "?"
  return $ Hole 0

abstr :: ReadP Expr
abstr = do
  (char '\\' <|> char 'λ')     <* space
  xs <- sepBy1 ident space     <* space
  (string "->" <|> string "→") <* space
  t <- expr
  return $ foldr Abs t xs

letRecExpr :: ReadP Expr
letRecExpr = do
  string "rec" <* space
  (Let n v b) <- letExpr
  return $ LetRec n v b

letExpr :: ReadP Expr
letExpr = do
  string "let"          <* space
  Definition n v <- def <* space
  string "in"           <* space
  body <- expr
  return $ Let n v body

ifExpr :: ReadP Expr
ifExpr = do
  string "if"      <* space
  cond <- expr     <* space
  string "then"    <* space
  positive <- expr <* space
  string "else"    <* space
  negative <- expr
  return $ If cond positive negative

litInt :: ReadP Expr
litInt = LitInt <$> int

litBool :: ReadP Expr
litBool = LitBool . read <$> (string "True" <|> string "False")

litChar :: ReadP Expr
litChar = do
  char '\''
  c <- satisfy (/= '\'')
  char '\''
  return $ LitChar c

litList :: ReadP Expr
litList = do
  string "[" <* space
  exprs <- sepBy expr (space >> string "," >> space)
  string "]" <* space
  return $ LitList exprs

bracket :: ReadP Expr
bracket = do
  char '('  <* space
  t <- expr <* space
  char ')'
  return t

ident :: ReadP Ident
ident = do
  id <- (:) <$> satisfy isLetter <*> munch validIdent
  guard $ not (id `elem` keywords)
  return id

int :: ReadP Int
int = read <$> munch1 isDigit

space :: ReadP ()
space = skipMany (satisfy isSpace)

validIdent :: Char -> Bool
validIdent c = isAlphaNum c || c `elem` "_-'"

keywords :: [Ident]
keywords = [ "let"
           , "in"
           , "if"
           , "then"
           , "else"
           , "True"
           , "False" ]

instance Show Expr where
  show (Var v) = v
  show (App f x) = show f ++ " " ++ brack x
  
  show (Abs v t) = "λ" ++ intercalate " " vs ++ " → " ++ show t'
    where (vs, t') = unfoldAbs (Abs v t)
    
  show (Let v val body) = "let " ++ v ++ " " ++ intercalate " " vs ++ " = "
                          ++ show val' ++ " in " ++ show body
    where (vs, val') = unfoldAbs val
    
  show (LetRec v val body) = "rec let " ++ v ++ " " ++ intercalate " " vs ++ " = "
                             ++ show val' ++ " in " ++ show body
    where (vs, val') = unfoldAbs val
    
  show (If cond t f) = "if " ++ show cond ++ " then " ++ show t ++ " else " ++ show f
  show (LitInt i) = show i
  show (LitBool b) = show b
  show (LitChar c) = show c
  show (LitList xs) = "[" ++ intercalate ", " (map show xs) ++ "]"
  show (Hole n) = "?" ++ show n

unfoldAbs :: Expr -> ([Ident], Expr)
unfoldAbs (Abs v t) = (v:vs, t')
  where (vs, t') = unfoldAbs t
unfoldAbs t = ([], t)

brack :: Expr -> String
brack (Var v) = v
brack (LitInt i) = show i
brack (LitBool b) = show b
brack (Hole n) = show (Hole n)
brack e = "(" ++ show e ++ ")"

numberHoles :: Expr -> Expr
numberHoles e = evalState (num e) 0
  where num :: Expr -> State Int Expr
        num (Var v) = return $ Var v
        num (App f x) = App <$> num f <*> num x
        num (Abs v t) = Abs v <$> num t
        num (Let v val body) = Let v <$> num val <*> num body
        num (LetRec v val body) = LetRec v <$> num val <*> num body
        num (If cond t f) = If <$> num cond <*> num t <*> num f
        num (LitInt i) = return $ LitInt i
        num (LitBool b) = return $ LitBool b
        num (LitChar c) = return $ LitChar c
        num (LitList xs) = LitList <$> mapM num xs
        num (Hole _) = do
          n <- S.get
          modify (+1)
          return $ Hole n

foldExpr :: (a -> a -> a) -> (Expr -> a) -> a -> Expr -> a
foldExpr c l a (App f x) = foldExpr c l a f `c` foldExpr c l a x 
foldExpr c l a (Abs v t) = foldExpr c l a t
foldExpr c l a (Let v val body) = foldExpr c l a body `c` foldExpr c l a val
foldExpr c l a (LetRec v val body) = foldExpr c l a body `c` foldExpr c l a val
foldExpr c l a (If cond t f) = foldExpr c l a f `c` foldExpr c l a t `c` foldExpr c l a cond
foldExpr c l a (LitList xs) = foldr c a (map (foldExpr c l a) xs)
foldExpr c l a t = l t
