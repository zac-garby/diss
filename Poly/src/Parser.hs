module Parser ( Expr (..)
              , Definition (..)
              , Ident
              , Program
              , parseProgram
              , parseExpr ) where

import Text.ParserCombinators.ReadP
import Data.Char
import Data.List
import Control.Monad
import Control.Monad.Except
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
          | Hole
          deriving (Eq, Ord)

parseProgram = parseWrapper program
parseExpr = parseWrapper expr

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
atom = choice [var, hole, bracket, litInt, litBool]

app :: ReadP Expr
app = chainl1 atom (space >> return App)

var :: ReadP Expr
var = Var <$> ident

hole :: ReadP Expr
hole = string "?" >> return Hole

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

unfoldAbs :: Expr -> ([Ident], Expr)
unfoldAbs (Abs v t) = (v:vs, t')
  where (vs, t') = unfoldAbs t
unfoldAbs t = ([], t)

brack :: Expr -> String
brack (Var v) = v
brack (LitInt i) = show i
brack (LitBool b) = show b
brack e = "(" ++ show e ++ ")"
