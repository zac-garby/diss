module Parser ( Term (..)
              , Definition (..)
              , Ident
              , Program
              , parseProgram
              , parseTerm ) where

import Text.ParserCombinators.ReadP
import Data.Char
import Control.Monad
import Control.Applicative hiding (many)

type Ident = String
data Definition = Definition Ident Term
type Program = [Definition]

data Term = Var Ident
          | App Term Term
          | Abs Ident Term
          | Let Ident Term Term
          | If Term Term Term
          | LitInt Int
          | LitBool Bool
          deriving (Eq, Ord)

instance Show Term where
  show (Var v) = v
  show (App f x) = "(" ++ show f ++ " " ++ show x ++ ")"
  show (Abs v t) = "λ" ++ v ++ "." ++ show t
  show (Let v val body) = "let " ++ v ++ " = " ++ show val ++ " in " ++ show body
  show (If cond t f) = "if " ++ show cond ++ " then " ++ show t ++ " else " ++ show f
  show (LitInt i) = show i
  show (LitBool b) = show b

parseProgram :: String -> Maybe Program
parseProgram s = case readP_to_S (space *> program <* space <* eof) s of
  ((p, _):_) -> Just p
  _ -> Nothing

parseTerm :: String -> Maybe Term
parseTerm s = case readP_to_S (space *> term <* space <* eof) s of
  ((t, _):_) -> Just t
  _ -> Nothing

program :: ReadP Program
program = sepBy def space

def :: ReadP Definition
def = do
  name <- ident             <* space
  args <- sepBy ident space <* space
  char '='                  <* space
  body <- term              <* space
  char '.'
  return $ Definition name (foldr Abs body args)

term :: ReadP Term
term = choice [ app
              , abstr
              , letExpr
              , ifExpr
              , atom ]

atom :: ReadP Term
atom = choice [var, bracket, litInt, litBool]

app :: ReadP Term
app = chainl1 atom (space >> return App)

var :: ReadP Term
var = Var <$> ident

abstr :: ReadP Term
abstr = do
  (char '\\' <|> char 'λ') <* space
  xs <- sepBy1 ident space <* space
  string "->"              <* space
  t <- term
  return $ foldr Abs t xs

letExpr :: ReadP Term
letExpr = do
  string "let" <* space
  x <- ident   <* space
  string "="   <* space
  val <- term  <* space
  string "in"  <* space
  body <- term
  return $ Let x val body

ifExpr :: ReadP Term
ifExpr = do
  string "if"      <* space
  cond <- term     <* space
  string "then"    <* space
  positive <- term <* space
  string "else"    <* space
  negative <- term
  return $ If cond positive negative

litInt :: ReadP Term
litInt = LitInt <$> int

litBool :: ReadP Term
litBool = LitBool . read <$> (string "True" <|> string "False")

bracket :: ReadP Term
bracket = do
  char '('  <* space
  t <- term <* space
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

