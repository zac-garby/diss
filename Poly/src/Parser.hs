module Parser ( Expr (..)
              , Definition (..)
              , Ident
              , Program
              , parseExpr
              , parseProgram
              , foldExpr ) where

import qualified Control.Monad.State.Lazy as S

import Text.Parsec
import Data.Char
import Data.List
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Lazy
-- import Control.Applicative hiding (many)
import Debug.Trace

type Ident = String
data Definition = Definition Ident Expr
  deriving Show
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
          deriving (Show, Eq, Ord)

type Parser = Parsec String Int

data Associativity = LeftAssoc | RightAssoc
  deriving (Show, Eq, Ord)

type Operators = [(Associativity, [(Ident, Ident)])]

ops :: Operators
ops = [ (LeftAssoc,  [ ("==", "__eq") ])
      , (RightAssoc, [ ("::", "__cons") ])
      , (LeftAssoc,  [ ("++", "__app"), ("+", "__add"), ("-", "__sub") ])
      , (LeftAssoc,  [ ("*", "__mul"), ("/", "__div") ]) ]

allOps :: Operators -> [(Ident, Ident)]
allOps ops = concat [ os | (_, os) <- ops ]

parseProgram = parseWrapper program
parseExpr = parseWrapper expr

parseWrapper :: Parser a -> FilePath -> String -> Except ParseError a
parseWrapper p f s = case runParser p 0 f s of
  Left e -> throwError e
  Right a -> return a

program :: Parser Program
program = sepEndBy def (keyword ".")

expr :: Parser Expr
expr = mkOpParser term ops

term :: Parser Expr
term = choice [ try app, abstr, try letRecExpr, letExpr, ifExpr ]
       <?> "term"

app :: Parser Expr
app = chainl1 atom (whitespace >> return App)

abstr :: Parser Expr
abstr = do
  lambda
  xs <- idents
  arrow
  body <- expr
  return $ foldr Abs body xs

letRecExpr :: Parser Expr
letRecExpr = do
  keyword "let"
  keyword "rec"
  Definition n v <- def
  keyword "in"
  body <- expr
  return $ LetRec n v body

letExpr :: Parser Expr
letExpr = do
  keyword "let"
  Definition n v <- def
  keyword "in"
  body <- expr
  return $ Let n v body

ifExpr :: Parser Expr
ifExpr = do
  keyword "if"
  cond <- expr
  keyword "then"
  positive <- expr
  keyword "else"
  negative <- expr
  return $ If cond positive negative

atom :: Parser Expr
atom = choice [ var, hole, try section, bracket, list, litInt, litBool, litChar, litString ]
  <?> "atomic expression"

var :: Parser Expr
var = lexeme $ Var <$> ident

hole :: Parser Expr
hole = do
  keyword "?"
  h <- getState
  modifyState (+1)
  return $ Hole h

section :: Parser Expr
section = parens $ choice [ try (string o >> return (Var to))
                          | (o, to) <- allOps ops ]

bracket :: Parser Expr
bracket = parens expr

list :: Parser Expr
list = between listStart listEnd $ do
  LitList <$> sepBy expr (keyword ",")

litInt :: Parser Expr
litInt = lexeme $ LitInt <$> int

litBool :: Parser Expr
litBool = lexeme $ LitBool . read <$> (keyword "True" <|> keyword "False")

litChar :: Parser Expr
litChar = lexeme $ do
  char '\''
  c <- satisfy (/= '\'')
  char '\''
  return $ LitChar c

litString :: Parser Expr
litString = lexeme $ do
  char '"'
  s <- many $ satisfy (/= '"')
  char '"'
  return $ LitList (map LitChar s)

ident :: Parser Ident
ident = try $ lexeme $ do
  id <- (:) <$> satisfy validFirstId <*> many (satisfy validIdent)
  guard $ not (id `elem` keywords)
  return id

idents :: Parser [Ident]
idents = sepEndBy1 ident whitespace

int :: Parser Int
int = lexeme $ read <$> many1 (satisfy isDigit)

whitespace :: Parser ()
whitespace = void $ many $ oneOf " \n\t"

lexeme :: Parser a -> Parser a
lexeme p = p <* whitespace

def :: Parser Definition
def = lexeme $ do
  name <- ident
  args <- sepBy ident whitespace
  equals
  body <- expr
  return $ Definition name (foldr Abs body args)

lambda = keyword "\\" <|> keyword "λ"
  <?> "lambda"

arrow = keyword "->" <|> keyword "→"
  <?> "arrow"

equals = keyword "="
  <?> "equals"

listStart = keyword "["
listEnd = keyword "]"

parens :: Parser a -> Parser a
parens = between (lexeme $ char '(') (lexeme $ char ')')

keyword :: String -> Parser String
keyword = try . lexeme . string

validIdent :: Char -> Bool
validIdent c = isAlphaNum c || c `elem` "_-'"

validFirstId :: Char -> Bool
validFirstId c = isLetter c || c `elem` "_"

keywords :: [Ident]
keywords = [ "let"
           , "rec"
           , "in"
           , "if"
           , "then"
           , "else"
           , "True"
           , "False" ]

mkOpParser :: Parser Expr -> Operators -> Parser Expr
mkOpParser p [] = p
mkOpParser p ((assoc, ops):rest) = assocFn assoc next mkOp
  where next = mkOpParser p rest
        mkOp = choice [ try (keyword op) >> return (\l r -> App (App (Var to) l) r)
                      | (op, to) <- ops ]

assocFn :: Associativity -> Parser a -> Parser (a -> a -> a) -> Parser a
assocFn LeftAssoc = chainl1
assocFn RightAssoc = chainr1

{-
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
-}

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

foldExpr :: (a -> a -> a) -> (Expr -> a) -> a -> Expr -> a
foldExpr c l a (App f x) = foldExpr c l a f `c` foldExpr c l a x 
foldExpr c l a (Abs v t) = foldExpr c l a t
foldExpr c l a (Let v val body) = foldExpr c l a body `c` foldExpr c l a val
foldExpr c l a (LetRec v val body) = foldExpr c l a body `c` foldExpr c l a val
foldExpr c l a (If cond t f) = foldExpr c l a f `c` foldExpr c l a t `c` foldExpr c l a cond
foldExpr c l a (LitList xs) = foldr c a (map (foldExpr c l a) xs)
foldExpr c l a t = l t
