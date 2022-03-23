module Parser ( Expr (..)
              , Definition (..)
              , Ident
              , Program
              , ops
              , parseExpr
              , parseProgram
              , parseType
              , pprintIdent
              , foldExpr
              , isComplete
              , holesIn ) where

import qualified Control.Monad.State.Lazy as S

import Text.Parsec
import Data.Char
import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Lazy
-- import Control.Applicative hiding (many)
import Debug.Trace

import Types

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
          | LitTuple [Expr]
          | LitChar Char
          | TypeSpec Expr Type
          | Hole Int
          deriving (Show, Eq)

type Parser = Parsec String Int

data Associativity = LeftAssoc | RightAssoc
  deriving (Show, Eq, Ord)

type Operators = [(Associativity, [(Ident, Ident)])]

-- the operators, listed from lowest to highest precedence
ops :: Operators
ops = [ (LeftAssoc,  [ ("$", "__apply") ])
      , (LeftAssoc,  [ ("==", "__eq") ])
      , (LeftAssoc,  [ ("<=", "__lte"), (">=", "__gte"), ("<", "__lt"), (">", "__gt") ])
      , (RightAssoc, [ ("::", "__cons") ])
      , (RightAssoc, [ (".", "__comp") ])
      , (LeftAssoc,  [ ("++", "__app"), ("+", "__add"), ("-", "__sub") ])
      , (LeftAssoc,  [ ("*", "__mul"), ("/", "__div") ]) ]

allOps :: Operators -> [(Ident, Ident)]
allOps ops = concat [ os | (_, os) <- ops ]

pprintIdent :: Operators -> Ident -> String
pprintIdent [] id = id
pprintIdent ((_, level):ops) id = case find ((== id) . snd) level of
  Just (op, _) -> "(" ++ op ++ ")"
  Nothing -> pprintIdent ops id

parseProgram = parseWrapper (only program)
parseExpr = parseWrapper (only expr)
parseType = parseWrapper (only typeExpr)

only p = whitespace *> p <* whitespace <* eof

parseWrapper :: Parser a -> FilePath -> String -> Except ParseError a
parseWrapper p f s = case runParser p 0 f s of
  Left e -> throwError e
  Right a -> return a

program :: Parser Program
program = sepEndBy def (keyword ";")

expr :: Parser Expr
expr = choice [try typeSpec, op]

typeSpec :: Parser Expr
typeSpec = do
  e <- op
  colon
  t <- typeExpr
  return $ TypeSpec e t

op :: Parser Expr
op = mkOpParser term ops

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
atom = choice [ var, hole, try section, try bracket, list, tuple, litInt, litBool, litChar, litString ]
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

tuple :: Parser Expr
tuple = parens $ do
  LitTuple <$> sepEndBy expr (keyword ",")

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

typeExpr :: Parser Type
typeExpr = choice [try funcType, atomType]

funcType :: Parser Type
funcType = do
  l <- atomType
  arrow
  r <- typeExpr
  return $ l --> r

listType :: Parser Type
listType = do
  listStart
  t <- typeExpr
  listEnd
  return $ tyList t

tupleType :: Parser Type
tupleType = parens $ tyTuple <$> sepEndBy typeExpr (keyword ",")

atomType :: Parser Type
atomType = choice [listType, try typeVar, try typeConstr, try (parens typeExpr), tupleType]

typeVar :: Parser Type
typeVar = do
  id <- ident
  guard $ all isLower id
  return $ TyVar id

typeConstr :: Parser Type
typeConstr = do
  id <- ident
  guard $ isUpper (head id)
  args <- many (try atomType)
  return $ TyConstr id args

ident :: Parser Ident
ident = try $ lexeme $ do
  id <- (:) <$> satisfy validFirstId <*> many (satisfy validIdent)
  guard $ not (id `elem` keywords)
  return id

idents :: Parser [Ident]
idents = sepEndBy1 ident whitespace

int :: Parser Int
int = try $ do
  m <- option "" (string "-")
  n <- many1 (satisfy isDigit)
  return $ read (m ++ n)

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

colon = keyword ":"
  <?> "colon"

listStart = keyword "["
listEnd = keyword "]"

lparen = keyword "("
rparen = keyword ")"

parens :: Parser a -> Parser a
parens = between lparen rparen

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

        assocFn LeftAssoc = chainl1
        assocFn RightAssoc = chainr1

unfoldAbs :: Expr -> ([Ident], Expr)
unfoldAbs (Abs v t) = (v:vs, t')
  where (vs, t') = unfoldAbs t
unfoldAbs t = ([], t)

foldExpr :: (a -> a -> a) -> (Expr -> a) -> a -> Expr -> a
foldExpr c l a (App f x) = foldExpr c l a f `c` foldExpr c l a x 
foldExpr c l a (Abs v t) = foldExpr c l a t
foldExpr c l a (Let v val body) = foldExpr c l a body `c` foldExpr c l a val
foldExpr c l a (LetRec v val body) = foldExpr c l a body `c` foldExpr c l a val
foldExpr c l a (If cond t f) = foldExpr c l a f `c` foldExpr c l a t `c` foldExpr c l a cond
foldExpr c l a (LitList xs) = foldr c a (map (foldExpr c l a) xs)
foldExpr c l a (LitTuple xs) = foldr c a (map (foldExpr c l a) xs)
foldExpr c l a (TypeSpec e _) = foldExpr c l a e
foldExpr c l a t = l t

isComplete :: Expr -> Bool
isComplete = null . holesIn

holesIn :: Expr -> [HoleIndex]
holesIn = foldExpr (++) f []
  where f (Hole i) = [i]
        f _ = []
