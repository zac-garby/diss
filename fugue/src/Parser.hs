{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}

module Parser ( Expr (..)
              , Definition (..)
              , DataConstructor (..)
              , ReplInput (..)
              , Ident
              , Program
              , ops
              , parseExpr
              , parseExpr'
              , parseProgram
              , parseType
              , parseRepl
              , pprintIdent
              , foldExpr
              , subExpr
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
                | TypeDefinition Ident Type
                | DataDefinition Ident DataType
                deriving Show

data ReplInput = ReplDef Definition | ReplExpr Expr
  deriving Show

type Program = [Definition]

data Expr = Var Ident
          | App Expr Expr
          | Abs Ident Expr
          | Let Ident Expr Expr
          | LetRec Ident Expr Expr
          | If Expr Expr Expr
          | Case Expr [(Ident, [Ident], Expr)]
          | LitInt Int
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
ops = [ (RightAssoc, [ ("$", "__apply") ])
      , (LeftAssoc,  [ ("||", "__or") ])
      , (LeftAssoc,  [ ("&&", "__and") ])
      , (LeftAssoc,  [ ("=/=", "__neq"), ("==", "__eq") ])
      , (LeftAssoc,  [ ("<=", "__lte"), (">=", "__gte"), ("<", "__lt"), (">", "__gt") ])
      , (LeftAssoc,  [ ("!", "__index") ])
      , (RightAssoc, [ ("::", "Cons") ])
      , (RightAssoc, [ (".", "__comp") ])
      , (LeftAssoc,  [ ("++", "__app"), ("+", "__add"), ("-", "__sub") ])
      , (LeftAssoc,  [ ("*", "__mul"), ("/", "__div"), ("%", "__mod") ]) ]

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
parseRepl = parseWrapper (only replInput)

parseExpr' = parseWrapper' expr

only p = whitespace *> p <* whitespace <* eof

parseWrapper' :: Parser a -> String -> a
parseWrapper' p s = case runParser p 0 "parseWrapper'" s of
  Left e -> error (show e)
  Right a -> a

parseWrapper :: Parser a -> FilePath -> String -> Except ParseError a
parseWrapper p f s = case runParser p 0 f s of
  Left e -> throwError e
  Right a -> return a

program :: Parser Program
program = sepEndBy (choice [try def, try dataDef, typeDef]) (keyword ";")

replInput :: Parser ReplInput
replInput = (ReplExpr <$> try expr)
        <|> (ReplDef <$> try (keyword "let" >> def))

def :: Parser Definition
def = lexeme $ do
  name <- ident
  args <- sepBy ident whitespace
  equals
  body <- expr
  return $ Definition name (foldr Abs body args)

typeDef :: Parser Definition
typeDef = lexeme $ do
  name <- ident
  colon
  t <- typeExpr
  return $ TypeDefinition name t

dataDef :: Parser Definition
dataDef = lexeme $ do
  keyword "data"
  name <- constrName
  vars <- sepBy ident whitespace
  equals
  constrs <- sepBy dataConstructor (keyword "|")
  return $ DataDefinition name (DataType vars constrs)

constrName :: Parser Ident
constrName = do
  name <- ident
  guard $ isUpper (head name)
  return name

dataConstructor :: Parser DataConstructor
dataConstructor = lexeme $ do
  name <- ident
  guard $ isUpper (head name)
  args <- sepBy typeExpr whitespace
  return $ DataConstructor name args

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
term = choice [ try app, abstr, try letRecExpr, letExpr, ifExpr, caseExpr ]
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

caseExpr :: Parser Expr
caseExpr = do
  keyword "case"
  t <- expr
  keyword "of"
  cases <- sepBy caseClause (keyword ",")
  return $ Case t cases

caseClause :: Parser (Ident, [Ident], Expr)
caseClause = do
  constr <- constrName
  args <- sepBy ident whitespace
  arrow
  body <- expr
  return (constr, args, body)

atom :: Parser Expr
atom = choice [ try var, hole, try bracket, list, tuple, litInt, litChar, litString ]
  <?> "atomic expression"

var :: Parser Expr
var = lexeme $ Var <$> ident

hole :: Parser Expr
hole = do
  keyword "?"
  h <- getState
  modifyState (+1)
  return $ Hole h

bracket :: Parser Expr
bracket = parens expr

list :: Parser Expr
list = between listStart listEnd $ do
  LitList <$> sepBy expr (keyword ",")

tuple :: Parser Expr
tuple = parens $ do
  vals <- sepEndBy expr (keyword ",")
  guard $ length vals `elem` [0, 2]
  return $ LitTuple vals

litInt :: Parser Expr
litInt = lexeme $ LitInt <$> int

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
tupleType = parens $ do
  args <- sepEndBy typeExpr (keyword ",")
  guard $ length args `elem` [0, 2]
  case args of
    [] -> return tyUnit
    [a, b] -> return $ tyPair [a, b]
    _ -> error "only units and 2-tuples supported"

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
ident = litIdent <|> opIdent

litIdent :: Parser Ident
litIdent = try $ lexeme $ do
  id <- (:) <$> satisfy validFirstId <*> many (satisfy validIdent)
  guard $ notElem id keywords
  return id

opIdent :: Parser Ident
opIdent = parens $ choice [ try (string o) >> return to
                          | (o, to) <- allOps ops ]

idents :: Parser [Ident]
idents = sepEndBy1 ident whitespace

int :: Parser Int
int = try $ do
  m <- option "" (string "-")
  n <- many1 (satisfy isDigit)
  return $ read (m ++ n)

whitespace :: Parser ()
whitespace = skipMany (try lineComment <|> void (oneOf " \n\t"))

lineComment :: Parser ()
lineComment = do
  string "--"
  skipMany (satisfy (/= '\n'))
  <?> "comment"

lexeme :: Parser a -> Parser a
lexeme p = p <* whitespace

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
           , "case"
           , "of"
           , "then"
           , "else"
           , "data" ]

mkOpParser :: Parser Expr -> Operators -> Parser Expr
mkOpParser p [] = p
mkOpParser p ((assoc, ops):rest) = assocFn assoc next mkOp
  where next = mkOpParser p rest
        mkOp = choice [ try (keyword op) >> return (App . App (Var to))
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
foldExpr c l a (Case co cases) = foldExpr c l a co `c`
                                foldr c a [ foldExpr c l a b | (_, _, b) <- cases ]
foldExpr c l a (LitList xs) = foldr (c . foldExpr c l a) a xs
foldExpr c l a (LitTuple xs) = foldr (c . foldExpr c l a) a xs
foldExpr c l a (TypeSpec e _) = foldExpr c l a e
foldExpr c l a t = l t

subExpr :: [(Ident, Expr)] -> Expr -> Expr
subExpr s (Var x) = case lookup x s of
  Just e -> e
  Nothing -> Var x
subExpr s (App e1 e2) = App (subExpr s e1) (subExpr s e2)
subExpr s (Abs x e) = Abs x (subExpr (unbind x s) e)
subExpr s (Let x e1 e2) = Let x (subExpr s e1) (subExpr (unbind x s) e2)
subExpr s (LetRec x e1 e2) = LetRec x (subExpr (unbind x s) e1) (subExpr (unbind x s) e2)
subExpr s (If e1 e2 e3) = If (subExpr s e1) (subExpr s e2) (subExpr s e3)
subExpr s (Case e1 cases) = Case (subExpr s e1)
                                 [ (c, xs, subExpr (unbindMany xs s) b)
                                 | (c, xs, b) <- cases ]
subExpr s (LitInt n) = LitInt n
subExpr s (LitList es) = LitList (map (subExpr s) es)
subExpr s (LitTuple es) = LitTuple (map (subExpr s) es)
subExpr s (LitChar c) = LitChar c
subExpr s (TypeSpec e t) = TypeSpec (subExpr s e) t
subExpr s (Hole n) = Hole n

unbind :: Ident -> [(Ident, Expr)] -> [(Ident, Expr)]
unbind x = filter ((/= x) . fst)

unbindMany :: [Ident] -> [(Ident, Expr)] -> [(Ident, Expr)]
unbindMany xs = filter (not . (`elem` xs) . fst)

isComplete :: Expr -> Bool
isComplete = null . holesIn

holesIn :: Expr -> [HoleIndex]
holesIn = foldExpr (++) f []
  where f (Hole i) = [i]
        f _ = []
