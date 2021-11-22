module Named ( Term (..)
             , parseTerm
             , parseTerm1 ) where

import Text.ParserCombinators.ReadP
import Control.Applicative hiding (many)
import Control.Monad (guard)
import Data.Char
import Data.Maybe

type Name = String

data Term = Var Name
          | Abs Name Term
          | App Term Term
          | Let Name Term Term
          | IntLit Int
          deriving (Eq, Show)

parseTerm1 = fromJust . parseTerm

parseTerm :: String -> Maybe Term
parseTerm s = case readP_to_S (space *> termP <* eof) s of
  ((t, _):_) -> Just t
  _ -> Nothing

{-
GRAMMAR:

  term ::= let name = term in term | abs | app
  abs  ::= ('\' | 'λ') name '.' term
  app  ::= { atom }
  atom ::= var | bracket | int
  
  bracket ::= '(' term ')'
  name    ::= string of non-space chars except "().\λ" or "let" or "in"
-}

termP :: ReadP Term
termP = choice [letP, absP, appP]

letP :: ReadP Term
letP = do
  string "let" <* space
  n <- nameP <* space
  char '=' <* space
  val <- termP <* space
  string "in" <* space
  body <- termP
  return $ Let n val body

absP :: ReadP Term
absP = do
  (char '\\' <|> char 'λ') <* space
  n <- nameP <* space
  char '.' <* space
  t <- termP
  return $ Abs n t

appP :: ReadP Term
appP = chainl1 atomP (space >> return App)

atomP :: ReadP Term
atomP = choice [intP, varP, bracketP]

bracketP :: ReadP Term
bracketP = do
  char '(' <* space
  t <- termP <* space
  char ')'
  return t

varP :: ReadP Term
varP = Var <$> nameP

intP :: ReadP Term
intP = IntLit . read <$> munch1 isDigit

nameP :: ReadP Name
nameP = do
  n <- munch1 validNameChar
  guard $ not (n `elem` ["λ", "\\", "let", "in"])
  return n

validNameChar '(' = False
validNameChar ')' = False
validNameChar '.' = False
validNameChar '\\' = False
validNameChar 'λ' = False
validNameChar c = not (isSpace c)

space :: ReadP ()
space = skipMany (satisfy isSpace)
