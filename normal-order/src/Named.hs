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
          deriving (Eq, Show)

parseTerm1 = fromJust . parseTerm

parseTerm :: String -> Maybe Term
parseTerm s = case readP_to_S (space *> termP <* space <* eof) s of
  ((t, _):_) -> Just t
  _ -> Nothing

{-
GRAMMAR:

  term ::= abs | app
  abs  ::= ('\' | 'λ') name '.' term
  app  ::= { var | bracket }

  bracket ::= '(' term ')'
  name    ::= string of letters
-}

termP :: ReadP Term
termP = choice [absP, appP]

absP :: ReadP Term
absP = do
  (char '\\' <|> char 'λ') <* space
  n <- nameP <* space
  char '.' <* space
  t <- termP
  return $ Abs n t

appP :: ReadP Term
appP = chainl1 (choice [varP, bracketP]) (space >> return App)

bracketP :: ReadP Term
bracketP = do
  char '(' <* space
  t <- termP <* space
  char ')'
  return t

varP :: ReadP Term
varP = Var <$> nameP

nameP :: ReadP Name
nameP = munch1 isLetter

space :: ReadP ()
space = skipMany (satisfy isSpace)
