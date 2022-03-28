module Pretty ( prettyTerm
              , prettyType
              , prettyScheme
              , prettyEnv ) where

import Data.List
import Data.Char

import Compiler
import Types
import Holes
import Env
import Parser
import Infer

-- a pretty-printer for terms.
-- if the term is not designed to be user-visible, Nothing is returned
prettyTerm :: Term -> Maybe String
prettyTerm (CInt i) = Just $ colour 32 (show i)
prettyTerm (CBool b) = Just $ colour 32 (show b)
prettyTerm (CChar c) = Just $ colour 32 (show c)
prettyTerm (CNil) = Just $ "[]"
prettyTerm c@(CCons (CChar _) _) = do
  cs <- clist2list c
  return $ colour 32 ("\"" ++ map (\(CChar c) -> c) cs ++ "\"")
prettyTerm c@(CCons h t) = do
  ts <- clist2list c
  strings <- mapM prettyTerm ts
  return $ "[" ++ intercalate ", " strings ++ "]"
prettyTerm (CTuple xs) = do
  xs' <- mapM prettyTerm xs
  return $ "(" ++ intercalate ", " xs' ++ ")"
prettyTerm _ = Nothing

prettyType :: Type -> String
prettyType (TyVar v) = colour (92 + m) v
  where m = (sum (map ord v) - ord 'a') `mod` 5
prettyType (TyConstr "→" [l,r]) = bracketType l ++ " → " ++ prettyType r
prettyType (TyConstr "List" [t]) = "[" ++ prettyType t ++ "]"
prettyType (TyConstr "Tuple" xs) = "(" ++ intercalate ", " (map prettyType xs) ++ ")"
prettyType (TyConstr c []) = colour 32 c
prettyType (TyConstr c ts) = colour 32 c ++ " " ++ intercalate " " (map bracketType ts)
prettyType (TyHole i) = colour 91 (show i ++ "?")

prettyScheme :: Scheme -> String
prettyScheme (Forall [] t) = prettyType t
prettyScheme (Forall vs t) = colour 90 ("∀ " ++ intercalate " " vs ++ " . ") ++ prettyType t

prettyEnv :: Environment -> String
prettyEnv env = intercalate "\n" [ "  " ++ colour 33 (leftPad longestName (pprintIdent ops name)) ++
                                   " : " ++ prettyScheme sch
                                 | (name, (sch, _)) <- env ]
  where longestName = maximum (map (length . fst) env)

prettyHole :: BoundHole -> String
prettyHole bh@(BoundHole i ty env)
  = "    hole " ++ colour 33 (show i) ++ ":\n" ++
    "      wants : " ++ prettyType ty ++
    case relevant bh of
      [] -> ""
      relevant -> "\n      given ="
              ++ drop 13 (intercalate ",\n" [ "              " ++ colour 33 (pprintIdent ops id) ++
                                            " : " ++ prettyScheme t | (id, (t, l)) <- relevant ])
    ++
    case possibleFits bh of
      [] -> ""
      fits -> "\n      fits include ="
             ++ drop 20 (intercalate ",\n" [ "                     " ++ colour 33 (pprintIdent ops id) ++
                                           " : " ++ prettyScheme t | (id, (t, l)) <- take 5 fits ])
              
bracketType :: Type -> String
bracketType t@(TyConstr "→" _) = "(" ++ prettyType t ++ ")"
bracketType t = prettyType t

colour :: Int -> String -> String
colour n s = "\ESC[0;" ++ show n ++ "m" ++ s ++ "\ESC[0m"

leftPad :: Int -> String -> String
leftPad n s
  | n > len = replicate (n - len) ' ' ++ s
  | otherwise = s
  where len = length s

instance Show TypeError where
  show (UnifyInfiniteError v t) =
    "could not construct infinite type " ++ prettyType (TyVar v) ++ " ~ " ++ prettyType t
  show (UnifyConstructorsError c1 c2) =
    "could not unify type : " ++ prettyType c1 ++ " with : " ++ prettyType c2
  show (TypeSpecMismatch te tr) =
    "expression of type : " ++ prettyScheme te ++ " does not match requested type : " ++ prettyScheme tr
  show (UnboundVariableError v) =
    "unbound variable: " ++ colour 33 (pprintIdent ops v)
  show (FoundHoles sch hs) =
    "found holes in " ++ prettyScheme sch ++ ":\n"
    ++ intercalate "\n" (map prettyHole hs)

instance Show CompilerError where
  show (UndefinedVariable v) = "undeclared variable: " ++ v
  show FoundHole = "attempted to compile an incomplete expression containing a hole"
