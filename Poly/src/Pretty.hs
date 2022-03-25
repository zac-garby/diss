module Pretty ( prettyTerm
              , prettyType
              , prettyScheme
              , prettyEnv ) where

import Data.List

import Compiler
import Types
import Env
import Parser
import Infer

-- a pretty-printer for terms.
-- if the term is not designed to be user-visible, Nothing is returned
prettyTerm :: Term -> Maybe String
prettyTerm (CLitInt i) = Just $ colour 32 (show i)
prettyTerm (CLitBool b) = Just $ colour 32 (show b)
prettyTerm (CLitChar c) = Just $ colour 32 (show c)
prettyTerm (CLitNil) = Just $ "[]"
prettyTerm c@(CLitCons (CLitChar _) _) = do
  cs <- clist2list c
  return $ colour 32 ("\"" ++ map (\(CLitChar c) -> c) cs ++ "\"")
prettyTerm c@(CLitCons h t) = do
  ts <- clist2list c
  strings <- mapM prettyTerm ts
  return $ "[" ++ intercalate ", " strings ++ "]"
prettyTerm (CLitTuple xs) = do
  xs' <- mapM prettyTerm xs
  return $ "(" ++ intercalate ", " xs' ++ ")"
prettyTerm _ = Nothing

prettyType :: Type -> String
prettyType (TyVar v) = emph 32 v
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

prettyHole (BoundHole i ty env)
  = "    hole " ++ colour 33 (show i) ++ ":\n" ++
    "      wants : " ++ prettyType ty
  ++ case relevant of
      [] -> ""
      relevant -> "\n      given ="
              ++ drop 13 (intercalate ",\n" [ "              " ++ colour 33 (pprintIdent ops id) ++
                                            " : " ++ prettyScheme t | (id, (t, l)) <- relevant ])
  where relevant = reverse $ nubBy (\(i, _) (j, _) -> i == j)
                   [ (id, (t, l)) | (id, (t, l)) <- env, l == Local ]

bracketType :: Type -> String
bracketType t@(TyConstr "→" _) = "(" ++ prettyType t ++ ")"
bracketType t = prettyType t

colour :: Int -> String -> String
colour n s = "\ESC[0;" ++ show n ++ "m" ++ s ++ "\ESC[0m"

emph :: Int -> String -> String
emph n s = "\ESC[4;" ++ show n ++ "m" ++ s ++ "\ESC[0m"

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
    "unbound variable: " ++ colour 33 v
  show (FoundHoles sch hs) =
    "found holes in " ++ prettyScheme sch ++ ":\n"
    ++ intercalate "\n" (map prettyHole hs)
