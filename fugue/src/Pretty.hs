module Pretty ( prettyTerm
              , prettyType
              , prettyScheme
              , prettyTypes
              , prettyDataTypes ) where

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
prettyTerm (CConstr c) = Just $ colour 32 c
prettyTerm (CApp fn arg) = do
  fn' <- prettyTerm fn
  arg' <- bracketTerm arg
  Just $ fn' ++ " " ++ arg'
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

bracketTerm :: Term -> Maybe String
bracketTerm t@(CApp _ _) = do
  t' <- prettyTerm t
  return $ "(" ++ t' ++ ")"
bracketTerm t = prettyTerm t

prettyType :: Type -> String
prettyType (TyVar v) = colour (92 + m) v
  where m = (sum (map ord v) - ord 'a') `mod` 5
prettyType (TyConstr "->" [l,r]) = bracketType l ++ " → " ++ prettyType r
-- prettyType (TyConstr "List" [t]) = "[" ++ prettyType t ++ "]"
-- prettyType (TyConstr "Tuple" xs) = "(" ++ intercalate ", " (map prettyType xs) ++ ")"
prettyType (TyConstr c []) = colour 32 c
prettyType (TyConstr c ts) = colour 32 c ++ " " ++ intercalate " " (map bracketTypeApp ts)
prettyType (TyHole i) = colour 91 (show i ++ "?")

bracketType :: Type -> String
bracketType t@(TyConstr "->" _) = "(" ++ prettyType t ++ ")"
bracketType t = prettyType t

bracketTypeApp :: Type -> String
bracketTypeApp t@(TyConstr _ (_:_)) = "(" ++ prettyType t ++ ")"
bracketTypeApp t = bracketType t

prettyScheme :: Scheme -> String
prettyScheme (Forall [] t) = prettyType t
prettyScheme (Forall vs t) = colour 90 ("∀ " ++ intercalate " " vs ++ " . ") ++ prettyType t

prettyTypes :: [(Ident, (Scheme, Term))] -> String
prettyTypes env = intercalate "\n" [ "  " ++ colour 33 (leftPad longestName (pprintIdent ops name)) ++
                                   " : " ++ prettyScheme sch
                                 | (name, (sch, _)) <- env ]
  where longestName = maximum (map (length . fst) env)

prettyDataTypes :: [(Ident, DataType)] -> String
prettyDataTypes dts = intercalate "\n" $ do
  (name, DataType as cs) <- dts
  return $ colour 90 "data "
        ++ intercalate " " (colour 32 name : map (prettyType . TyVar) as)
        ++ " = "
        ++ (intercalate " | " $ do
             DataConstructor c args <- cs
             return $ intercalate " " (colour 32 c : map bracketTypeApp args))

prettyHole :: BoundHole -> String
prettyHole bh@(BoundHole i ty env)
  = "    hole " ++ colour 33 (show i) ++ ":\n" ++
    "    | wants : " ++ prettyType ty ++
    case relevant bh of
      [] -> ""
      relevant -> "\n    | given:\n"
                 ++ intercalate ",\n" [ "    |   " ++ colour 33 (pprintIdent ops id) ++
                                        " : " ++ prettyScheme t | (id, (t, l)) <- relevant ]
    ++ case viableFits bh of
         [] -> ""
         fits ->
           "\n    | fits include:\n"
           ++ intercalate ",\n" (map prettyFit (take 3 fits))
           ++ if length fits > 3
              then "\n    | " ++ colour 90 ("  ... (" ++ show (length fits - 3) ++ " more) ...")
              else ""
    ++ "\n    '---"

prettyFit :: Fit -> String
prettyFit (Fit id args sch) =
  "    |   " ++ colour 33 (pprintIdent ops id) ++ -- identifier of function
  concat [ colour 92 (" x" ++ show i) | (i, _) <- zip [0..] args ] ++ -- any arguments, arbitrary names
  " : " ++ prettyScheme sch ++ -- principal type
  case args of -- if exist, argument types
    [] -> ""
    args -> "\n" ++ intercalate ",\n" [ "    |     " ++ colour 92 ("x" ++ show i) ++
                                       " : " ++ prettyType t
                                     | (i, t) <- zip [0..] args ]

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
  show (CaseNonConstructor t) =
    "attempted case-analysis on non-datatype " ++ prettyType t
  show (TypeNotDefined name) =
    "undefined type '" ++ name ++ "'"

instance Show CompilerError where
  show (UndefinedVariable v) = "undeclared variable: " ++ v
  show FoundHole = "attempted to compile an incomplete expression containing a hole"
