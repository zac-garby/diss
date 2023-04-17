module Pretty ( prettyExpr
              , prettyTerm
              , prettyTerm'
              , prettyType
              , prettyScheme
              , prettyTypes
              , prettyDataTypes
              , prettyFunction
              , prettyFunctionImg
              , prettyExample ) where

import qualified Graphics.Vty as V

import Data.List
import Data.Char
import Data.Maybe
import Graphics.Vty ((<|>), (<->))

import Compiler
import Types
import Holes
import Env
import Parser
import Infer
import Synthesis

-- a pretty-printer for expressions.
-- they will be outputted in a way which can be parsed back in.
prettyExpr :: Expr -> String
prettyExpr (Var i) = i
prettyExpr (App f x) = prettyExpr f ++ " " ++ bracketExpr x
prettyExpr (Abs x body) = "\\" ++ x ++ " -> " ++ prettyExpr body
prettyExpr (Let x val body) = "let " ++ x ++ " = " ++ prettyExpr val ++ " in " ++ prettyExpr body
prettyExpr (LetRec x val body) = "let rec " ++ x ++ " = " ++ prettyExpr val ++ " in " ++ prettyExpr body
prettyExpr (If cond t f) = "if " ++ prettyExpr cond ++ " then " ++ prettyExpr t ++ " else " ++ prettyExpr f
prettyExpr (Case cond cases) = "case " ++ prettyExpr cond ++ " of "
  ++ intercalate ", " [  unwords (x:xs) ++ " -> " ++ prettyExpr body | (x, xs, body) <- cases ]
prettyExpr (LitInt i) = show i
prettyExpr (LitList xs) = "[" ++ intercalate ", " (map prettyExpr xs) ++ "]"
prettyExpr (LitTuple xs) = "(" ++ intercalate ", " (map prettyExpr xs) ++ ")"
prettyExpr (LitChar c) = show c
prettyExpr (TypeSpec e ty) = bracketExpr e ++ " : " ++ prettyType ty
prettyExpr (Hole i) = "?"

bracketExpr :: Expr -> String
bracketExpr ex@(App f x) = "(" ++ prettyExpr ex ++ ")"
bracketExpr ex@(TypeSpec e t) = "(" ++ prettyExpr ex ++ ")"
bracketExpr ex@(Case cond cases) = "(" ++ prettyExpr ex ++ ")"
bracketExpr ex = prettyExpr ex

prettyExprImg :: Expr -> V.Image
prettyExprImg e = case e of
  Var i -> if isUpper (head i) then con i else white i
  App f x -> ex f <||> bracketExprImg x
  Abs x b -> kw "λ" <|> white x <||> kw "." <||> ex b
  Let x v b -> (kw "let" <||> white x) <-> (kw "in" <||> ex b)
  LetRec x v b -> (kw "let rec" <||> white x) <-> (kw "in" <||> ex b)
  If c t f -> V.vertCat [ kw "if" <||> ex c <||> kw "then"
                        ,   V.translateX 2 (ex t)
                        , kw "else"
                        ,   V.translateX 2 (ex f) ]
  Case c cases -> V.vertCat $ (kw "case" <||> ex c <||> kw "of")
                            : [ V.translateX 2 $ con constr
                                <|> if null args then
                                      white ""
                                    else
                                      space <|> V.horizCat (intersperse space (map white args))
                                <||> kw "→"
                                <||> ex body
                              | (constr, args, body) <- cases ]
  LitInt n -> lit (show n)
  LitList exs -> kw "[" <||> V.horizCat (intersperse (kw ", ") (map ex exs)) <||> kw "]"
  LitTuple exs -> kw "(" <||> V.horizCat (intersperse (kw ", ") (map ex exs)) <||> kw ")"
  LitChar c -> lit (show c)
  TypeSpec e t -> bracketExprImg e <||> kw ":" <||> white (prettyType t)
  Hole _ -> V.string (V.defAttr `V.withForeColor` V.black `V.withBackColor` V.brightRed) " ? " <|> white ""
  where white = V.string (V.defAttr `V.withForeColor` V.brightWhite)
        lit = V.string (V.defAttr `V.withForeColor` V.brightBlue)
        kw = V.string (V.defAttr `V.withForeColor` V.white `V.withStyle` V.bold)
        con = V.string (V.defAttr `V.withForeColor` V.brightGreen `V.withStyle` V.bold)
        space = white " "
        paren i = white "(" <|> i <|> white ")"
        a <||> b = a <|> space <|> b
        ex = prettyExprImg

        bracketExprImg e@(App f x) = paren (ex e)
        bracketExprImg e@(TypeSpec e' t) = paren (ex e)
        bracketExprImg e = ex e

-- a pretty-printer for terms.
-- if the term is not designed to be user-visible, Nothing is returned
prettyTerm :: Term -> Maybe String
prettyTerm (CInt i) = Just $ colour 32 (show i)
prettyTerm (CChar c) = Just $ colour 32 (show c)
prettyTerm c@(CCons (CChar _) _) = do
  cs <- clist2list c
  return $ colour 32 ("\"" ++ map (\(CChar c) -> c) cs ++ "\"")
prettyTerm c@(CCons h t) = do
  ts <- clist2list c
  strings <- mapM prettyTerm ts
  return $ "[" ++ intercalate ", " strings ++ "]"
prettyTerm (CConstr "Nil") = Just $ colour 32 "[]"
prettyTerm (CConstr c) = Just $ colour 32 c
prettyTerm (fn :$ arg) = do
  fn' <- prettyTerm fn
  arg' <- bracketTerm arg
  Just $ fn' ++ " " ++ arg'
prettyTerm CUnit = return "()"
prettyTerm (CPair x y) = do
  xs' <- mapM prettyTerm [x, y]
  return $ "(" ++ intercalate ", " xs' ++ ")"
prettyTerm _ = Nothing

prettyTerm' :: Term -> String
prettyTerm' t = fromMaybe (show t) (prettyTerm t)

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
prettyType (TyConstr c ts) = colour 32 c ++ " " ++ unwords (map bracketTypeApp ts)
prettyType (TyHole i) = colour 91 (show i ++ "?")

bracketType :: Type -> String
bracketType t@(TyConstr "->" _) = "(" ++ prettyType t ++ ")"
bracketType t = prettyType t

bracketTypeApp :: Type -> String
bracketTypeApp t@(TyConstr _ (_:_)) = "(" ++ prettyType t ++ ")"
bracketTypeApp t = bracketType t

prettyScheme :: Scheme -> String
prettyScheme (Forall [] t) = prettyType t
prettyScheme (Forall vs t) = colour 90 ("∀ " ++ unwords vs ++ " . ") ++ prettyType t

prettyTypes :: [(Ident, (Scheme, Term))] -> String
prettyTypes env = intercalate "\n" [ "  " ++ colour 33 (leftPad longestName (pprintIdent ops name)) ++
                                   " : " ++ prettyScheme sch
                                 | (name, (sch, _)) <- env ]
  where longestName = maximum (map (length . fst) env)

prettyFunction :: Ident -> Function -> String
prettyFunction name (Function args ret body egs) =
  name ++ " : " ++ intercalate " -> " (map prettyType (map snd args ++ [ret])) ++ "\n"
    ++ name ++ " " ++ unwords (map fst args) ++ " = " ++ prettyExpr body

prettyFunctionImg :: Ident -> Function -> V.Image
prettyFunctionImg name (Function args ret body egs) =
  V.vertCat [ green name <|> grey " : " <|> ty
            , green name <|> grey " = " <|> prettyExprImg body ]

  where white = V.string (V.defAttr `V.withForeColor` V.brightWhite)
        grey = V.string (V.defAttr `V.withForeColor` V.white)
        green = V.string (V.defAttr `V.withForeColor` V.brightGreen)
        ty = V.horizCat $ intersperse (grey " → ") (map (white . prettyType) (map snd args ++ [ret]))

prettyExample :: Example -> String
prettyExample (Eg args ret) = intercalate ", " (map prettyEgArg args) ++ " => " ++ show ret

prettyEgArg :: Arg -> String
prettyEgArg (Val v) = show v
prettyEgArg (Thunk t is) = "<" ++ show t ++ "|" ++ unwords is ++ ">"

prettyDataTypes :: [(Ident, DataType)] -> String
prettyDataTypes dts = intercalate "\n" $ do
  (name, DataType as cs) <- dts
  return $ colour 90 "data "
        ++ unwords (colour 32 name : map (prettyType . TyVar) as)
        ++ " = "
        ++ intercalate " | " (do
             DataConstructor c args <- cs
             return $ unwords (colour 32 c : map bracketTypeApp args))

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

prettyConstructor :: DataConstructor -> String
prettyConstructor (DataConstructor name args) = colour 32 name

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
  show (MissingCases cases) = show (length cases) ++ " missing cases: "
    ++ intercalate ", " (map prettyConstructor cases)
  show (UnknownConstructor con) = "undefined constructor: " ++ con
