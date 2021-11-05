module Env where

import Named

type Env = [(String, Term)]

sub :: Env -> Term -> Term
sub e (Var x) = case lookup x e of
  Just t' -> t'
  Nothing -> Var x
sub e (Abs name t) = Abs name (sub e t)
sub e (App f x) = App (sub e f) (sub e x)

defaultEnv :: Env
defaultEnv = [ (name, parseTerm1 t) |
               (name, t) <- [ ("id", "λx.x")
                            , ("Y", "λf.(λx.f (x x)) (λx.f (x x))")
                            , ("isZero", "λn.λz.λe.n (λf.e) z")
                            , ("add", "λm.λn.λf.λx.m f (n f x)")
                            , ("multiply", "λm.λn.λf.m (n f)")
                            , ("pred", "λn.λf.λx.n (λg.λh.h (g f)) (λu.x) (λu.u)")
                            , ("cons", "λa.λb.λf.f a b")
                            , ("head", "λc.c (λa.λb.a)")
                            , ("tail", "λc.c (λa.λb.b)") ]]
