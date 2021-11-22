module Main (main) where

import Test.QuickCheck
import Test.Hspec

import qualified Named as N
import DeBruijn
import Env

freeVars = [ [v] | v <- ['A'..] ]

instance Arbitrary Term where
  arbitrary = sized (f 0)
    where letters = [ [v] | v <- ['a'..'z'] ]
          f m 0 = Var <$> choose (0, m)
          f m n | n > 10 = f m 10
                | otherwise = oneof [ Var <$> choose (0, m)
                                    , Abs (letters !! m) <$> f (m + 1) (n - 1)
                                    , App <$> (f m (n - 1)) <*> (f m (n - 1)) ]

instance Arbitrary N.Term where
  arbitrary = do
    t <- arbitrary :: Gen Term
    return $ N.parseTerm1 (showTerm freeVars t)

main :: IO ()
main = hspec $ do
  describe "Named.parseTerm" $ do
    it "can parse abstractions" $ do
      N.parseTerm1 "λx.x" `shouldBe` N.Abs "x" (N.Var "x")
      N.parseTerm1 "λx.\\y.x y" `shouldBe` N.Abs "x" (N.Abs "y" (N.App (N.Var "x") (N.Var "y")))

    it "can parse applications" $ do
      N.parseTerm1 "x y z" `shouldBe` N.App (N.App (N.Var "x") (N.Var "y")) (N.Var "z")
      N.parseTerm1 "foo (bar eee)" `shouldBe` N.App (N.Var "foo") (N.App (N.Var "bar") (N.Var "eee"))

    it "can parse some mixed terms" $ do
      N.parseTerm1 "f (\\x.y) z" `shouldBe` N.App (N.App (N.Var "f") (N.Abs "x" (N.Var "y"))) (N.Var "z")
      N.parseTerm1 "(\\f.λx.f (f (f x))) z" `shouldBe` N.App (N.Abs "f" (N.Abs "x" (N.App (N.Var "f") (N.App (N.Var "f") (N.App (N.Var "f") (N.Var "x")))))) (N.Var "z")

    it "can ignore whitespace" $ do
      N.parseTerm1 " \\ x  .\n \\  \t y .x y  \n " `shouldBe` N.Abs "x" (N.Abs "y" (N.App (N.Var "x") (N.Var "y")))

  describe "DeBruijn.fromNamed" $ do
    it "showTerm . fromNamed . N.parseTerm1 =(ish) id" $ do
      property $ \t -> let (t', ns) = fromNamed (N.parseTerm1 (showTerm freeVars t))
                       in showTerm ns t' == showTerm freeVars t
                          
  describe "DeBruijn.shift" $ do
    it "shift 0 = id" $ do
      property $ \t -> shift 0 t == t

    it "not (hasFreeVariables t) => shift n t == t" $ do
      property $ \t n -> shift n (bindFree t) == bindFree t

    it "hasFreeVariables t, n > 0 => shift n t /= t" $ do
      property $ \t n -> if hasFreeVariables t && n > 0 then shift n t /= t
                         else True

  describe "DeBruijn.(-->)" $ do
    it "n >= 0 => (n --> Var n) == id" $ do
      property $ \t m -> let n = abs m in (n --> Var n) t == t

    it "substitutes into variables" $ do
      property $ \t -> (0 --> t) (Var 0) == t

    it "substitutes into abstractions properly" $ do
      property $ \t -> (0 --> t) (Abs "x" (Var 1)) == Abs "x" (shift 1 t)

    it "shift (-1) . unAbs . (0 --> t) . Abs \"x\" (Var 1) == t" $ do
      property $ \t -> shift (-1) (unAbs ((0 --> t) (Abs "x" (Var 1)))) == t

  describe "DeBruijn.eval" $ do
    it "works on some examples" $ do
      "(λx.x) y" `evalsTo` "y"
      "add (λf.λx.f (f x)) (λf.λx.f x) f x" `evalsTo` "f (f (f x))"
      "(λx.x y) y" `evalsTo` "y y"
      "(λx.λy.x y) y" `evalsTo` "λy.z y"
      "Y (λf.λn.(isZero n) (λf.λx.f x) (mul n (f (pred n)))) (λf.λx.f (f (f x))) f x" `evalsTo` "f(f(f(f(f(f x)))))"

hasFreeVariables :: Term -> Bool
hasFreeVariables = f 0
  where f ns (Var i) = i >= ns
        f ns (Abs _ t) = f (ns + 1) t
        f ns (App a b) = f ns a || f ns b

bindFree :: Term -> Term
bindFree t | hasFreeVariables t = bindFree (Abs "b" t)
           | otherwise = t

unAbs :: Term -> Term
unAbs (Abs _ t) = t

-- checks that one term evaluates to another, up to alpha-renaming
evalsTo :: String -> String -> Expectation
evalsTo from to = let (t1, _) = fromNamed (sub defaultEnv (N.parseTerm1 from))
                      (t2, _) = parseTerm1 to
                  in eval t1 `shouldBe` t2
