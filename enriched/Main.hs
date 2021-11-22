module Main where

import qualified Named

import Env
import DeBruijn
import Control.Monad

main :: IO ()
main = forever $ do
  putStr "> "
  l <- getLine
  
  let t = do        
        nt <- sub defaultEnv <$> Named.parseTerm l
        return $ fromNamed nt
        
  case t of
    Just (t, ns) -> do
      putStrLn $ "you entered: " ++ showTerm ns t
      putStrLn $ "       (aka: " ++ show t ++ ")"
      let t' = eval t
      putStrLn $ " -> " ++ showTerm ns t'
    Nothing -> putStrLn "invalid syntax"
