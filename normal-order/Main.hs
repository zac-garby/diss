module Main where

import qualified Named

import Env
import DeBruijn
import Control.Monad
import System.IO

main :: IO ()
main = forever $ do
  putStr "> "
  hFlush stdout
  l <- getLine
  
  let term = fromNamed . sub defaultEnv <$> Named.parseTerm l
  
  case term of
    Just (t, ns) -> do
      putStrLn $ "you entered: " ++ showTerm ns t
      putStrLn $ "       (aka: " ++ show t ++ ")"
      let t' = eval t
      putStrLn $ " -> " ++ showTerm ns t'
    Nothing -> putStrLn "invalid syntax"
