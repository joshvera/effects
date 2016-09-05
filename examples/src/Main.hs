{-# LANGUAGE DataKinds #-}

module Main where

import Control.Monad.Effect
import Teletype

runner :: Eff '[Teletype] ()
runner = do
  x <- getLine'
  putStrLn' x
  y <- getLine'
  putStrLn' y

main :: IO ()
main = do
  let xs = Teletype.runPure ["cat", "fish"] runner
  print xs
  Teletype.run runner
