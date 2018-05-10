{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
module Tests.State (
  testPutGet,
  testPutGetPutGetPlus,
  testGetStart
) where

import Control.Monad.Effect
import Control.Monad.Effect.State

testPutGet :: Int -> Int -> (Int,Int)
testPutGet n start = run @Eff (runState start go)
  where go = put n >> get

testPutGetPutGetPlus :: Int -> Int -> Int -> (Int,Int)
testPutGetPutGetPlus p1 p2 start = run @Eff (runState start go)
  where go = do
          put p1
          x <- get
          put p2
          y <- get
          return (x+y)

testGetStart :: Int -> (Int,Int)
testGetStart start = run @Eff (runState start get)
