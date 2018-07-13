{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
module Tests.StateRW (
  testPutGetRW,
  testPutGetPutGetPlusRW,
  testGetStartRW
) where

import Control.Monad.Effect
import Control.Monad.Effect.StateRW

testPutGetRW :: Int -> Int -> (Int,Int)
testPutGetRW n start = run @Eff (runStateR start go)
  where go = tell n >> ask

testPutGetPutGetPlusRW :: Int -> Int -> Int -> (Int,Int)
testPutGetPutGetPlusRW p1 p2 start = run @Eff (runStateR start go)
  where go = do
          tell p1
          x <- ask
          tell p2
          y <- ask
          return (x+y)

testGetStartRW :: Int -> (Int,Int)
testGetStartRW start = run @Eff (runStateR start go)
  where go = ask
