{-# LANGUAGE FlexibleContexts #-}
module Tests.Fresh where

import Control.Monad
import Control.Monad.Effect
import Control.Monad.Effect.Fresh

makeFresh :: Effects r => Int -> Eff r Int
makeFresh n = runFresh 0 (liftM last (replicateM n fresh))

testFresh :: Int -> Int
testFresh = run . makeFresh
