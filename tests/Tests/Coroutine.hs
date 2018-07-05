{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Tests.Coroutine (
  runTestCoroutine
) where

import Control.Monad
import Control.Monad.Effect
import Control.Monad.Effect.Coroutine
import Control.Monad.Effect.State

runTestCoroutine :: [Int] -> Int
runTestCoroutine list = fst . run $ runState 0 effTestCoroutine
  where
    testCoroutine :: (Member (Yield () Int) e, Member (State Int) e) => Eff e ()
    testCoroutine = do
      -- yield for two elements and hope they're both odd
      b <- (&&)
        <$> yield () (even :: Int -> Bool)
        <*> yield () (even :: Int -> Bool)
      unless b (modify ((+1) :: Int -> Int) >> testCoroutine)

    effTestCoroutine = do
      status <- runC testCoroutine
      handleStatus list status
        where
          handleStatus (i:is) (Continue () k) = k i >>= handleStatus is
          handleStatus _ _                    = pure ()
