{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
module Tests.Reader (
  testReader,
  testMultiReader,
  testLocal
) where

import Control.Monad.Effect
import Control.Monad.Effect.Reader

import Tests.Common

--------------------------------------------------------------------------------
                            -- Examples --
--------------------------------------------------------------------------------
testReader :: Int -> Int -> Int
testReader n x = run @Eff . runReader n $ ask `add` pure x

{-
t1rr' = run t1
    No instance for (Member (Reader Int) Void)
      arising from a use of `t1'
-}

testMultiReader :: Float -> Int -> Float
testMultiReader f n = run @Eff . runReader f . runReader n $ t2
  where t2 = do
          v1 <- ask
          v2 <- ask
          return $ fromIntegral (v1 + (1::Int)) + (v2 + (2::Float))

-- The opposite order of layers
{- If we mess up, we get an error
t2rrr1' = run $ runReader (10::Float) (runReader (20::Float) t2)
    No instance for (Member (Reader Int) [])
      arising from a use of `t2'
-}

testLocal :: Int -> Int -> Int
testLocal env inc = run @Eff $ runReader env t3
  where t3 = t1 `add` local (+ inc) t1
        t1 = ask `add` return (1 :: Int)
