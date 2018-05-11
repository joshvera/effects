{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
module Trace where

import Control.Monad.Effect
import Control.Monad.Effect.Reader
import Control.Monad.Effect.Trace

import Common

-- Higher-order effectful function
-- The inferred type shows that the Trace affect is added to the effects
-- of r
mapMdebug:: (Show a, Member Trace r) =>
     (a -> Eff r b) -> [a] -> Eff r [b]
mapMdebug _ [] = return []
mapMdebug f (h:t) = do
  trace $ "mapMdebug: " ++ show h
  h' <- f h
  t' <- mapMdebug f t
  return (h':t')

tMd :: IO [Int]
tMd = runM @Eff . runPrintingTrace $ runReader (10::Int) (mapMdebug f [1..5])
 where f x = ask `add` return x
{-
mapMdebug: 1
mapMdebug: 2
mapMdebug: 3
mapMdebug: 4
mapMdebug: 5
[11,12,13,14,15]
-}

-- duplicate layers
tdup :: IO ()
tdup = runM @Eff . runPrintingTrace $ runReader (10::Int) m
 where
 m = do
     runReader (20::Int) tr
     tr
 tr = do
      v <- ask
      trace $ "Asked: " ++ show (v::Int)
{-
Asked: 20
Asked: 10
-}
