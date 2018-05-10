{-# LANGUAGE FlexibleContexts, TypeOperators #-}
module Tests.NonDet where

import Control.Applicative
import Control.Monad
import Control.Monad.Effect
import Control.Monad.Effect.NonDet

ifte :: Member NonDet e
     => Eff e a
     -> (a -> Eff e b)
     -> Eff e b
     -> Eff e b
ifte t th el = msplit t >>= maybe el (\(a,m) -> th a <|> (m >>= th))

generatePrimes :: Member NonDet e => [Int] -> Eff e Int
generatePrimes xs = do
  n <- gen
  ifte (do d <- gen
           guard $ d < n && n `mod` d == 0)
       (const mzero)
       (pure n)
  where gen = msum (fmap pure xs)

testIfte :: [Int] -> [Int]
testIfte = run . runNonDetA . generatePrimes
