{-# LANGUAGE FlexibleContexts, TypeOperators #-}
module Tests.NonDetEff where

import Control.Applicative
import Control.Monad
import Control.Monad.Freer
import Control.Monad.Freer.NonDetEff

ifte :: (NonDetEff :< effs)
     => Eff effs a
     -> (a -> Eff effs b)
     -> Eff effs b
     -> Eff effs b
ifte t th el = msplit t >>= maybe el (\(a,m) -> th a <|> (m >>= th))

generatePrimes :: (NonDetEff :< effs) => [Int] -> Eff effs Int
generatePrimes xs = do
  n <- gen
  ifte (do d <- gen
           guard $ d < n && n `mod` d == 0)
       (const mzero)
       (return n)
  where gen = msum (fmap return xs)

testIfte :: [Int] -> [Int]
testIfte = run . makeChoiceA . generatePrimes
