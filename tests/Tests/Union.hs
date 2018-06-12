{-# LANGUAGE DataKinds, KindSignatures #-}
module Tests.Union where

import Data.Functor.Identity
import Data.Union

newtype I (m :: * -> *) a = I { getI :: a }
newtype K s (m :: * -> *) a = K { getK :: s }

testUnaryUnion :: Int -> Union '[I] Identity Int
testUnaryUnion n = inj (I n)

testBinaryUnion0 :: Int -> Union '[I, K String] Identity Int
testBinaryUnion0 n = inj (I n)

testBinaryUnion1 :: String -> Union '[I, K String] Identity Int
testBinaryUnion1 s = inj (K s)
