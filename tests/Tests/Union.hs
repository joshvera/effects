{-# LANGUAGE DataKinds #-}
module Tests.Union where

import Data.Functor.Const
import Data.Functor.Identity
import Data.Union

testUnaryUnion :: Int -> Union '[Identity] Int
testUnaryUnion n = inj (Identity n)

testBinaryUnion0 :: Int -> Union '[Identity, Const String] Int
testBinaryUnion0 n = inj (Identity n)

testBinaryUnion1 :: String -> Union '[Identity, Const String] Int
testBinaryUnion1 s = inj (Const s)
