{-# LANGUAGE DataKinds #-}
module Tests.Union where

import Data.Functor.Identity
import Data.Union

testUnaryUnion :: Int -> Union '[Identity] Int
testUnaryUnion n = inj (Identity n)
