{-# LANGUAGE DataKinds #-}
module Tests.Union where

import Data.Functor.Identity
import Data.Union

testUnion :: Int -> Union '[Identity] Int
testUnion n = inj (Identity n)
