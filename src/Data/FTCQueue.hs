{-# LANGUAGE GADTs #-}

{-|
Module      : Data.FTCQueue
Description : Fast type-aligned concatable queue optimized to effectful functions.
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX

* Constant-time append/(><) and snoc/(|>)
* Average constant-time viewL (left-edge deconstruction)

Using <http://okmij.org/ftp/Haskell/extensible/FTCQueue1.hs> as a
starting point.

A minimal version of FTCQueue from "Reflection w/o Remorse":

* research: http://okmij.org/ftp/Haskell/Reflection.html
* type-aligned(FTCQueue): https://hackage.haskell.org/package/type-aligned

-}
module Data.FTCQueue (
  FTCQueue,
  tsingleton,
  (|>),
  (><),
  TAViewL(..),
  tviewl
) where

import Data.TASequence

-- |
-- Non-empty tree. Deconstruction operations make it more and more
-- left-leaning
data FTCQueue arrow a b where
  Empty :: FTCQueue arrow a a
  Leaf :: arrow a b -> FTCQueue arrow a b
  Node :: FTCQueue arrow a x -> FTCQueue arrow x b -> FTCQueue arrow a b

instance TASequence FTCQueue where
  tempty = Empty
  {-# INLINE tempty #-}

  tsingleton = Leaf
  {-# INLINE tsingleton #-}

  t |> r = Node t (Leaf r)
  {-# INLINE (|>) #-}

  t1 >< t2 = Node t1 t2
  {-# INLINE (><) #-}

  tviewl Empty = TAEmptyL
  tviewl (Leaf r) = r :< Empty
  tviewl (Node t1 t2) = go t1 t2
   where
     go :: FTCQueue arrow a x -> FTCQueue arrow x b -> TAViewL FTCQueue arrow a b
     go Empty tr = tviewl tr
     go (Leaf r) tr = r :< tr
     go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)
