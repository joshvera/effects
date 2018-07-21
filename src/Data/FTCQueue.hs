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
  ViewL(..),
  tviewl
) where

-- |
-- Non-empty tree. Deconstruction operations make it more and more
-- left-leaning
data FTCQueue arrow a b where
  Leaf :: arrow a b -> FTCQueue arrow a b
  Node :: FTCQueue arrow a x -> FTCQueue arrow x b -> FTCQueue arrow a b

-- | Build a leaf from a single operation [O(1)]
tsingleton :: arrow a b -> FTCQueue arrow a b
tsingleton = Leaf
{-# INLINE tsingleton #-}

-- | Append an operation to the right of the tree [O(1)]
(|>) :: FTCQueue arrow a x -> arrow x b -> FTCQueue arrow a b
t |> r = Node t (Leaf r)
{-# INLINE (|>) #-}

-- | Append two trees of operations [O(1)]
(><)   :: FTCQueue arrow a x -> FTCQueue arrow x b -> FTCQueue arrow a b
t1 >< t2 = Node t1 t2
{-# INLINE (><) #-}

-- | Left view deconstruction data structure
data ViewL arrow a b where
  TOne  :: arrow a b -> ViewL arrow a b
  (:<)  :: arrow a x -> FTCQueue arrow x b -> ViewL arrow a b

-- | Left view deconstruction [average O(1)]
tviewl :: FTCQueue arrow a b -> ViewL arrow a b
tviewl (Leaf r) = TOne r
tviewl (Node t1 t2) = go t1 t2
 where
   go :: FTCQueue arrow a x -> FTCQueue arrow x b -> ViewL arrow a b
   go (Leaf r) tr = r :< tr
   go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)
