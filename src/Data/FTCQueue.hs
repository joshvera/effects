{-# LANGUAGE GADTs #-}

{-|
Module      : Data.FTCQueue
Description : Fast type-aligned concatable queue optimized to effectful functions.
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX

* Constant-time (><) and (|>)
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
data FTCQueue m a b where
  Leaf :: (a -> m b) -> FTCQueue m a b
  Node :: FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b

-- | Build a leaf from a single operation [O(1)]
tsingleton :: (a -> m b) -> FTCQueue m a b
tsingleton = Leaf
{-# INLINE tsingleton #-}

-- | Append an operation to the right of the tree [O(1)]
(|>) :: FTCQueue m a x -> (x -> m b) -> FTCQueue m a b
t |> r = Node t (Leaf r)
{-# INLINE (|>) #-}

-- | Append two trees of operations [O(1)]
(><)   :: FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b
t1 >< t2 = Node t1 t2
{-# INLINE (><) #-}

-- | Left view deconstruction data structure
data ViewL m a b where
  TOne  :: (a -> m b) -> ViewL m a b
  (:<)  :: (a -> m x) -> FTCQueue m x b -> ViewL m a b

-- | Left view deconstruction [average O(1)]
tviewl :: FTCQueue m a b -> ViewL m a b
tviewl (Leaf r) = TOne r
tviewl (Node t1 t2) = go t1 t2
 where
   go :: FTCQueue m a x -> FTCQueue m x b -> ViewL m a b
   go (Leaf r) tr = r :< tr
   go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)
