{-# LANGUAGE GADTs, RankNTypes #-}

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
module Data.FTCQueue
( FTCQueue
, TANonEmptySequence(..)
, TANonEmptyViewL(..)
) where

import qualified Control.Category as Cat

-- |
-- Non-empty tree. Deconstruction operations make it more and more
-- left-leaning
data FTCQueue arrow a b where
  Leaf :: arrow a b -> FTCQueue arrow a b
  Node :: FTCQueue arrow a x -> FTCQueue arrow x b -> FTCQueue arrow a b

class TANonEmptySequence sequence where
  {-# MINIMAL tsingleton, (><), tviewl, tmap #-}
  -- | Build a leaf from a single operation [O(1)]
  tsingleton :: arrow x y -> sequence arrow x y

  -- | Append an operation to the right of the tree [O(1)]
  (|>) :: sequence arrow x y -> arrow y z -> sequence arrow x z
  as |> a = as >< tsingleton a

  -- | Append two trees of operations [O(1)]
  (><) :: sequence arrow x y -> sequence arrow y z -> sequence arrow x z

  -- | Left view deconstruction [average O(1)]
  tviewl :: sequence arrow x y -> TANonEmptyViewL sequence arrow x y

  -- | Map over leaf arrows [O(n)]
  tmap :: (forall x y. arrow x y -> arrow' x y) -> sequence arrow x y -> sequence arrow' x y

data TANonEmptyViewL s arrow a b where
  TOneL :: arrow a b -> TANonEmptyViewL s arrow a b
  (:<)  :: arrow a x -> s arrow x b -> TANonEmptyViewL s arrow a b

instance TANonEmptySequence FTCQueue where
  tsingleton = Leaf
  {-# INLINE tsingleton #-}

  t |> r = Node t (Leaf r)
  {-# INLINE (|>) #-}

  t1 >< t2 = Node t1 t2
  {-# INLINE (><) #-}

  tviewl (Leaf r) = TOneL r
  tviewl (Node t1 t2) = go t1 t2
    where
      go :: FTCQueue arrow a x -> FTCQueue arrow x b -> TANonEmptyViewL FTCQueue arrow a b
      go (Leaf r) tr = r :< tr
      go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)

  tmap f (Leaf r) = Leaf (f r)
  tmap f (Node l r) = Node (tmap f l) (tmap f r)


instance Cat.Category arrow => Cat.Category (FTCQueue arrow) where
  id = Leaf Cat.id
  (.) = flip (><)
