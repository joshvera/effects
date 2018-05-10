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
, TANonEmptyViewR(..)
) where

import qualified Control.Category as Cat

-- |
-- Non-empty tree. Deconstruction operations make it more and more
-- left-leaning
data FTCQueue arrow a b where
  Leaf :: arrow a b -> FTCQueue arrow a b
  Node :: FTCQueue arrow a x -> FTCQueue arrow x b -> FTCQueue arrow a b

class TANonEmptySequence sequence where
  {-# MINIMAL tsingleton, ((><) | (<|) | (|>)), (tviewl | tviewr), tmap #-}
  -- | Build a leaf from a single operation
  tsingleton :: arrow x y -> sequence arrow x y

  -- | Append an operation to the right of the tree
  (|>) :: sequence arrow x y -> arrow y z -> sequence arrow x z
  as |> a = as >< tsingleton a

  -- | Append an operation to the left of the tree
  (<|) :: arrow x y -> sequence arrow y z -> sequence arrow x z
  a <| as = tsingleton a >< as

  -- | Append two trees of operations
  (><) :: sequence arrow x y -> sequence arrow y z -> sequence arrow x z
  l >< r = case tviewl l of
    TOneL x -> x <| r
    h :< t  -> h <| (t >< r)

  -- | Left view deconstruction
  tviewl :: sequence arrow x y -> TANonEmptyViewL sequence arrow x y
  tviewl q = case tviewr q of
    TOneR x -> TOneL x
    p :> l  -> case tviewl p of
        TOneL x -> x :< tsingleton l
        h :< t  -> h :< (t |> l)

  -- | Right view deconstruction
  tviewr :: sequence arrow x y -> TANonEmptyViewR sequence arrow x y
  tviewr q = case tviewl q of
    TOneL x -> TOneR x
    h :< t  -> case tviewr t of
        TOneR x -> tsingleton h :> x
        p :> l  -> (h <| p)     :> l

  -- | Map over leaf arrows
  tmap :: (forall x y. arrow x y -> arrow' x y) -> sequence arrow x y -> sequence arrow' x y

data TANonEmptyViewL s arrow a b where
  TOneL :: arrow a b -> TANonEmptyViewL s arrow a b
  (:<)  :: arrow a x -> s arrow x b -> TANonEmptyViewL s arrow a b

data TANonEmptyViewR s arrow a b where
  TOneR :: arrow a b                -> TANonEmptyViewR s arrow a b
  (:>)  :: s arrow a x -> arrow x b -> TANonEmptyViewR s arrow a b

instance TANonEmptySequence FTCQueue where
  -- O(1)
  tsingleton = Leaf
  {-# INLINE tsingleton #-}

  -- O(1)
  t |> r = Node t (Leaf r)
  {-# INLINE (|>) #-}

  -- O(1)
  t1 >< t2 = Node t1 t2
  {-# INLINE (><) #-}

  -- average O(1)
  tviewl (Leaf r) = TOneL r
  tviewl (Node t1 t2) = go t1 t2
    where
      go :: FTCQueue arrow a x -> FTCQueue arrow x b -> TANonEmptyViewL FTCQueue arrow a b
      go (Leaf r) tr = r :< tr
      go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)

  -- O(n)
  tmap f (Leaf r) = Leaf (f r)
  tmap f (Node l r) = Node (tmap f l) (tmap f r)


instance Cat.Category arrow => Cat.Category (FTCQueue arrow) where
  id = Leaf Cat.id
  (.) = flip (><)
