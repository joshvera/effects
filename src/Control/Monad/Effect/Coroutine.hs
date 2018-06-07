{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

{-|
Module      : Control.Monad.Effect.Coroutine
Description : Composable Coroutine effects
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : broken
Portability : POSIX

An effect to compose functions with the ability to yield.

Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a
starting point.

-}
module Control.Monad.Effect.Coroutine (
  Yield(..),
  yield,
  Status(..),
  runC,
  runCoro
) where

import Control.Monad ((<=<))
import Control.Monad.Effect.Internal

-- | A type representing a yielding of control
-- a: The current type
-- b: The input to the continuation function
-- v: The output of the continuation
data Yield a b (m :: * -> *) v = Yield a (b -> v)
    deriving (Functor)

-- | Lifts a value and a function into the Coroutine effect
yield :: (Member (Yield a b) e, Effectful m) => a -> (b -> c) -> m e c
yield x f = send (Yield x f)

-- |
-- Status of a thread: done or reporting the value of the type a and
-- resuming with the value of type b
data Status m (e :: [(* -> *) -> (* -> *)]) a b w = Done w | Continue a (b -> m e (Status m e a b w))
  deriving (Functor)

-- | Launch a thread and report its status
runC :: Effectful m => m (Yield a b ': e) w -> m e (Status m e a b w)
runC = relay (raiseEff . pure . Done) (\ (Yield a k) arr -> raiseEff (pure (Continue a (arr . k))))

-- | Launch a thread and run it to completion using a helper function to provide new inputs.
runCoro :: Effectful m => (a -> b) -> m (Yield a b ': e) w -> m e w
runCoro f = raiseHandler (loop <=< runC)
  where loop (Done a)       = pure a
        loop (Continue a k) = k (f a) >>= loop
