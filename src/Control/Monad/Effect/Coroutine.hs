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

raiseStatus :: Effectful m => Status Eff e a b w -> Status m e a b w
raiseStatus = status Done (\ a f -> Continue a (raiseEff . fmap raiseStatus . f))

status :: (w -> x) -> (a -> (b -> m e (Status m e a b w)) -> x) -> Status m e a b w -> x
status f _ (Done w) = f w
status _ g (Continue a f) = g a f

bindStatus :: Effect (Union effs) => Status Eff effs a b (Eff (Yield a b : effs) x) -> (x -> Eff (Yield a b : effs) y) -> Eff effs (Status Eff effs a b y)
bindStatus (Done w) yield' = runC (w >>= yield')
bindStatus (Continue a f) yield' = pure (Continue a (\ b -> f b >>= flip bindStatus yield'))

-- | Launch a thread and report its status
runC :: (Effectful m, Effect (Union effs)) => m (Yield a b ': effs) w -> m effs (Status m effs a b w)
runC = raiseHandler (fmap raiseStatus . go)
  where go (Return a)             = pure (Done a)
        go (Effect (Yield a f) k) = pure (Continue a (runC . k . f))
        go (Other u k)            = liftStatefulHandler (Done ()) (\act yield' -> act `bindStatus` yield') u k

-- | Launch a thread and run it to completion using a helper function to provide new inputs.
runCoro :: (Effectful m, Effect (Union effs)) => (a -> b) -> m (Yield a b ': effs) w -> m effs w
runCoro f = raiseHandler (loop <=< runC)
  where loop (Done a)       = pure a
        loop (Continue a k) = k (f a) >>= loop


instance Effect (Yield a bs) where
  handleState c dist (Yield a f) k = Request (Yield a f) (\result -> dist (pure result <$ c) k)
