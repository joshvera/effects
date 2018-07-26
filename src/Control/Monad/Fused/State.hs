{-# LANGUAGE EmptyCase, RankNTypes, GADTs, UndecidableInstances, FlexibleContexts, TypeOperators, MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies #-} -- to enable 'forall' keyword
module Control.Monad.Fused.State where

import Control.Monad.Fused.Internal
import Control.Monad.State.Class
import GHC.Generics

run' :: Codensity (StateCarrier Int (Free Void)) a -> Int -> a
run' = fmap runFree . run

run :: (Monad m, TermAlgebra m f) => Codensity (StateCarrier s m) a -> s -> m a
run = unSC . flip runCodensity var

data State s a where
  Get :: (s -> a) -> State s a
  Put :: s -> a -> State s a

getState :: TermAlgebra f (State s :+: g) => Codensity f s
getState = con (L1 (Get pure))

putState :: TermAlgebra f (State s :+: g) => s -> Codensity f ()
putState s = con (L1 (Put s (pure ())))

genState :: (Monad m, TermAlgebra m f) => a -> (s -> m a)
genState x = const (var x)

algState :: (Monad m, TermAlgebra m f) => State s (s -> m a) -> (s -> m a)
algState (Put s k) _ = k s
algState (Get k) s = k s s

instance Functor (State s) where
  fmap f (Get k) = (Get (f . k))
  fmap f (Put s a) = (Put s (f a))
  {-# INLINE fmap #-}

newtype StateCarrier s m a = SC { unSC :: s -> m a }

instance (Monad m, TermAlgebra m f) => TermAlgebra (StateCarrier s m) (State s :+: f) where
  con = SC . (algState \/ conState) . fmap unSC
  {-# INLINE con #-}
  var = SC . genState
  {-# INLINE var #-}

instance TermAlgebra f (State s :+: g) => MonadState s (Codensity f) where
  get = getState
  put s = putState s

