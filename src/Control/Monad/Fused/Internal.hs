{-# LANGUAGE EmptyCase, RankNTypes, UndecidableInstances, FlexibleContexts, TypeOperators, MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies #-} -- to enable 'forall' keyword
module Control.Monad.Fused.Internal ((\/), runFree, conState, Codensity(..), TermAlgebra(..), Void, Free) where

import Control.Monad
import Control.Monad.State.Class
import GHC.Generics

class Functor f => TermAlgebra h f | h -> f where
  var :: a -> h a
  con :: f (h a) -> h a

data Free f a = Var a | Con (f (Free f a))

instance Functor f => Monad (Free f) where
  return = pure
  {-# INLINE return #-}
  Var a >>= f = f a
  Con m >>= f = Con ((>>= f) <$> m)
  {-# INLINE (>>=) #-}

instance Functor f => Applicative (Free f) where
  pure = Var
  {-# INLINE pure #-}
  Var a <*> Var b = Var $ a b
  Var a <*> Con mb = Con $ fmap a <$> mb
  Con ma <*> b = Con $ (<*> b) <$> ma
  {-# INLINE (<*>) #-}

instance Functor f => Functor (Free f) where
  fmap f = go where
    go (Var a)  = Var (f a)
    go (Con fa) = Con (go <$> fa)
  {-# INLINE fmap #-}

instance Functor f => TermAlgebra (Free f) f where
  var = Var
  {-# INLINE var #-}
  con = Con
  {-# INLINE con #-}

data Void a
instance Functor Void where
  fmap f a = case a of {}
  {-# INLINE fmap #-}

runFree :: Free Void a -> a
runFree = fold undefined id

fold alg gen (Var x) = gen x
fold alg gen (Con op) = alg (fmap (fold alg gen) op)

conState :: (Functor g, TermAlgebra m g) => g (s -> m a) -> (s -> m a)
conState op s = con (fmap (\m -> m s) op)

(\/) :: (f b -> b) -> (g b -> b) -> ((f :+: g) b -> b)
(\/) algF algG (L1 s) = algF s
(\/) algF algG (R1 s) = algG s

instance TermAlgebra h f => TermAlgebra (Codensity h) f where
  var = return
  {-# INLINE var #-}
  con = alg_cod con
  {-# INLINE con #-}

alg_cod :: Functor f => (forall x. f (h x) -> h x) -> (f (Codensity h a) -> Codensity h a)
alg_cod alg = \op -> Codensity (\k -> alg (fmap (flip runCodensity k) op))

-- Could as well use Control.Monad.Copdensity from kan-extensions, except
-- that it has instances that overlap with the one for MonadState above.

newtype Codensity f a = Codensity {
  runCodensity :: forall b. (a -> f b) -> f b
}

instance Functor (Codensity f) where
  fmap f m = Codensity (\k -> runCodensity m (k. f))

instance Applicative (Codensity f) where
  pure = return
  (<*>) = ap

instance Monad (Codensity f) where
  return a = Codensity (\k -> k a)
  c >>= f  = Codensity (\k -> runCodensity c (\a -> runCodensity (f a) k))
