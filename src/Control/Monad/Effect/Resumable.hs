{-# LANGUAGE DataKinds, FlexibleContexts, GADTs, LambdaCase, KindSignatures, Rank2Types, TypeOperators #-}
module Control.Monad.Effect.Resumable
  ( Resumable(..)
  , SomeExc(..)
  , throwResumable
  , runResumable
  , runResumableWith
  ) where

import Control.Monad.Effect.Internal
import Data.Functor.Classes

data Resumable exc (m :: * -> *) a where
  Throw :: exc a -> Resumable exc m a

throwResumable :: (Member (Resumable exc) e, Effectful m) => exc v -> m e v
throwResumable = send . Throw

runResumable :: (Effectful m, Effect (Union e)) => m (Resumable exc ': e) a -> m e (Either (SomeExc exc) a)
runResumable = raiseHandler go
  where go (Return a)           = pure (Right a)
        go (Effect (Throw e) _) = pure (Left (SomeExc e))
        go (Other u k)          = liftStatefulHandler (Right ()) (either (pure . Left) runResumable) u k

-- | Run a 'Resumable' effect in an 'Effectful' context, using a handler to resume computation.
runResumableWith :: (Effectful m, Effect (Union effects)) => (forall resume . exc resume -> m effects resume) -> m (Resumable exc ': effects) a -> m effects a
runResumableWith handler = interpret (\ (Throw e) -> handler e)


data SomeExc exc where
  SomeExc :: exc v -> SomeExc exc

instance Eq1 exc => Eq (SomeExc exc) where
  SomeExc exc1 == SomeExc exc2 = liftEq (const (const True)) exc1 exc2

instance (Show1 exc) => Show (SomeExc exc) where
  showsPrec num (SomeExc exc) = liftShowsPrec (const (const id)) (const id) num exc


instance Effect (Resumable exc) where
  handleState c dist (Request (Throw exc) k) = Request (Throw exc) (dist . (<$ c) . k)
