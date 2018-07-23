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

newtype Resumable exc (m :: * -> *) a = Resumable (exc a)

throwResumable :: (Member (Resumable exc) e, Effectful m) => exc v -> m e v
throwResumable = send . Resumable

runResumable :: (Effectful m, Effects e) => m (Resumable exc ': e) a -> m e (Either (SomeExc exc) a)
runResumable = raiseHandler go
  where go (Return a)           = pure (Right a)
        go (Effect (Resumable e) _) = pure (Left (SomeExc e))
        go (Other u k)          = liftStatefulHandler (Right ()) (either (pure . Left) runResumable) u k

-- | Run a 'Resumable' effect in an 'Effectful' context, using a handler to resume computation.
runResumableWith :: (Effectful m, PureEffects effects) => (forall resume . exc resume -> m effects resume) -> m (Resumable exc ': effects) a -> m effects a
runResumableWith handler = interpret (\ (Resumable e) -> handler e)


data SomeExc exc where
  SomeExc :: exc v -> SomeExc exc

instance Eq1 exc => Eq (SomeExc exc) where
  SomeExc exc1 == SomeExc exc2 = liftEq (const (const True)) exc1 exc2

instance (Show1 exc) => Show (SomeExc exc) where
  showsPrec num (SomeExc exc) = liftShowsPrec (const (const id)) (const id) num exc


instance PureEffect (Resumable exc)
instance Effect (Resumable exc) where
  handleState c dist (Request (Resumable exc) k) = Request (Resumable exc) (dist . (<$ c) . k)
