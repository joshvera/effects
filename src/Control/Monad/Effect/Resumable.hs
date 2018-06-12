{-# LANGUAGE DataKinds, FlexibleContexts, GADTs, KindSignatures, Rank2Types, TypeOperators #-}
module Control.Monad.Effect.Resumable
  ( Resumable(..)
  , SomeExc(..)
  , throwResumable
  , catchResumable
  , handleResumable
  , runResumable
  , runResumableWith
  ) where

import Control.Monad.Effect.Internal
import Data.Functor.Classes

data Resumable exc (m :: * -> *) a = Resumable (exc a)

throwResumable :: (Member (Resumable exc) e, Effectful m) => exc v -> m e v
throwResumable = send . Resumable

catchResumable :: (Member (Resumable exc) e, Effectful m)
               => m e a
               -> (forall v. exc v -> m e v)
               -> m e a
catchResumable m handler = handleResumable handler m

handleResumable :: (Member (Resumable exc) e, Effectful m)
                => (forall v. exc v -> m e v)
                -> m e a
                -> m e a
handleResumable handler = raiseHandler (interpose pure (\(Resumable e) yield -> lowerEff (handler e) >>= yield))


runResumable :: (Effectful m, Effect (Union e)) => m (Resumable exc ': e) a -> m e (Either (SomeExc exc) a)
runResumable = raiseHandler go
  where go (Return a)               = pure (Right a)
        go (Effect (Resumable e) _) = pure (Left (SomeExc e))
        go (Other u k)              = handleStateful (Right ()) (either (pure . Left) runResumable) u k

-- | Run a 'Resumable' effect in an 'Effectful' context, using a handler to resume computation.
runResumableWith :: (Effectful m, Effect (Union effects)) => (forall resume . exc resume -> m (Resumable exc ': effects) resume) -> m (Resumable exc ': effects) a -> m effects a
runResumableWith handler = go . lowerEff
  where go (Return a)               = raiseEff (pure a)
        go (Effect (Resumable e) k) = runResumableWith handler (raiseEff (lowerEff (handler e) >>= k))
        go (Other u k)              = handle (runResumableWith handler) u (raiseEff . k)


data SomeExc exc where
  SomeExc :: exc v -> SomeExc exc

instance Eq1 exc => Eq (SomeExc exc) where
  SomeExc exc1 == SomeExc exc2 = liftEq (const (const True)) exc1 exc2

instance (Show1 exc) => Show (SomeExc exc) where
  showsPrec num (SomeExc exc) = liftShowsPrec (const (const id)) (const id) num exc
