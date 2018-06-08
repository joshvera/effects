{-# LANGUAGE DataKinds, FlexibleContexts, GADTs, KindSignatures, Rank2Types, TypeApplications, TypeOperators #-}
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

data Resumable exc (m :: * -> *) a where
  Throw :: exc a                 -> Resumable exc m a
  Catch :: m a -> (forall b . exc b -> m b) -> Resumable exc m a

throwResumable :: (Member (Resumable exc) e, Effectful m) => exc v -> m e v
throwResumable = send . Throw

catchResumable :: (Member (Resumable exc) e, Effectful m)
               => m e a
               -> (forall v. exc v -> m e v)
               -> m e a
catchResumable m handler = send (Catch (lowerEff m) (lowerEff . handler))

handleResumable :: (Member (Resumable exc) e, Effectful m)
                => (forall v. exc v -> m e v)
                -> m e a
                -> m e a
handleResumable handler m = catchResumable m handler


runResumable :: (Effectful m, Effect (Union e)) => m (Resumable exc ': e) a -> m e (Either (SomeExc exc) a)
-- runResumable = raiseHandler (relay (pure . Right) (\ (Resumable e) _ -> pure (Left (SomeExc e))))
runResumable = raiseHandler go
  where go (Return a)           = pure (Right a)
        go (Effect (Throw e) _) = pure (Left (SomeExc e))
        go (Other r)            = fromRequest (handleState (Right ()) (either (pure . Left) runResumable) r)

-- | Run a 'Resumable' effect in an 'Effectful' context, using a handler to resume computation.
runResumableWith :: (Effectful m, Effect (Union effects)) => (forall resume . exc resume -> m (Resumable exc ': effects) resume) -> m (Resumable exc ': effects) a -> m effects a
runResumableWith handler = raiseHandler go
  where go (Return a)             = pure a
        go (Effect (Throw e) k)   = runResumableWith (lowerEff . handler) (lowerEff (handler e) >>= k)
        go (Effect (Catch m _) k) = runResumableWith (lowerEff . handler) (m >>= k)
        go (Other r)              = fromRequest (handle (runResumableWith (lowerEff . handler)) r)


data SomeExc exc where
  SomeExc :: exc v -> SomeExc exc

instance Eq1 exc => Eq (SomeExc exc) where
  SomeExc exc1 == SomeExc exc2 = liftEq (const (const True)) exc1 exc2

instance (Show1 exc) => Show (SomeExc exc) where
  showsPrec num (SomeExc exc) = liftShowsPrec (const (const id)) (const id) num exc
