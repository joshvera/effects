{-# LANGUAGE DataKinds, FlexibleContexts, GADTs, Rank2Types, TypeOperators #-}
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

data Resumable exc m a where
  Throw :: exc a                            -> Resumable exc m a
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
runResumable = raiseHandler (go Nothing)
  where go :: Effect (Union effects) => Maybe (Handler exc effects) -> Eff (Resumable exc ': effects) a -> Eff effects (Either (SomeExc exc) a)
        go _ (Return a)             = pure (Right a)
        go h (Effect (Throw e) k)   = maybe (pure (Left (SomeExc e))) (\ h' -> go h (runHandler h' e >>= k)) h
        go _ (Effect (Catch m h) k) = go (Just (Handler h)) (m >>= k)
        go h (Other r)              = fromRequest (handleState (Right ()) (either (pure . Left) (go h)) r)

newtype Handler exc effects = Handler { runHandler :: forall resume . exc resume -> Eff (Resumable exc ': effects) resume }

-- | Run a 'Resumable' effect in an 'Effectful' context, using a handler to resume computation.
runResumableWith :: (Effectful m, Effect (Union effects)) => (forall resume . exc resume -> m (Resumable exc ': effects) resume) -> m (Resumable exc ': effects) a -> m effects a
runResumableWith handler = raiseHandler (go (lowerEff . handler))
  where go :: Effect (Union effects) => (forall resume . exc resume -> Eff (Resumable exc ': effects) resume) -> Eff (Resumable exc ': effects) a -> Eff effects a
        go _ (Return a)             = pure a
        go h (Effect (Throw e) k)   = runResumableWith h (h e >>= k)
        go _ (Effect (Catch m h) k) = runResumableWith h (m >>= k)
        go h (Other r)              = fromRequest (handle (runResumableWith h) r)


data SomeExc exc where
  SomeExc :: exc v -> SomeExc exc

instance Eq1 exc => Eq (SomeExc exc) where
  SomeExc exc1 == SomeExc exc2 = liftEq (const (const True)) exc1 exc2

instance (Show1 exc) => Show (SomeExc exc) where
  showsPrec num (SomeExc exc) = liftShowsPrec (const (const id)) (const id) num exc
