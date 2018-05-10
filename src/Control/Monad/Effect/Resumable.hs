{-# LANGUAGE TypeOperators, TypeApplications, ScopedTypeVariables, GADTs, FlexibleContexts, DataKinds, Rank2Types #-}
module Control.Monad.Effect.Resumable
  ( Resumable(..)
  , SomeExc(..)
  , throwResumable
  , runResumable
  , resumeError
  , catchError
  ) where

import Data.Functor.Classes
import Control.Monad.Effect.Internal

data Resumable exc a = Resumable (exc a)

throwResumable :: (Member (Resumable exc) e, Effectful m) => exc v -> m e v
throwResumable = send . Resumable

runResumable :: Effectful m => m (Resumable exc ': e) a -> m e (Either (SomeExc exc) a)
runResumable = raiseHandler (relay (pure . Right) (\ (Resumable e) _ -> pure (Left (SomeExc e))))

resumeError :: forall exc e a. Member (Resumable exc) e =>
       Eff e a -> (forall v. Arrow Eff e v a -> exc v -> Eff e a) -> Eff e a
resumeError m handle = interpose @(Resumable exc) pure (\(Resumable e) yield -> handle yield e) m

catchError :: Member (Resumable exc) e => Eff e a -> (forall v. exc v -> Eff e a) -> Eff e a
catchError m handle = resumeError m (const handle)

data SomeExc exc where
  SomeExc :: exc v -> SomeExc exc

instance Eq1 exc => Eq (SomeExc exc) where
  SomeExc exc1 == SomeExc exc2 = liftEq (const (const True)) exc1 exc2

instance (Show1 exc) => Show (SomeExc exc) where
  showsPrec num (SomeExc exc) = liftShowsPrec (const (const id)) (const id) num exc
