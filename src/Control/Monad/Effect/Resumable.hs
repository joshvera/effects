{-# LANGUAGE TypeOperators, TypeApplications, ScopedTypeVariables, GADTs, FlexibleContexts, DataKinds, Rank2Types #-}
module Control.Monad.Effect.Resumable
  ( Resumable(..)
  , SomeExc(..)
  , throwError
  , runError
  , resumeError
  , catchError
  ) where

import Data.Functor.Classes
import Control.Monad.Effect.Internal

data Resumable exc a where
  Resumable :: exc v -> Resumable exc v

throwError :: forall exc v e. Member (Resumable exc) e => exc v -> Eff e v
throwError e = send (Resumable e :: Resumable exc v)

runError :: Eff (Resumable exc ': e) a -> Eff e (Either (SomeExc exc) a)
runError = relay (pure . Right) (\ (Resumable e) _k -> pure (Left (SomeExc e)))

resumeError :: forall exc e a. Member (Resumable exc) e =>
       Eff e a -> (forall v. Arrow Eff e v a -> exc v -> Eff e a) -> Eff e a
resumeError m handle = interpose @(Resumable exc) pure (\(Resumable e) yield -> handle yield e) m

catchError :: forall exc e a. Member (Resumable exc) e => Eff e a -> (forall v. exc v -> Eff e a) -> Eff e a
catchError m handle = resumeError m (const handle)

data SomeExc exc where
  SomeExc :: exc v -> SomeExc exc

instance Eq1 exc => Eq (SomeExc exc) where
  SomeExc exc1 == SomeExc exc2 = liftEq (const (const True)) exc1 exc2

instance (Show1 exc) => Show (SomeExc exc) where
  showsPrec num (SomeExc exc) = liftShowsPrec (const (const id)) (const id) num exc
