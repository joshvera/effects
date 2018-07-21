{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds, KindSignatures #-}

{-|
Module      : Control.Monad.Effect.Writer
Description : Composable Writer effects
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX

Writer effects, for writing changes to an attached environment.

Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a
starting point.

-}
module Control.Monad.Effect.Writer (
  Writer(..),
  tell,
  runWriter
) where

import Control.Monad.Effect.Internal

-- | Writer effects - send outputs to an effect environment
data Writer o (m :: * -> *) x where
  Writer :: o -> Writer o m ()

-- | Send a change to the attached environment
tell :: (Member (Writer o) e, Effectful m) => o -> m e ()
tell = send . Writer

-- | Simple handler for Writer effects
runWriter :: (Monoid o, Effectful m, Effects e) => m (Writer o ': e) a -> m e (o, a)
runWriter = raiseHandler (go mempty)
  where go :: (Monoid o, Effects e) => o -> Eff (Writer o ': e) a -> Eff e (o, a)
        go w (Return a)            = pure (w, a)
        go w (Effect (Writer o) k) = go (w `mappend` o) (k ())
        go w (Other u k)           = liftStatefulHandler (w, ()) (uncurry go) u k


instance PureEffect (Writer o)
instance Effect (Writer o) where
  handleState c dist (Request (Writer o) k) = Request (Writer o) (dist . (<$ c) . k)
