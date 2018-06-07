{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds, KindSignatures, PatternSynonyms, ViewPatterns #-}

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
runWriter :: (Monoid o, Effectful m, Effect (Union e)) => m (Writer o ': e) a -> m e (o, a)
runWriter = raiseHandler (go mempty)
  where go :: (Monoid o, Effect (Union e)) => o -> Eff (Writer o ': e) a -> Eff e (o, a)
        go w (Return a) = pure (w, a)
        go w (Tell o k) = go (w `mappend` o) (k ())
        go w (Other r)  = fromRequest (handle (w, ()) (uncurry go) r)

pattern Tell o k <- (decomposeEff -> Right (Right (Request (Writer o) k)))
