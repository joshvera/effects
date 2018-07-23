{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds, KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

{-|
Module      : Control.Monad.Effect.Fresh
Description : Generation of fresh integers as an effect.
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : broken
Portability : POSIX

Composable handler for Fresh effects. This is likely to be of use when
implementing De Bruijn naming/scopes.

Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a
starting point.

-}
module Control.Monad.Effect.Fresh
( Fresh(..)
, fresh
, resetFresh
, runFresh
) where

import Control.Monad.Effect.Internal

--------------------------------------------------------------------------------
                             -- Fresh --
--------------------------------------------------------------------------------
-- | Fresh effect model
data Fresh (m :: * -> *) v where
  Fresh :: Fresh m Int
  Reset :: Int -> m a -> Fresh m a

-- | Request a fresh effect
fresh :: (Member Fresh e, Effectful m) => m e Int
fresh = send Fresh

resetFresh :: (Effectful m, Member Fresh effects) => Int -> m effects a -> m effects a
resetFresh i a = send (Reset i (lowerEff a))

-- | Handler for Fresh effects, with an Int for a starting value
runFresh :: (Effectful m, Effects e) => Int -> m (Fresh ': e) a -> m e a
runFresh i = raiseHandler (fmap snd . go i)
  where go :: Effects e => Int -> Eff (Fresh ': e) a -> Eff e (Int, a)
        go s (Return a)              = pure (s, a)
        go s (Effect Fresh k)        = go (succ s) (k s)
        go s (Effect (Reset s' a) k) = go s' a >>= go s . k . snd
        go s (Other u k)             = liftStatefulHandler (s, ()) (uncurry go) u k


instance PureEffect Fresh
instance Effect Fresh where
  handleState c dist (Request Fresh k) = Request Fresh (dist . (<$ c) . k)
  handleState c dist (Request (Reset i a) k) = Request (Reset i (dist (a <$ c))) (dist . fmap k)
