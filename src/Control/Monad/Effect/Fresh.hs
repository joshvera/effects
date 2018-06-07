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

-- | Request a fresh effect
fresh :: (Member Fresh e, Effectful m) => m e Int
fresh = send Fresh

resetFresh :: (Effectful m, Member Fresh effects) => Int -> m effects a -> m effects a
resetFresh start = raiseHandler (interposeState start (const pure) (\ counter Fresh yield -> (yield $! succ counter) counter))

-- | Handler for Fresh effects, with an Int for a starting value
runFresh :: Effectful m => Int -> m (Fresh ': e) a -> m e a
runFresh s = raiseHandler (relayState s (const pure) (\s' Fresh k -> (k $! s'+1) s'))
