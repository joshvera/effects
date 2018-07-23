{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

{-|
Module      : Control.Monad.Effect.StateRW
Description : State effects in terms of Reader/Writer
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX

Composable handler for State effects in terms of Reader/Writer
effects. This module is more a tutorial on how to compose handlers. It
is slightly slower than a dedicated State handler.

Using <http://okmij.org/ftp/Haskell/extensible/Eff1.hs> as a
starting point.

-}
module Control.Monad.Effect.StateRW (
  runStateR,
  Reader(..),
  Writer(..),
  tell,
  ask
) where

import Control.Monad.Effect.Reader
import Control.Monad.Effect.Writer
import Control.Monad.Effect.Internal

-- | State handler, using Reader/Writer effects
runStateR :: (Effectful m, Effects e) => s -> m (Writer s ': Reader s ': e) a -> m e (s, a)
runStateR = raiseHandler . go
  where go :: Effects e => s -> Eff (Writer s ': Reader s ': e) a -> Eff e (s, a)
        go s (Return a)                = pure (s, a)
        go _ (Effect2_1 (Writer s) k)  = go s (k ())
        go s (Effect2_2 Reader k)      = go s (k s)
        go s (Effect2_2 (Local f m) k) = go (f s) (m >>= k)
        go s (Other2 u k)              = liftStatefulHandler (s, ()) (uncurry runStateR) u k
