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
runStateR :: Effectful m => m (Writer s ': Reader s ': e) a -> s -> m e (a, s)
runStateR m s = raiseHandler (loop s) m
 where
   loop :: s -> Eff (Writer s ': Reader s ': e) a -> Eff e (a, s)
   loop s' (Val x) = pure (x,s')
   loop s' (E u q) = case decompose u of
     Right (Writer o) -> k o ()
     Left  u'  -> case decompose u' of
       Right Reader -> k s' s'
       Left u'' -> E u'' (tsingleton (k s'))
    where k s'' = q >>> loop s''
