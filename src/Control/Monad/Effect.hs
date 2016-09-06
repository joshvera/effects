{-# LANGUAGE TypeOperators #-}
{-|
Module      : Control.Monad.Effect
Description : Freer - an extensible effects library
Copyright   : Alej Cabrera 2015
License     : BSD-3
Maintainer  : cpp.cabrera@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Control.Monad.Effect (
  -- * Running and Sending Effects
  Eff,
  run,
  send,
  -- * Checking a List of Effects
  type(:<),
  type(:<:)
) where

import Control.Monad.Effect.Internal
