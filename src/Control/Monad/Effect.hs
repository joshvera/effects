{-# LANGUAGE TypeOperators #-}
{-|
Module      : Control.Monad.Effect
Description : Effects - an extensible effects library
Copyright   : Allele Dev 2016
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
