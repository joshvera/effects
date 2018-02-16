{-# LANGUAGE TypeOperators #-}
{-|
Module      : Control.Monad.Effect
Description : Effects - an extensible effects library
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX

-}
module Control.Monad.Effect (
  -- * Running and Sending Effects
  Eff
  , run
  , send
  -- * Checking a List of Effects#
  , type(:<)
  , type(:<:)
  , Member
  , Members

) where

import Control.Monad.Effect.Internal
