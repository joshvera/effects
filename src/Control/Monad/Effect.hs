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
module Control.Monad.Effect
  (
  -- * Running and Sending Effects
    Eff
  , Effectful
  , raiseEff
  , lowerEff
  , run
  , runM
  , send
  -- * Effect handlers
  , interpret
  , reinterpret
  , reinterpret2
  -- * Local effect handlers
  , interpose
  , interposeState
  -- * Checking a List of Effects
  , Member
  -- * Effects
  , Lift(..)
  , Embedded
  , Exc
  , Fail
  , NonDet
  , Reader
  , Resumable
  , SomeExc(..)
  , State
  , Trace
  , Writer
) where

import Control.Monad.Effect.Internal

import Control.Monad.Effect.Embedded (Embedded)
import Control.Monad.Effect.Exception (Exc)
import Control.Monad.Effect.Fail (Fail)
import Control.Monad.Effect.NonDet (NonDet)
import Control.Monad.Effect.Reader (Reader)
import Control.Monad.Effect.Resumable (Resumable, SomeExc(..))
import Control.Monad.Effect.State (State)
import Control.Monad.Effect.Trace (Trace)
import Control.Monad.Effect.Writer (Writer)
