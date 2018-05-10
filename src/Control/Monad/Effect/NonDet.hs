{-# LANGUAGE DataKinds, FlexibleContexts, GADTs, TypeOperators, UndecidableInstances #-}

{-|
Module      : Control.Monad.Effect.NonDet
Description : Nondeterministic Choice effects
Copyright   : Allele Dev 2015
License     : BSD-3
Maintainer  : allele.dev@gmail.com
Stability   : experimental
Portability : POSIX
-}


module Control.Monad.Effect.NonDet (
  NonDet(..),
  runNonDetM,
  gatherM,
  makeChoiceA,
  msplit
) where

import Control.Applicative
import Control.Monad
import Control.Monad.Effect.Internal

--------------------------------------------------------------------------------
                    -- Nondeterministic Choice --
--------------------------------------------------------------------------------

runNonDetM :: (Monoid b, Effectful m) => (a -> b) -> m (NonDet ': e) a -> m e b
runNonDetM f = raiseHandler (relay (pure . f) (\ m k -> case m of
  MZero -> pure mempty
  MPlus -> mappend <$> k True <*> k False))

gatherM :: (Monoid b, Member NonDet e, Effectful m)
        => (a -> b) -- ^ A function constructing a 'Monoid'al value from a single computed result. This might typically be @unit@ (for @Reducer@s), 'pure' (for 'Applicative's), or some similar singleton constructor.
        -> m e a    -- ^ The computation to run locally-nondeterministically.
        -> m e b
gatherM f = raiseHandler (interpose (pure . f) (\ m k -> case m of
  MZero -> pure mempty
  MPlus -> mappend <$> k True <*> k False))

-- | A handler for nondeterminstic effects
makeChoiceA :: (Alternative f, Effectful m)
            => m (NonDet ': e) a
            -> m e (f a)
makeChoiceA = raiseHandler (relay (pure . pure) (\ m k -> case m of
  MZero -> pure empty
  MPlus -> liftM2 (<|>) (k True) (k False)))

msplit :: Member NonDet e
       => Eff e a -> Eff e (Maybe (a, Eff e a))
msplit = loop []
  where loop jq (Val x) = pure (Just (x, msum jq))
        loop jq (E u q) =
          case prj u of
            Just MZero ->
              case jq of
                []      -> pure Nothing
                (j:jq') -> loop jq' j
            Just MPlus  -> loop (q `apply` False : jq) (q `apply` True)
            Nothing     -> E u (tsingleton k)
              where k = q >>> loop jq
