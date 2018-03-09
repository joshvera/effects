{-# LANGUAGE DataKinds, FlexibleContexts, GADTs, TypeFamilies, TypeOperators, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Control.Monad.Effect.NonDet
  ( MonadNonDet(..)
  , NonDetEff(..)
  , makeChoiceA
  , msplit
  ) where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Effect.Internal

--------------------------------------------------------------------------------
                    -- Nondeterministic Choice --
--------------------------------------------------------------------------------
-- | A data type for representing nondeterminstic choice
data NonDetEff a where
  MZero :: NonDetEff a
  MPlus :: NonDetEff Bool

instance (NonDetEff :< e) => Alternative (Eff e) where
  empty = mzero
  (<|>) = mplus

instance (NonDetEff :< a) => MonadPlus (Eff a) where
  mzero       = send MZero
  mplus m1 m2 = send MPlus >>= \x -> if x then m1 else m2

-- | A handler for nondeterminstic effects
makeChoiceA :: Alternative f
            => Eff (NonDetEff ': e) a -> Eff e (f a)
makeChoiceA =
  relay (pure . pure) $ \m k ->
    case m of
      MZero -> pure empty
      MPlus -> liftM2 (<|>) (k True) (k False)

msplit :: (NonDetEff :< e)
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


-- | 'Monad's offering local isolation of nondeterminism effects.
class (Alternative m, Monad m) => MonadNonDet m where
  -- | Run a computation, gathering any nondeterministically produced results into a single 'Monoid'al value.
  gather :: Monoid b
         => (a -> b) -- ^ A function constructing a 'Monoid'al value from a single computed result. This might typically be @point@ (for @Pointed@ functors), 'pure' (for 'Applicative's), or some similar singleton constructor.
         -> m a      -- ^ The computation to run locally-nondeterministically.
         -> m b      -- ^ A _deterministic_ computation producing the 'Monoid'al accumulation of the _locally-nondeterministic_ result values.

-- | Effect stacks containing 'NonDetEff' offer a 'MonadNonDet' instance which implements 'gather' by interpreting the requests for nondeterminism locally, without removing 'NonDetEff' from the stack—i.e. the _capacity_ for nondeterminism is still present in the effect stack, but any local nondeterminism has been applied.
instance (NonDetEff :< fs) => MonadNonDet (Eff fs) where
  gather f = interpose (pure . f) (\ m k -> case m of
    MZero -> pure mempty
    MPlus -> mappend <$> k True <*> k False)
