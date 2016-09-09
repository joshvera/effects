{-# LANGUAGE TypeOperators, GADTs, FlexibleContexts, FlexibleInstances, UndecidableInstances, DataKinds #-}
module Control.Monad.Effect.NonDetEff (
  NonDetEff(..),
  makeChoiceA,
  msplit
) where

import Control.Monad
import Control.Applicative
import Control.Monad.Effect.Internal

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

instance (NonDetEff :< e) => MonadPlus (Eff e) where
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