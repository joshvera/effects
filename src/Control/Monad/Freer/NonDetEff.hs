{-# LANGUAGE TypeOperators, GADTs, FlexibleContexts, UndecidableInstances, DataKinds #-}
module Control.Monad.Freer.NonDetEff (
  NonDetEff(..),
  makeChoiceA,
  msplit
) where

import Control.Monad
import Control.Applicative
import Control.Monad.Freer.Internal

--------------------------------------------------------------------------------
                    -- Nondeterministic Choice --
--------------------------------------------------------------------------------
-- | A data type for representing nondeterminstic choice
data NonDetEff a where
  MZero :: NonDetEff a
  MPlus :: NonDetEff Bool

instance (NonDetEff :< effs) => Alternative (Eff effs) where
  empty = mzero
  (<|>) = mplus

instance (NonDetEff :< effs) => MonadPlus (Eff effs) where
  mzero       = send MZero
  mplus m1 m2 = send MPlus >>= \x -> if x then m1 else m2

-- | A handler for nondeterminstic effects
makeChoiceA :: Alternative f
            => Eff (NonDetEff ': effs) a -> Eff effs (f a)
makeChoiceA =
  handleRelay (return . pure) $ \m k ->
    case m of
      MZero -> return empty
      MPlus -> liftM2 (<|>) (k True) (k False)

msplit :: (NonDetEff :< effs)
       => Eff effs a -> Eff effs (Maybe (a, Eff effs a))
msplit = loop []
  where loop jq (Val x)     = return (Just (x, msum jq))
        loop jq (E u q) =
          case prj u of
            Just MZero ->
              case jq of
                []     -> return Nothing
                (j:jq') -> loop jq' j
            Just MPlus -> loop (applyEffs q False : jq) (applyEffs q True)
            Nothing    -> E u (tsingleton k)
              where k = composeEffs q (loop jq)