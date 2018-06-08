{-# LANGUAGE AllowAmbiguousTypes, DataKinds, DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, FlexibleInstances, GADTs, GeneralizedNewtypeDeriving, KindSignatures, PatternSynonyms, RankNTypes, TypeOperators, UndecidableInstances, ViewPatterns #-}
module Control.Monad.Effect.Internal (
  -- * Constructing and Sending Effects
  Eff(..)
  , pattern Return
  , pattern Effect
  , pattern Other
  , send
  , NonDet(..)
  , Fail(..)
  , Lift(..)
  , Request(..)
  , requestMap
  , fromRequest
  , decomposeEff
  , Effect(..)
  , handle
  , Effectful(..)
  , raiseHandler
  -- * Decomposing Unions
  , Member
  , decompose
  -- | Inserts multiple effects into 'E'.
  , inj
  , prj
  -- * Constructing and Decomposing Queues of Effects
  , Queue
  , tsingleton
  , Arrow
  , Union
  -- * Composing and Applying Effects
  , apply
  , (<<<)
  , (>>>)
  -- * Running Effects
  , run
  , runM
) where

import Control.Applicative (Alternative (..))
import Control.Monad (MonadPlus (..))
import Control.Monad.Fail (MonadFail (..))
import Control.Monad.IO.Class (MonadIO (..))
import Data.FTCQueue
import Data.Functor.Identity
import Data.Union

-- | An effectful computation that returns 'b' and sends a list of 'effects'.
data Eff effects b
  -- | Done with the value of type `b`.
  = Val b
  -- | Send an union of 'effects' and 'eff a' to handle, and a queues of effects to apply from 'a' to 'b'.
  | forall a. E (Union effects (Eff effects) a) (Queue (Eff effects) a b)

pattern Return :: b -> Eff effects b
pattern Return a <- Val a

pattern Effect :: effect (Eff (effect ': effects)) b -> Arrow (Eff (effect ': effects)) b a -> Eff (effect ': effects) a
pattern Effect eff k <- (decomposeEff -> Right (Right (Request eff k)))

pattern Other :: Request (Union effects) (Eff (effect ': effects)) a -> Eff (effect ': effects) a
pattern Other r <- (decomposeEff -> Right (Left r))
{-# COMPLETE Return, Effect, Other #-}


-- | A queue of effects to apply from 'a' to 'b'.
type Queue = FTCQueue

-- | An effectful function from 'a' to 'b'
--   that also performs a list of 'effects'.
type Arrow m a b = a -> m b


data Request effect m a = forall b . Request (effect m b) (Arrow m b a)

instance Functor m => Functor (Request effect m) where
  fmap f (Request eff k) = Request eff (fmap f . k)

requestMap :: (forall x . effect m x -> effect' m x) -> Request effect m a -> Request effect' m a
requestMap f (Request effect q) = Request (f effect) q

fromRequest :: Request (Union effects) (Eff effects) a -> Eff effects a
fromRequest (Request u k) = E u (tsingleton k)

decomposeEff :: Eff (effect ': effects) a -> Either a (Either (Request (Union effects) (Eff (effect ': effects)) a) (Request effect (Eff (effect ': effects)) a))
decomposeEff (Val a) = Left a
decomposeEff (E u q) = Right $ case decompose u of
  Left u' -> Left (Request u' (apply q))
  Right eff -> Right (Request eff (apply q))

class Effect effect where
  handleState :: Functor c => c () -> (forall x . c (Eff effects x) -> Eff effects' (c x)) -> (Request effect (Eff effects) a -> Request effect (Eff effects') (c a))

handle :: Effect effect => (forall x . Eff effects x -> Eff effects' x) -> (Request effect (Eff effects) a -> Request effect (Eff effects') a)
handle handler r = runIdentity <$> handleState (Identity ()) (fmap Identity . handler . runIdentity) r

instance Effect (Union '[]) where
  handleState _ _ _ = error "impossible: handleState on empty Union"

instance (Effect effect, Effect (Union effects)) => Effect (Union (effect ': effects)) where
  handleState c dist (Request u q) = case decompose u of
    Left u' -> weaken `requestMap` handleState c dist (Request u' q)
    Right eff -> inj `requestMap` handleState c dist (Request eff q)


-- | Types wrapping 'Eff' actions.
--
--   Most instances of 'Effectful' will be derived using @-XGeneralizedNewtypeDeriving@, with these ultimately bottoming out on the instance for 'Eff' (for which 'raise' and 'lower' are simply the identity). Because of this, types can be nested arbitrarily deeply and still call 'raiseEff'/'lowerEff' just once to get at the (ultimately) underlying 'Eff'.
class Effectful m where
  -- | Raise an action in 'Eff' into an action in @m@.
  raiseEff :: Eff effects a -> m   effects a
  -- | Lower an action in @m@ into an action in 'Eff'.
  lowerEff :: m   effects a -> Eff effects a

instance Effectful Eff where
  raiseEff = id
  lowerEff = id

-- | Raise a handler on 'Eff' to a handler on some 'Effectful' @m@.
raiseHandler :: Effectful m => (Eff effectsA a -> Eff effectsB b) -> m effectsA a -> m effectsB b
raiseHandler handler = raiseEff . handler . lowerEff
{-# INLINE raiseHandler #-}


-- * Composing and Applying Effects

-- | Returns an effect by applying a given value to a queue of effects.
apply :: Queue (Eff effects) a b -> a -> Eff effects b
apply q' x =
   case tviewl q' of
   TOne k  -> k x
   k :< t -> case k x of
     Val y -> t `apply` y
     E u q -> E u (q >< t)

-- | Compose queues left to right.
(>>>) :: Queue (Eff effects) a b
      -> (Eff effects b -> Eff effects' c) -- ^ An function to compose.
      -> Arrow (Eff effects') a c
(>>>) queue f = f . apply queue

-- | Compose queues right to left.
(<<<) :: (Eff effects b -> Eff effects' c) -- ^ An function to compose.
      -> Queue (Eff effects)  a b
      -> Arrow (Eff effects') a c
(<<<) f queue  = f . apply queue

-- * Sending and Running Effects

-- | Send a effect and wait for a reply.
send :: (Effectful m, Member eff e) => eff (Eff e) b -> m e b
send t = raiseEff (E (inj t) (tsingleton Val))

-- | Runs an effect whose effects has been consumed.
--
-- Typically composed as follows:
--
-- @
-- run . runEff1 eff1Arg . runEff2 eff2Arg1 eff2Arg2 (program)
-- @
run :: Effectful m => m '[] b -> b
run m = case lowerEff m of
  Val x -> x
  _     -> error "Internal:run - This (E) should never happen"
-- the other case is unreachable since Union [] a cannot be
-- constructed. Therefore, run is a total function if its argument
-- terminates.

-- | Runs an effect for which all but one Monad effect has been consumed,
-- and returns an 'm a'.
--
-- This is useful for plugging in traditional transformer stacks.
runM :: (Effectful m, Monad m1) => m '[Lift m1] a -> m1 a
runM m = case lowerEff m of
  Val x -> pure x
  E u q -> unLift (strengthen u) >>= runM . apply q


-- * Effect Instances

instance Functor (Eff e) where
  fmap f (Val x) = Val (f x)
  fmap f (E u q) = E u (q |> (Val . f))
  {-# INLINE fmap #-}

instance Applicative (Eff e) where
  pure = Val
  {-# INLINE pure #-}

  Val f <*> Val x = Val $ f x
  Val f <*> E u q = E u (q |> (Val . f))
  E u q <*> m     = E u (q |> (`fmap` m))
  {-# INLINE (<*>) #-}

instance Monad (Eff e) where
  return = Val
  {-# INLINE return #-}

  Val x >>= k = k x
  E u q >>= k = E u (q |> k)
  {-# INLINE (>>=) #-}

instance Member (Lift IO) e => MonadIO (Eff e) where
  liftIO = send . Lift
  {-# INLINE liftIO #-}


-- | Lift a first-order effect (e.g. a 'Monad' like 'IO') into an 'Eff'.
newtype Lift effect (m :: * -> *) a = Lift { unLift :: effect a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Functor effect => Effect (Lift effect) where
  handleState c dist (Request (Lift op) k) = Request (Lift op) (dist . (<$ c) . k)


-- | A data type for representing nondeterminstic choice
data NonDet (m :: * -> *) a where
  MZero :: NonDet m a
  MPlus :: NonDet m Bool

instance Member NonDet e => Alternative (Eff e) where
  empty = mzero
  (<|>) = mplus

instance Member NonDet a => MonadPlus (Eff a) where
  mzero       = send MZero
  mplus m1 m2 = send MPlus >>= \x -> if x then m1 else m2

instance Effect NonDet where
  handleState c dist (Request MZero k) = Request MZero (dist . (<$ c) . k)
  handleState c dist (Request MPlus k) = Request MPlus (dist . (<$ c) . k)


-- | An effect representing failure.
newtype Fail (m :: * -> *) a = Fail { failMessage :: String }

instance Member Fail fs => MonadFail (Eff fs) where
  fail = send . Fail

instance Effect Fail where
  handleState c dist (Request (Fail s) k) = Request (Fail s) (dist . (<$ c) . k)
