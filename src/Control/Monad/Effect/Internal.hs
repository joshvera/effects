{-# LANGUAGE ConstraintKinds, DataKinds, DeriveFoldable, DeriveFunctor, DeriveTraversable, FlexibleContexts, FlexibleInstances, GADTs, GeneralizedNewtypeDeriving, KindSignatures, PatternSynonyms, RankNTypes, TypeOperators, UndecidableInstances, ViewPatterns #-}
module Control.Monad.Effect.Internal (
  -- * Constructing and Sending Effects
  Eff(..)
  , send
  , NonDet(..)
  , Fail(..)
  , Lift(..)
  -- * Handling effects
  , pattern Effect
  , pattern Other
  , pattern Effect2_1
  , pattern Effect2_2
  , pattern Other2
  , Request(..)
  , decomposeEff
  , Effects
  , Effect(..)
  , liftStatefulHandler
  , liftHandler
  , Effectful(..)
  , raiseHandler
  , lowerHandler
  -- * Decomposing Unions
  , Member
  , decompose
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
  -- * Local effect handlers
  , eavesdrop
  , interpose
  -- * Effect handlers
  , interpret
  , reinterpret
  , reinterpret2
) where

import Control.Applicative (Alternative (..))
import Control.Monad (MonadPlus (..))
import Control.Monad.Fail (MonadFail (..))
import Control.Monad.IO.Class (MonadIO (..))
import Data.Coerce
import Data.FTCQueue
import Data.Functor.Identity
import Data.Union

-- | An effectful computation that returns 'b' and sends a list of 'effects'.
data Eff effects b
  -- | Done with the value of type `b`.
  = Return b
  -- | Send an union of 'effects' and 'eff a' to handle, and a queues of effects to apply from 'a' to 'b'.
  | forall a. E (Union effects (Eff effects) a) (Queue (Eff effects) a b)

-- | The topmost effect, and the continuation following it.
pattern Effect :: effect (Eff (effect ': effects)) b -> Arrow (Eff (effect ': effects)) b a -> Eff (effect ': effects) a
pattern Effect eff k <- (decomposeEff -> Right (Request (decompose -> Right eff) k))

-- | Another effect in the 'Union', and the continuation following it.
pattern Other :: Union effects (Eff (effect ': effects)) b -> Arrow (Eff (effect ': effects)) b a -> Eff (effect ': effects) a
pattern Other u k <- (decomposeEff -> Right (Request (decompose -> Left u) k))
{-# COMPLETE Return, Effect, Other #-}

-- | The first of the topmost two effects in the 'Union', and the continuation following it.
pattern Effect2_1 :: effect1 (Eff (effect1 ': effect2 ': effects)) b -> Arrow (Eff (effect1 ': effect2 ': effects)) b a -> Eff (effect1 ': effect2 ': effects) a
pattern Effect2_1 eff k <- (decomposeEff -> Right (Request (decompose -> Right eff) k))

-- | The second of the topmost two effects in the 'Union', and the continuation following it.
pattern Effect2_2 :: effect2 (Eff (effect1 ': effect2 ': effects)) b -> Arrow (Eff (effect1 ': effect2 ': effects)) b a -> Eff (effect1 ': effect2 ': effects) a
pattern Effect2_2 eff k <- (decomposeEff -> Right (Request (decompose -> Left (decompose -> Right eff)) k))

-- | Another effect in the 'Union', and the continuation following it.
pattern Other2 :: Union effects (Eff (effect1 ': effect2 ': effects)) b -> Arrow (Eff (effect1 ': effect2 ': effects)) b a -> Eff (effect1 ': effect2 ': effects) a
pattern Other2 u k <- (decomposeEff -> Right (Request (decompose -> Left (decompose -> Left u)) k))
{-# COMPLETE Return, Effect2_1, Effect2_2, Other2 #-}


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

-- | Decompose an 'Eff' into 'Either' a value or a 'Request' for one of a 'Union' of effects.
decomposeEff :: Eff effects a -> Either a (Request (Union effects) (Eff effects) a)
decomposeEff (Return a) = Left a
decomposeEff (E u q) = Right (Request u (apply q))

-- | Effects are higher-order (may themselves contain effectful actions), and as such must be able to thread an effect handler (structured as a distributive law) through themselves.
class Effect effect where
  -- | Lift some initial state and a handler for some effect through another effect.
  --
  --   First-order effects (ones not using the @m@ parameter) have relatively simple definitions, more or less just pushing the distributive law through the continuation. Higher-order effects (like @Reader@’s @Local@ constructor) must additionally apply the handler to their scoped actions.
  handleState :: Functor c
              => c ()
              -> (forall x . c (Eff effects x) -> Arrow (Eff effects) x a -> Eff effects' (c a))
              -> Request effect (Eff effects) a
              -> Request effect (Eff effects') (c a)

-- | Lift a stateful effect handler through other effects in the 'Union'.
--
--   Useful when defining effect handlers which maintain some state (such as @runState@) or which must return values in some carrier functor encapsulating the effects (such as @runError@).
liftStatefulHandler :: (Functor c, Effects effects')
                    => c ()
                    -> (forall x . c (Eff effects x) -> Arrow (Eff effects) x a -> Eff effects' (c a))
                    -> Union effects' (Eff effects) b
                    -> Arrow (Eff effects) b a
                    -> Eff effects' (c a)
liftStatefulHandler c handler u k = fromRequest (handleState c handler (Request u k))

-- | Lift a pure effect handler through other effects in the 'Union'.
--
--   Useful when defining pure effect handlers (such as @runReader@).
liftHandler :: (Effectful m, Effects effects')
            => (forall x . m effects x -> Arrow (m effects) x a -> m effects' a)
            -> Union effects' (Eff effects) b
            -> Arrow (m effects) b a
            -> m effects' a
liftHandler handler u k = raiseEff $ runIdentity <$> liftStatefulHandler (Identity ()) (\act k' -> fmap Identity . lowerEff $ handler (raiseEff (runIdentity act)) (raiseEff . k')) u (lowerEff . k)

instance Effect (Union '[]) where
  handleState _ _ _ = error "impossible: handleState on empty Union"

instance (Effect effect, Effect (Union effects)) => Effect (Union (effect ': effects)) where
  handleState c dist (Request u k) = case decompose u of
    Left u' -> weaken `requestMap` handleState c dist (Request u' k)
    Right eff -> inj `requestMap` handleState c dist (Request eff k)


-- | Require an 'Effect' instance for each effect in the list.
type Effects effects = Effect (Union effects)


-- | Types wrapping 'Eff' actions.
--
--   Most instances of 'Effectful' will be derived using @-XGeneralizedNewtypeDeriving@, with these ultimately bottoming out on the instance for 'Eff' (for which 'raise' and 'lower' are simply the identity). Because of this, types can be nested arbitrarily deeply and still call 'raiseEff'/'lowerEff' just once to get at the (ultimately) underlying 'Eff'.
class Effectful m where
  -- | Raise an action in 'Eff' into an action in @m@.
  raiseEff :: Eff effects a -> m   effects a

  -- | Lower an action in @m@ into an action in 'Eff'.
  lowerEff :: m   effects a -> Eff effects a

instance Effectful Eff where
  raiseEff = coerce
  {-# INLINE raiseEff #-}

  lowerEff = coerce
  {-# INLINE lowerEff #-}

-- | Raise a handler on 'Eff' to a handler on some 'Effectful' @m@.
raiseHandler :: Effectful m => (Eff effectsA a -> Eff effectsB b) -> m effectsA a -> m effectsB b
raiseHandler handler = raiseEff . handler . lowerEff
{-# INLINE raiseHandler #-}

-- | Lower a handler on some 'Effectful' @m@ to a handler on 'Eff'.
lowerHandler :: Effectful m => (m effectsA a -> m effectsB b) -> Eff effectsA a -> Eff effectsB b
lowerHandler handler = lowerEff . handler . raiseEff
{-# INLINE lowerHandler #-}


-- * Composing and Applying Effects

-- | Returns an effect by applying a given value to a queue of effects.
apply :: Queue (Eff effects) a b -> a -> Eff effects b
apply q' x =
   case tviewl q' of
   TOne k  -> k x
   k :< t -> case k x of
     Return y -> t `apply` y
     E u q -> E u (q >< t)

-- | Compose queues left to right.
(>>>) :: Queue (Eff effects) a b
      -> (Eff effects b -> Eff effects' c) -- ^ A function to compose.
      -> Arrow (Eff effects') a c
(>>>) queue f = f . apply queue

-- | Compose queues right to left.
(<<<) :: (Eff effects b -> Eff effects' c) -- ^ A function to compose.
      -> Queue (Eff effects)  a b
      -> Arrow (Eff effects') a c
(<<<) f queue  = f . apply queue

-- * Sending and Running Effects

-- | Send an effect and wait for a reply.
send :: (Member eff e, Effectful m) => eff (Eff e) b -> m e b
send t = raiseEff (E (inj t) (tsingleton Return))

-- | Runs an effect whose effects has been consumed.
--
-- Typically composed as follows:
--
-- @
-- run . runEff1 eff1Arg . runEff2 eff2Arg1 eff2Arg2 (program)
-- @
run :: Effectful m => m '[] b -> b
run m = case lowerEff m of
  Return x -> x
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
  Return x -> pure x
  E u q -> unLift (strengthen u) >>= runM . apply q


-- * Local handlers

-- | Listen for an effect, and take some action before re-sending it.
eavesdrop :: (Member eff effects, Effectful m, Effects effects)
          => (forall v. eff (Eff effects) v -> m effects ())
          -> m effects a
          -> m effects a
eavesdrop listener = raiseHandler loop
  where loop (Return a) = pure a
        loop (E u q) = case prj u of
          Just eff -> lowerEff (listener eff) >> send eff >>= (q >>> loop)
          _        -> liftHandler (\ m yield -> eavesdrop (lowerEff . listener) m >>= yield) u (apply q)

-- | Intercept the request and possibly reply to it, but leave it
-- unhandled
interpose :: (Member eff e, Effectful m, Effects e)
          => (forall v. eff (Eff e) v -> m e v)
          -> m e a
          -> m e a
interpose handler = raiseHandler loop
  where loop (Return a) = pure a
        loop (E u q) = case prj u of
          Just eff -> lowerEff (handler eff) >>= k
          _        -> liftHandler (\ m yield -> interpose (lowerEff . handler) m >>= yield) u k
          where k = q >>> loop


-- * Effect handlers

-- | Handle the topmost effect by interpreting it into the underlying effects.
interpret :: (Effectful m, Effects effs)
          => (forall v. eff (Eff (eff ': effs)) v -> m effs v)
          -> m (eff ': effs) a
          -> m effs a
interpret bind = raiseHandler loop
  where loop (Return a)     = pure a
        loop (Effect eff k) = lowerEff (bind eff) >>= loop . k
        loop (Other u k)    = liftHandler (\ m yield -> interpret (lowerEff . bind) (m >>= yield)) u k


-- | Interpret an effect by replacing it with another effect.
reinterpret :: (Effectful m, Effects (newEffect ': effs))
            => (forall v. effect (Eff (effect ': effs)) v -> m (newEffect ': effs) v)
            -> m (effect ': effs) a
            -> m (newEffect ': effs) a
reinterpret bind = raiseHandler loop
  where loop (Return a)     = pure a
        loop (Effect eff k) = lowerEff (bind eff) >>= loop . k
        loop (Other u k)    = liftHandler (\ m yield -> reinterpret (lowerEff . bind) (m >>= yield)) (weaken u) k

-- | Interpret an effect by replacing it with two new effects.
reinterpret2 :: (Effectful m, Effects (newEffect1 ': newEffect2 ': effs))
             => (forall v. effect (Eff (effect ': effs)) v -> m (newEffect1 ': newEffect2 ': effs) v)
             -> m (effect ': effs) a
             -> m (newEffect1 ': newEffect2 ': effs) a
reinterpret2 bind = raiseHandler loop
  where loop (Return a)     = pure a
        loop (Effect eff k) = lowerEff (bind eff) >>= loop . k
        loop (Other u k)    = liftHandler (\m yield -> reinterpret2 (lowerEff . bind) (m >>= yield)) (weaken (weaken u)) k


-- * Effect Instances

instance Functor (Eff e) where
  fmap f (Return x) = Return (f x)
  fmap f (E u q) = E u (q |> (Return . f))
  {-# INLINE fmap #-}

instance Applicative (Eff e) where
  pure = Return
  {-# INLINE pure #-}

  Return f <*> Return x = Return $ f x
  Return f <*> E u q = E u (q |> (Return . f))
  E u q <*> m     = E u (q |> (`fmap` m))
  {-# INLINE (<*>) #-}

instance Monad (Eff e) where
  return = Return
  {-# INLINE return #-}

  Return x >>= k = k x
  E u q >>= k = E u (q |> k)
  {-# INLINE (>>=) #-}

instance Member (Lift IO) e => MonadIO (Eff e) where
  liftIO = send . Lift
  {-# INLINE liftIO #-}


-- | Lift a first-order effect (e.g. a 'Monad' like 'IO') into an 'Eff'.
newtype Lift effect (m :: * -> *) a = Lift { unLift :: effect a }
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Effect (Lift effect) where
  handleState c dist (Request (Lift op) k) = Request (Lift op) (\result -> dist (pure result <$ c) k)


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
  handleState c dist (Request MZero k) = Request MZero (\result -> dist (pure result <$ c) k)
  handleState c dist (Request MPlus k) = Request MPlus (\result -> dist (pure result <$ c) k)

-- | An effect representing failure.
newtype Fail (m :: * -> *) a = Fail { failMessage :: String }

instance Member Fail fs => MonadFail (Eff fs) where
  fail = send . Fail

instance Effect Fail where
  handleState c dist (Request (Fail s) k) = Request (Fail s) (\result -> dist (pure result <$ c) k)
