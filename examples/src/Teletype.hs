{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds, KindSignatures #-}
module Teletype where

import Control.Monad.Effect
import Control.Monad.Effect.Internal as I
import System.Exit hiding (ExitSuccess)

data Teletype (m :: * -> *) s where
  PutStrLn    :: String -> Teletype m ()
  GetLine     :: Teletype m String
  ExitSuccess :: Teletype m ()

-- Takes a string and returns a teletype effect.
putStrLn' :: Member Teletype e => String -> Eff e ()
putStrLn' = send . PutStrLn

-- Gets a line from a Teletype.
getLine'  :: Member Teletype e => Eff e String
getLine' = send GetLine

-- An exit success effect that returns ().
exitSuccess' :: Member Teletype e => Eff e ()
exitSuccess' = send ExitSuccess

-- Runs a Teletype effect b and returns IO b.
run :: Eff '[Teletype] a -> IO a
run (Return x) = pure x
run (E u q) = case decompose u of
  Right (PutStrLn msg) -> putStrLn msg  >> Teletype.run (apply q ())
  Right GetLine        -> getLine      >>= \s -> Teletype.run (apply q s)
  Right ExitSuccess    -> exitSuccess
  Left  _              -> error "This cannot happen"

-- Takes a list of strings and a teletype effect to run and
-- returns the list of strings printed in that effect.
runPure :: [String] -> Eff '[Teletype] a -> [String]
runPure inputs req = reverse (go inputs req [])
  where go :: [String] -> Eff '[Teletype] w -> [String] -> [String]
        go _  (Return _) acc = acc
        go xs (E u q) acc = case xs of
          (x:xs') -> case decompose u of
            Right (PutStrLn msg) -> go (x:xs') (apply q ()) (msg:acc)
            Right GetLine        -> go xs'     (apply q x) acc
            Right ExitSuccess    -> go xs'     (Return ())   acc
            Left _               -> go xs'     (Return ())   acc
          _      -> case decompose u of
            Right (PutStrLn msg) -> go xs (apply q ()) (msg:acc)
            _                    -> go xs     (Return ())   acc
