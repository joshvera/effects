{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
module Teletype where

import Control.Monad.Freer
import Control.Monad.Freer.Internal as I
import System.Exit hiding (ExitSuccess)

--------------------------------------------------------------------------------
                          -- Effect Model --
                          --------------------------------------------------------------------------------
data Teletype s where
  PutStrLn    :: String -> Teletype ()
  GetLine     :: Teletype String
  ExitSuccess :: Teletype ()

putStrLn' :: (Teletype :< r) => String -> Eff r ()
putStrLn' = send . PutStrLn

getLine'  :: (Teletype :< r) => Eff r String
getLine' = send GetLine

exitSuccess' :: (Teletype :< r) => Eff r ()
exitSuccess' = send ExitSuccess

--------------------------------------------------------------------------------
                     -- Effectful Interpreter --
--------------------------------------------------------------------------------
run :: Eff '[Teletype] w -> IO w
run (Val x) = return x
run (E u q) = case decomp u of
              Right (PutStrLn msg) -> putStrLn msg  >> Teletype.run (qApp q ())
              Right GetLine        -> getLine      >>= \s -> Teletype.run (qApp q s)
              Right ExitSuccess    -> exitSuccess
              Left  _              -> error "This cannot happen"

--------------------------------------------------------------------------------
                        -- Pure Interpreter --
--------------------------------------------------------------------------------

-- Takes a list of strings and a teletype effect to run and
-- returns a list of strings.
runPure :: [String] -> Eff '[Teletype] w -> [String]
runPure inputs req = reverse (go inputs req [])
  where go :: [String] -> Eff '[Teletype] w -> [String] -> [String]
        go _      (Val _) acc = acc
        go []     _       acc = acc
        go (x:xs) (E u q) acc = case decomp u of
          Right (PutStrLn msg) -> go (x:xs) (qApp q ()) (msg:acc)
          Right GetLine        -> go xs     (qApp q x) acc
          Right ExitSuccess    -> go xs     (Val ())   acc
          Left _               -> go xs     (Val ())   acc
