-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Main module for the Tamarin prover.
module Main.Mode.Batch.ToSmtlib (
    toSmtlib
  ) where

data Smtlib = Smtlib
  deriving (Show)

toSmtlib :: a -> Smtlib
toSmtlib _ = Smtlib
