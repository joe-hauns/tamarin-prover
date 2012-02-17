-- |
-- Copyright   : (c) 2010, 2011 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
-- 
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Main module for the tamarin prover without a GUI
module Main_Full where

import Main.Console          (defaultMain)
import Main.Mode.Batch       (batchMode)
import Main.Mode.Intruder    (intruderMode)
import Main.Mode.Interactive (interactiveMode)

main :: IO ()
main = defaultMain batchMode [interactiveMode, intruderMode]
