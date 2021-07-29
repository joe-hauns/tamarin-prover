{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveAnyClass        #-}
module Theory.Module (
      ModuleType (..)
    , description
)
where

import GHC.Generics (Generic)
import Control.DeepSeq ( NFData )
import Data.Binary ( Binary )
import Data.Data ( Data )

data ModuleType =
   -- Too generate a parser from the show() values, these need to be ordered
   -- such that no preceding show value is a prefix of another one that comes
  ModuleSpthyTyped  
  | ModuleSpthy 
  | ModuleMsr 
  | ModuleProVerif 
  | ModuleDeepSec
  deriving (Eq, Ord, Enum, Bounded, Generic, Data, NFData, Binary)
instance Show ModuleType where
    show ModuleSpthyTyped ="spthytyped"
    show ModuleSpthy = "spthy"
    show ModuleMsr ="msr"
    show ModuleProVerif ="proverif"
    show ModuleDeepSec ="deepsec"

description :: ModuleType -> String
description ModuleSpthy = "spthy (including Sapic Processes)"
description ModuleSpthyTyped ="spthy with explicit types inferred"
description ModuleMsr ="pure msrs (with Sapic translation)"
description ModuleProVerif ="ProVerif"
description ModuleDeepSec ="DeepSec"
