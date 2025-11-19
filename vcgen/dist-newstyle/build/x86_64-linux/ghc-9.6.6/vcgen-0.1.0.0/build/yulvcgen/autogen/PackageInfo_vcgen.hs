{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module PackageInfo_vcgen (
    name,
    version,
    synopsis,
    copyright,
    homepage,
  ) where

import Data.Version (Version(..))
import Prelude

name :: String
name = "vcgen"
version :: Version
version = Version [0,1,0,0] []

synopsis :: String
synopsis = "A sample verification conditions generator for a simple language of while programs with procedures called by value."
copyright :: String
copyright = ""
homepage :: String
homepage = ""
