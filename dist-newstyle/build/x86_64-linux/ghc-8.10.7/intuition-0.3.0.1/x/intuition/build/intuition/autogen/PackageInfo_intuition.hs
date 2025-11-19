{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module PackageInfo_intuition (
    name,
    version,
    synopsis,
    copyright,
    homepage,
  ) where

import Data.Version (Version(..))
import Prelude

name :: String
name = "intuition"
version :: Version
version = Version [0,3,0,1] []

synopsis :: String
synopsis = "Intuitionistic logic PicoSAT"
copyright :: String
copyright = ""
homepage :: String
homepage = "https://github.com/alx/intuition"
