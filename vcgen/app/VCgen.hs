{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use fewer imports" #-}
module Main where

import Prelude

import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( join, when )

import Data.Map
import qualified Data.Set as Set
import qualified GHC.Integer (leInteger) 
import qualified GHC.Integer (gtInteger)

import ParTiny   ( myLexer, pStmt )
import PrintTiny ( Print, printTree )
import AbsTiny ( BExpr(..), FormulaD (..), Formula (..))

import Logic


compute s =
    case pStmt (myLexer s) of
        Left err -> do
            putStrLn "\nParse              Failed...\n"
            putStrLn err
            exitFailure
        Right e -> do
            putStrLn "\nParse Successful!"
            putStrLn $ show (iS e rhoP0 rhoV0 sto0)
            let (fEnv, pre) = vcGen e (Data.Map.empty) Set.empty (FormulaDA $ FormulaDB BTrue) in
              do
                putStrLn "\nVerification Conditions: ["
                putStrLn $ printVCs (Prelude.map printTree (Set.toList fEnv))
                putStrLn ""
                putStrLn $ "Main condition: " ++ printTree pre
            putStrLn "\nDone."


main :: IO ()
main = do
    getContents >>= compute
    putStrLn ""
