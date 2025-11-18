{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use fewer imports" #-}
module Main where

import Prelude
import System.Environment ( getArgs )
import System.Exit        ( exitFailure )
import Control.Monad      ( when )

import ParYul   ( myLexer, pYulProgram )
import PrintYul ( printTree )
import AbsYul

import YulLogic

{-|
  YulVCgen - Verification Condition Generator for Yul

  This tool parses Yul intermediate representation and generates
  verification conditions to check assertions.

  Usage:
    yulvcgen < input.yul
-}

main :: IO ()
main = do
  putStrLn "=== Yul Verification Condition Generator ==="
  putStrLn "Strategy 2: Custom Yul Parser with BNFC"
  putStrLn ""
  getContents >>= compute

compute :: String -> IO ()
compute s =
    case pYulProgram (myLexer s) of
        Left err -> do
            putStrLn "\nParse Failed...\n"
            putStrLn err
            exitFailure
        Right prog -> do
            putStrLn "\nParse Successful!"
            putStrLn $ "AST: " ++ show prog
            putStrLn ""
            putStrLn "Pretty printed:"
            putStrLn $ printTree prog

            -- Extract assertions and generate VCs
            let assertions = extractAssertions s
            putStrLn $ "\nFound " ++ show (length assertions) ++ " assertions"

            -- TODO: Generate and check VCs
            putStrLn "\nDone."
