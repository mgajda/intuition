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
            let assertions = extractAssertions prog
            putStrLn $ "\nFound " ++ show (length assertions) ++ " assertion(s)"

            -- Print assertion details with VCs and abstractions
            mapM_ printAssertion (zip [1..] assertions)

            -- Statistics
            let verifiable = length $ filter isVerifiableAssertion assertions
            let total = length assertions
            putStrLn $ "\n=== Verification Statistics ==="
            putStrLn $ "Total assertions: " ++ show total
            putStrLn $ "Verifiable by Intuition Prover: " ++ show verifiable ++ " (" ++ show (verifiable * 100 `div` max 1 total) ++ "%)"
            putStrLn $ "Require SMT solver: " ++ show (total - verifiable) ++ " (" ++ show ((total - verifiable) * 100 `div` max 1 total) ++ "%)"

            putStrLn "\nDone."
  where
    printAssertion (n, ctx) = do
      putStrLn $ "\n=== Assertion " ++ show n ++ " ==="
      putStrLn $ "Location: " ++ assertLocation ctx
      case assertCondition ctx of
        Nothing -> putStrLn "Condition: unconditional failure"
        Just expr -> do
          -- Generate VC
          let vc = generateVC ctx
          putStrLn $ "\nVerification Condition:"
          putStrLn $ "  " ++ vc

          -- Generate propositional abstraction
          let abstraction = abstractAssertion expr
          putStrLn $ "\nPropositional Abstraction:"
          putStrLn $ "  Formula: " ++ propFormula abstraction
          putStrLn $ "  Verifiable: " ++ show (isVerifiable abstraction)
          putStrLn $ "  Reason: " ++ verifiabilityReason abstraction

          when (not $ null $ propMapping abstraction) $ do
            putStrLn $ "\nAtom Mapping:"
            mapM_ (\(atom, var) -> putStrLn $ "    " ++ var ++ " := " ++ atom) (propMapping abstraction)

          -- Generate TPTP with axioms
          let axioms = detectNeededAxioms expr
          when (not $ null axioms) $ do
            putStrLn $ "\nTheory Axioms Needed: " ++ show (length axioms)
            mapM_ (\ax -> putStrLn $ "  - " ++ axiomName ax ++ ": " ++ axiomDescription ax) axioms

          -- Presburger classification
          let presburger = classifyPresburger expr
          putStrLn $ "\nPresburger Arithmetic Classification:"
          putStrLn $ "  Is Presburger: " ++ show (isPresburger presburger)
          putStrLn $ "  Reason: " ++ reason presburger
          when (not $ null $ nonLinearOps presburger) $ do
            putStrLn $ "  Non-linear ops: " ++ show (nonLinearOps presburger)

          -- Generate SMT-LIB2 file for Z3
          let smtContent = generateSMTLIB2 ctx
          let smtFilename = "vc_" ++ show n ++ ".smt2"
          writeFile smtFilename smtContent
          putStrLn $ "\n📄 SMT-LIB2 file generated: " ++ smtFilename

          -- Generate TPTP file
          let tptpContent = generateTPTPWithAxioms ctx
          let filename = "vc_" ++ show n ++ ".p"
          writeFile filename tptpContent
          putStrLn $ "📄 TPTP file generated: " ++ filename

    isVerifiableAssertion ctx = case assertCondition ctx of
      Nothing -> False
      Just expr -> isVerifiable (abstractAssertion expr)
