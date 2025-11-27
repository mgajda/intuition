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
            mapM_ (printAssertion prog) (zip [1..] assertions)

            -- Statistics
            let verifiableByIntuition = length $ filter isVerifiableAssertion assertions
            let verifiedByIntuitionWP = length $ filter (\ctx -> intuitionSuccess (verifyWithIntuitionWP prog ctx)) assertions
            let total = length assertions
            putStrLn $ "\n=== Verification Statistics ==="
            putStrLn $ "Total assertions: " ++ show total
            putStrLn $ "Verifiable by Intuition alone (no WP): " ++ show verifiableByIntuition ++ " (" ++ show (verifiableByIntuition * 100 `div` max 1 total) ++ "%)"
            putStrLn $ "✅ VERIFIED by Intuition + WP + Presburger: " ++ show verifiedByIntuitionWP ++ " (" ++ show (verifiedByIntuitionWP * 100 `div` max 1 total) ++ "%)"
            putStrLn $ "Require full SMT solver: " ++ show (total - verifiedByIntuitionWP) ++ " (" ++ show ((total - verifiedByIntuitionWP) * 100 `div` max 1 total) ++ "%)"

            putStrLn "\nDone."
  where
    printAssertion prog (n, ctx) = do
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

          -- Intuition + Presburger verification (homegrown SMT)
          let intuitionResult = verifyWithIntuitionWP prog ctx
          putStrLn $ "\n🎯 Intuition + Presburger Verification:"
          putStrLn $ "  WP Computed: " ++ show (wpComputed intuitionResult)
          putStrLn $ "  Propositional Formula: " ++ propositionalFormula intuitionResult
          putStrLn $ "  Intuition Verifiable: " ++ show (not . null $ propositionalFormula intuitionResult)
          when (not $ null $ arithmeticAtoms intuitionResult) $ do
            putStrLn $ "  Arithmetic Atoms:"
            mapM_ (\(atomId, atomExpr) -> do
              let atomValid = lookup atomId (atomCheckResults intuitionResult)
              let status = case atomValid of
                    Just True -> "✅"
                    Just False -> "❌"
                    Nothing -> "?"
              putStrLn $ "    " ++ status ++ " " ++ atomId ++ " := " ++ atomExpr
              ) (arithmeticAtoms intuitionResult)
          putStrLn $ "  Result: " ++ verificationMessage intuitionResult
          putStrLn $ "  VERIFIED: " ++ show (intuitionSuccess intuitionResult)

          -- Generate SMT-LIB2 file for Z3 with WP
          let smtContent = generateSMTLIB2_WP prog ctx
          let smtFilename = "vc_" ++ show n ++ ".smt2"
          writeFile smtFilename smtContent
          putStrLn $ "\n📄 SMT-LIB2 file generated with WP: " ++ smtFilename

          -- Generate TPTP file with bit-blasting
          let tptpContent = generateTPTPWithImplications ctx
          let filename = "vc_" ++ show n ++ ".p"
          writeFile filename tptpContent
          putStrLn $ "📄 TPTP file generated (bit-blasted): " ++ filename

    isVerifiableAssertion ctx = case assertCondition ctx of
      Nothing -> False
      Just expr -> isVerifiable (abstractAssertion expr)
