module Main where

import System.Environment (getArgs)
import SolcASTStrategy

{-|
  SolcASTVCgen - Verification Condition Generator from Solidity AST

  This executable implements Strategy 3: parsing solc's AST JSON output
  and generating verification conditions in TPTP format.

  Usage:
    solcastvcgen <contract.sol> [output_dir]

  Example:
    solcastvcgen examples/Counter.sol build/

  Output:
    build/vcs.p - TPTP file with verification conditions

  Then verify with intuition prover:
    intuition -f build/vcs.p
-}

main :: IO ()
main = do
  args <- getArgs

  case args of
    [] -> do
      putStrLn "Usage: solcastvcgen <contract.sol> [output_dir]"
      putStrLn ""
      putStrLn "Example:"
      putStrLn "  solcastvcgen examples/Counter.sol build/"
      putStrLn ""
      putStrLn "Running default example workflow..."
      putStrLn ""

      let config = Config
            { solidityFile = "examples/Counter.sol"
            , outputDir = "build"
            }
      exampleWorkflow config

    [contractFile] -> do
      putStrLn $ "=== Generating VCs from " ++ contractFile ++ " ==="
      putStrLn ""

      let config = Config
            { solidityFile = contractFile
            , outputDir = "build"
            }
      exampleWorkflow config

    [contractFile, outDir] -> do
      putStrLn $ "=== Generating VCs from " ++ contractFile ++ " ==="
      putStrLn ""

      let config = Config
            { solidityFile = contractFile
            , outputDir = outDir
            }
      exampleWorkflow config

    _ -> putStrLn "Error: Too many arguments"
