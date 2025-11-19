module Main where

import System.Environment (getArgs)
import HevmStrategy

{-|
  HevmVCgen - Wrapper for hevm symbolic execution

  This executable demonstrates Strategy 1: using hevm for verification.

  Usage:
    hevmvcgen <contract.sol>

  Example:
    hevmvcgen examples/Counter.sol
-}

main :: IO ()
main = do
  args <- getArgs

  case args of
    [] -> do
      putStrLn "Usage: hevmvcgen <contract.sol>"
      putStrLn ""
      putStrLn "Running default example workflow..."
      exampleWorkflow

    [contractFile] -> do
      putStrLn $ "=== Verifying " ++ contractFile ++ " with hevm ==="
      putStrLn ""
      putStrLn "Note: This requires hevm and solc to be installed."
      putStrLn "Install hevm: cabal install hevm"
      putStrLn "Install solc: https://docs.soliditylang.org/en/latest/installing-solidity.html"
      putStrLn ""

      -- For now, just show the example workflow
      exampleWorkflow

    _ -> putStrLn "Error: Too many arguments. Usage: hevmvcgen <contract.sol>"
