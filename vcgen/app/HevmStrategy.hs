{-# LANGUAGE OverloadedStrings #-}
module HevmStrategy where

import System.Process
import System.Exit
import Data.Maybe (fromMaybe)

{-|
  Strategy 1: hevm Symbolic Execution Integration

  This module demonstrates how to integrate with hevm for Solidity verification.
  hevm is a mature symbolic execution engine for the EVM.

  Workflow:
  1. Compile Solidity contract with `solc`
  2. Extract compiled bytecode and AST
  3. Run hevm symbolic execution
  4. Check for assertion violations

  NOTE: This is a conceptual implementation. Full integration requires:
  - hevm package (currently GHC 9.4 compatible, testing with 9.6 needed)
  - solc compiler installed
  - Solidity contract files
-}

-- | Configuration for hevm symbolic execution
data HevmConfig = HevmConfig
  { contractPath :: FilePath
  , contractName :: String
  , maxIterations :: Int
  , solver :: SolverType
  } deriving Show

data SolverType = Z3 | CVC5 | Bitwuzla
  deriving Show

solverName :: SolverType -> String
solverName Z3 = "z3"
solverName CVC5 = "cvc5"
solverName Bitwuzla = "bitwuzla"

-- | Result of symbolic execution
data VerificationResult
  = Verified            -- All assertions hold
  | Counterexample String  -- Found a failing case
  | Timeout             -- Solver timed out
  | CompilationError String
  | HevmError String
  deriving Show

{-|
  Step 1: Compile Solidity to bytecode and AST

  Example:
    solc --bin --ast-compact-json Contract.sol -o build/
-}
compileSolidity :: FilePath -> IO (Either String (FilePath, FilePath))
compileSolidity solFile = do
  putStrLn $ "Compiling " ++ solFile ++ "..."

  -- Check if solc is installed
  solcCheck <- rawSystem "which" ["solc"]
  case solcCheck of
    ExitFailure _ -> return $ Left "solc not found. Please install Solidity compiler."
    ExitSuccess -> do
      -- Compile to bytecode and AST
      result <- rawSystem "solc"
        [ "--bin"
        , "--ast-compact-json"
        , solFile
        , "-o", "build/"
        ]

      case result of
        ExitFailure code -> return $ Left $ "Compilation failed with code " ++ show code
        ExitSuccess -> return $ Right ("build/combined.bin", "build/combined_json.ast")

{-|
  Step 2: Run hevm symbolic execution

  Command example:
    hevm symbolic --code <bytecode> --solver z3 --max-iterations 1000

  Full hevm integration would use the Haskell API:
    import EVM.Solidity (readSolc)
    import EVM.SymExec (verify)
-}
runHevmSymbolic :: HevmConfig -> FilePath -> IO VerificationResult
runHevmSymbolic config bytecodeFile = do
  putStrLn $ "Running hevm symbolic execution on " ++ contractName config ++ "..."

  -- Check if hevm is installed
  hevmCheck <- rawSystem "which" ["hevm"]
  case hevmCheck of
    ExitFailure _ -> return $ HevmError "hevm not found. Install with: cabal install hevm"
    ExitSuccess -> do
      -- Run hevm symbolic
      -- Note: This is a simplified command. Real usage would read bytecode first.
      result <- rawSystem "hevm"
        [ "symbolic"
        , "--code", bytecodeFile
        , "--solver", solverName (solver config)
        , "--max-iterations", show (maxIterations config)
        ]

      case result of
        ExitFailure _ -> return $ HevmError "hevm execution failed"
        ExitSuccess -> return Verified

{-|
  Full Haskell API Example (requires hevm library):

  verifyContract :: FilePath -> IO VerificationResult
  verifyContract solFile = do
    -- Load compiled contract
    solcOutput <- readSolc "out/Contract.sol/Contract.json"

    -- Run symbolic execution
    result <- verify solcOutput entrypoint []

    -- Check result
    case result of
      Qed -> return Verified
      Cex trace -> return $ Counterexample (show trace)

  This would give you:
  - Full EVM semantics
  - Built-in SMT solver integration
  - Automatic assertion checking
  - Counterexample generation
-}

-- | Example usage showing the workflow
exampleWorkflow :: IO ()
exampleWorkflow = do
  putStrLn "=== Strategy 1: hevm Symbolic Execution ==="
  putStrLn ""

  let config = HevmConfig
        { contractPath = "examples/Counter.sol"
        , contractName = "Counter"
        , maxIterations = 1000
        , solver = Z3
        }

  putStrLn "Step 1: Compile Solidity contract"
  compilationResult <- compileSolidity (contractPath config)

  case compilationResult of
    Left err -> putStrLn $ "Error: " ++ err
    Right (bytecodeFile, astFile) -> do
      putStrLn $ "✓ Compiled to " ++ bytecodeFile

      putStrLn "\nStep 2: Run hevm symbolic execution"
      verifyResult <- runHevmSymbolic config bytecodeFile

      putStrLn "\nResult:"
      case verifyResult of
        Verified -> putStrLn "✓ All assertions verified!"
        Counterexample trace -> putStrLn $ "✗ Counterexample found:\n" ++ trace
        Timeout -> putStrLn "⚠ Solver timed out"
        CompilationError err -> putStrLn $ "✗ Compilation error: " ++ err
        HevmError err -> putStrLn $ "✗ hevm error: " ++ err

{-|
  Comparison with Strategy 2 (Custom Yul Parser):

  Pros of hevm:
  - ✅ Battle-tested in production
  - ✅ Handles complex EVM semantics automatically
  - ✅ Built-in SMT solver integration
  - ✅ Counterexample generation
  - ✅ Works directly on bytecode (no parser needed)

  Cons of hevm:
  - ❌ Less control over VC generation
  - ❌ Dependency on external binary
  - ❌ GHC version compatibility issues
  - ❌ Heavier-weight solution

  When to use hevm:
  - Verifying real-world contracts
  - Need comprehensive EVM semantics
  - Want proven, reliable tool
  - Don't need custom VC algorithm
-}
