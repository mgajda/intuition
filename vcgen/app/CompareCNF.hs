module Main where

import qualified BitBlast as BB
import Data.List (intercalate)

main :: IO ()
main = do
  putStrLn "=== Comparing Implication vs CNF Encoding Sizes ==="
  putStrLn ""

  -- Test with different bit widths
  let bitWidths = [4, 8, 16, 32, 64, 128, 256]

  putStrLn "Bit-Width,Impl-Size,Impl-Ops,CNF-Clauses,CNF-Literals,CNF-Size,Ratio"

  mapM_ testBitWidth bitWidths

  putStrLn ""
  putStrLn "=== Analysis ==="
  putStrLn ""
  putStrLn "Key observations:"
  putStrLn "- Implication encoding grows with formula complexity"
  putStrLn "- CNF introduces auxiliary variables (Tseitin transformation)"
  putStrLn "- Both are O(n) for n-bit comparisons"
  putStrLn "- Logarithmic tree keeps implication depth at O(log n)"
  putStrLn "- CNF is flat (all clauses at same level)"

testBitWidth :: Int -> IO ()
testBitWidth n = do
  let x = BB.mkBitVector "x" n
      y = BB.mkBitVector "y" n
      formula = BB.bitGt x y

  -- Measure implication encoding
  let implStr = BB.bitFormulaToTPTP formula
      implSize = length implStr
      implOps = countOps implStr

  -- Convert to CNF and measure
  let (cnf, auxVars) = BB.bitFormulaToCNF formula
      (numClauses, numLiterals) = BB.measureCNF cnf
      cnfStr = BB.cnfToTPTP cnf
      cnfSize = length cnfStr
      ratio = if cnfSize > 0
              then fromIntegral implSize / fromIntegral cnfSize :: Double
              else 0.0

  putStrLn $ intercalate "," [
      show n,
      show implSize,
      show implOps,
      show numClauses,
      show numLiterals,
      show cnfSize,
      printf "%.2f" ratio
    ]

-- Count operators in implication formula
countOps :: String -> Int
countOps s = length (filter (`elem` "=>~()") s)

-- Printf helper
printf :: String -> Double -> String
printf _ val = show ((fromIntegral (round (val * 100)) :: Double) / 100)
