#!/bin/bash
# Verification script for all Yul examples
# Runs yulvcgen on each example and aggregates results

YULVCGEN="./dist-newstyle/build/x86_64-linux/ghc-9.6.6/vcgen-0.1.0.0/build/yulvcgen/yulvcgen"

if [ ! -f "$YULVCGEN" ]; then
  echo "Error: yulvcgen not found. Please run 'cabal build yulvcgen' first."
  exit 1
fi

echo "========================================"
echo "  Yul Assertion Verification Report"
echo "========================================"
echo "Date: $(date +"%Y-%m-%d %H:%M:%S")"
echo ""

# Counters
total_examples=0
total_assertions=0
total_verifiable=0
total_smt=0

# Process each example
for file in examples/*.yul; do
  if [ ! -f "$file" ]; then
    continue
  fi

  total_examples=$((total_examples + 1))
  name=$(basename "$file")

  echo "----------------------------------------"
  echo "Example: $name"
  echo "----------------------------------------"

  # Run verification
  result=$($YULVCGEN < "$file" 2>&1)

  # Extract statistics
  found=$(echo "$result" | grep "^Found" | grep -oE '[0-9]+' | head -1)
  verifiable=$(echo "$result" | grep "Verifiable by Intuition" | grep -oE '[0-9]+ \(' | grep -oE '[0-9]+' | head -1)
  smt_needed=$(echo "$result" | grep "Require SMT" | grep -oE '[0-9]+ \(' | grep -oE '[0-9]+' | head -1)

  # Default to 0 if empty
  found=${found:-0}
  verifiable=${verifiable:-0}
  smt_needed=${smt_needed:-0}

  echo "Assertions found: $found"
  echo "  ✓ Verifiable by Intuition Prover: $verifiable"
  echo "  ⚠ Require SMT solver: $smt_needed"

  # Show verifiable assertions
  if [ "$verifiable" -gt 0 ]; then
    echo ""
    echo "Verifiable Assertions:"
    echo "$result" | awk '/=== Assertion/,/^$/' | grep -B 2 -A 5 "Verifiable: True" | grep -E "(Assertion [0-9]|Formula:|Verification Condition:)" | sed 's/^/  /'
  fi

  echo ""

  # Update totals
  total_assertions=$((total_assertions + found))
  total_verifiable=$((total_verifiable + verifiable))
  total_smt=$((total_smt + smt_needed))
done

# Calculate percentages
if [ $total_assertions -gt 0 ]; then
  percent_verifiable=$((total_verifiable * 100 / total_assertions))
  percent_smt=$((total_smt * 100 / total_assertions))
else
  percent_verifiable=0
  percent_smt=0
fi

# Print summary
echo "========================================"
echo "  SUMMARY"
echo "========================================"
echo "Examples analyzed: $total_examples"
echo "Total assertions: $total_assertions"
echo ""
echo "✓ Verifiable by Intuition Prover: $total_verifiable ($percent_verifiable%)"
echo "  - Pure propositional logic"
echo "  - Fast verification (~5ms)"
echo "  - No arithmetic needed"
echo ""
echo "⚠ Require SMT solver: $total_smt ($percent_smt%)"
echo "  - Arithmetic comparisons (>, <, =)"
echo "  - Slower verification (~100ms)"
echo "  - Need Z3/CVC5"
echo ""

# Recommendations
echo "========================================"
echo "  RECOMMENDATIONS"
echo "========================================"

if [ $total_verifiable -gt 0 ]; then
  echo "✅ ${total_verifiable} assertions can be verified quickly with Intuition Prover"
  echo "   Run: intuition -f <generated_tptp_file>"
fi

if [ $total_smt -gt 0 ]; then
  echo "⚡ ${total_smt} assertions need SMT solver for full verification"
  echo "   Consider: Z3, CVC5, or Solidity SMTChecker"
fi

echo ""
echo "For hybrid approach: use Intuition as fast pre-check,"
echo "then SMT for full arithmetic verification."
echo "========================================"
