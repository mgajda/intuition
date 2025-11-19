#!/bin/bash
# Benchmark script for Presburger arithmetic approach
# Uses Z3 with QF_LIA (Quantifier-Free Linear Integer Arithmetic) logic

echo "=== Presburger Arithmetic Verification Benchmark ==="
echo "Date: $(date)"
echo ""

# Check if Z3 is available
if ! command -v z3 &> /dev/null; then
    echo "❌ Z3 not found. Please install Z3:"
    echo "   sudo apt-get install z3"
    exit 1
fi

Z3_VERSION=$(z3 --version | head -1)
echo "Using: $Z3_VERSION"
echo ""

# Generate SMT-LIB2 files
echo "=== Generating SMT-LIB2 files ==="
for file in examples/*.yul; do
    echo "Processing $(basename $file)..."
    ./dist-newstyle/build/x86_64-linux/ghc-9.6.6/vcgen-0.1.0.0/build/yulvcgen/yulvcgen < "$file" > /dev/null 2>&1
done
echo ""

# Count generated VCs
VC_COUNT=$(ls vc_*.smt2 2>/dev/null | wc -l)
echo "Generated $VC_COUNT verification conditions"
echo ""

# Test each VC with Z3
TOTAL_VERIFIED=0
TOTAL_FALSIFIABLE=0
TOTAL_PRESBURGER=0
TOTAL_NON_PRESBURGER=0

for vc in vc_*.smt2; do
    echo "=== Testing $vc ==="

    # Check if it's Presburger
    if grep -q "Classification: Presburger" "$vc"; then
        echo "  Type: ✅ Presburger (linear arithmetic)"
        TOTAL_PRESBURGER=$((TOTAL_PRESBURGER + 1))
    else
        echo "  Type: ⚠️  Non-Presburger (contains non-linear ops)"
        TOTAL_NON_PRESBURGER=$((TOTAL_NON_PRESBURGER + 1))
    fi

    # Show reason
    REASON=$(grep "Reason:" "$vc" | head -1 | sed 's/^; Reason: //')
    echo "  Reason: $REASON"

    # Run Z3
    echo -n "  Z3 Result: "
    RESULT=$(timeout 5 z3 "$vc" 2>&1)

    if echo "$RESULT" | grep -q "^unsat$"; then
        echo "✅ VERIFIED (assertion holds)"
        TOTAL_VERIFIED=$((TOTAL_VERIFIED + 1))
    elif echo "$RESULT" | grep -q "^sat$"; then
        echo "❌ FALSIFIABLE (counterexample exists)"
        TOTAL_FALSIFIABLE=$((TOTAL_FALSIFIABLE + 1))
    elif echo "$RESULT" | grep -q "^unknown$"; then
        echo "❓ UNKNOWN (Z3 couldn't decide)"
    else
        echo "⚠️  ERROR ($(echo "$RESULT" | head -1 | cut -c1-50))"
    fi
    echo ""
done

# Summary
echo "=== Summary ==="
echo "Total VCs: $VC_COUNT"
echo ""
echo "By Classification:"
echo "  Presburger-decidable: $TOTAL_PRESBURGER ($(( TOTAL_PRESBURGER * 100 / VC_COUNT ))%)"
echo "  Non-Presburger: $TOTAL_NON_PRESBURGER ($(( TOTAL_NON_PRESBURGER * 100 / VC_COUNT ))%)"
echo ""
echo "Verification Results:"
echo "  ✅ Verified: $TOTAL_VERIFIED"
echo "  ❌ Falsifiable: $TOTAL_FALSIFIABLE"
echo "  ❓ Unknown/Error: $(( VC_COUNT - TOTAL_VERIFIED - TOTAL_FALSIFIABLE ))"
echo ""

if [ $TOTAL_VERIFIED -gt 0 ]; then
    SUCCESS_RATE=$((TOTAL_VERIFIED * 100 / VC_COUNT))
    echo "✅ Success rate: $SUCCESS_RATE%"

    if [ $TOTAL_PRESBURGER -gt 0 ]; then
        PRESBURGER_SUCCESS=$((TOTAL_VERIFIED * 100 / TOTAL_PRESBURGER))
        echo "✅ Success rate on Presburger-decidable: $PRESBURGER_SUCCESS%"
    fi
else
    echo "❌ No proofs found"
fi
