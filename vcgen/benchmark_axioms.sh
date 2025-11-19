#!/bin/bash
# Benchmark script for theory-axioms approach
# Tests all generated TPTP files with available provers

echo "=== Theory Axioms Verification Benchmark ==="
echo "Date: $(date)"
echo ""

# Check available provers
PROVERS=""
if command -v eprover &> /dev/null; then
    PROVERS="$PROVERS eprover"
fi
if command -v vampire &> /dev/null; then
    PROVERS="$PROVERS vampire"
fi
if [ -z "$PROVERS" ]; then
    echo "❌ No FOL theorem provers found (need eprover or vampire)"
    exit 1
fi

echo "Available provers: $PROVERS"
echo ""

# Generate fresh TPTP files
echo "=== Generating TPTP files with axioms ==="
for file in examples/*.yul; do
    echo "Processing $(basename $file)..."
    ./dist-newstyle/build/x86_64-linux/ghc-9.6.6/vcgen-0.1.0.0/build/yulvcgen/yulvcgen < "$file" > /dev/null 2>&1
done
echo ""

# Count generated VCs
VC_COUNT=$(ls vc_*.p 2>/dev/null | wc -l)
echo "Generated $VC_COUNT verification conditions"
echo ""

# Test each VC with each prover
TOTAL_VERIFIED=0
TOTAL_FAILED=0
TOTAL_TIMEOUT=0

for vc in vc_*.p; do
    echo "=== Testing $vc ==="

    # Show what this VC is about
    grep "% Location:" "$vc" | head -1
    grep "fof(vc, conjecture" "$vc"

    for prover in $PROVERS; do
        echo -n "  $prover: "

        # Run prover with timeout
        case $prover in
            eprover)
                RESULT=$(timeout 5 eprover --auto --silent "$vc" 2>&1)
                ;;
            vampire)
                RESULT=$(timeout 5 vampire --mode casc "$vc" 2>&1)
                ;;
        esac

        # Check result
        if echo "$RESULT" | grep -q "Theorem\|Proof found\|SZS status Theorem"; then
            echo "✅ VERIFIED"
            TOTAL_VERIFIED=$((TOTAL_VERIFIED + 1))
        elif echo "$RESULT" | grep -q "CounterSatisfiable\|SZS status CounterSatisfiable"; then
            echo "❌ FALSIFIABLE"
            TOTAL_FAILED=$((TOTAL_FAILED + 1))
        elif echo "$RESULT" | grep -q "Timeout\|ResourceOut"; then
            echo "⏱️  TIMEOUT"
            TOTAL_TIMEOUT=$((TOTAL_TIMEOUT + 1))
        else
            echo "❓ UNKNOWN ($(echo "$RESULT" | head -1 | cut -c1-50))"
            TOTAL_TIMEOUT=$((TOTAL_TIMEOUT + 1))
        fi
    done
    echo ""
done

# Summary
echo "=== Summary ==="
echo "Total VCs: $VC_COUNT"
echo "Verified: $TOTAL_VERIFIED"
echo "Falsifiable: $TOTAL_FAILED"
echo "Timeout/Unknown: $TOTAL_TIMEOUT"
echo ""

if [ $TOTAL_VERIFIED -gt 0 ]; then
    SUCCESS_RATE=$((TOTAL_VERIFIED * 100 / VC_COUNT))
    echo "✅ Success rate: $SUCCESS_RATE%"
else
    echo "❌ No proofs found"
fi
