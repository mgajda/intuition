#!/bin/bash
# Performance benchmark: QF_LIA vs QF_BV timing with Z3

set -e

YULVCGEN="./dist-newstyle/build/x86_64-linux/ghc-9.6.6/vcgen-0.1.0.0/build/yulvcgen/yulvcgen"
Z3="z3"

echo "=== QF_LIA vs QF_BV Performance Benchmark ==="
echo ""
echo "Z3 Version:"
z3 --version
echo ""

# Test cases
TESTS=(
    "test_qflia_simple.yul:Linear arithmetic (QF_LIA)"
    "test_qfbv_div_inline.yul:Division (QF_BV)"
    "test_qfbv_shift_inline.yul:Shift operations (QF_BV)"
)

for test_entry in "${TESTS[@]}"; do
    IFS=':' read -r test_file description <<< "$test_entry"

    if [ ! -f "$test_file" ]; then
        echo "⚠️  Test file not found: $test_file"
        continue
    fi

    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "Test: $description"
    echo "File: $test_file"
    echo ""

    # Generate VC
    echo "1. VC Generation:"
    time_vc_start=$(date +%s%N)
    $YULVCGEN "$test_file" > /dev/null 2>&1 || true
    time_vc_end=$(date +%s%N)
    time_vc=$((($time_vc_end - $time_vc_start) / 1000000))  # Convert to milliseconds

    echo "   Time: ${time_vc}ms"

    # Find generated SMT files
    smt_files=$(find . -maxdepth 1 -name "vc_*.smt2" -newer "$test_file" 2>/dev/null | sort)

    if [ -z "$smt_files" ]; then
        echo "   ⚠️  No VCs generated"
        continue
    fi

    vc_count=$(echo "$smt_files" | wc -l)
    echo "   Generated: $vc_count VC(s)"
    echo ""

    # Analyze each VC
    for smt_file in $smt_files; do
        # Extract logic from SMT file
        logic=$(grep "set-logic" "$smt_file" | sed 's/.*(set-logic \([^)]*\)).*/\1/')

        # Check classification comments
        classification=$(grep "; Classification:" "$smt_file" | sed 's/.*: //')
        reason=$(grep "; Reason:" "$smt_file" | sed 's/.*: //')

        echo "   VC: $(basename $smt_file)"
        echo "   Logic: $logic"
        echo "   Classification: $classification"
        if [ -n "$reason" ]; then
            echo "   Reason: $reason"
        fi

        # Time Z3 solving (10 runs for average)
        echo -n "   Z3 solving (10 runs): "

        total_time=0
        for i in {1..10}; do
            time_z3_start=$(date +%s%N)
            result=$($Z3 "$smt_file" 2>/dev/null | head -1)
            time_z3_end=$(date +%s%N)
            run_time=$((($time_z3_end - $time_z3_start) / 1000000))
            total_time=$(($total_time + $run_time))
        done

        avg_time=$(($total_time / 10))

        echo "${avg_time}ms avg"
        echo "   Result: $result"
        echo ""
    done
done

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "=== Summary ==="
echo ""
echo "Expected findings:"
echo "- QF_LIA: Fast (Cooper's algorithm decidable)"
echo "- QF_BV: Potentially slower (bit-blasting)"
echo "- Routing overhead: Negligible (classification is O(n) tree walk)"
echo ""
echo "Note: Both logics solve these simple examples very quickly."
echo "Performance differences emerge on complex VCs with many operations."
