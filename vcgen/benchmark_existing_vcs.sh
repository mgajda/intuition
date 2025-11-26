#!/bin/bash
# Performance benchmark: QF_LIA vs QF_BV on existing VCs

set -e

Z3="z3"

echo "=== QF_LIA vs QF_BV Performance Benchmark ==="
echo ""
echo "Z3 Version:"
z3 --version
echo ""

# Find existing SMT files
smt_files=$(find . -maxdepth 1 -name "vc_*.smt2" 2>/dev/null | sort -V | head -20)

if [ -z "$smt_files" ]; then
    echo "⚠️  No VC files found. Generate some first."
    exit 1
fi

vc_count=$(echo "$smt_files" | wc -l)
echo "Found: $vc_count VCs"
echo ""

# Statistics
qflia_count=0
qfbv_count=0
qflia_total_time=0
qfbv_total_time=0

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Individual VC Timings (5 runs each)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

for smt_file in $smt_files; do
    # Extract logic from SMT file
    logic=$(grep "set-logic" "$smt_file" | sed 's/.*(set-logic \([^)]*\)).*/\1/')

    if [ -z "$logic" ]; then
        continue
    fi

    # Extract classification
    classification=$(grep "; Classification:" "$smt_file" | sed 's/.*: //')

    # Time Z3 solving (5 runs for average)
    total_time=0
    for i in {1..5}; do
        time_z3_start=$(date +%s%N)
        result=$($Z3 "$smt_file" 2>/dev/null | head -1)
        time_z3_end=$(date +%s%N)
        run_time=$((($time_z3_end - $time_z3_start) / 1000000))
        total_time=$(($total_time + $run_time))
    done

    avg_time=$(($total_time / 5))

    printf "%-15s %8s %12s %6dms %s\n" "$(basename $smt_file)" "$logic" "$classification" "$avg_time" "$result"

    # Accumulate stats
    if [ "$logic" = "QF_LIA" ]; then
        qflia_count=$((qflia_count + 1))
        qflia_total_time=$((qflia_total_time + avg_time))
    elif [ "$logic" = "QF_BV" ]; then
        qfbv_count=$((qfbv_count + 1))
        qfbv_total_time=$((qfbv_total_time + avg_time))
    fi
done

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Summary Statistics"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if [ $qflia_count -gt 0 ]; then
    qflia_avg=$((qflia_total_time / qflia_count))
    echo "QF_LIA:"
    echo "  Count: $qflia_count VCs"
    echo "  Total time: ${qflia_total_time}ms"
    echo "  Average: ${qflia_avg}ms per VC"
    echo ""
fi

if [ $qfbv_count -gt 0 ]; then
    qfbv_avg=$((qfbv_total_time / qfbv_count))
    echo "QF_BV:"
    echo "  Count: $qfbv_count VCs"
    echo "  Total time: ${qfbv_total_time}ms"
    echo "  Average: ${qfbv_avg}ms per VC"
    echo ""
fi

if [ $qflia_count -gt 0 ] && [ $qfbv_count -gt 0 ]; then
    qflia_avg=$((qflia_total_time / qflia_count))
    qfbv_avg=$((qfbv_total_time / qfbv_count))

    echo "Comparison:"
    if [ $qfbv_avg -gt 0 ]; then
        ratio=$((qflia_avg * 100 / qfbv_avg))
        echo "  QF_LIA is ${ratio}% the time of QF_BV"

        if [ $qflia_avg -lt $qfbv_avg ]; then
            speedup=$((qfbv_avg * 100 / qflia_avg))
            echo "  QF_LIA is ${speedup}% faster"
        else
            slowdown=$((qflia_avg * 100 / qfbv_avg))
            echo "  QF_BV is ${slowdown}% faster"
        fi
    fi
    echo ""
fi

echo "Interpretation:"
echo "- Both logics solve simple VCs very quickly (<50ms typical)"
echo "- QF_LIA uses Cooper's algorithm (decidable, predictable)"
echo "- QF_BV uses bit-blasting (more expensive for complex operations)"
echo "- Routing overhead is negligible (O(n) tree walk during codegen)"
echo ""
echo "Note: Performance differences become significant on:"
echo "  - Large VCs with many operations"
echo "  - Complex nested expressions"
echo "  - Multiple quantifier alternations (not applicable here)"
