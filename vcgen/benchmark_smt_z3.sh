#!/bin/bash
# Benchmark SMT files with Z3
# Compares QF_LIA vs QF_BV performance and success rate

set -euo pipefail

RESULTS_FILE="z3_benchmark_results.csv"
SUMMARY_FILE="z3_benchmark_summary.txt"

echo "filename,logic,result,time_ms,error" > "$RESULTS_FILE"

echo "=== Z3 Benchmark on SMT Files ===" | tee "$SUMMARY_FILE"
echo "Date: $(date)" | tee -a "$SUMMARY_FILE"
echo "Z3 Version: $(z3 --version)" | tee -a "$SUMMARY_FILE"
echo "" | tee -a "$SUMMARY_FILE"

# Find all SMT files
SMT_FILES=(vc_*.smt2)

echo "Testing ${#SMT_FILES[@]} SMT files..." | tee -a "$SUMMARY_FILE"
echo "" | tee -a "$SUMMARY_FILE"

for smt_file in "${SMT_FILES[@]}"; do
    # Determine logic from file
    logic=$(grep "set-logic" "$smt_file" | head -1 | sed 's/.*(set-logic \([^)]*\)).*/\1/' || echo "unknown")

    # Run Z3 with timeout
    start=$(date +%s%3N)

    if result=$(timeout 10 z3 "$smt_file" 2>&1); then
        end=$(date +%s%3N)
        time_ms=$((end - start))

        # Extract first word (sat/unsat/unknown)
        status=$(echo "$result" | head -1)

        echo "${smt_file},${logic},${status},${time_ms}," >> "$RESULTS_FILE"

        if [ "$status" = "sat" ] || [ "$status" = "unsat" ]; then
            echo "  ✓ $smt_file ($logic): $status (${time_ms}ms)"
        else
            echo "  ⚠ $smt_file ($logic): $status (${time_ms}ms)"
        fi
    else
        end=$(date +%s%3N)
        time_ms=$((end - start))

        # Check for error
        error=$(echo "$result" | grep -i "error" | head -1 || echo "timeout")

        echo "${smt_file},${logic},timeout,${time_ms},${error}" >> "$RESULTS_FILE"
        echo "  ✗ $smt_file ($logic): timeout/error (${time_ms}ms)"
    fi
done

echo "" | tee -a "$SUMMARY_FILE"
echo "=== Results Analysis ===" | tee -a "$SUMMARY_FILE"
echo "" | tee -a "$SUMMARY_FILE"

# Analyze results by logic
awk -F, '
NR>1 {
    logic[$2]++;
    result_count[$2","$3]++;
    if($3 == "sat" || $3 == "unsat") {
        solved[$2]++;
        total_time[$2] += $4;
    }
    if($3 == "sat" || $3 == "unsat" || $3 == "unknown" || $3 == "timeout") {
        total[$2]++;
    }
}
END {
    print "By Logic:";
    for(l in logic) {
        printf "\n%s:\n", l;
        printf "  Total: %d\n", total[l];
        printf "  Solved (sat/unsat): %d (%.1f%%)\n", solved[l], solved[l]*100.0/total[l];
        if(solved[l] > 0)
            printf "  Average time: %.1fms\n", total_time[l]/solved[l];

        printf "  Breakdown:\n";
        for(r in result_count) {
            split(r, parts, ",");
            if(parts[1] == l)
                printf "    %s: %d\n", parts[2], result_count[r];
        }
    }

    print "\n\nComparison:";
    if(total["QF_LIA"] > 0 && total["QF_BV"] > 0) {
        printf "  QF_LIA success rate: %.1f%% (%d/%d)\n",
               solved["QF_LIA"]*100.0/total["QF_LIA"], solved["QF_LIA"], total["QF_LIA"];
        printf "  QF_BV success rate: %.1f%% (%d/%d)\n",
               solved["QF_BV"]*100.0/total["QF_BV"], solved["QF_BV"], total["QF_BV"];

        if(solved["QF_LIA"] > 0 && solved["QF_BV"] > 0) {
            printf "  QF_LIA avg time: %.1fms\n", total_time["QF_LIA"]/solved["QF_LIA"];
            printf "  QF_BV avg time: %.1fms\n", total_time["QF_BV"]/solved["QF_BV"];
        }
    }
}' "$RESULTS_FILE" | tee -a "$SUMMARY_FILE"

echo "" | tee -a "$SUMMARY_FILE"
echo "Detailed results in: $RESULTS_FILE" | tee -a "$SUMMARY_FILE"
