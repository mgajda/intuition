#!/bin/bash
# Benchmark QF_BV implementation on existing Yul files
# Uses pre-compiled Yul files from disl_results/

set -euo pipefail

RESULTS_DIR="disl_results"
QFBV_RESULTS="qfbv_results"
YULVCGEN="./dist-newstyle/build/x86_64-linux/ghc-9.6.6/vcgen-0.1.0.0/build/yulvcgen/yulvcgen"
TIMING_FILE="$QFBV_RESULTS/timings.csv"
JOBS=${1:-12}  # Default to 12 parallel jobs
SAMPLE=${2:-""}  # Optional: number of contracts to sample

mkdir -p "$QFBV_RESULTS"
rm -f "$TIMING_FILE"
echo "filename,verify_time_ms,assertions,verified,status" > "$TIMING_FILE"

echo "=== QF_BV Benchmark ===" | tee "$QFBV_RESULTS/summary.txt"
echo "Date: $(date)" | tee -a "$QFBV_RESULTS/summary.txt"
echo "Binary: $YULVCGEN" | tee -a "$QFBV_RESULTS/summary.txt"
echo "Parallel jobs: $JOBS" | tee -a "$QFBV_RESULTS/summary.txt"
if [ -n "$SAMPLE" ]; then
    echo "Sample mode: $SAMPLE contracts" | tee -a "$QFBV_RESULTS/summary.txt"
fi
echo "" | tee -a "$QFBV_RESULTS/summary.txt"

# Get list of Yul files
YUL_FILES=()
if [ -n "$SAMPLE" ]; then
    mapfile -t YUL_FILES < <(safefind "$RESULTS_DIR" -name "*.yul" -type f | head -n "$SAMPLE")
else
    mapfile -t YUL_FILES < <(safefind "$RESULTS_DIR" -name "*.yul" -type f)
fi

TOTAL=${#YUL_FILES[@]}
echo "Processing $TOTAL contracts with $JOBS parallel jobs..." | tee -a "$QFBV_RESULTS/summary.txt"
echo "Start time: $(date)" | tee -a "$QFBV_RESULTS/summary.txt"
echo "" | tee -a "$QFBV_RESULTS/summary.txt"

# Function to process a single contract
process_contract() {
    local yul_file="$1"
    local filename
    filename=$(basename "$yul_file" .yul)
    local result_file="$QFBV_RESULTS/${filename}_result.txt"

    local start
    start=$(date +%s%3N)

    # Run verification
    if timeout 120 "$YULVCGEN" < "$yul_file" > "$result_file" 2>&1; then
        local end
        end=$(date +%s%3N)
        local time_ms=$((end - start))

        # Count assertions
        local assertions
        assertions=$(grep -c "=== Assertion" "$result_file" 2>/dev/null || echo 0)

        # Count verified assertions (looking for "Assertion verified" or similar)
        local verified
        verified=$(grep -c "VERIFIED" "$result_file" 2>/dev/null || echo 0)

        # Determine status
        local status="success"
        if [ "$assertions" -eq 0 ]; then
            status="no_assertions"
        elif grep -q "Parse Failed" "$result_file"; then
            status="parse_failed"
        fi

        echo "${filename},${time_ms},${assertions},${verified},${status}" >> "$TIMING_FILE"

    else
        local end
        end=$(date +%s%3N)
        local time_ms=$((end - start))

        echo "${filename},${time_ms},0,0,timeout" >> "$TIMING_FILE"
    fi
}

export -f process_contract
export YULVCGEN QFBV_RESULTS TIMING_FILE

# Process in parallel
printf '%s\n' "${YUL_FILES[@]}" | xargs -P "$JOBS" -I {} bash -c 'process_contract "$@"' _ {}

echo "" | tee -a "$QFBV_RESULTS/summary.txt"
echo "End time: $(date)" | tee -a "$QFBV_RESULTS/summary.txt"
echo "" | tee -a "$QFBV_RESULTS/summary.txt"

# Analyze results
echo "=== Analysis ===" | tee -a "$QFBV_RESULTS/summary.txt"

awk -F, '
NR>1 {
    status[$5]++
    if($5=="success") {
        total_assertions += $3
        verified_assertions += $4
        total_time += $2
        count++
    }
}
END {
    print "Status breakdown:"
    for(s in status)
        printf "  %s: %d\n", s, status[s]

    print ""
    print "Verification metrics:"
    printf "  Total assertions: %d\n", total_assertions
    printf "  Verified assertions: %d\n", verified_assertions
    if(total_assertions > 0)
        printf "  Verification rate: %.1f%%\n", verified_assertions*100.0/total_assertions

    print ""
    print "Performance:"
    if(count > 0) {
        printf "  Average time: %.1fms\n", total_time/count
        printf "  Contracts with assertions: %d\n", count
    }
}' "$TIMING_FILE" | tee -a "$QFBV_RESULTS/summary.txt"

echo "" | tee -a "$QFBV_RESULTS/summary.txt"
echo "Detailed results in: $QFBV_RESULTS/" | tee -a "$QFBV_RESULTS/summary.txt"
