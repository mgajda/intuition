#!/bin/bash

# Comparative benchmark script
# Compares intuition prover with E-prover on TPTP problems

INTUITION="./dist-newstyle/build/x86_64-linux/ghc-8.10.7/intuition-0.3.0.1/x/intuition/build/intuition/intuition"
EPROVER="eprover"
TEST_DIR="tests/simple"
RESULTS_FILE="comparative_results.txt"

echo "========================================" > $RESULTS_FILE
echo "Comparative Theorem Prover Benchmarks" >> $RESULTS_FILE
echo "Date: $(date)" >> $RESULTS_FILE
echo "========================================" >> $RESULTS_FILE
echo "" >> $RESULTS_FILE
echo "Provers tested:" >> $RESULTS_FILE
echo "  - Intuition: Custom intuitionistic logic prover" >> $RESULTS_FILE
echo "  - E-prover $(eprover --version 2>&1 | head -1): Classical FOL theorem prover" >> $RESULTS_FILE
echo "" >> $RESULTS_FILE

# Create CSV header
echo "test,intuition_ms,eprover_ms,intuition_result,eprover_result,speedup" > comparison_data.csv

# Function to run intuition test
run_intuition() {
    local file=$1
    local runs=5
    local total=0

    for i in $(seq 1 $runs); do
        result=$( { time $INTUITION -f "$file" > /tmp/intuition_out.txt 2>&1; } 2>&1 | grep real | awk '{print $2}' )
        ms=$(echo $result | sed 's/0m//' | sed 's/s//' | awk '{print $1 * 1000}')
        total=$(echo "$total + $ms" | bc)
    done

    avg=$(echo "scale=3; $total / $runs" | bc)

    # Get result
    if grep -q "Just (MInt" /tmp/intuition_out.txt; then
        result_type="PROVED"
    elif grep -q "Nothing" /tmp/intuition_out.txt; then
        result_type="DISPROVED"
    else
        result_type="ERROR"
    fi

    echo "${avg}|${result_type}"
}

# Function to run E-prover test
run_eprover() {
    local file=$1
    local runs=5
    local total=0

    for i in $(seq 1 $runs); do
        # E-prover with timeout of 10 seconds, auto mode
        result=$( { time timeout 10s $EPROVER --auto "$file" > /tmp/eprover_out.txt 2>&1; } 2>&1 | grep real | awk '{print $2}' )
        ms=$(echo $result | sed 's/0m//' | sed 's/s//' | awk '{print $1 * 1000}')
        total=$(echo "$total + $ms" | bc)
    done

    avg=$(echo "scale=3; $total / $runs" | bc)

    # Get result
    if grep -q "Proof found!" /tmp/eprover_out.txt; then
        result_type="PROVED"
    elif grep -q "No proof found!" /tmp/eprover_out.txt || grep -q "Failure" /tmp/eprover_out.txt; then
        result_type="NO_PROOF"
    elif grep -q "Timeout" /tmp/eprover_out.txt; then
        result_type="TIMEOUT"
    else
        result_type="UNKNOWN"
    fi

    echo "${avg}|${result_type}"
}

# Run comparative tests
echo "=== Valid Formulas (dobry-*.p) ===" | tee -a $RESULTS_FILE
echo "" | tee -a $RESULTS_FILE
printf "%-25s %15s %15s %15s %15s %10s\n" "Test" "Intuition (ms)" "E-prover (ms)" "Int. Result" "E Result" "Speedup" | tee -a $RESULTS_FILE
printf "%-25s %15s %15s %15s %15s %10s\n" "----" "--------------" "--------------" "-----------" "--------" "-------" | tee -a $RESULTS_FILE

for file in $TEST_DIR/dobry-*.p; do
    if [ -f "$file" ]; then
        name=$(basename $file)

        # Run intuition
        int_result=$(run_intuition "$file")
        int_time=$(echo $int_result | cut -d'|' -f1)
        int_status=$(echo $int_result | cut -d'|' -f2)

        # Run E-prover
        epr_result=$(run_eprover "$file")
        epr_time=$(echo $epr_result | cut -d'|' -f1)
        epr_status=$(echo $epr_result | cut -d'|' -f2)

        # Calculate speedup
        if [ "$epr_time" != "0" ] && [ -n "$epr_time" ]; then
            speedup=$(echo "scale=2; $epr_time / $int_time" | bc)
        else
            speedup="N/A"
        fi

        printf "%-25s %15s %15s %15s %15s %10s\n" "$name" "$int_time" "$epr_time" "$int_status" "$epr_status" "${speedup}x" | tee -a $RESULTS_FILE
        echo "$name,$int_time,$epr_time,$int_status,$epr_status,$speedup" >> comparison_data.csv
    fi
done

echo "" | tee -a $RESULTS_FILE
echo "=== Invalid Formulas (zly-*.p) ===" | tee -a $RESULTS_FILE
echo "" | tee -a $RESULTS_FILE
printf "%-25s %15s %15s %15s %15s %10s\n" "Test" "Intuition (ms)" "E-prover (ms)" "Int. Result" "E Result" "Speedup" | tee -a $RESULTS_FILE
printf "%-25s %15s %15s %15s %15s %10s\n" "----" "--------------" "--------------" "-----------" "--------" "-------" | tee -a $RESULTS_FILE

for file in $TEST_DIR/zly-*.p; do
    if [ -f "$file" ]; then
        name=$(basename $file)

        # Run intuition
        int_result=$(run_intuition "$file")
        int_time=$(echo $int_result | cut -d'|' -f1)
        int_status=$(echo $int_result | cut -d'|' -f2)

        # Run E-prover
        epr_result=$(run_eprover "$file")
        epr_time=$(echo $epr_result | cut -d'|' -f1)
        epr_status=$(echo $epr_result | cut -d'|' -f2)

        # Calculate speedup
        if [ "$epr_time" != "0" ] && [ -n "$epr_time" ]; then
            speedup=$(echo "scale=2; $epr_time / $int_time" | bc)
        else
            speedup="N/A"
        fi

        printf "%-25s %15s %15s %15s %15s %10s\n" "$name" "$int_time" "$epr_time" "$int_status" "$epr_status" "${speedup}x" | tee -a $RESULTS_FILE
        echo "$name,$int_time,$epr_time,$int_status,$epr_status,$speedup" >> comparison_data.csv
    fi
done

echo "" | tee -a $RESULTS_FILE
echo "Notes:" | tee -a $RESULTS_FILE
echo "- Intuition is an intuitionistic logic prover" | tee -a $RESULTS_FILE
echo "- E-prover is a classical first-order logic theorem prover" | tee -a $RESULTS_FILE
echo "- Problems marked 'dobry' should be theorems in intuitionistic logic" | tee -a $RESULTS_FILE
echo "- Problems marked 'zly' should NOT be theorems in intuitionistic logic" | tee -a $RESULTS_FILE
echo "- E-prover may prove some 'zly' problems (classically valid but not intuitionistically)" | tee -a $RESULTS_FILE
echo "" | tee -a $RESULTS_FILE
echo "Results saved to $RESULTS_FILE and comparison_data.csv"
