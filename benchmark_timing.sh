#!/bin/bash

# Benchmark timing script for intuition prover
# Compares performance with popular SMT/theorem provers

INTUITION="./dist-newstyle/build/x86_64-linux/ghc-8.10.7/intuition-0.3.0.1/x/intuition/build/intuition/intuition"
TEST_DIR="tests/simple"
RESULTS_FILE="benchmark_results.txt"

echo "========================================" > $RESULTS_FILE
echo "Intuition Prover Timing Benchmarks" >> $RESULTS_FILE
echo "Date: $(date)" >> $RESULTS_FILE
echo "========================================" >> $RESULTS_FILE
echo "" >> $RESULTS_FILE

# Function to run a test multiple times and get average
run_test() {
    local file=$1
    local name=$(basename $file)
    local runs=10
    local total=0

    echo "Testing: $name" | tee -a $RESULTS_FILE

    for i in $(seq 1 $runs); do
        result=$( { time $INTUITION -f "$file" > /dev/null 2>&1; } 2>&1 | grep real | awk '{print $2}' )
        # Convert time to milliseconds
        ms=$(echo $result | sed 's/0m//' | sed 's/s//' | awk '{print $1 * 1000}')
        total=$(echo "$total + $ms" | bc)
    done

    avg=$(echo "scale=3; $total / $runs" | bc)
    echo "  Average time: ${avg}ms (over $runs runs)" | tee -a $RESULTS_FILE
    echo "$name,$avg" >> timing_data.csv
}

# Create CSV header
echo "test,time_ms" > timing_data.csv

echo "=== Valid Formulas (dobry-*.p) ===" | tee -a $RESULTS_FILE
for file in $TEST_DIR/dobry-*.p; do
    if [ -f "$file" ]; then
        run_test "$file"
    fi
done

echo "" | tee -a $RESULTS_FILE
echo "=== Invalid Formulas (zly-*.p) ===" | tee -a $RESULTS_FILE
for file in $TEST_DIR/zly-*.p; do
    if [ -f "$file" ]; then
        run_test "$file"
    fi
done

echo "" | tee -a $RESULTS_FILE
echo "Benchmark complete. Results saved to $RESULTS_FILE and timing_data.csv"
