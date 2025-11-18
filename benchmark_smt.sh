#!/bin/bash

# SMT solver benchmark script
# Tests Z3 and CVC5 on propositional logic problems

SMTLIB_DIR="tests/smtlib"
RESULTS_FILE="smt_results.txt"

echo "========================================" > $RESULTS_FILE
echo "SMT Solver Benchmarks" >> $RESULTS_FILE
echo "Date: $(date)" >> $RESULTS_FILE
echo "========================================" >> $RESULTS_FILE
echo "" >> $RESULTS_FILE
echo "Solvers tested:" >> $RESULTS_FILE
echo "  - Z3 $(z3 --version)" >> $RESULTS_FILE
cvc5 --version | head -1 >> $RESULTS_FILE
echo "" >> $RESULTS_FILE

# Create CSV header
echo "test,z3_ms,cvc5_ms,z3_result,cvc5_result" > smt_data.csv

# Function to run Z3 test
run_z3() {
    local file=$1
    local runs=10
    local total=0

    for i in $(seq 1 $runs); do
        result=$( { time z3 "$file" > /tmp/z3_out.txt 2>&1; } 2>&1 | grep real | awk '{print $2}' )
        ms=$(echo $result | sed 's/0m//' | sed 's/s//' | awk '{print $1 * 1000}')
        total=$(echo "$total + $ms" | bc)
    done

    avg=$(echo "scale=3; $total / $runs" | bc)

    # Get result
    result_type=$(cat /tmp/z3_out.txt | tr -d '\n')

    echo "${avg}|${result_type}"
}

# Function to run CVC5 test
run_cvc5() {
    local file=$1
    local runs=10
    local total=0

    for i in $(seq 1 $runs); do
        result=$( { time cvc5 "$file" > /tmp/cvc5_out.txt 2>&1; } 2>&1 | grep real | awk '{print $2}' )
        ms=$(echo $result | sed 's/0m//' | sed 's/s//' | awk '{print $1 * 1000}')
        total=$(echo "$total + $ms" | bc)
    done

    avg=$(echo "scale=3; $total / $runs" | bc)

    # Get result
    result_type=$(cat /tmp/cvc5_out.txt | tr -d '\n')

    echo "${avg}|${result_type}"
}

# Run tests
echo "=== Valid Formulas (should be unsat) ===" | tee -a $RESULTS_FILE
echo "" | tee -a $RESULTS_FILE
printf "%-20s %15s %15s %15s %15s\n" "Test" "Z3 (ms)" "CVC5 (ms)" "Z3 Result" "CVC5 Result" | tee -a $RESULTS_FILE
printf "%-20s %15s %15s %15s %15s\n" "----" "--------" "---------" "---------" "-----------" | tee -a $RESULTS_FILE

for file in $SMTLIB_DIR/dobry-*.smt2; do
    if [ -f "$file" ]; then
        name=$(basename $file)

        # Run Z3
        z3_result=$(run_z3 "$file")
        z3_time=$(echo $z3_result | cut -d'|' -f1)
        z3_status=$(echo $z3_result | cut -d'|' -f2)

        # Run CVC5
        cvc5_result=$(run_cvc5 "$file")
        cvc5_time=$(echo $cvc5_result | cut -d'|' -f1)
        cvc5_status=$(echo $cvc5_result | cut -d'|' -f2)

        printf "%-20s %15s %15s %15s %15s\n" "$name" "$z3_time" "$cvc5_time" "$z3_status" "$cvc5_status" | tee -a $RESULTS_FILE
        echo "$name,$z3_time,$cvc5_time,$z3_status,$cvc5_status" >> smt_data.csv
    fi
done

echo "" | tee -a $RESULTS_FILE
echo "=== Invalid in Intuitionistic Logic (classically valid) ===" | tee -a $RESULTS_FILE
echo "" | tee -a $RESULTS_FILE
printf "%-20s %15s %15s %15s %15s\n" "Test" "Z3 (ms)" "CVC5 (ms)" "Z3 Result" "CVC5 Result" | tee -a $RESULTS_FILE
printf "%-20s %15s %15s %15s %15s\n" "----" "--------" "---------" "---------" "-----------" | tee -a $RESULTS_FILE

for file in $SMTLIB_DIR/zly-*.smt2; do
    if [ -f "$file" ]; then
        name=$(basename $file)

        # Run Z3
        z3_result=$(run_z3 "$file")
        z3_time=$(echo $z3_result | cut -d'|' -f1)
        z3_status=$(echo $z3_result | cut -d'|' -f2)

        # Run CVC5
        cvc5_result=$(run_cvc5 "$file")
        cvc5_time=$(echo $cvc5_result | cut -d'|' -f1)
        cvc5_status=$(echo $cvc5_result | cut -d'|' -f2)

        printf "%-20s %15s %15s %15s %15s\n" "$name" "$z3_time" "$cvc5_time" "$z3_status" "$cvc5_status" | tee -a $RESULTS_FILE
        echo "$name,$z3_time,$cvc5_time,$z3_status,$cvc5_status" >> smt_data.csv
    fi
done

echo "" | tee -a $RESULTS_FILE
echo "Note: SMT solvers use classical logic, so 'zly' problems will be proven valid (unsat)" | tee -a $RESULTS_FILE
echo "Results saved to $RESULTS_FILE and smt_data.csv"
