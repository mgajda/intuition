#!/bin/bash

# Comprehensive SAT solver benchmark
# Compares Kissat (2024 winner), Glucose, CaDiCaL, MiniSat, and PicoSAT

KISSAT="/tmp/kissat/build/kissat"
GLUCOSE="/tmp/glucose/simp/glucose"
CADICAL="/tmp/cadical/build/cadical"
MINISAT="minisat"
PICOSAT="picosat"

RESULTS_FILE="sat_comprehensive_results.txt"

echo "========================================" > $RESULTS_FILE
echo "Comprehensive SAT Solver Benchmarks" >> $RESULTS_FILE
echo "Date: $(date)" >> $RESULTS_FILE
echo "========================================" >> $RESULTS_FILE
echo "" >> $RESULTS_FILE
echo "SAT Solvers tested:" >> $RESULTS_FILE
echo "  - Kissat $($KISSAT --version) (SAT Competition 2024 winner)" >> $RESULTS_FILE
echo "  - Glucose 4.2.1" >> $RESULTS_FILE
echo "  - CaDiCaL $($CADICAL --version | head -1)" >> $RESULTS_FILE
echo "  - MiniSat (classic reference solver)" >> $RESULTS_FILE
echo "  - PicoSAT 965" >> $RESULTS_FILE
echo "" >> $RESULTS_FILE

# CSV header
echo "test,kissat_ms,glucose_ms,cadical_ms,minisat_ms,picosat_ms" > sat_comp_data.csv

run_sat_solver() {
    local solver=$1
    local file=$2
    local runs=10
    local total=0
    local timeout_ms=5000

    for i in $(seq 1 $runs); do
        if [[ "$solver" == "$KISSAT" ]]; then
            result=$( { time timeout 5s $solver --quiet "$file" > /dev/null 2>&1; } 2>&1 | grep real | awk '{print $2}' )
        elif [[ "$solver" == "$GLUCOSE" ]]; then
            result=$( { time timeout 5s $solver "$file" > /dev/null 2>&1; } 2>&1 | grep real | awk '{print $2}' )
        elif [[ "$solver" == "$CADICAL" ]]; then
            result=$( { time timeout 5s $solver --quiet "$file" > /dev/null 2>&1; } 2>&1 | grep real | awk '{print $2}' )
        elif [[ "$solver" == "$MINISAT" ]]; then
            result=$( { time timeout 5s $solver "$file" /tmp/sat_out.txt > /dev/null 2>&1; } 2>&1 | grep real | awk '{print $2}' )
        elif [[ "$solver" == "$PICOSAT" ]]; then
            result=$( { time timeout 5s $solver "$file" > /dev/null 2>&1; } 2>&1 | grep real | awk '{print $2}' )
        fi

        ms=$(echo $result | sed 's/0m//' | sed 's/s//' | awk '{print $1 * 1000}')
        if [ -z "$ms" ]; then
            ms=$timeout_ms
        fi
        total=$(echo "$total + $ms" | bc)
    done

    avg=$(echo "scale=2; $total / $runs" | bc)
    echo "$avg"
}

printf "%-30s %12s %12s %12s %12s %12s\n" "Test" "Kissat(ms)" "Glucose(ms)" "CaDiCaL(ms)" "MiniSat(ms)" "PicoSAT(ms)" | tee -a $RESULTS_FILE
printf "%-30s %12s %12s %12s %12s %12s\n" "----" "-----------" "-----------" "-----------" "-----------" "-----------" | tee -a $RESULTS_FILE

for cnf_file in tests/cnf/*.cnf; do
    if [ -f "$cnf_file" ]; then
        name=$(basename "$cnf_file")

        echo "Testing $name..." >&2

        kissat_time=$(run_sat_solver "$KISSAT" "$cnf_file")
        glucose_time=$(run_sat_solver "$GLUCOSE" "$cnf_file")
        cadical_time=$(run_sat_solver "$CADICAL" "$cnf_file")
        minisat_time=$(run_sat_solver "$MINISAT" "$cnf_file")
        picosat_time=$(run_sat_solver "$PICOSAT" "$cnf_file")

        printf "%-30s %12s %12s %12s %12s %12s\n" "$name" "$kissat_time" "$glucose_time" "$cadical_time" "$minisat_time" "$picosat_time" | tee -a $RESULTS_FILE
        echo "$name,$kissat_time,$glucose_time,$cadical_time,$minisat_time,$picosat_time" >> sat_comp_data.csv
    fi
done

echo "" | tee -a $RESULTS_FILE
echo "Note: All times in milliseconds, averaged over 10 runs" | tee -a $RESULTS_FILE
echo "These are propositional SAT problems derived from intuitionistic logic test cases" | tee -a $RESULTS_FILE
echo "Results saved to $RESULTS_FILE and sat_comp_data.csv"
