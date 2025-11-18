#!/bin/bash

# Benchmark: Intuition Prover vs Solidity SMTChecker
# Measures completeness and time on smart contract assertions

set +e

echo "════════════════════════════════════════════════════════════"
echo "Verification Benchmark: Intuition vs SMTChecker"
echo "Time limit: 10 seconds per assertion"
echo "════════════════════════════════════════════════════════════"
echo ""

# Paths
INTUITION="../dist-newstyle/build/x86_64-linux/ghc-8.10.7/intuition-0.3.0.1/x/intuition/build/intuition/intuition"
RESULTS_DIR="benchmark_results"
mkdir -p "$RESULTS_DIR"

# Counters
intuition_proved=0
intuition_failed=0
intuition_total_time=0

smtchecker_proved=0
smtchecker_failed=0
smtchecker_timeout=0
smtchecker_total_time=0

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "═══ Part 1: Intuition Prover on Propositional Abstractions ═══"
echo ""

test_intuition() {
    local name=$1
    local file=$2

    printf "%-40s " "$name"

    start_time=$(date +%s.%N)
    $INTUITION -f "$file" > "$RESULTS_DIR/intuition_$name.log" 2>&1 || true
    end_time=$(date +%s.%N)

    elapsed=$(echo "$end_time - $start_time" | bc)
    intuition_total_time=$(echo "$intuition_total_time + $elapsed" | bc)

    if grep -q "Just (MInt" "$RESULTS_DIR/intuition_$name.log"; then
        echo -e "${GREEN}✓ PROVED${NC} (${elapsed}s)"
        ((intuition_proved++))
    else
        echo -e "${RED}✗ FAILED${NC} (${elapsed}s)"
        ((intuition_failed++))
    fi
}

# Test all propositional formulas
test_intuition "Ownable auth" "../tests/solidity/01_ownable.p"
test_intuition "Pausable state" "../tests/solidity/02_pausable.p"
test_intuition "Escrow no double release" "../tests/solidity/03_escrow.p"
test_intuition "Voting no double vote" "../tests/solidity/04_voting.p"
test_intuition "MultiSig confirmation" "../tests/solidity/05_multisig.p"
test_intuition "State transitivity" "../tests/solidity/06_state_invariant.p"
test_intuition "Require precondition" "../tests/solidity/07_require_logic.p"
test_intuition "Assert postcondition" "../tests/solidity/08_assert_logic.p"
test_intuition "Balance conservation" "../tests/solidity/09_conservation.p"
test_intuition "Control flow composition" "../tests/solidity/10_control_flow.p"

echo ""
echo "═══ Part 2: Solidity SMTChecker on Full Contracts ═══"
echo ""

if ! command -v solc &> /dev/null; then
    echo -e "${YELLOW}⚠ solc not found - skipping SMTChecker tests${NC}"
    echo "Install with: sudo apt-get install solc"
    echo ""
else
    SOLC_VERSION=$(solc --version | head -1)
    echo "Using: $SOLC_VERSION"
    echo ""

    test_smtchecker() {
        local name=$1
        local file=$2

        printf "%-40s " "$name"

        start_time=$(date +%s.%N)

        # Run SMTChecker (solc sets its own timeout via --model-checker-timeout)
        solc --model-checker-engine chc \
             --model-checker-targets assert \
             --model-checker-timeout 10000 \
             "$file" > "$RESULTS_DIR/smt_$name.log" 2>&1 || true

        end_time=$(date +%s.%N)
        elapsed=$(echo "$end_time - $start_time" | bc)
        smtchecker_total_time=$(echo "$smtchecker_total_time + $elapsed" | bc)

        if grep -q "CHC: Success" "$RESULTS_DIR/smt_$name.log"; then
            echo -e "${GREEN}✓ PROVED${NC} (${elapsed}s)"
            ((smtchecker_proved++))
        elif grep -q "Assertion violation" "$RESULTS_DIR/smt_$name.log"; then
            echo -e "${YELLOW}✗ COUNTEREXAMPLE${NC} (${elapsed}s)"
            ((smtchecker_failed++))
        elif grep -q "timeout" "$RESULTS_DIR/smt_$name.log"; then
            echo -e "${YELLOW}⏱ TIMEOUT${NC} (${elapsed}s)"
            ((smtchecker_timeout++))
        else
            echo -e "${RED}✗ FAILED${NC} (${elapsed}s)"
            ((smtchecker_failed++))
        fi
    }

    test_smtchecker "SimpleERC20" "../examples/test-contracts/01_SimpleERC20.sol"
    test_smtchecker "SafeMath" "../examples/test-contracts/02_SafeMath.sol"
    test_smtchecker "Ownable" "../examples/test-contracts/03_Ownable.sol"
    test_smtchecker "Pausable" "../examples/test-contracts/04_Pausable.sol"
    test_smtchecker "SimpleAuction" "../examples/test-contracts/05_SimpleAuction.sol"
    test_smtchecker "Escrow" "../examples/test-contracts/06_Escrow.sol"
    test_smtchecker "Voting" "../examples/test-contracts/07_Voting.sol"
    test_smtchecker "MultiSig" "../examples/test-contracts/08_MultiSig.sol"
    test_smtchecker "TokenVesting" "../examples/test-contracts/09_TokenVesting.sol"
    test_smtchecker "SimpleDEX" "../examples/test-contracts/10_SimpleDEX.sol"
fi

echo ""
echo "════════════════════════════════════════════════════════════"
echo "RESULTS SUMMARY"
echo "════════════════════════════════════════════════════════════"
echo ""

echo "Intuition Prover (Propositional Logic):"
echo "  Proved:      $intuition_proved / 10"
echo "  Failed:      $intuition_failed / 10"
echo "  Total Time:  ${intuition_total_time}s"
echo "  Avg Time:    $(echo "scale=3; $intuition_total_time / 10" | bc)s per formula"
echo ""

if command -v solc &> /dev/null; then
    smtchecker_total=$((smtchecker_proved + smtchecker_failed + smtchecker_timeout))
    echo "Solidity SMTChecker (Full Arithmetic):"
    echo "  Proved:      $smtchecker_proved / $smtchecker_total"
    echo "  Failed:      $smtchecker_failed / $smtchecker_total"
    echo "  Timeout:     $smtchecker_timeout / $smtchecker_total"
    echo "  Total Time:  ${smtchecker_total_time}s"
    if [ $smtchecker_total -gt 0 ]; then
        echo "  Avg Time:    $(echo "scale=3; $smtchecker_total_time / $smtchecker_total" | bc)s per contract"
    fi
    echo ""

    # Calculate speedup
    if (( $(echo "$smtchecker_total_time > 0" | bc -l) )); then
        speedup=$(echo "scale=1; $smtchecker_total_time / $intuition_total_time" | bc)
        echo "Speed Comparison:"
        echo "  Intuition is ${speedup}x faster"
        echo "  (but on simpler problems!)"
        echo ""
    fi

    # Completeness comparison
    echo "Completeness Comparison (within 10s time limit):"
    intuition_rate=$(echo "scale=1; 100 * $intuition_proved / 10" | bc)
    echo "  Intuition:   ${intuition_rate}% success rate"

    if [ $smtchecker_total -gt 0 ]; then
        smt_rate=$(echo "scale=1; 100 * $smtchecker_proved / $smtchecker_total" | bc)
        echo "  SMTChecker:  ${smt_rate}% success rate"
    fi
fi

echo ""
echo "════════════════════════════════════════════════════════════"
echo "INTERPRETATION"
echo "════════════════════════════════════════════════════════════"
echo ""
echo "1. Intuition Prover is MUCH faster but limited to propositional logic"
echo "2. SMTChecker can verify arithmetic properties that Intuition cannot"
echo "3. Both tools are incomplete (may fail to prove valid assertions)"
echo "4. Intuition excels at pure control flow, SMTChecker at data properties"
echo ""
echo "Recommendation:"
echo "- Use Intuition for: Fast sanity checks on logical structure"
echo "- Use SMTChecker for: Production contract verification"
echo ""

# Save summary
{
    echo "Benchmark Results - $(date)"
    echo ""
    echo "Intuition: $intuition_proved proved, $intuition_failed failed, ${intuition_total_time}s total"
    if command -v solc &> /dev/null; then
        echo "SMTChecker: $smtchecker_proved proved, $smtchecker_failed failed, $smtchecker_timeout timeout, ${smtchecker_total_time}s total"
    fi
} > "$RESULTS_DIR/summary.txt"

echo "Results saved to: $RESULTS_DIR/"
