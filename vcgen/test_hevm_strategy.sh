#!/bin/bash

# Strategy 1: hevm Symbolic Execution Test Script
# Tests Counter.sol using hevm

set +e  # Don't exit on errors, we want to report them

echo "════════════════════════════════════════════════════════════"
echo "Strategy 1: hevm Symbolic Execution"
echo "════════════════════════════════════════════════════════════"
echo ""

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check dependencies
echo "Checking dependencies..."
echo ""

# Check solc
if command -v solc &> /dev/null; then
    SOLC_VERSION=$(solc --version | grep Version | head -1)
    echo -e "${GREEN}✓ solc found:${NC} $SOLC_VERSION"
else
    echo -e "${RED}✗ solc not found${NC}"
    echo ""
    echo "Install solc:"
    echo "  sudo apt-get install solc"
    echo "  or visit: https://docs.soliditylang.org/en/latest/installing-solidity.html"
    echo ""
    MISSING_DEPS=1
fi

# Check hevm
if command -v hevm &> /dev/null; then
    HEVM_VERSION=$(hevm version 2>&1 || echo "hevm (version unknown)")
    echo -e "${GREEN}✓ hevm found:${NC} $HEVM_VERSION"
else
    echo -e "${RED}✗ hevm not found${NC}"
    echo ""
    echo "Install hevm:"
    echo "  Option 1 (Nix): nix-env -i hevm"
    echo "  Option 2 (Cabal): cabal install hevm"
    echo "  Option 3 (Source): git clone https://github.com/ethereum/hevm"
    echo ""
    MISSING_DEPS=1
fi

# Check Z3
if command -v z3 &> /dev/null; then
    Z3_VERSION=$(z3 --version)
    echo -e "${GREEN}✓ z3 found:${NC} $Z3_VERSION"
else
    echo -e "${YELLOW}⚠ z3 not found${NC} (hevm can use cvc5 or bitwuzla instead)"
    echo "  Install: sudo apt-get install z3"
fi

echo ""

# Exit if missing critical dependencies
if [ ! -z "$MISSING_DEPS" ]; then
    echo -e "${RED}Critical dependencies missing. Exiting.${NC}"
    echo ""
    echo "This is a conceptual demonstration."
    echo "Once dependencies are installed, this script will:"
    echo "  1. Compile Counter.sol to bytecode"
    echo "  2. Run hevm symbolic execution"
    echo "  3. Check all assertions in the contract"
    echo "  4. Report verification results"
    exit 1
fi

# Create build directory
mkdir -p build

# Compile Counter.sol
echo "════════════════════════════════════════════════════════════"
echo "Step 1: Compiling Counter.sol"
echo "════════════════════════════════════════════════════════════"
echo ""

if [ ! -f "examples/Counter.sol" ]; then
    echo -e "${RED}✗ Counter.sol not found${NC}"
    echo "Expected at: examples/Counter.sol"
    exit 1
fi

echo "Running: solc --bin-runtime examples/Counter.sol -o build/"
solc --bin-runtime examples/Counter.sol -o build/ 2>&1

if [ $? -eq 0 ]; then
    echo -e "${GREEN}✓ Compilation successful${NC}"
    echo "Output: build/Counter.bin-runtime"
else
    echo -e "${RED}✗ Compilation failed${NC}"
    exit 1
fi

echo ""

# Run hevm symbolic execution
echo "════════════════════════════════════════════════════════════"
echo "Step 2: hevm Symbolic Execution"
echo "════════════════════════════════════════════════════════════"
echo ""

BYTECODE=$(cat build/Counter.bin-runtime)

echo "Running: hevm symbolic --code <bytecode> --solver z3"
echo ""

start_time=$(date +%s.%N)

# Run hevm symbolic
hevm symbolic \
  --code "0x$BYTECODE" \
  --solver z3 \
  --max-iterations 1000 \
  --timeout 10 \
  > build/hevm_output.txt 2>&1

hevm_exit=$?
end_time=$(date +%s.%N)
elapsed=$(echo "$end_time - $start_time" | bc)

echo ""
echo "════════════════════════════════════════════════════════════"
echo "Results"
echo "════════════════════════════════════════════════════════════"
echo ""

# Check results
if [ $hevm_exit -eq 0 ]; then
    # Check if output indicates success
    if grep -q "QED" build/hevm_output.txt || grep -q "No violations" build/hevm_output.txt; then
        echo -e "${GREEN}✓ All assertions verified!${NC}"
        echo "Time: ${elapsed}s"
    else
        echo -e "${YELLOW}⚠ hevm completed but result unclear${NC}"
        echo "See: build/hevm_output.txt"
    fi
else
    # Check for counterexample
    if grep -q "Counterexample" build/hevm_output.txt || grep -q "Violation" build/hevm_output.txt; then
        echo -e "${RED}✗ Counterexample found!${NC}"
        echo ""
        echo "Assertion violation detected:"
        grep -A 5 "Counterexample\|Violation" build/hevm_output.txt || echo "(see build/hevm_output.txt for details)"
    else
        echo -e "${YELLOW}⚠ hevm exited with code $hevm_exit${NC}"
        echo "Time: ${elapsed}s"
        echo ""
        echo "This might indicate:"
        echo "  - Solver timeout"
        echo "  - Invalid bytecode"
        echo "  - hevm configuration issue"
        echo ""
        echo "See build/hevm_output.txt for details"
    fi
fi

echo ""
echo "Full output saved to: build/hevm_output.txt"
echo ""

# Show summary
echo "════════════════════════════════════════════════════════════"
echo "Summary: Strategy 1 (hevm)"
echo "════════════════════════════════════════════════════════════"
echo ""
echo "Contract: Counter.sol (4 functions with assertions)"
echo "Method: Symbolic execution with SMT solver"
echo "Solver: Z3"
echo "Time: ${elapsed}s"
echo "Exit code: $hevm_exit"
echo ""

if [ $hevm_exit -eq 0 ]; then
    echo "Status: ✓ VERIFIED"
else
    echo "Status: ✗ FAILED or TIMEOUT"
fi

echo ""
echo "Next steps:"
echo "  - Compare with Strategy 2 (Yul Parser): cd vcgen && ./test_yul_parser.sh"
echo "  - Compare with Strategy 3 (Solc AST): (not yet implemented)"
echo "  - View detailed results: cat build/hevm_output.txt"
echo ""
