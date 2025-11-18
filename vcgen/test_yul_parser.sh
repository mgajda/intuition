#!/bin/bash

# Script to test Yul parser on popular smart contract patterns
# This compiles Solidity contracts to Yul IR and tests the parser

set -e

echo "=== Testing Yul Parser on Real Smart Contracts ==="
echo ""

# Check if solc is installed
if ! command -v solc &> /dev/null; then
    echo "Error: solc not found. Please install Solidity compiler:"
    echo "  sudo add-apt-repository ppa:ethereum/ethereum"
    echo "  sudo apt-get update"
    echo "  sudo apt-get install solc"
    exit 1
fi

echo "Using solc version: $(solc --version | head -1)"
echo ""

# Build yulvcgen if needed
if [ ! -f dist-newstyle/build/x86_64-linux/ghc-9.6.6/vcgen-0.1.0.0/build/yulvcgen/yulvcgen ]; then
    echo "Building yulvcgen..."
    cabal build yulvcgen
    echo ""
fi

YULVCGEN="./dist-newstyle/build/x86_64-linux/ghc-9.6.6/vcgen-0.1.0.0/build/yulvcgen/yulvcgen"

# Create output directory
mkdir -p build/yul-tests

# Test counter
passed=0
failed=0

test_contract() {
    local contract=$1
    local name=$(basename "$contract" .sol)

    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "Testing: $name"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

    # Compile to Yul IR
    echo "1. Compiling to Yul IR..."
    if solc --ir "$contract" -o "build/yul-tests/$name/" 2>&1 | tee "build/yul-tests/$name/compile.log"; then
        echo "   ✓ Compilation successful"

        # Find the generated Yul file
        yul_file=$(find "build/yul-tests/$name/" -name "*.yul" | head -1)

        if [ -f "$yul_file" ]; then
            echo "   Generated: $yul_file"
            echo ""

            # Test with Yul parser
            echo "2. Parsing Yul IR..."
            if $YULVCGEN < "$yul_file" > "build/yul-tests/$name/parse.log" 2>&1; then
                echo "   ✓ Parse successful!"
                ((passed++))

                # Show first few lines of AST
                echo ""
                echo "   AST preview:"
                grep "Parse Successful" "build/yul-tests/$name/parse.log" | head -3
            else
                echo "   ✗ Parse failed"
                ((failed++))
                echo "   Error log:"
                tail -10 "build/yul-tests/$name/parse.log"
            fi
        else
            echo "   ✗ No Yul file generated"
            ((failed++))
        fi
    else
        echo "   ✗ Compilation failed"
        ((failed++))
    fi

    echo ""
}

# Test all contracts
for contract in examples/test-contracts/*.sol; do
    if [ -f "$contract" ]; then
        test_contract "$contract"
    fi
done

# Summary
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "SUMMARY"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "Passed: $passed"
echo "Failed: $failed"
echo "Total:  $((passed + failed))"
echo ""

if [ $failed -eq 0 ]; then
    echo "✓ All tests passed!"
    exit 0
else
    echo "✗ Some tests failed"
    exit 1
fi
