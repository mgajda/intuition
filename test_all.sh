#!/bin/bash

PROVER="./dist-newstyle/build/x86_64-linux/ghc-8.10.7/intuition-0.3.0.1/x/intuition/build/intuition/intuition"

echo "=== Testing all dobry (valid) formulas ==="
for file in tests/simple/dobry-*.p; do
  result=$("$PROVER" -f "$file" 2>&1)
  if echo "$result" | grep -q "MInt"; then
    echo "✓ $(basename $file)"
  else
    echo "✗ $(basename $file)"
  fi
done

echo ""
echo "=== Testing all zly (invalid) formulas ==="
for file in tests/simple/zly-*.p; do
  result=$("$PROVER" -f "$file" 2>&1)
  if echo "$result" | grep -q "Nothing\|MError"; then
    echo "✓ $(basename $file) - correctly rejected"
  else
    echo "✗ $(basename $file) - incorrectly accepted"
  fi
done

echo ""
echo "=== Testing negation support ==="
result=$("$PROVER" -f tests/simple/test-simple-negation.p 2>&1)
if echo "$result" | grep -q "MInt"; then
  echo "✓ p => ~~p"
else
  echo "✗ p => ~~p"
fi

echo ""
echo "=== Testing disjunction support ==="
result=$("$PROVER" -f tests/simple/test-disjunction-simple.p 2>&1)
if echo "$result" | grep -q "MInt"; then
  echo "✓ p => (p | q)"
else
  echo "✗ p => (p | q)"
fi

echo ""
echo "=== Testing classical tautologies via ~~translation ==="
result=$("$PROVER" -f tests/simple/classical-lem.p 2>&1)
if echo "$result" | grep -q "MInt"; then
  echo "✓ ~~(p | ~p) - Law of Excluded Middle"
else
  echo "✗ ~~(p | ~p) - Law of Excluded Middle"
fi
