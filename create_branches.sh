#!/bin/bash
echo "=== Tworzenie branchy eksperymentalnych ==="

# Branch 1: Theory Axioms
git checkout -b theory-axioms strategy-2-yul-parser
echo "✅ Branch 1: theory-axioms utworzony"

# Branch 2: Presburger Solver
git checkout strategy-2-yul-parser
git checkout -b presburger-solver strategy-2-yul-parser
echo "✅ Branch 2: presburger-solver utworzony"

# Branch 3: Z3 Integration
git checkout strategy-2-yul-parser
git checkout -b z3-integration strategy-2-yul-parser
echo "✅ Branch 3: z3-integration utworzony"

# Wróć do głównego brancha
git checkout strategy-2-yul-parser

echo ""
echo "=== Branche utworzone ==="
git branch | grep -E "(theory-axioms|presburger-solver|z3-integration)"
