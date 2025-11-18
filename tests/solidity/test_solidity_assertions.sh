#!/bin/bash

# Test suite for Solidity contract assertions using intuition prover
# These are propositional abstractions of smart contract logic

PROVER="./dist-newstyle/build/x86_64-linux/ghc-8.10.7/intuition-0.3.0.1/x/intuition/build/intuition/intuition"

echo "=== Testing Solidity Contract Assertions with Intuition Prover ==="
echo ""

test_formula() {
    local name=$1
    local file=$2

    echo "Testing: $name"
    echo "  File: $file"

    result=$($PROVER -f "$file" 2>&1)

    if echo "$result" | grep -q "Just (MInt"; then
        echo "  Result: ✓ PROVABLE (intuitionistically valid)"
    elif echo "$result" | grep -q "Nothing"; then
        echo "  Result: ✗ NOT PROVABLE (may still be classically valid)"
    else
        echo "  Result: ERROR - $result"
    fi
    echo ""
}

# Create test formulas
mkdir -p tests/solidity

# Test 1: Ownable - if caller is owner, then authorized
cat > tests/solidity/01_ownable.p << 'EOF'
% Ownable access control
% If (caller is owner) then (action is authorized)
% Contrapositive: if action requires authorization, caller must be owner

fof(ownable_auth, conjecture,
    (is_owner => authorized)).
EOF

# Test 2: Pausable state machine
cat > tests/solidity/02_pausable.p << 'EOF'
% Pausable contract logic
% If paused, then not-paused is false (double negation)
% This tests: paused => ~~paused

fof(pausable_state, conjecture,
    (paused => ~ ~ paused)).
EOF

# Test 3: Escrow release logic
cat > tests/solidity/03_escrow.p << 'EOF'
% Escrow: if released once, cannot release again
% released => (try_release => already_released)
% Or: released => ~can_release

fof(escrow_no_double_release, conjecture,
    (released => ~ can_release)).
EOF

# Test 4: Voting - cannot vote twice
cat > tests/solidity/04_voting.p << 'EOF'
% Voting: if already voted, then cannot vote again
% voted => ~can_vote

fof(voting_no_double_vote, conjecture,
    (already_voted => ~ can_vote)).
EOF

# Test 5: MultiSig confirmation
cat > tests/solidity/05_multisig.p << 'EOF'
% MultiSig: if confirmed, then ~~confirmed (stability)

fof(multisig_confirmation_stable, conjecture,
    (confirmed => ~ ~ confirmed)).
EOF

# Test 6: General state invariant
cat > tests/solidity/06_state_invariant.p << 'EOF'
% If state S1 implies state S2, and S2 implies S3, then S1 implies S3
% Transitivity of implications

fof(state_transitivity, conjecture,
    (((s1 => s2) & (s2 => s3)) => (s1 => s3))).
EOF

# Test 7: Require precondition
cat > tests/solidity/07_require_logic.p << 'EOF'
% If precondition fails, execution doesn't continue
% ~precondition => ~execution
% Contrapositive: execution => precondition

fof(require_precondition, conjecture,
    (execution => precondition)).
EOF

# Test 8: Assert postcondition
cat > tests/solidity/08_assert_logic.p << 'EOF'
% Assert checks postcondition
% If execution completes, postcondition holds
% (precondition & execution_completes) => postcondition
% Simplified: execution_completes => postcondition

fof(assert_postcondition, conjecture,
    (execution_completes => postcondition)).
EOF

# Test 9: Balance conservation (abstract)
cat > tests/solidity/09_conservation.p << 'EOF'
% Balance conservation: if transfer happens, balances change oppositely
% (transfer_from_a_to_b) => (a_decreased & b_increased)
% But in propositional logic, we can only test:
% If transfer occurred, then state changed

fof(balance_change, conjecture,
    (transfer_occurred => state_changed)).
EOF

# Test 10: Complex control flow
cat > tests/solidity/10_control_flow.p << 'EOF'
% If condition C leads to action A, and A leads to state S,
% then condition C leads to state S
% (C => A) => ((A => S) => (C => S))

fof(control_flow_composition, conjecture,
    ((c => a) => ((a => s) => (c => s)))).
EOF

# Run all tests
echo "Running tests..."
echo "==============="
echo ""

test_formula "Ownable authorization" "tests/solidity/01_ownable.p"
test_formula "Pausable state" "tests/solidity/02_pausable.p"
test_formula "Escrow no double release" "tests/solidity/03_escrow.p"
test_formula "Voting no double vote" "tests/solidity/04_voting.p"
test_formula "MultiSig confirmation stable" "tests/solidity/05_multisig.p"
test_formula "State transitivity" "tests/solidity/06_state_invariant.p"
test_formula "Require precondition" "tests/solidity/07_require_logic.p"
test_formula "Assert postcondition" "tests/solidity/08_assert_logic.p"
test_formula "Balance conservation" "tests/solidity/09_conservation.p"
test_formula "Control flow composition" "tests/solidity/10_control_flow.p"

echo "=== Summary ==="
echo "These tests demonstrate that the intuition prover can verify"
echo "the LOGICAL STRUCTURE of smart contract assertions, even though"
echo "it doesn't handle arithmetic or first-order quantification."
echo ""
echo "For full verification, you would need:"
echo "- SMT solver for arithmetic (Z3, CVC5)"
echo "- First-order prover for quantifiers"
echo "- Or: translate to intuitionistic propositional logic"
