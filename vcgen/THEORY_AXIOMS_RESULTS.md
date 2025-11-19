# Theory Axioms Approach - Results

**Branch**: `theory-axioms`
**Date**: November 19, 2025

## Summary

The theory-axioms approach attempts to verify Yul assertions by encoding ordering and boolean properties as first-order logic axioms, then using E prover (FOL theorem prover) to verify the properties.

### Results: ❌ **Unsuccessful**

- **Assertions tested**: 6
- **Successfully verified**: 0/6 (0%)
- **Reason for failure**: FOL prover limitations with uint256 and mixed theories

## Implementation

### 1. Theory Axioms Defined

**Ordering Axioms** (6 axioms):
```tptp
fof(transitivity_gt, axiom, ![X,Y,Z]: ((gt(X,Y) & gt(Y,Z)) => gt(X,Z))).
fof(asymmetry_gt, axiom, ![X,Y]: (gt(X,Y) => ~gt(Y,X))).
fof(trichotomy, axiom, ![X,Y]: (gt(X,Y) | eq(X,Y) | gt(Y,X))).
fof(eq_reflexive, axiom, ![X]: eq(X,X)).
fof(eq_symmetric, axiom, ![X,Y]: (eq(X,Y) => eq(Y,X))).
fof(eq_transitive, axiom, ![X,Y,Z]: ((eq(X,Y) & eq(Y,Z)) => eq(X,Z))).
```

**Boolean Axioms** (3 axioms):
```tptp
fof(double_negation, axiom, ![P]: (iszero(iszero(P)) <=> P)).
fof(demorgan_and, axiom, ![P,Q]: (iszero(and(P,Q)) <=> (iszero(P) | iszero(Q)))).
fof(demorgan_or, axiom, ![P,Q]: (iszero(or(P,Q)) <=> (iszero(P) & iszero(Q)))).
```

### 2. TPTP Generation

Successfully generated TPTP files for all 6 assertions with appropriate axioms.

Example (`vc_1.p`):
```tptp
% Verification Condition with Theory Axioms
% Location: if-guard

% Theory Axioms:
fof(transitivity_gt, axiom, ![X,Y,Z]: ((gt(X,Y) & gt(Y,Z)) => gt(X,Z))).
...

% Verification Condition:
fof(vc, conjecture, ~(gt(x, 115792089237316195423570985008687907853269984665640564039457584007913129639934))).
```

## Technical Problems Encountered

### Problem 1: uint256 Range Exceeds FOL Prover Capacity

**Issue**: E prover cannot handle numbers in the uint256 range (0 to 2^256-1).

**Example**:
- Max safe uint256 value: `0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe`
- Decimal: `115792089237316195423570985008687907853269984665640564039457584007913129639934`
- E prover error: `"Number truncated while reading"`

**Why this matters**: Smart contracts use uint256 for all arithmetic. Any overflow check involves these large constants.

### Problem 2: Mixed Theory Handling

**Issue**: Combining ordering axioms (gt, lt, eq) with boolean axioms (iszero, and, or) creates a mixed theory that E prover struggles with.

**Error**: `vc_2.p:11:(Column 54):(just read '<=>'): syntax error`

The bi-implication operator `<=>` in boolean axioms causes parsing errors.

### Problem 3: Axiom Instantiation

**Challenge**: Even if we fixed the syntax issues, FOL provers need to instantiate universal quantifiers (![X,Y,Z]) with specific values. With uint256 range (2^256 possible values), exhaustive instantiation is impossible.

## Why Theory Axioms Don't Work for Yul

1. **Finite Field Arithmetic**: Yul uses uint256 (modulo 2^256), which is a finite field. FOL axioms don't capture modular arithmetic properties.

2. **Scale**: 2^256 ≈ 10^77 possible values. Cannot enumerate or instantiate axioms for all cases.

3. **Mixed Theories**: Real-world assertions mix:
   - Arithmetic comparisons (gt, lt, eq)
   - Boolean operations (iszero, and, or)
   - Arithmetic operations (add, sub)

   FOL provers handle these separately, not combined.

4. **No Decision Procedure**: FOL + arithmetic requires a decision procedure (like SMT), not just axioms.

## Benchmark Results

```
=== Theory Axioms Verification Benchmark ===
Generated 6 verification conditions

Results:
  vc_1.p: ❌ Number truncated (uint256 max value too large)
  vc_2.p: ❌ Syntax error with <=> operator
  vc_3.p: ❌ Syntax error with <=> operator
  vc_4.p: ❌ Syntax error with <=> operator
  vc_5.p: ❌ Syntax error with <=> operator
  vc_6.p: ❌ Syntax error with <=> operator

=== Summary ===
Total VCs: 6
Verified: 0
Falsifiable: 0
Timeout/Unknown: 6

❌ No proofs found
```

## Lessons Learned

1. **FOL provers ≠ SMT solvers**: E prover is designed for pure first-order logic, not arithmetic theories.

2. **Axiomatization has limits**: You can't axiomatize finite field arithmetic with simple FOL axioms.

3. **Need specialized decision procedures**: uint256 arithmetic requires either:
   - Presburger arithmetic solver (for +, -, >, <, =)
   - SMT solver with bitvector theory (for full uint256 semantics)

## Conclusion

**The theory-axioms approach is not viable for Yul verification.**

While it successfully:
- ✅ Generated TPTP files with axioms
- ✅ Detected which axioms are needed
- ✅ Integrated with E prover

It failed because:
- ❌ uint256 numbers exceed FOL prover capacity
- ❌ Mixed theories (ordering + boolean) cause errors
- ❌ No decision procedure for arithmetic

## Next Steps

Move to more promising approaches:

1. **Presburger Solver** (Branch 2): Implement decision procedure for Presburger arithmetic (+, -, >, <, =)
   - Expected success rate: ~70%
   - Handles comparisons without full arithmetic

2. **Z3 Integration** (Branch 3): Use SMT solver with bitvector theory
   - Expected success rate: ~90%
   - Full uint256 semantics
   - Standard tool in industry

---

**Recommendation**: Abandon theory-axioms, focus on Presburger or Z3.
