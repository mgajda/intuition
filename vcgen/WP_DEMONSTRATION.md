# Weakest Precondition Calculus - Demonstration

**Branch**: `z3-integration`
**Date**: November 19, 2025

## Implementation

Added WP calculus for Yul with key rules:

```haskell
wp(x := e, φ) = φ[e/x]              -- Substitute e for x
wp(S1; S2, φ) = wp(S1, wp(S2, φ))  -- Compose backwards
wp(if cond { invalid() }, φ) = ¬cond ∧ φ  -- Guard must not trigger
```

## Example: Simple Increment

**Yul Code**:
```yul
function increment(x) -> result {
    result := add(x, 1)
    if iszero(gt(result, x)) {
        invalid()  // Assert result > x
    }
}
```

**WP Calculation**:
```
Postcondition: true (function returns)
wp(if iszero(gt(result, x)) { invalid() }, true)
  = ¬iszero(gt(result, x)) ∧ true
  = gt(result, x)

wp(result := add(x, 1), gt(result, x))
  = gt(add(x, 1), x)
  = (x + 1) > x

Final VC: (x + 1) > x
```

**With uint256 constraints**: This is VALID for x < 2^256-1

## Status: Partial Implementation

✅ **Implemented**:
- WP calculus for assignments, if-statements
- Expression substitution
- Logical operators (and, or, implies)

⏳ **Not Yet Integrated**:
- Full program traversal (currently only works on individual statements)
- Function call handling (need inlining or contracts)
- Loop handling (need invariants)
- Integration with YulVCgen.hs

⏳ **Testing**:
- Need to wire WP into extraction pipeline
- Generate SMT-LIB with computed VCs
- Benchmark on test contracts

## Key Insight

WP calculus is **essential but insufficient** for full verification:

1. **What WP Solves**: Data flow in straight-line code
2. **What WP Needs**:
   - Function summaries/contracts for calls
   - Loop invariants for iteration
   - Aliasing analysis for memory

For smart contracts with function calls like `increment(42)`, we need:
- **Option A**: Inline functions (simple but doesn't scale)
- **Option B**: Function contracts (manual annotations)
- **Option C**: Symbolic execution (automatic but complex)

## Next Steps

Three paths forward:

### Path A: Simple WP + Inlining (Quick Demo)
- Inline small functions automatically
- Compute WP for inlined code
- Test on simple examples
- **Pros**: Can demo WP working
- **Cons**: Doesn't scale to real contracts

### Path B: Full Verification Infrastructure (Proper Solution)
- Function contracts/summaries
- Loop invariants
- Aliasing analysis
- **Pros**: Scales to real contracts
- **Cons**: Major engineering effort (weeks)

### Path C: Hybrid with SMT (Pragmatic)
- Use WP for straight-line code
- Use SMT uninterpreted functions for calls
- Add axioms for function behavior
- **Pros**: Balance of automation and power
- **Cons**: Still needs some annotations

## Recommendation

Given time constraints and research goals:

1. **Complete current branch** with simple inlining demo
2. **Document limitations** clearly
3. **Create comparative report** of all three branches:
   - theory-axioms: Failed (FOL limitations)
   - presburger-solver: Right logic, needs WP ✓
   - z3-integration: WP foundation laid, needs completion

The key finding is: **Presburger + WP** is the right approach, but full implementation requires significant program analysis infrastructure beyond scope of current comparison.
