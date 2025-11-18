# Solver Capabilities Clarification

## Theoretical vs Actual Implementation

### Theoretical Observation (Correct)

**Claim**: "Intuitionistic logic provers can solve classical logic via double-negation translation"

**Status**: ✅ **Theoretically correct** via Gödel-Gentzen translation

For any classical tautology `φ`, the formula `¬¬φ` is provable in intuitionistic logic. Therefore, a complete intuitionistic prover could verify classical validity by proving `¬¬φ`.

### Actual Implementation (Current Limitation)

**Current Status of intuition prover**: ❌ **Cannot handle negation or conjunction in goals**

From `src/Prover.hs:239-241`:
```haskell
prover context (Connected phi1 Conjunction phi2) measure =
  Just (MError "Unhandled conjunction in goal")
prover context (Negated phi) measure =
  Just (MError "Unhandled negation in goal")
```

### What intuition CAN Prove

✅ **Implicational formulas**: p₁ ⇒ p₂ ⇒ ... ⇒ pₙ
✅ **Nested implications**: (p ⇒ q) ⇒ ((q ⇒ r) ⇒ (p ⇒ r))
✅ **Atomic conclusions**: Any formula ending in an atomic proposition

### What intuition CANNOT Currently Prove

❌ **Negation in goals**: ¬φ, ¬¬φ
❌ **Conjunction in goals**: φ ∧ ψ
❌ **Disjunction in goals**: φ ∨ ψ (likely - would need to test)
❌ **Classical tautologies via ¬¬translation**: ¬¬(p ∨ ¬p)

## Test Results

```bash
$ ./intuition -f classical-lem.p    # ¬¬(p ∨ ¬p)
[Just (MError "Unhandled negation in goal")]

$ ./intuition -f classical-dne.p    # ¬¬(¬¬p ⇒ p)
[Just (MError "Unhandled negation in goal")]

$ ./intuition -f classical-peirce.p # ¬¬(((p⇒q)⇒p)⇒p)
[Just (MError "Unhandled negation in goal")]
```

## Conclusion

### Domain Specificity

**Verdict**: The intuition prover **IS domain-specific** to:
- Intuitionistic propositional logic
- Specifically: implicational fragment (goals must be implications or atoms)

### To Make It General-Purpose

To handle classical logic via ¬¬translation, would need to implement:

1. **Negation handling in goals**:
   ```haskell
   prover context (Negated phi) measure =
     -- Try to derive contradiction from phi in context
   ```

2. **Conjunction handling in goals**:
   ```haskell
   prover context (Connected phi1 Conjunction phi2) measure =
     -- Prove both phi1 and phi2 separately
   ```

3. **Disjunction handling in goals**:
   ```haskell
   prover context (Connected phi1 Disjunction phi2) measure =
     -- Non-trivial: need proof search for either phi1 or phi2
   ```

## Benchmark Implications

The benchmark comparisons remain valid:
- intuition is 55-100x faster than SAT/SMT/FOL solvers
- **But only on its supported fragment** (implicational intuitionistic logic)
- It is correctly characterized as **domain-specific**

## Future Work

Possible extensions:
1. Implement negation/conjunction/disjunction in goals
2. Add classical mode via ¬¬translation
3. Support full intuitionistic propositional logic (not just implicational fragment)

---

**Summary**: While the theoretical observation about using ¬¬translation is correct, the **current implementation** does not support this, making the solver domain-specific as originally stated in the benchmarks.
