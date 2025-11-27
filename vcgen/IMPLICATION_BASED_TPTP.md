# Implication-Based TPTP Generation for Intuition Prover

## Overview

Intuition prover natively uses implications as its core format. Instead of converting to CNF (Conjunctive Normal Form) via Tseitin transformation, we use Stålmarck reduction rules to generate implication-based formulas.

## Implementation

### 1. Datatype-Based Approach

**File**: `vcgen/app/YulLogic.hs:429-443`

Separate logic conversion from serialization:

```haskell
data ImplicationFormula
  = ImpAtom String [ImplicationTerm]  -- Atomic predicate: gt(x, y)
  | ImpNot ImplicationFormula           -- Negation: ~P
  | ImpImpl ImplicationFormula ImplicationFormula  -- Implication: P => Q
  | ImpFalse                            -- Falsity: ⊥

data ImplicationTerm
  = TermVar String                      -- Variable: x
  | TermLit Integer                     -- Literal: 42
  | TermApp String [ImplicationTerm]    -- Function application: add(x, y)
```

### 2. Stålmarck Reduction Rules

**File**: `vcgen/app/YulLogic.hs:456-495`

Reference: https://arxiv.org/pdf/2509.16172

Apply ONLY to propositional connectives:
- **Disjunction**: A ∨ B ⟹ (¬A → B)
- **Conjunction**: A ∧ B ⟹ ¬(A → ¬B)
- **Biconditional**: P ↔ Q ⟹ ((P → Q) → ((Q → P) → ⊥)) → ⊥

**Key Distinction**:
- **Propositional connectives** (and, or, iszero): Apply Stålmarck rules
- **Atomic predicates** (gt, lt, eq): Keep as atomic formulas
- **Function applications** (add, div, shl): Keep as terms

### 3. Serialization to TPTP

**File**: `vcgen/app/YulLogic.hs:497-515`

```haskell
impFormulaToTPTP :: ImplicationFormula -> String
impFormulaToTPTP f = case f of
  ImpAtom pred terms ->
    pred ++ "(" ++ intercalate ", " (map termToTPTP terms) ++ ")"
  ImpNot p ->
    "~(" ++ impFormulaToTPTP p ++ ")"
  ImpImpl p q ->
    "(" ++ impFormulaToTPTP p ++ " => " ++ impFormulaToTPTP q ++ ")"
  ImpFalse ->
    "$false"
```

### 4. Theory Axioms

**File**: `vcgen/app/YulLogic.hs:314-585`

Axioms for non-Presburger operations:

**Ordering Relations**:
- Transitivity: gt(X,Y) ∧ gt(Y,Z) => gt(X,Z)
- Asymmetry: gt(X,Y) => ~gt(Y,X)
- Trichotomy: gt(X,Y) ∨ eq(X,Y) ∨ gt(Y,X)

**Division**:
- div_positive: (gt(X,0) ∧ gt(Y,0)) => gt(div(X,Y),0)
- div_bounds: gt(Y,0) => (gt(div(X,Y),0) ∨ eq(div(X,Y),0))
- div_monotonic: Preserves ordering

**Shifts**:
- shl_doubles: eq(shl(X,1), mul(X,2))
- shr_halves: eq(shr(X,1), div(X,2))

## Arithmetic Encoding Strategy

### Current Approach (Phase 1)

**Atomic predicates with theory axioms**:
- Comparisons: gt(x, y), lt(x, y), eq(x, y) as atomic predicates
- Operations: add(x, y), div(x, y), shl(x, n) as function applications
- Theory axioms help Intuition reason about relationships

### Future Work (Phase 2): Bit-Level Encoding

**Key insight**: For single-bit arithmetic, `a => b` encodes `a ≤ b`
- If a=1, then b=1 (for implication to hold)
- If a=0, b can be 0 or 1
- This is exactly the less-than-or-equal relation!

**Multi-bit comparisons**: Use logarithmic tree structure
- For gt(x, y) with n-bit x, y:
  - Compare MSB first
  - If MSBs equal, recurse on remaining bits
  - Depth: O(log n)

**Implementation strategy**:
1. Start with theory axioms (current approach)
2. Implement bit-level encoding for critical operations
3. Use logarithmic trees for 256-bit EVM integers

See `ARITHMETIC_ENCODING_DESIGN.md` for details.

## References

- Stålmarck Procedure: https://arxiv.org/pdf/2509.16172
- Encoding Linear Constraints with Implication Chains (adapted for implications)
- Encoding Basic Arithmetic Operations for SAT-Solvers (adapted for implications)
- **Key difference**: CNF papers use clauses; we use pure implications

## Status

- ✅ Stålmarck reduction rules implemented
- ✅ ImplicationFormula datatype created
- ✅ TPTP serialization implemented
- ✅ Theory axioms for non-Presburger operations
- ⏳ Bit-level encoding (future work)
- ⏳ Testing with Intuition prover
- ⏳ Benchmarking on DISL dataset
