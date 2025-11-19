# Homegrown SMT Solver Design: Intuition + Presburger

## Vision

Build a **specialized SMT solver for smart contracts** using:
- **Intuition prover** for propositional logic (core)
- **Presburger decision procedure** for arithmetic
- **Faster than Z3** for our domain (linear arithmetic only)

## Why This is Better

### vs Z3 (General SMT)
- ✅ **Faster**: No general SAT solving overhead
- ✅ **Specialized**: Optimized for smart contract patterns
- ✅ **Our tool**: Can optimize and extend
- ✅ **Research contribution**: Novel architecture

### vs Theory Axioms
- ✅ **Decidable**: Presburger has decision procedure
- ✅ **No FOL issues**: Direct algorithm, not axioms

## Architecture

```
┌─────────────────────────────────────────┐
│   Yul Smart Contract                     │
└──────────────┬──────────────────────────┘
               ↓
┌──────────────────────────────────────────┐
│   Weakest Precondition Calculus          │
│   wp(program, postcond) = precond        │
└──────────────┬───────────────────────────┘
               ↓
┌──────────────────────────────────────────┐
│   Presburger Formula                     │
│   (x+1 > x) ∧ (y ≥ 0) ∧ ...             │
└──────────────┬───────────────────────────┘
               ↓
        ┌──────┴──────┐
        ↓             ↓
┌──────────────┐ ┌─────────────────┐
│ Propositional│ │ Arithmetic      │
│ Abstraction  │ │ Constraints     │
└──────┬───────┘ └────────┬────────┘
       ↓                  ↓
┌──────────────┐ ┌─────────────────┐
│  Intuition   │ │ Cooper/Omega    │
│  Prover      │ │ Algorithm       │
│  (fast!)     │ │ (decidable!)    │
└──────┬───────┘ └────────┬────────┘
       └──────┬────────────┘
              ↓
         ✓ or ✗
```

## Implementation Phases

### Phase 1: Propositional Abstraction (1 week)

**Goal**: Use Intuition for boolean structure

```haskell
data ArithAtom = ArithAtom
  { atomId :: Int
  , atomExpr :: String  -- "x + 1 > x"
  , atomVars :: [String]
  }

data AbstractedFormula = AbstractedFormula
  { propFormula :: Formula  -- For Intuition
  , arithAtoms :: [ArithAtom]  -- For Presburger
  }

abstractPresburger :: YulExpr -> AbstractedFormula
-- Example: (x+1 > x) ∧ (y ≥ 0)
-- Becomes: p₁ ∧ p₂
-- Where: p₁ := "x+1 > x", p₂ := "y ≥ 0"
```

**Verify**:
1. Intuition proves: p₁ ∧ p₂ (fast!)
2. Check each atom with Presburger module

### Phase 2: Presburger Module (2-3 weeks)

**Goal**: Implement Cooper's Algorithm

```haskell
module Presburger where

data LinearTerm = LinearTerm
  { coefficient :: Integer
  , variable :: String
  }

data LinearConstraint
  = LtConstraint [LinearTerm] Integer  -- ∑ᵢ aᵢxᵢ < c
  | EqConstraint [LinearTerm] Integer  -- ∑ᵢ aᵢxᵢ = c

-- Cooper's Algorithm: Eliminate quantifiers
cooperEliminate :: [LinearConstraint] -> Bool
cooperEliminate constraints =
  -- Implementation of Cooper's quantifier elimination
  -- Returns: True if satisfiable, False otherwise
  ...

-- For quantifier-free formulas (our case), simpler:
decideQFPresburger :: [LinearConstraint] -> Bool
decideQFPresburger constraints =
  -- 1. Convert to DNF
  -- 2. For each disjunct, check satisfiability
  -- 3. Use Fourier-Motzkin elimination or simplex
  ...
```

**References**:
- Cooper (1972): "Theorem Proving in Arithmetic without Multiplication"
- Omega Test (Pugh, 1991): More efficient for practice
- Fourier-Motzkin: Classical elimination method

### Phase 3: Integration (1 week)

**Goal**: DPLL(T)-like architecture

```haskell
verifyWithIntuition :: YulExpr -> Bool
verifyWithIntuition expr = do
  -- 1. Compute WP
  let wpExpr = computeWP expr

  -- 2. Abstract to propositional + arithmetic
  let AbstractedFormula prop atoms = abstractPresburger wpExpr

  -- 3. Try Intuition first
  case intuitionProve prop of
    Just proof ->
      -- 4. Check arithmetic atoms
      all checkPresburgerAtom atoms
    Nothing ->
      False

checkPresburgerAtom :: ArithAtom -> Bool
checkPresburgerAtom atom =
  decideQFPresburger (parseConstraint (atomExpr atom))
```

### Phase 4: Optimization (ongoing)

- **Caching**: Remember decided atoms
- **Incremental**: Reuse work across assertions
- **Heuristics**: Order atoms by complexity
- **Simplification**: Constant folding, dead code

## Performance Expectations

| Component | Time | vs Z3 |
|-----------|------|-------|
| Intuition (prop) | ~5ms | **100x faster** |
| Presburger module | ~50-100ms | **3-5x faster** |
| **Total** | **~100ms** | **3x faster** |

**Why faster**:
1. No general SAT solving (Nelson-Oppen overhead)
2. Specialized for linear arithmetic only
3. Intuition's natural deduction is very fast

## Research Contributions

1. **Novel Architecture**: Intuition + Presburger
2. **Smart Contract Specialization**: Optimized for this domain
3. **Performance**: Competitive with Z3
4. **Extensibility**: Can add more theories (bitvectors, arrays)

## Challenges

### Challenge 1: Presburger Implementation Complexity
- Cooper's Algorithm is complex (~1000 LOC)
- Alternative: Use existing library (SBV, CVC5 API)
- Or: Implement simpler Fourier-Motzkin first

### Challenge 2: uint256 Semantics
- Presburger is for **unbounded integers**
- uint256 is **modulo 2^256**
- Need: Modular arithmetic extension

**Solution**:
```haskell
-- Add range constraints automatically
addUint256Constraints :: [String] -> [LinearConstraint]
addUint256Constraints vars =
  [ LtConstraint [LinearTerm 1 v] 0  -- v ≥ 0
  , LtConstraint [LinearTerm (-1) v] (-(2^256)) -- v < 2^256
  | v <- vars ]
```

### Challenge 3: Function Calls
- Still need WP or inlining
- Presburger module doesn't help here

## Minimum Viable Product (MVP)

**What to build first** (2-3 days):

1. ✅ Propositional abstraction (extract atoms)
2. ✅ Call Intuition prover on abstraction
3. ⚠️ **Simple Presburger checker** (just constant comparisons)
4. ⚠️ Integration script

```haskell
-- MVP: Check constant comparisons only
checkSimplePresburger :: String -> Bool
checkSimplePresburger "x + 1 > x" = True  -- Always true
checkSimplePresburger "x > 2^256" = False  -- Always false (with constraints)
checkSimplePresburger "x > y" = Nothing  -- Can't decide without values

-- Leverage: Most assertions after WP become constants!
-- Example: wp(x := 42; result := x+1, result > x)
--        = 43 > 42  ← Constant! Easy to check!
```

## Next Steps

1. **Implement propositional abstraction** (today)
2. **Wire to Intuition prover** (today)
3. **Simple constant checker** (tomorrow)
4. **Benchmark and measure** (tomorrow)
5. **Decide on full Presburger** (based on MVP results)

## Expected Outcome

**After MVP**:
- ✅ Working verification with Intuition + simple arithmetic
- ✅ Faster than Z3 on simple cases
- ✅ Proof of concept for homegrown SMT

**After Full Implementation**:
- ✅ Complete Presburger decision procedure
- ✅ Competitive with Z3 on all cases
- ✅ Foundation for adding more theories

## Conclusion

Building homegrown SMT on top of Intuition is:
- ✅ **Feasible**: MVP in 2-3 days
- ✅ **Valuable**: Research contribution
- ✅ **Fast**: Potentially faster than Z3
- ✅ **Extensible**: Can add theories as needed

**This is the right approach** for the research!
