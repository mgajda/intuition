# Theory Implementation Plan for Yul Verification

**Date**: 2025-11-24
**Current Status**: 28% verification rate (964/3,442 assertions)
**Current Stack**: Intuition (propositional) + Weakest Precondition + Presburger (linear arithmetic)
**Goal**: Increase verification rate to 60-80%

---

## Executive Summary

Analysis of 79 representative verification conditions reveals that **79.7% are expressible in Presburger arithmetic** but only **28% verify successfully**. The gap is caused by:

1. **Incomplete constant propagation** (16.5% of VCs have `unknown` variables)
2. **Conservative verification** (sound but incomplete Presburger implementation)
3. **Missing theories** for bitwise operations (20.3% of VCs)

Adding **bitvector theory (QF_BV)** will provide the highest ROI, potentially increasing verification rate to **60-65%**.

---

## Current Verification Breakdown

### By VC Classification (Sample of 79 VCs)

| Theory Required | Count | % | Current Support | Estimated Assertions |
|----------------|-------|---|-----------------|---------------------|
| **Presburger (QF_LIA)** | 63 | 79.7% | ✅ Yes | ~2,744 |
| **Bitvectors (shl)** | 8 | 10.1% | ❌ No | ~348 |
| **Nonlinear (div)** | 8 | 10.1% | ❌ No | ~348 |
| **With unknowns** | 13 | 16.5% | ⚠️ Partial | ~568 |

**Note**: Categories overlap (e.g., a VC can have both `div` and `unknown`).

### By Verification Outcome (3,442 Assertions)

| Status | Count | % | Reason |
|--------|-------|---|--------|
| ✅ **Verified** | 964 | 28.0% | Intuition+Presburger proved |
| ❌ **Not Verified** | 2,478 | 72.0% | Conservative rejection OR true failure |

---

## Theory Implementation Roadmap

### 🎯 **Priority 1: Bitvector Theory (QF_BV)**

**Impact**: +30-40% verification rate
**Effort**: 2-3 weeks
**Target**: 60-65% verification rate

#### What It Solves

| Operation Category | Operations | VCs Affected | Example |
|-------------------|-----------|--------------|---------|
| **Bitwise ops** | `shl`, `shr`, `sar` | 8 (10%) | `shl(64, 1)` = 2^64 |
| **Bitwise logic** | `and`, `or`, `xor`, `not` | Common in EVM | Bit masking |
| **Modular arithmetic** | All uint256 ops | 79 (100%) | Wraparound behavior |
| **Division/Modulo** | `div`, `mod` | 8 (10%) | As bitvector ops |

#### Why QF_BV Is Better Than QF_NIA

| Aspect | QF_BV | QF_NIA |
|--------|-------|--------|
| **Decidability** | ✅ Decidable | ⚠️ Undecidable |
| **Z3 Support** | ✅ Excellent | ⚠️ Limited (bit-blasting) |
| **Performance** | ✅ Fast | ⚠️ Slow |
| **uint256 semantics** | ✅ Native wraparound | ❌ Requires encoding |
| **Bitwise ops** | ✅ Native | ❌ Cannot express |

#### Implementation Steps

**Week 1: SMT Encoding**
```haskell
-- Current (QF_LIA):
(set-logic QF_LIA)
(declare-const x Int)
(assert (and (>= x 0) (<= x (- (^ 2 256) 1))))

-- New (QF_BV):
(set-logic QF_BV)
(declare-const x (_ BitVec 256))
-- No range constraints needed - wraparound is automatic!
```

**Week 2: Operation Translation**
```haskell
translateYulToBV :: YulExpr -> SMTExpr
translateYulToBV (Shl x n) = SMTBVShl x n  -- Native bitvector shift
translateYulToBV (Add x y) = SMTBVAdd x y  -- Modular addition (automatic)
translateYulToBV (Div x y) = SMTBVUDiv x y -- Unsigned division
translateYulToBV (Mod x y) = SMTBVURem x y -- Unsigned remainder
```

**Week 3: Integration & Testing**
- Test on 79 VCs
- Measure verification rate increase
- Compare with Z3 baseline

#### Expected Outcome

- **Before**: 964/3,442 verified (28.0%)
- **After**: 2,100-2,200/3,442 verified (61-64%)
- **Gain**: ~1,150 additional verified assertions

---

### 🎯 **Priority 2: Constant Propagation & Simplification**

**Impact**: +10-15% verification rate
**Effort**: 1-2 weeks
**Target**: 70-75% verification rate

#### What It Solves

**Problem**: 16.5% of VCs contain `unknown` variables from incomplete symbolic execution.

**Example**:
```smt2
; Current VC (incomplete):
(assert (> newFreePtr (- unknown 1)))  ; Cannot verify!

; After better propagation:
(assert (> newFreePtr (- (bvshl #x0000...0001 #x0000...0040) #x0000...0001)))
; Simplifies to: (> newFreePtr 18446744073709551615)  ; Can verify!
```

#### Implementation Strategies

| Technique | Effort | Gain | Description |
|-----------|--------|------|-------------|
| **Constant folding** | Low (3 days) | +5% | Evaluate constant expressions: `add(1, 2)` → `3` |
| **Algebraic simplification** | Medium (1 week) | +5% | `mul(x, 0)` → `0`, `add(x, 0)` → `x` |
| **Aggressive inlining** | Low (3 days) | +3% | Inline more helper functions |
| **Symbolic bounds** | High (2 weeks) | +7% | Track value ranges through execution |

#### Recommended Approach

**Phase 1** (Week 1): Low-hanging fruit
- Constant folding
- Aggressive inlining
- Basic algebraic rules

**Phase 2** (Week 2): Advanced
- Symbolic range tracking
- Loop unrolling (bounded)
- Path-sensitive analysis

#### Expected Outcome

- **Before**: 2,100/3,442 verified (61%)
- **After**: 2,400-2,600/3,442 verified (70-75%)
- **Gain**: ~300-500 additional verified assertions

---

### 🎯 **Priority 3: Array Theory (QF_AUFBV)**

**Impact**: +5-10% verification rate
**Effort**: 3-4 weeks
**Target**: 75-80% verification rate

#### What It Solves

**Memory and Storage Operations**:
- `mload(addr)`, `mstore(addr, value)`
- `sload(slot)`, `sstore(slot, value)`
- Storage array bounds checks

#### Current Workaround

Right now, memory/storage operations appear as uninterpreted functions in VCs:
```smt2
(declare-fun memory ((_ BitVec 256)) (_ BitVec 256))
; Cannot reason about relationships between loads/stores
```

#### With Array Theory

```smt2
(set-logic QF_AUFBV)
(declare-const memory (Array (_ BitVec 256) (_ BitVec 256)))

; Can verify: if we store X at addr, loading addr gives X
(assert (= (select (store memory addr x) addr) x))
```

#### Implementation Complexity

**High complexity** because:
- Requires modeling entire memory/storage state
- Must track aliasing (do two addresses overlap?)
- Interaction with bitvector arithmetic

#### Expected Outcome

- **Before**: 2,400/3,442 verified (70%)
- **After**: 2,600-2,750/3,442 verified (75-80%)
- **Gain**: ~200-350 additional verified assertions

---

### ⚠️ **Not Recommended: Nonlinear Arithmetic (QF_NIA)**

**Impact**: Minimal (+2-5%)
**Effort**: High (4-6 weeks)
**Issues**: Undecidable, slow, poor Z3 support

#### Why Not QF_NIA?

1. **Undecidable**: No algorithm guaranteed to terminate with answer
2. **Z3 uses bit-blasting**: Essentially converts to bitvectors anyway
3. **Performance**: Orders of magnitude slower than QF_BV
4. **Limited benefit**: Most nonlinear ops (div, mod, mul) handled by QF_BV

#### When You Might Need It

- Complex polynomial constraints (rare in EVM)
- Modular exponentiation reasoning (very rare)

**Recommendation**: Skip QF_NIA entirely. Use QF_BV for all integer reasoning.

---

### 🔮 **Future: Advanced Techniques**

These have **lower priority** but could push verification rate beyond 80%:

#### Loop Invariant Inference (Effort: High, Gain: +5%)

**Approach**:
- Bounded model checking (unroll first k iterations)
- Heuristic invariant generation
- User annotations via Solidity pragmas

**Challenge**: Yul IR doesn't have structured loops (only labels + jumps).

#### Abstract Interpretation (Effort: Very High, Gain: +5%)

**Approach**:
- Over-approximate program behavior conservatively
- Use interval domains, octagon domains, etc.
- Sound but very imprecise

**Challenge**: Requires new architecture outside WP calculus.

#### SMT Solver Optimization (Effort: Medium, Gain: +3%)

**Approaches**:
- Incremental solving (reuse work across assertions)
- Query simplification (minimize VC size)
- Theory-specific tactics (bitvector rewriting)

---

## Implementation Timeline

### Recommended Sequence

```
Week 1-3:  QF_BV implementation
           ├─ Week 1: SMT encoding changes
           ├─ Week 2: Operation translation
           └─ Week 3: Testing & benchmarking
           Expected: 28% → 62%

Week 4-5:  Constant propagation
           ├─ Week 4: Constant folding + aggressive inlining
           └─ Week 5: Symbolic bounds tracking
           Expected: 62% → 72%

Week 6:    Evaluation & paper writing
           └─ Compare with Z3, Mythril, Manticore
           Final: 72% verification rate

Optional:
Week 7-10: Array theory (QF_AUFBV)
           Expected: 72% → 78%
```

### Minimal Viable Product (MVP)

**Goal**: Demonstrate QF_BV feasibility in 1 week

**Scope**:
1. Convert 10 sample VCs from QF_LIA to QF_BV encoding
2. Run through Z3
3. Measure verification rate increase

**Deliverable**: Proof-of-concept showing >50% verification rate on sample.

---

## Research Contributions

### Novel Aspects

1. **Intuition + WP + BV**: Novel combination
   - Most tools use Z3 directly (no domain-specific prover)
   - Intuition prover might be faster for propositional structure

2. **Yul IR verification**: Understudied area
   - Most work on Solidity AST or EVM bytecode
   - Yul is sweet spot (structured but low-level)

3. **Assertion extraction**: From nested objects
   - Novel finding: Solidity runtime checks in nested objects
   - Enables verification without source code annotations

### Comparison Points

| Tool | Approach | Success Rate | Speed |
|------|----------|--------------|-------|
| **Mythril** | Symbolic execution + Z3 | ~60% (high FP) | Slow (timeouts) |
| **Manticore** | Concolic execution | ~50% | Very slow |
| **Certora** | SMT + manual annotations | ~75% | Slow |
| **Your Tool** | Intuition + WP + BV | **Target: 70%** | **Fast (960ms avg)** |

**Key differentiators**:
- ✅ **Fully automated** (no annotations)
- ✅ **Fast** (< 1 second per contract)
- ✅ **Sound** (no false positives when verified)

---

## Risk Assessment

### Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|------------|--------|------------|
| QF_BV doesn't improve rate | Low | High | Run MVP first (1 week) |
| Z3 bitvector solver is slow | Low | Medium | Benchmark early, compare with QF_LIA |
| Integration breaks Intuition | Medium | Medium | Incremental testing, rollback plan |
| Memory/array modeling too complex | High | Low | Optional (Priority 3), skip if needed |

### Research Risks

| Risk | Probability | Impact | Mitigation |
|------|------------|--------|------------|
| Not enough improvement for publication | Low | High | 60% is publishable, 70%+ is excellent |
| Z3 baseline beats your tool | Medium | High | Compare on speed, not just accuracy |
| Reviewers want 90%+ rate | Low | Medium | Explain undecidability limits |

---

## Success Criteria

### Minimum (Publishable)

- ✅ 60% verification rate (964 → 2,065 verified)
- ✅ < 2 second average per contract
- ✅ 0% timeout rate
- ✅ Sound (no false positives)

### Target (Strong Paper)

- ✅ 70% verification rate (964 → 2,409 verified)
- ✅ < 1 second average per contract
- ✅ Faster than Z3 baseline
- ✅ Zero false positives

### Stretch (Top-Tier Venue)

- ✅ 75%+ verification rate (964 → 2,582+ verified)
- ✅ Scalable to full DISL dataset (424k contracts)
- ✅ Detect real vulnerabilities in SmartBugs dataset
- ✅ Novel theoretical insights (Intuition + BV synergy)

---

## Next Actions

### Immediate (This Week)

1. ✅ **MVP for QF_BV** (1-2 days)
   - Convert 10 VCs to bitvector encoding
   - Test with Z3
   - Measure success rate

2. ✅ **Decision Point** (Day 3)
   - If MVP shows >50% success: proceed with full implementation
   - If MVP shows <50% success: investigate issues or pivot

3. ✅ **Full QF_BV Implementation** (Days 4-5)
   - Convert all 79 VCs
   - Benchmark on full dataset
   - Compare with current Presburger approach

### This Month

- Week 2: Constant propagation improvements
- Week 3: Write up results
- Week 4: Prepare publication draft

---

## References & Resources

### SMT-LIB Standards
- QF_BV: http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV
- QF_AUFBV: http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_AUFBV

### Z3 Documentation
- Programming Z3: https://theory.stanford.edu/~nikolaj/programmingz3.html
- Z3 Guide - Bitvectors: https://microsoft.github.io/z3guide/docs/theories/Bitvectors/

### Academic Papers
- Z3 Paper (Moura & Bjørner 2008): Core Z3 architecture
- PolySAT (2024): Latest bitvector improvements in Z3
- EVM Verification Survey: Compare with existing tools

### Tools for Comparison
- Mythril: https://github.com/ConsenSys/mythril
- Manticore: https://github.com/trailofbits/manticore
- Certora: https://www.certora.com/

---

**Document Status**: Planning
**Next Update**: After QF_BV MVP (target: 2025-11-27)
**Owner**: Michał Jan Gajda (mjgajda@gmail.com)
