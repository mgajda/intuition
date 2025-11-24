# Yul Verification Implementation Roadmap

**Project**: Intuition + WP + SMT for Yul/Solidity Verification
**Current**: 28% verification rate (964/3,442 assertions)
**Target**: 70%+ verification rate
**Timeline**: 12 weeks (3 months)

**References**:
- This document: Yul-specific implementation plan
- `~/Projects/smt/PROJECT_PLAN.md`: General SMT optimization strategies
- `PLANNED_THEORIES.md`: Theory analysis and requirements
- `ASSERTION_THEORIES.md`: Detailed assertion statistics

---

## Current Status Summary

### What Works (28% Verified)
✅ **Parser**: 100% success on real-world Yul IR (79/79 VCs, 3,442 assertions)
✅ **Intuition Prover**: Fast propositional reasoning
✅ **Weakest Precondition**: VC generation from Yul
✅ **Presburger Arithmetic**: 63/79 VCs (79.7%) expressible
✅ **Function Inlining**: Eliminates function call complexity

### What's Missing (72% Not Verified)

| Gap | Assertions | % | Solution | Priority |
|-----|-----------|---|----------|----------|
| **Bitwise ops** (shl, div) | ~698 | 20% | QF_BV theory | 🎯 **1** |
| **Unknown variables** | ~568 | 16% | Constraint propagation | 🎯 **2** |
| **Conservative verification** | ~600 | 17% | Better simplification | 🎯 **2** |
| **Truly unprovable** | ~612 | 18% | Unavoidable limit | - |

---

## Phase 1: Foundation (Weeks 1-6) → Target: 60-65%

### Week 1-3: QF_BV Implementation 🎯

**Goal**: Replace QF_LIA with QF_BV for native EVM semantics

**Why QF_BV Over QF_NIA**:
- ✅ Decidable (vs. undecidable)
- ✅ Z3's native bitvector solver is excellent
- ✅ Handles modular arithmetic automatically (uint256 wraparound)
- ✅ Native bitwise operations (shl, shr, and, or, xor)
- ✅ Division/modulo as bitvector ops (not nonlinear arithmetic)

**Implementation Location**: `vcgen/app/YulLogic.hs`

#### Week 1: Research & Setup

**Research Questions** (from `~/Projects/smt/PROJECT_PLAN.md`):
1. ✅ Is QF_BV appropriate? → YES (20.3% of VCs need it, rest benefit from uint256 semantics)
2. ✅ Which Z3 version? → 4.13+ (has PolySAT optimization)
3. ✅ Which SMT-LIB logic? → QF_BV (not QF_NIA!)
4. ⚠️ How to handle mixed theories? → Test Z3's int2bv conversion

**Tasks**:
```bash
# 1. Verify Z3 version
z3 --version  # Need 4.13+

# 2. Test QF_BV on 5 sample VCs
cd /home/m/Projects/intuition/vcgen
cp vc_3.smt2 vc_3_qfbv.smt2   # Division example
cp vc_10.smt2 vc_10_qfbv.smt2 # Shift example

# 3. Manual conversion test (validate approach)
# Edit vc_3_qfbv.smt2:
# Change: (set-logic QF_LIA) → (set-logic QF_BV)
# Change: (declare-const x Int) → (declare-const x (_ BitVec 256))
# Change: (div x y) → (bvudiv x y)

z3 vc_3_qfbv.smt2
# Expected: sat/unsat with timing

# 4. Document results
echo "Results in WEEK1_QF_BV_RESEARCH.md"
```

**Deliverable**: `WEEK1_QF_BV_RESEARCH.md` with Z3 test results

#### Week 2: Type System Changes

**File to Modify**: `vcgen/app/YulLogic.hs`

**Current Code** (approximate location: around line 150-200):
```haskell
-- Current: Generate QF_LIA
generateSMTLIB2_WP :: YulProgram -> AssertionContext -> String
generateSMTLIB2_WP prog ctx = unlines [
    "(set-logic QF_LIA)",
    declareVars vars,
    emitConstraints constraints,
    "(check-sat)",
    "(get-model)"
  ]
  where
    vars = extractVariables prog
    constraints = generateWPConstraints prog ctx

-- Variable declaration (current)
declareVar :: String -> String
declareVar var = "(declare-const " ++ var ++ " Int)"

-- Range constraint (current)
emitRangeConstraint :: String -> String
emitRangeConstraint var =
  "(assert (and (>= " ++ var ++ " 0) (<= " ++ var ++ " " ++ uint256Max ++ ")))"
  where uint256Max = "115792089237316195423570985008687907853269984665640564039457584007913129639935"
```

**New Code** (QF_BV):
```haskell
-- New: Generate QF_BV
generateSMTLIB2_BV :: YulProgram -> AssertionContext -> String
generateSMTLIB2_BV prog ctx = unlines [
    "(set-logic QF_BV)",
    declareVarsBV vars,
    emitConstraintsBV constraints,
    "(check-sat)",
    "(get-model)"
  ]
  where
    vars = extractVariables prog
    constraints = generateWPConstraints prog ctx

-- Variable declaration (bitvector)
declareVarBV :: String -> String
declareVarBV var = "(declare-const " ++ var ++ " (_ BitVec 256))"

-- NO range constraints needed! Bitvectors have implicit bounds
-- This is a major simplification
```

**Testing**:
```bash
# Recompile
cd /home/m/Projects/intuition/vcgen
cabal build

# Test on 10 VCs
for i in 1 2 3 10 11 12 20 30 40 50; do
  ./dist-newstyle/build/x86_64-linux/ghc-9.6.6/vcgen-0.1.0.0/build/yulvcgen/yulvcgen \
    datasets/disl-0.6-plus/contract_${i}.sol --output vc_${i}_bv.smt2

  # Compare with Z3
  z3 vc_${i}_bv.smt2
done
```

**Deliverable**: Type system converted, 10 VCs successfully encode to QF_BV

#### Week 3: Operation Mapping

**File to Modify**: `vcgen/app/YulLogic.hs` (expression translation)

**Current Code** (approximate location: around line 250-350):
```haskell
-- Current: Translate Yul operations to QF_LIA
translateExpr :: YulExpr -> SMTExpr
translateExpr (YulAdd x y) = SMTAdd (translateExpr x) (translateExpr y)
translateExpr (YulSub x y) = SMTSub (translateExpr x) (translateExpr y)
translateExpr (YulMul x y) = SMTMul (translateExpr x) (translateExpr y)
translateExpr (YulDiv x y) = SMTDiv (translateExpr x) (translateExpr y)  -- Problem!
translateExpr (YulShl x y) = SMTUnknown  -- Cannot express in QF_LIA!
-- ... etc
```

**New Code** (QF_BV operations):
```haskell
-- New: Translate Yul operations to QF_BV
translateExprBV :: YulExpr -> SMTExpr
translateExprBV (YulAdd x y) = SMTBVAdd (translateExprBV x) (translateExprBV y)
translateExprBV (YulSub x y) = SMTBVSub (translateExprBV x) (translateExprBV y)
translateExprBV (YulMul x y) = SMTBVMul (translateExprBV x) (translateExprBV y)

-- Division: Unsigned bitvector division (not integer division!)
translateExprBV (YulDiv x y) = SMTBVUDiv (translateExprBV x) (translateExprBV y)
translateExprBV (YulMod x y) = SMTBVURem (translateExprBV x) (translateExprBV y)

-- Signed operations (EVM has these too)
translateExprBV (YulSDiv x y) = SMTBVSDiv (translateExprBV x) (translateExprBV y)
translateExprBV (YulSMod x y) = SMTBVSRem (translateExprBV x) (translateExprBV y)

-- Comparisons: Unsigned!
translateExprBV (YulLt x y) = SMTBVULt (translateExprBV x) (translateExprBV y)
translateExprBV (YulGt x y) = SMTBVUGt (translateExprBV x) (translateExprBV y)
translateExprBV (YulEq x y) = SMTEq (translateExprBV x) (translateExprBV y)

-- Signed comparisons
translateExprBV (YulSLt x y) = SMTBVSLt (translateExprBV x) (translateExprBV y)
translateExprBV (YulSGt x y) = SMTBVSGt (translateExprBV x) (translateExprBV y)

-- Bitwise operations (native!)
translateExprBV (YulShl x y) = SMTBVShl (translateExprBV x) (translateExprBV y)
translateExprBV (YulShr x y) = SMTBVLShr (translateExprBV x) (translateExprBV y)  -- Logical
translateExprBV (YulSar x y) = SMTBVAShr (translateExprBV x) (translateExprBV y)  -- Arithmetic
translateExprBV (YulAnd x y) = SMTBVAnd (translateExprBV x) (translateExprBV y)
translateExprBV (YulOr x y) = SMTBVOr (translateExprBV x) (translateExprBV y)
translateExprBV (YulXor x y) = SMTBVXor (translateExprBV x) (translateExprBV y)
translateExprBV (YulNot x) = SMTBVNot (translateExprBV x)

-- Boolean operations (EVM's iszero)
translateExprBV (YulIsZero x) =
  SMTEq (translateExprBV x) (SMTBVLit 256 0)
```

**SMT-LIB2 Emission**:
```haskell
-- Emit SMT-LIB2 bitvector operations
emitSMTExpr :: SMTExpr -> String
emitSMTExpr (SMTBVAdd x y) = "(bvadd " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVSub x y) = "(bvsub " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVMul x y) = "(bvmul " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVUDiv x y) = "(bvudiv " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVURem x y) = "(bvurem " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVSDiv x y) = "(bvsdiv " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVSRem x y) = "(bvsrem " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVULt x y) = "(bvult " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVUGt x y) = "(bvugt " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVSLt x y) = "(bvslt " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVSGt x y) = "(bvsgt " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVShl x y) = "(bvshl " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVLShr x y) = "(bvlshr " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVAShr x y) = "(bvashr " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVAnd x y) = "(bvand " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVOr x y) = "(bvor " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVXor x y) = "(bvxor " ++ emitSMTExpr x ++ " " ++ emitSMTExpr y ++ ")"
emitSMTExpr (SMTBVNot x) = "(bvnot " ++ emitSMTExpr x ++ ")"

-- Literals (256-bit hex)
emitSMTExpr (SMTBVLit 256 n) =
  "#x" ++ printf "%064x" n  -- 64 hex digits = 256 bits
```

**Testing**:
```bash
# Full benchmark run
cd /home/m/Projects/intuition/vcgen
./test_disl_parallel.sh

# Compare results
# Before (QF_LIA): 964/3,442 verified (28%)
# After (QF_BV):   Expected ~2,100/3,442 verified (61%)
```

**Evaluation Criteria** (from PROJECT_PLAN.md):
- ✅ All 79 VCs translate without errors
- ✅ At least 50% verification rate achieved (target: 60-65%)
- ✅ No performance regression (avg < 500ms per VC)

**Deliverable**:
- QF_BV implementation complete
- Benchmark results: `WEEK3_QF_BV_RESULTS.md`
- Expected: 28% → 60-65% verification rate (+1,150-1,280 assertions)

---

### Week 4-6: Constraint Propagation 🎯

**Goal**: Eliminate "unknown" variables through aggressive constant propagation

**Why This Matters**: 16.5% of VCs (13/79) have unknown variables from incomplete symbolic execution.

**Implementation Location**: New module `vcgen/app/Propagator.hs`

#### Week 4: Analysis Phase

**Research Questions** (from PROJECT_PLAN.md):
1. ✅ Is event-driven propagation appropriate? → YES (Beaver paper: 5-100X on software)
2. ✅ Which unknowns are constants? → Need to analyze VC generation
3. ⚠️ Forward or backward propagation? → Test both
4. ⚠️ Integration point: WP generation or VC encoding? → Profile both

**Task**: Analyze unknown variable sources

```bash
# Create analysis script
cat > analyze_unknowns.py << 'EOF'
#!/usr/bin/env python3
import re
from pathlib import Path

vcgen_dir = Path("/home/m/Projects/intuition/vcgen")
smt_files = sorted(vcgen_dir.glob("vc_*.smt2"))

unknown_sources = {
    'shl_uncalculated': 0,   # shl(64, 1) → unknown
    'div_uncalculated': 0,   # div operations
    'mload_symbolic': 0,     # mload(addr) where addr unknown
    'function_result': 0,    # function call result not inlined
}

for smt_file in smt_files:
    content = smt_file.read_text()

    if 'unknown' in content:
        # Classify the unknown
        if 'shl' in content:
            unknown_sources['shl_uncalculated'] += 1
        elif 'div' in content:
            unknown_sources['div_uncalculated'] += 1
        # ... more classification logic

        print(f"{smt_file.name}: {content.count('unknown')} unknowns")

print("\n=== Unknown Sources ===")
for source, count in sorted(unknown_sources.items(), key=lambda x: -x[1]):
    print(f"{source}: {count} VCs")
EOF

python3 analyze_unknowns.py > UNKNOWN_SOURCES_ANALYSIS.txt
```

**Deliverable**: `UNKNOWN_SOURCES_ANALYSIS.txt` with classification

#### Week 5: Implementation

**Create New Module**: `vcgen/app/Propagator.hs`

```haskell
module Propagator where

import qualified Data.Map as Map
import Control.Monad.State

-- Event-driven constraint propagator (Beaver-style)
data PropagatorState = PropagatorState
  { constants :: Map.Map String Integer  -- var → value
  , queue :: [PropagationEvent]           -- pending rewrites
  , constraints :: [SMTExpr]              -- accumulated constraints
  }

data PropagationEvent
  = Rewrite SMTExpr String Integer  -- (expr, var, value)
  | Simplify SMTExpr

-- Initialize empty propagator
emptyPropagator :: PropagatorState
emptyPropagator = PropagatorState Map.empty [] []

-- Add constraint and trigger propagation
addConstraint :: SMTExpr -> State PropagatorState ()
addConstraint expr = do
  state <- get

  -- Check if this is a constant equality: var = value
  case extractConstantEquality expr of
    Just (var, value) -> do
      -- Record constant
      modify $ \s -> s { constants = Map.insert var value (constants s) }

      -- Trigger: propagate to all existing constraints
      let affected = filter (usesVariable var) (constraints state)
      modify $ \s -> s { queue = map (\c -> Rewrite c var value) affected ++ queue s }

    Nothing -> do
      -- Not a constant, just record
      modify $ \s -> s { constraints = expr : constraints s }

-- Process queue until fixpoint
propagate :: State PropagatorState ()
propagate = do
  state <- get
  case queue state of
    [] -> return ()  -- Done

    (event:rest) -> do
      modify $ \s -> s { queue = rest }
      handleEvent event
      propagate  -- Continue

-- Handle one propagation event
handleEvent :: PropagationEvent -> State PropagatorState ()
handleEvent (Rewrite expr var value) = do
  let expr' = substitute expr var (SMTBVLit 256 value)
  let simplified = simplifyExpr expr'

  -- Simplified form may reveal new constants!
  case extractConstantEquality simplified of
    Just (newVar, newValue) ->
      addConstraint simplified  -- Recursive propagation
    Nothing ->
      modify $ \s -> s { constraints = simplified : constraints s }

handleEvent (Simplify expr) = do
  let simplified = simplifyExpr expr
  modify $ \s -> s { constraints = simplified : constraints s }

-- Constant folding and algebraic simplification
simplifyExpr :: SMTExpr -> SMTExpr
simplifyExpr (SMTBVAdd (SMTBVLit w1 n) (SMTBVLit w2 m))
  | w1 == w2 = SMTBVLit w1 ((n + m) `mod` (2^w1))  -- Modular arithmetic!

simplifyExpr (SMTBVMul x (SMTBVLit _ 0)) = SMTBVLit (getBVWidth x) 0
simplifyExpr (SMTBVMul x (SMTBVLit _ 1)) = x

simplifyExpr (SMTBVShl (SMTBVLit w 1) (SMTBVLit _ shift)) =
  SMTBVLit w (2^shift `mod` (2^w))  -- Compute 2^shift

simplifyExpr (SMTBVUDiv x (SMTBVLit _ 1)) = x

-- ... many more simplification rules

simplifyExpr expr = expr  -- No simplification applicable

-- Extract constant equality: x = 42
extractConstantEquality :: SMTExpr -> Maybe (String, Integer)
extractConstantEquality (SMTEq (SMTVar name) (SMTBVLit _ value)) =
  Just (name, value)
extractConstantEquality (SMTEq (SMTBVLit _ value) (SMTVar name)) =
  Just (name, value)
extractConstantEquality _ = Nothing

-- Check if expression uses variable
usesVariable :: String -> SMTExpr -> Bool
usesVariable var (SMTVar name) = var == name
usesVariable var (SMTBVAdd x y) = usesVariable var x || usesVariable var y
-- ... recursive for all expression types
```

**Testing**:
```bash
# Test on 13 VCs with unknowns
cd /home/m/Projects/intuition/vcgen

# VCs known to have unknowns: 10, 11, 16, ... (from earlier analysis)
for i in 10 11 16 19 28 38 43 50 52 64 65 67 74; do
  echo "Testing vc_${i}.smt2"

  # Before propagation: has "unknown"
  grep "unknown" vc_${i}.smt2

  # After propagation: should eliminate some/all
  ./yulvcgen --with-propagation datasets/.../contract_${i}.sol
done
```

**Evaluation Criteria**:
- ✅ Reduce unknowns: 16.5% → <5% of VCs (13 → <4 VCs)
- ✅ Verification rate: +10-15 percentage points
- ✅ Performance: <10% overhead

**Deliverable**:
- `Propagator.hs` module
- `WEEK5_PROPAGATION_RESULTS.md`
- Expected: 60% → 70-72% verification rate (+350-400 assertions)

#### Week 6: Integration & Benchmarking

**Integrate into Pipeline**: Modify `vcgen/app/YulVCgen.hs`

```haskell
-- Current pipeline (simplified):
main = do
  yulCode <- readFile inputFile
  prog <- parseYul yulCode
  assertions <- extractAssertions prog

  forM_ assertions $ \assertion -> do
    vc <- generateVC prog assertion
    result <- verifyWithIntuition vc
    putStrLn $ if result then "✅ VERIFIED" else "❌ NOT VERIFIED"

-- New pipeline (with propagation):
main = do
  yulCode <- readFile inputFile
  prog <- parseYul yulCode
  assertions <- extractAssertions prog

  forM_ assertions $ \assertion -> do
    vc <- generateVC prog assertion

    -- NEW: Apply propagation
    let (vcSimplified, stats) = runPropagator vc
    putStrLn $ "Propagation: " ++ show (unknownsEliminated stats) ++ " unknowns eliminated"

    result <- verifyWithIntuition vcSimplified
    putStrLn $ if result then "✅ VERIFIED" else "❌ NOT VERIFIED"

-- Propagator integration
runPropagator :: [SMTExpr] -> ([SMTExpr], PropagationStats)
runPropagator constraints =
  let initialState = emptyPropagator
      finalState = execState (mapM_ addConstraint constraints >> propagate) initialState
      stats = PropagationStats
        { unknownsBefore = countUnknowns constraints
        , unknownsAfter = countUnknowns (constraints finalState)
        , constantsFound = Map.size (constants finalState)
        }
  in (constraints finalState, stats)
```

**Full Benchmark**:
```bash
cd /home/m/Projects/intuition/vcgen
./test_disl_parallel.sh > benchmark_with_propagation.log

# Extract statistics
grep "VERIFIED" benchmark_with_propagation.log | wc -l
# Expected: ~2,400-2,500 / 3,442 (70-72%)
```

**Deliverable**:
- Integration complete
- `benchmark_with_propagation.log`
- `PHASE1_FINAL_RESULTS.md`:
  - Before: 964/3,442 (28%)
  - After QF_BV: ~2,100/3,442 (61%)
  - After Propagation: ~2,450/3,442 (71%)
  - **Total Gain: +43 percentage points (+1,486 assertions)**

---

## Phase 1 Evaluation Checkpoint

### Success Criteria

**Must Achieve**:
- ✅ Verification rate: 60-70% (target: 70%)
- ✅ Performance: <1s average per contract
- ✅ Soundness: No false positives (Z3 sanity check)
- ✅ All 79 VCs process without errors

**If Not Achieved (<60%)**:
1. Debug QF_BV implementation (check operation mappings)
2. Profile propagation effectiveness (analyze remaining unknowns)
3. Consider fallback: Boolector instead of Z3?

**If Achieved (≥70%)**:
- ✅ Publish results! (This is strong paper material)
- ⏸️ Pause optimizations (Phase 2 optional)
- 📝 Write paper draft

---

## Phase 2: Optimizations (Weeks 7-12) → Target: 75-80%

**Prerequisites**:
- ✅ Phase 1 complete with ≥60% verification rate
- ✅ QF_BV + Propagation working
- ⚠️ Bottlenecks identified through profiling

### Week 7-8: Incremental Solving (Conditional) ⚠️

**Decision Point**: Test Z3's incremental API first!

```bash
# Week 7: Research phase
cd /home/m/Projects/intuition/vcgen

# Create test script
cat > test_incremental.py << 'EOF'
import z3
import time

# Load representative VC
vc = load_vc("vc_10.smt2")

# Test 1: Non-incremental
solver_fresh = z3.Solver()
solver_fresh.add(vc)
start = time.time()
result1 = solver_fresh.check()
time1 = time.time() - start

# Test 2: Incremental with push/pop
solver_incr = z3.Solver()
solver_incr.push()
solver_incr.add(cheap_constraints(vc))
start = time.time()
result2_base = solver_incr.check()
solver_incr.add(expensive_constraints(vc))
result2_full = solver_incr.check()
time2 = time.time() - start
solver_incr.pop()

print(f"Fresh: {time1}ms, Incremental: {time2}ms")
print(f"Speedup: {time1/time2}x" if time2 < time1 else "No benefit")
EOF

python3 test_incremental.py
```

**Decision Criteria**:
- ✅ Proceed: If average speedup >1.5x on complex VCs
- ❌ Skip: If overhead or no benefit

**If Beneficial** (Week 8):
- Implement incremental wrapper in `IncrementalSolver.hs`
- Integrate with k-induction for loop unrolling
- Expected gain: +5-10% on complex VCs

**If Not Beneficial**:
- Skip implementation entirely
- Document why in `INCREMENTAL_EVALUATION.md`

---

### Week 9-11: Truncating Abstraction (Conditional) ⭐

**Goal**: Optimize overflow checks by computing only necessary bits

**Motivation**: 55% of assertions (1,893/3,442) are overflow checks (panic_error_0x11, 0x41)

**Decision Point**: Profile overflow check performance

```bash
# Week 9: Profiling
cd /home/m/Projects/intuition/vcgen

# Classify assertions by type
cat > classify_assertions.py << 'EOF'
import re
from pathlib import Path

results = {
    'overflow_checks': [],
    'division_by_zero': [],
    'bounds_checks': [],
    'other': []
}

for vc_file in Path('.').glob('vc_*.smt2'):
    content = vc_file.read_text()

    # Classify by panic error code or operation
    if 'panic_error_0x11' in content or 'panic_error_0x41' in content:
        results['overflow_checks'].append(vc_file.name)
    elif 'panic_error_0x12' in content or 'iszero.*div' in content:
        results['division_by_zero'].append(vc_file.name)
    # ... more patterns

print(f"Overflow checks: {len(results['overflow_checks'])} VCs")
print(f"Division by zero: {len(results['division_by_zero'])} VCs")
# ...

# Profile these specifically
import subprocess
for vc in results['overflow_checks'][:10]:
    start = time.time()
    subprocess.run(['z3', vc], capture_output=True)
    elapsed = time.time() - start
    print(f"{vc}: {elapsed*1000:.1f}ms")
EOF

python3 classify_assertions.py > OVERFLOW_PROFILE.txt
```

**Decision Criteria**:
- ✅ Proceed: If overflow checks take >50% of total verification time
- ❌ Skip: If already fast enough

**If Beneficial** (Week 10-11):

Implement truncating abstraction for common patterns:

```haskell
-- Truncating abstraction for addition overflow
encodeAdditionOverflow :: SMTExpr -> SMTExpr -> SMTExpr
encodeAdditionOverflow x y =
  -- Addition overflows iff carry out of bit 255
  -- Fast path: Check only if both MSBs might overflow
  let x_msb = SMTExtract 255 255 x  -- Just bit 255
      y_msb = SMTExtract 255 255 y
  in
    -- If both MSBs are 0, definitely no overflow
    if x_msb == bv1_0 && y_msb == bv1_0
    then SMTFalse  -- Proven safe without full addition
    else
      -- Need full check (slow path)
      let sum = SMTBVAdd x y
          overflow = SMTBVULt sum x  -- Standard overflow check
      in overflow

-- Truncating abstraction for multiplication overflow
encodeMultiplicationOverflow :: SMTExpr -> SMTExpr -> SMTExpr
encodeMultiplicationOverflow x y =
  -- Multiplication overflows iff high 128 bits of result non-zero
  -- Fast path: If one operand ≤ 128 bits, use simpler check
  let x_high = SMTExtract 255 128 x
      y_high = SMTExtract 255 128 y
  in
    if x_high == bv128_0 then
      -- x fits in 128 bits, simpler overflow check
      let product_approx = SMTBVMul (SMTExtract 127 0 x) y
          overflow_approx = SMTBVUGt (SMTExtract 255 128 product_approx) bv128_0
      in overflow_approx
    else if y_high == bv128_0 then
      -- Symmetric case
      encodeMultiplicationOverflow y x
    else
      -- Slow path: Full 256×256 multiplication check
      let product = SMTBVMul x y
          overflow = SMTBVULt product x  -- Standard check
      in overflow
```

**Expected Gain**: 2-5X speedup on overflow checks (55% of assertions)
→ Overall: +10-15% verification rate

**Deliverable**:
- `TruncatingAbstraction.hs` module
- `TRUNCATING_RESULTS.md` with before/after timings
- **Novel Contribution** (cite Fedyukovich & Gurfinkel 2024)

---

### Week 12: Final Evaluation & Paper Draft

**Tasks**:
1. Run full benchmark on complete DISL dataset (1,000 contracts)
2. Compare with ESBMC-Solidity and other tools
3. Write paper draft with results
4. Create artifact for reproducibility

**Expected Final Results**:
- Verification rate: 70-75%
- Average time: <1s per contract
- Scalability: Handles 1,000+ contracts
- Soundness: 0% false positives

---

## Alternative Approaches (If Needed)

### Alternative 1: Pure Z3 (No Intuition)

**When to Consider**: If Intuition overhead is significant

**Test**:
```bash
# Compare Intuition + Z3 vs. Pure Z3
for vc in vc_*.smt2; do
  # With Intuition
  time1=$(./yulvcgen --with-intuition $vc)

  # Pure Z3
  time2=$(z3 $vc)

  echo "$vc: Intuition+Z3=${time1}ms, Z3=${time2}ms"
done
```

**Decision**: If Z3 consistently faster, bypass Intuition for SMT queries

### Alternative 2: Boolector Instead of Z3

**When to Consider**: If Z3's bitvector solver is slow

**Test**:
```bash
# Convert VCs to Boolector format
for vc in vc_*.smt2; do
  boolector $vc  # Test Boolector
  z3 $vc         # Compare with Z3
done
```

**Decision**: If Boolector >2x faster on average, switch backend

---

## Citation Strategy (From PROJECT_PLAN.md)

### Must Cite in Paper

**Foundational**:
- Barrett et al. (2009): "Satisfiability Modulo Theories" - SMT background
- de Moura & Bjørner (2008): "Z3: An Efficient SMT Solver" - SMT backend
- Kroening & Strichman (2016): "Decision Procedures" Ch. 6 - Bitvector theory

**Yul/Solidity Verification**:
- Alt & Reitwiessner (2018): "SMT-based verification of solidity" - Solidity SMTChecker
- Song et al. (2022): "ESBMC-Solidity: An SMT-Based Model Checker" - Baseline comparison

**Optimizations** (if implemented):
- Jha et al. (2009): "Beaver: Engineering an Efficient SMT Solver" - Constraint propagation justification
- Niemetz et al. (2024): "PolySAT: Word-level Bit-vector Reasoning in Z3" - If using PolySAT
- Fedyukovich & Gurfinkel (2024): "Truncating abstraction" - If implementing truncating abstraction

**Do NOT Cite** (not applicable):
- ❌ NFLSAT (different problem type)
- ❌ LTLf/temporal logic (no temporal properties)
- ❌ Full separation logic (overkill)

---

## Project Outputs

### Week 1-3: QF_BV Implementation
- [ ] `WEEK1_QF_BV_RESEARCH.md` - Z3 testing results
- [ ] `YulLogic.hs` - QF_BV encoding
- [ ] `WEEK3_QF_BV_RESULTS.md` - Benchmark (28% → 60%)

### Week 4-6: Constraint Propagation
- [ ] `UNKNOWN_SOURCES_ANALYSIS.txt` - Unknown variable classification
- [ ] `Propagator.hs` - Event-driven propagation module
- [ ] `WEEK5_PROPAGATION_RESULTS.md` - Unknown elimination stats
- [ ] `PHASE1_FINAL_RESULTS.md` - Combined results (28% → 70%)

### Week 7-12: Optimizations (Conditional)
- [ ] `INCREMENTAL_EVALUATION.md` - Incremental API test results (proceed/skip)
- [ ] `OVERFLOW_PROFILE.txt` - Overflow check profiling (proceed/skip)
- [ ] `TruncatingAbstraction.hs` - Overflow optimization (if beneficial)
- [ ] `TRUNCATING_RESULTS.md` - Final benchmark (70% → 75%+)

### Paper Draft
- [ ] Introduction (problem, 28% → 70%+ improvement)
- [ ] Background (Yul IR, SMT, bitvectors)
- [ ] Approach (QF_BV + WP + Propagation)
- [ ] Evaluation (DISL dataset, comparison with ESBMC)
- [ ] Related Work (citations above)
- [ ] Conclusion

---

## Integration with SMT Project

This roadmap integrates with `~/Projects/smt/PROJECT_PLAN.md`:

**Alignment**:
- ✅ QF_BV implementation follows PROJECT_PLAN.md Branch 1.1 (Weeks 1-3)
- ✅ Constraint propagation follows Branch 1.2 (Weeks 4-6)
- ✅ Incremental solving follows Branch 1.3 (Week 6-8, conditional)
- ✅ Truncating abstraction follows Branch 2.2 (Weeks 9-12, conditional)

**Differences**:
- This roadmap is Yul-specific (Haskell implementation in `vcgen/`)
- PROJECT_PLAN.md is general SMT strategy (Python examples)
- Both target same 28% → 70% improvement goal

**Coordination**:
- Use PROJECT_PLAN.md for research questions and decision criteria
- Use this roadmap for Yul-specific implementation details
- Document results in both locations

---

**Status**: Ready to begin Phase 1 (Weeks 1-6)
**Next Action**: Week 1 QF_BV research (test Z3 4.13+ on sample VCs)
**Updated**: 2025-11-24
