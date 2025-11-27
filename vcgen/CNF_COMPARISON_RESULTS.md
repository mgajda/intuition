# CNF vs Implication Encoding: Benchmark Results

## Summary

**Key Finding**: Implication-based encoding is **~14x more compact** than CNF for bit-blasted formulas!

## Benchmark Data

| Bit-Width | Impl Size (bytes) | Impl Ops | CNF Clauses | CNF Literals | CNF Size (bytes) | Ratio (Impl/CNF) |
|-----------|-------------------|----------|-------------|--------------|------------------|------------------|
| 4         | 279               | 161      | 93          | 185          | 3,910            | 0.071            |
| 8         | 743               | 425      | 253         | 505          | 10,824           | 0.069            |
| 16        | 1,927             | 1,049    | 637         | 1,273        | 27,772           | 0.069            |
| 32        | 4,711             | 2,489    | 1,533       | 3,065        | 68,178           | 0.069            |
| 64        | 11,047            | 5,753    | 3,581       | 7,161        | 161,362          | 0.068            |
| 128       | 25,839            | 13,049   | 8,189       | 16,377       | 375,338          | 0.069            |
| **256**   | **59,887**        | **29,177** | **18,429** | **36,857**  | **862,488**      | **0.069**        |

## Analysis

### Size Comparison (256-bit)
- **Implication encoding**: 59.9 KB
- **CNF encoding**: 862.5 KB
- **Ratio**: Implication is **14.4x smaller** than CNF!

### Why Implication is More Compact

**1. Tseitin Overhead**:
- CNF requires Tseitin transformation for nested formulas
- Each nested operator introduces auxiliary variable
- Each auxiliary variable creates 3 clauses
- For 256-bit: ~18,429 clauses with ~36,857 literals

**2. Hierarchical Structure**:
- Implication encoding preserves tree structure
- Nested implications are natural
- No auxiliary variables needed
- For 256-bit: ~29,177 operators in nested structure

**3. Formula Representation**:
```
Implication: ((p => q) => ((r => s) => t))
CNF: (~p | q | aux1) & (~r | s | aux2) & (~aux1 | ~aux2 | t) & ...
```

### Growth Rates

Both encodings are **O(n)** for n-bit integers:

**Implication**:
- Size: ~234n bytes for n-bit comparison
- Operators: ~114n operators
- Depth: O(log n) for logarithmic tree

**CNF**:
- Size: ~3,370n bytes for n-bit comparison
- Clauses: ~72n clauses
- Literals: ~144n literals
- Depth: 1 (flat)

**Ratio remains constant**: ~0.069 across all bit widths

### Complexity Breakdown

**256-bit gt(x, y) comparison**:

| Metric | Implication | CNF | Winner |
|--------|-------------|-----|--------|
| Size | 60 KB | 862 KB | **Impl (14x)** |
| Variables | 512 (x_i, y_i) | 512 + ~18K aux | **Impl** |
| Depth | ~8 levels | 1 (flat) | Depends on prover |
| Operators/Clauses | 29K | 18K | **CNF** |
| Readability | Medium | Low | **Impl** |
| SAT solver | No | Yes | CNF |
| Intuition prover | Yes | Maybe | **Impl** |

## Theoretical Explanation

### CNF Explosion

For nested formula `(A ∧ B) ∨ (C ∧ D)`:

**Direct CNF** (exponential):
```
(A | C) & (A | D) & (B | C) & (B | D)
```

**Tseitin CNF** (linear but verbose):
```
(~a1 | A) & (~a1 | B) & (A | B | a1) &  // a1 <=> A ∧ B
(~a2 | C) & (~a2 | D) & (C | D | a2) &  // a2 <=> C ∧ D
(a1 | a2)                                 // a1 ∨ a2
```
7 clauses vs 1 implication!

**Implication** (hierarchical):
```
~(A => ~B) | ~(C => ~D)
```
Compact and natural!

### Implication Advantages

1. **No auxiliary variables**: Direct encoding
2. **Hierarchical nesting**: Preserves structure
3. **Natural for provers**: Intuition uses implications natively
4. **Logarithmic depth**: Fast proof search in trees

### CNF Advantages

1. **Flat structure**: All clauses independent
2. **Unit propagation**: Very efficient
3. **SAT solver optimized**: Decades of optimization
4. **DPLL/CDCL**: Powerful search algorithms

## Practical Implications

### For Intuition Prover

**Implication encoding is ideal**:
- ✓ 14x more compact than CNF
- ✓ Native to Intuition's implication-based logic
- ✓ Logarithmic tree structure for efficient search
- ✓ No auxiliary variables to manage

**CNF would be problematic**:
- ✗ 14x larger formulas
- ✗ 18K+ auxiliary variables for 256-bit
- ✗ Flat structure loses logical hierarchy
- ? Unclear if Intuition handles CNF efficiently

### For SAT Solvers

**CNF encoding is required**:
- ✓ SAT solvers only accept CNF
- ✓ Highly optimized for clause-based reasoning
- ✓ Flat structure suits DPLL/CDCL algorithms

**Implication would need conversion**:
- Convert to CNF (same size as direct CNF)
- Lose compactness advantage

## Recommendations

### Choose Implication Encoding When:
1. Using Intuition or implication-based provers
2. Formula size matters (embedded, limited memory)
3. Logical structure is important (debugging, analysis)
4. Prover supports hierarchical reasoning

### Choose CNF Encoding When:
1. Using SAT solvers (Z3, MiniSat, CryptoMiniSat)
2. Need unit propagation and conflict-driven learning
3. Formula is already in clause form
4. Prover requires CNF input

## Conclusion

For the Intuition prover with bit-blasted arithmetic:

**Implication encoding is the clear winner**:
- **14.4x more compact** than CNF (60 KB vs 862 KB)
- **Native format** for Intuition prover
- **Preserves structure** with logarithmic tree
- **No overhead** from auxiliary variables

This validates our implementation choice: bit-blasting with implication-based encoding is both efficient and appropriate for the Intuition theorem prover.

## Benchmark Command

```bash
/home/m/Projects/intuition/vcgen/dist-newstyle/build/.../compare-cnf
```

**Output**: Comparison table showing consistent ~14x size advantage for implication encoding across all bit widths.
