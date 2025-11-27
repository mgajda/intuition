# Arithmetic Encoding with Implications

## Key Insight

For single-bit arithmetic, the implication operator => encodes less-than-or-equal:
- `a => b` means `a ≤ b` (if a=1 then b=1; if a=0 then b can be 0 or 1)
- `a <=> b` means `a = b` (bidirectional: a=>b and b=>a)

## Multi-Bit Encoding

For n-bit integers x = [x₀, x₁, ..., x_{n-1}] and y = [y₀, y₁, ..., y_{n-1}] (MSB at n-1):

### Greater-Than: gt(x, y)

Recursive definition:
```
gt(x, y) = (x_{n-1} > y_{n-1}) ∨
           (x_{n-1} = y_{n-1} ∧ gt(x[0:n-2], y[0:n-2]))
```

In implication encoding:
```
gt(x, y) ↔ gt_bit(x_{n-1}, y_{n-1}, gt(x[0:n-2], y[0:n-2]))

where gt_bit(x_i, y_i, rest) =
  (x_i ∧ ¬y_i) ∨    % x_i=1, y_i=0 → definitely greater
  (x_i ↔ y_i) ∧ rest % x_i=y_i → depends on rest
```

### Logarithmic Tree Structure

Instead of linear recursion, use balanced tree:
- Split bits into halves
- Compare upper half first
- If equal, compare lower half
- Depth: O(log n)

### Implementation Strategy

For 256-bit EVM integers:
1. **Start simple**: Keep atomic predicates gt(x,y), use theory axioms
2. **Phase 2**: Implement bit-level encoding for critical operations
3. **Optimization**: Use logarithmic trees for large bit-widths

## Encoding in ImplicationFormula

Current datatype:
```haskell
data ImplicationFormula
  = ImpAtom String [ImplicationTerm]  -- gt(x, y)
  | ImpNot ImplicationFormula
  | ImpImpl ImplicationFormula ImplicationFormula
  | ImpFalse
```

Future extension for bit-level:
```haskell
data ImplicationFormula
  = ...
  | ImpBitGt [ImplicationTerm] [ImplicationTerm]  -- Multi-bit gt
  | ImpBitEq [ImplicationTerm] [ImplicationTerm]  -- Multi-bit eq
```

## References

- Encoding Basic Arithmetic Operations for SAT-Solvers (adapted for implications)
- Encoding Linear Constraints with Implication Chains to CNF (adapted for implications)
- Key difference: CNF uses clauses, we use pure implications
