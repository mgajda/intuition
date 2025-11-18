# Strategy 2: Custom Yul Parser with BNFC

## Overview

This branch implements **Strategy 2** from the Solidity verification research plan: a custom Yul parser using BNFC (BNF Converter) to parse Yul intermediate representation and generate verification conditions.

## Implementation Status

### ✅ Completed

1. **Yul Grammar Definition** (`Yul.cf`)
   - Defined BNFC grammar for core Yul constructs
   - Supports: variables, literals, function calls, if statements, blocks, function definitions
   - Handles hex literals (common in EVM)
   - Includes switch statements and for loops

2. **Parser Generation**
   - BNFC successfully generates Haskell parser modules
   - Generated modules in `app/Yul/`:
     - `AbsYul.hs` - Abstract syntax tree types
     - `ParYul.hs` - Parser
     - `LexYul.x` - Lexer specification
     - `PrintYul.hs` - Pretty printer
     - `SkelYul.hs` - AST traversal skeleton

3. **Build Integration**
   - Updated `Setup.hs` to process both Tiny.cf and Yul.cf
   - Modified `vcgen.cabal` to include Yul modules
   - Created `yulvcgen` executable

4. **Example Program**
   - Created `examples/simple_assert.yul` demonstrating:
     - Function with overflow check
     - Assertions via `invalid()` calls
     - Hex literals for max uint256 value

### 🚧 In Progress

5. **Verification Condition Generation** (`app/YulLogic.hs`)
   - Skeleton created with type definitions
   - TODO: Implement `vcGenYul` function
   - TODO: Map Yul built-ins to logical formulas
   - TODO: Handle EVM-specific operations (sload, sstore)

### ❌ Not Yet Implemented

6. **SMT Integration**
   - SBV library dependency commented out (GHC version incompatibility)
   - Alternative: Can use existing Logic.hs infrastructure
   - Alternative: Generate SMT-LIB output directly

7. **Assertion Extraction**
   - Need to traverse AST to find `invalid()` calls
   - Generate VCs ensuring invalid() is unreachable

8. **Full VC Generation Pipeline**
   - Translate Yul expressions to Tiny formulas
   - Handle storage/memory models
   - Implement weakest precondition for Yul

## Usage

### Build

```bash
cd vcgen
cabal build
```

This will:
1. Run BNFC on `Yul.cf` to generate parser
2. Compile Haskell modules
3. Create `yulvcgen` executable

### Test

```bash
./dist-newstyle/build/x86_64-linux/ghc-9.6.6/vcgen-0.1.0.0/build/yulvcgen/yulvcgen < examples/simple_assert.yul
```

Output:
```
=== Yul Verification Condition Generator ===
Strategy 2: Custom Yul Parser with BNFC

Parse Successful!
AST: [Generated AST shown here]
Pretty printed:
[Formatted Yul code]
```

## Architecture

### Files Created/Modified

```
vcgen/
├── Yul.cf                    # BNFC grammar definition
├── Setup.hs                  # Modified: process Yul.cf
├── vcgen.cabal              # Modified: add Yul modules and yulvcgen executable
├── app/
│   ├── YulLogic.hs          # VC generation logic (skeleton)
│   ├── YulVCgen.hs          # Main executable
│   └── Yul/                 # BNFC-generated files
│       ├── AbsYul.hs
│       ├── ParYul.hs
│       ├── LexYul.x
│       ├── PrintYul.hs
│       └── ...
└── examples/
    └── simple_assert.yul    # Test case
```

### Key Design Decisions

1. **Yul Subset**: Focused on control flow and assertions, not full EVM semantics
2. **Reuse Infrastructure**: Plan to leverage existing Logic.hs for formulas
3. **Modular Design**: Separate parsing (BNFC) from VC generation (YulLogic.hs)
4. **SBV Deferred**: Skipped SBV library due to GHC compatibility; can add later or use alternatives

## Next Steps

### Short Term

1. Implement `extractAssertions` to find `invalid()` calls in AST
2. Create translation from Yul types to Tiny types
3. Implement basic `vcGenYul` for assignments and if statements

### Medium Term

4. Handle Yul function definitions and calls
5. Model EVM storage (simplified: Map Int Int)
6. Generate VCs for assertions

### Long Term

7. Add SBV integration for SMT solving
8. Generate SMT-LIB output
9. Integrate with Z3/CVC5 backend
10. Test on real Solidity-compiled Yul code

## Comparison with Other Strategies

### vs Strategy 1 (hevm)
- **Pro**: Full control over VC generation algorithm
- **Pro**: Educational value - understand SMT encoding
- **Con**: More implementation work
- **Con**: Need to handle EVM semantics ourselves

### vs Strategy 3 (solc AST + Aeson)
- **Pro**: Simpler syntax (Yul vs full Solidity)
- **Pro**: Yul is canonical IR used by solc
- **Con**: Limited to Yul (not full Solidity)
- **Con**: Still need to model EVM

## References

- [Yul Specification](https://docs.soliditylang.org/en/latest/yul.html)
- [BNFC Documentation](https://bnfc.digitalgrammars.com/)
- Original research notes: `SOLIDITY_SMT_TASKS.md`

## Testing

### Current Test Case

`examples/simple_assert.yul` demonstrates:
1. Overflow check: `if gt(x, MAX_UINT256-1) { invalid() }`
2. Post-increment assertion: `if iszero(gt(result, x)) { invalid() }`
3. Top-level assertion after function call

### Expected VC (not yet generated)

```
∀x. x ≤ MAX_UINT256-1 =>
  let result = x + 1 in
    result > x  -- This should be provable
```

## Known Limitations

1. **SBV Not Integrated**: GHC 9.6.6 incompatible with SBV 12.x
2. **No VC Generation Yet**: Parser works, but VC generation is TODO
3. **Simplified EVM Model**: No gas, no external calls, simplified storage
4. **Assertion Detection**: Only recognizes `invalid()`, not `require()/assert()`

## Conclusion

Strategy 2 successfully demonstrates:
- ✅ Yul parsing with BNFC
- ✅ AST generation and pretty printing
- ✅ Build integration
- 🚧 Foundation for VC generation (in progress)

This provides a solid base for custom verification condition generation with full control over the encoding strategy.
