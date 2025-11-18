# Solidity SMT Verification - Project Task List

Based on conversations with Gemini about implementing Solidity/Yul to SMT-LIB verification in Haskell.

## Overview

**Objective:** Implement a Haskell-based tool that translates Solidity's Yul intermediate representation to SMT-LIB verification conditions using the SBV library.

**Source Conversations:** Threads 11-24 (14 total threads)

**Related File:** `solidity_smt_conversations.md` (163 KB)

---

## Key Themes Identified

- **Haskell Implementation**: Threads 11, 13, 14, 15, 16, 17, 18, 20, 21, 23
- **Yul To Smt**: Threads 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24
- **Verification Conditions**: Threads 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24
- **Sbv Library**: Threads 12, 13, 14, 15
- **Solidity Compiler**: Threads 14, 16, 17, 18, 19, 21, 22, 24
- **Loops Conditions**: Threads 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 24
- **Binary Operators**: Threads 15, 17, 18, 20
- **Code Examples**: Threads 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 23

---

## Implementation Tasks

### 1. Core Yul Data Types and AST

**Threads:** 14, 15, 20, 21

- [ ] Define Yul type system (`YulType`: `YulBV256`, `YulBool`, etc.)
- [ ] Create generic binary operator data type
  - [ ] Arithmetic operators (Add, Sub, Mul, Div)
  - [ ] Comparison operators (Lt, Gt, Eq)
  - [ ] Logical operators (And, Or)
- [ ] Define Yul expression AST
  - [ ] Variables (`YulVar`)
  - [ ] Literals (`YulLitBV`, `YulLitBool`)
  - [ ] Binary operations
  - [ ] Function calls
- [ ] Define Yul statement types
  - [ ] Variable declarations
  - [ ] Assignments
  - [ ] Function definitions

### 2. Control Flow Handling

**Threads:** 17, 19, 23

- [ ] Implement loop translation
  - [ ] Loop invariants
  - [ ] Loop unrolling (bounded)
  - [ ] Termination conditions
- [ ] Implement conditional (if/switch) translation
  - [ ] Branch condition encoding
  - [ ] Path condition tracking
- [ ] Handle nested control structures

### 3. SBV Integration

**Threads:** 14, 15, 21

- [ ] Set up SBV library integration
- [ ] Map Yul types to SBV types
  - [ ] `YulBV256` → `SWord 256`
  - [ ] `YulBool` → `SBool`
- [ ] Implement symbolic variable management
- [ ] Create symbolic execution monad
- [ ] Generate SMT-LIB output from SBV

### 4. Verification Condition Generation

**Threads:** 13, 21, 23

- [ ] Define verification condition structure
- [ ] Implement weakest precondition calculation
- [ ] Generate assertions for:
  - [ ] No overflow/underflow
  - [ ] No division by zero
  - [ ] Valid memory access
  - [ ] Custom user assertions
- [ ] Path condition accumulation

### 5. Solidity Compiler Integration

**Threads:** 22, 24

- [ ] Study Solidity compiler's SMT checker implementation
  - [ ] Identify relevant source files
  - [ ] Understand CHC (Constrained Horn Clauses) encoding
  - [ ] Document SSA (Static Single Assignment) transformation
- [ ] Implement similar architecture in Haskell
- [ ] Support Yul IR (intermediate representation) input

### 6. EVM Bytecode Analysis (Optional)

**Threads:** 11, 12

- [ ] Integrate `hs-web3` for bytecode retrieval
- [ ] Parse EVM bytecode to recover Yul-like structure
- [ ] Test on real contracts (e.g., Uniswap)
  - Note: Full verification of complex contracts requires
    abstraction and bounded analysis

---

## Code Artifacts to Create

### Main Modules

```
src/
├── Yul/
│   ├── Types.hs           # Yul type system
│   ├── AST.hs             # Yul AST definitions
│   ├── Parser.hs          # Parse Yul code
│   └── Pretty.hs          # Pretty printer
├── SMT/
│   ├── Translation.hs     # Yul → SBV translation
│   ├── SymbolicExec.hs    # Symbolic execution monad
│   └── VerificationCondition.hs  # VC generation
├── Solidity/
│   ├── Compiler.hs        # Interface to solc
│   └── IR.hs              # Yul IR handling
└── Main.hs                # CLI tool
```

### Example Code Files

Based on the conversations, create these reference implementations:

1. **YulTypes.hs** - Generic type-safe operators (Thread 20, 21)
2. **YulSMTGenSBV.hs** - Complete Yul→SBV translator (Thread 21)
3. **ControlFlow.hs** - Loop and condition handling (Thread 17, 19, 23)
4. **VCGen.hs** - Verification condition generator (Thread 13, 23)

---

## Testing Strategy

- [ ] Unit tests for each Yul operator translation
- [ ] Integration tests with simple Yul programs
- [ ] Property-based testing with QuickCheck
- [ ] Benchmark against Solidity's built-in SMTChecker
- [ ] Real-world contract analysis (with bounded exploration)

---

## Documentation Needs

- [ ] Architecture overview
- [ ] Yul language subset supported
- [ ] SMT encoding specification
- [ ] API documentation
- [ ] Usage examples and tutorials
- [ ] Comparison with Solidity SMTChecker

---

## Research Questions from Conversations

- **Thread 12:** How to handle state explosion in complex contracts like Uniswap?
- **Thread 13:** What properties beyond "no revert" should be verified?
- **Thread 17:** How to encode loop invariants automatically?
- **Thread 19:** How does Solidity compiler handle CHC encoding?
- **Thread 22:** What is the SSA transformation in solc?
- **Thread 24:** Which files implement model checking in solc codebase?

---

## Recommended Next Steps

1. **Read** `solidity_smt_conversations.md` thoroughly
2. **Set up** Haskell project with SBV dependency
3. **Implement** basic Yul types and operators (Task 1)
4. **Study** Solidity compiler SMT checker source code (Task 5)
5. **Create** simple proof-of-concept translator
6. **Test** with minimal Yul examples
7. **Iterate** on control flow and VC generation

---

## References

- **Conversations:** `solidity_smt_conversations.md`
- **Solidity Docs:** https://docs.soliditylang.org/en/latest/smtchecker.html
- **SBV Library:** https://hackage.haskell.org/package/sbv
- **Yul Spec:** https://docs.soliditylang.org/en/latest/yul.html
- **SMT-LIB:** https://smtlib.cs.uiowa.edu/
- **Solidity Compiler:** https://github.com/ethereum/solidity

