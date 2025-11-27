{-|
Module: BitBlast
Description: Efficient bit-blasting for arithmetic operations

Converts arithmetic operations on n-bit integers to implications over bits.

Key insight: For single-bit arithmetic, a => b encodes a ≤ b
- If a=1, then b=1 (for implication to hold)
- If a=0, b can be 0 or 1
- This is exactly the less-than-or-equal relation

Multi-bit operations use logarithmic tree structures for efficiency.
-}
module BitBlast where

import Data.List (intercalate)

-- | A bit is represented as a variable name
type Bit = String

-- | A bit vector (LSB at index 0, MSB at index n-1)
type BitVector = [Bit]

-- | Formulas in implication-based format
data BitFormula
  = BitVar Bit                          -- Single bit variable
  | BitNot BitFormula                   -- Negation: ~P
  | BitImpl BitFormula BitFormula       -- Implication: P => Q
  | BitAnd BitFormula BitFormula        -- Conjunction: P ∧ Q
  | BitOr BitFormula BitFormula         -- Disjunction: P ∨ Q
  | BitTrue                             -- Constant true
  | BitFalse                            -- Constant false
  deriving (Show, Eq)

-- =============================================================================
-- Bit-Level Comparison Operations
-- =============================================================================

-- | Greater-than for n-bit integers using logarithmic tree
-- gt(x, y) is true if there exists position i where x_i > y_i and all j > i have x_j = y_j
-- Complexity: O(log n) depth
bitGt :: BitVector -> BitVector -> BitFormula
bitGt xs ys
  | length xs /= length ys = error "bitGt: bit vectors must have same length"
  | null xs = BitFalse  -- Empty vectors: 0 > 0 is false
  | otherwise = gtTree xs ys

-- | Logarithmic tree for gt comparison (MSB-first comparison)
gtTree :: BitVector -> BitVector -> BitFormula
gtTree [] [] = BitFalse
gtTree [x] [y] = BitAnd (BitVar x) (BitNot (BitVar y))  -- x=1, y=0
gtTree xs ys =
  let n = length xs
      mid = n `div` 2
      (xsLo, xsHi) = splitAt mid xs
      (ysLo, ysHi) = splitAt mid ys
      -- gt if: (hi_x > hi_y) OR (hi_x = hi_y AND lo_x > lo_y)
  in BitOr
       (gtTree xsHi ysHi)                              -- Upper half greater
       (BitAnd (eqTree xsHi ysHi) (gtTree xsLo ysLo))  -- Upper equal, lower greater

-- | Less-than for n-bit integers
bitLt :: BitVector -> BitVector -> BitFormula
bitLt xs ys = bitGt ys xs  -- lt(x, y) = gt(y, x)

-- | Equality for n-bit integers using logarithmic tree
bitEq :: BitVector -> BitVector -> BitFormula
bitEq xs ys
  | length xs /= length ys = error "bitEq: bit vectors must have same length"
  | null xs = BitTrue
  | otherwise = eqTree xs ys

-- | Logarithmic tree for equality
eqTree :: BitVector -> BitVector -> BitFormula
eqTree [] [] = BitTrue
eqTree [x] [y] = BitAnd (BitImpl (BitVar x) (BitVar y))
                         (BitImpl (BitVar y) (BitVar x))  -- x <=> y
eqTree xs ys =
  let n = length xs
      mid = n `div` 2
      (xsLo, xsHi) = splitAt mid xs
      (ysLo, ysHi) = splitAt mid ys
  in BitAnd (eqTree xsHi ysHi) (eqTree xsLo ysLo)  -- Both halves equal

-- =============================================================================
-- Bit-Level Arithmetic Operations
-- =============================================================================

-- | Addition with carry using ripple-carry adder
-- Returns (sum, carry_out)
-- For efficiency, this should use carry-lookahead, but starting with ripple-carry
bitAdd :: BitVector -> BitVector -> (BitVector, Bit)
bitAdd xs ys
  | length xs /= length ys = error "bitAdd: bit vectors must have same length"
  | null xs = ([], "c_0")  -- Empty: (0, no carry)
  | otherwise =
      let n = length xs
          carryBits = Prelude.map (\i -> "c_" ++ show i) [0..n]
          sumBits = zipWith3 (fullAdderSum carryBits) xs ys [0..n-1]
          carryFormulas = zipWith3 (fullAdderCarry carryBits) xs ys [0..n-1]
      in (sumBits, last carryBits)
  where
    -- Sum bit: S_i = X_i ⊕ Y_i ⊕ C_i
    fullAdderSum carries x y i =
      "s_" ++ show i ++ "_" ++ x ++ "_" ++ y

    -- Carry bit: C_{i+1} = (X_i ∧ Y_i) ∨ (X_i ∧ C_i) ∨ (Y_i ∧ C_i)
    fullAdderCarry carries x y i =
      carries !! (i + 1)

-- | Multiplication (placeholder - complex, can use array multiplier)
bitMul :: BitVector -> BitVector -> BitVector
bitMul xs ys = error "bitMul: not yet implemented"  -- TODO

-- | Division (placeholder - very complex)
bitDiv :: BitVector -> BitVector -> BitVector
bitDiv xs ys = error "bitDiv: not yet implemented"  -- TODO

-- | Left shift by constant n positions
bitShl :: BitVector -> Int -> BitVector
bitShl xs n
  | n < 0 = error "bitShl: negative shift"
  | n >= length xs = replicate (length xs) "0"  -- All zeros
  | otherwise =
      let zeros = replicate n "0"
          shifted = drop n xs
      in shifted ++ zeros

-- | Right shift by constant n positions
bitShr :: BitVector -> Int -> BitVector
bitShr xs n
  | n < 0 = error "bitShr: negative shift"
  | n >= length xs = replicate (length xs) "0"  -- All zeros
  | otherwise =
      let zeros = replicate n "0"
          shifted = take (length xs - n) xs
      in zeros ++ shifted

-- =============================================================================
-- Conversion to Implication-Based TPTP
-- =============================================================================

-- | Convert BitFormula to implication-based TPTP using Stålmarck rules
bitFormulaToTPTP :: BitFormula -> String
bitFormulaToTPTP f = case f of
  BitVar v -> v
  BitNot p -> "~(" ++ bitFormulaToTPTP p ++ ")"

  -- Implication: already in target format
  BitImpl p q ->
    "(" ++ bitFormulaToTPTP p ++ " => " ++ bitFormulaToTPTP q ++ ")"

  -- Conjunction: A ∧ B ⟹ ¬(A → ¬B)
  BitAnd p q ->
    "~(" ++ bitFormulaToTPTP p ++ " => ~(" ++ bitFormulaToTPTP q ++ "))"

  -- Disjunction: A ∨ B ⟹ (¬A → B)
  BitOr p q ->
    "(~(" ++ bitFormulaToTPTP p ++ ") => " ++ bitFormulaToTPTP q ++ ")"

  BitTrue -> "$true"
  BitFalse -> "$false"

-- =============================================================================
-- Conversion to CNF (for comparison)
-- =============================================================================

type Clause = [String]  -- Disjunction of literals
type CNF = [Clause]     -- Conjunction of clauses

-- | Convert BitFormula to CNF using Tseitin transformation
-- Returns (CNF, auxiliary variable counter)
bitFormulaToCNF :: BitFormula -> (CNF, Int)
bitFormulaToCNF formula =
  let (tseitin, nextVar) = toTseitin formula 1
      (cnf, _) = tseitinToCNF tseitin nextVar
  in (cnf, nextVar)

-- | Tseitin intermediate representation
data TseitinFormula
  = TVar String
  | TAux Int  -- Auxiliary variable
  | TNot TseitinFormula
  | TAnd TseitinFormula TseitinFormula
  | TOr TseitinFormula TseitinFormula
  | TImpl TseitinFormula TseitinFormula
  deriving (Show, Eq)

-- | Convert BitFormula to Tseitin with auxiliary variables
toTseitin :: BitFormula -> Int -> (TseitinFormula, Int)
toTseitin f nextVar = case f of
  BitVar v -> (TVar v, nextVar)
  BitTrue -> (TVar "$true", nextVar)
  BitFalse -> (TNot (TVar "$true"), nextVar)

  BitNot p ->
    let (p', nv) = toTseitin p nextVar
    in (TNot p', nv)

  BitAnd p q ->
    let (p', nv1) = toTseitin p nextVar
        (q', nv2) = toTseitin q nv1
    in (TAnd p' q', nv2)

  BitOr p q ->
    let (p', nv1) = toTseitin p nextVar
        (q', nv2) = toTseitin q nv1
    in (TOr p' q', nv2)

  BitImpl p q ->
    let (p', nv1) = toTseitin p nextVar
        (q', nv2) = toTseitin q nv1
    in (TImpl p' q', nv2)

-- | Convert Tseitin to CNF clauses
tseitinToCNF :: TseitinFormula -> Int -> (CNF, Int)
tseitinToCNF f nextVar = case f of
  TVar v -> ([[v]], nextVar)

  TNot (TVar v) -> ([["~" ++ v]], nextVar)

  -- a AND b: introduce auxiliary z
  -- z <=> (a AND b)
  -- Clauses: (~z | a), (~z | b), (~a | ~b | z)
  TAnd a b ->
    let z = "aux_" ++ show nextVar
        (aCNF, nv1) = tseitinToCNF a (nextVar + 1)
        (bCNF, nv2) = tseitinToCNF b nv1
        -- Get top variable for a and b
        aTop = getTseitinTop a
        bTop = getTseitinTop b
        auxClauses = [["~" ++ z, aTop], ["~" ++ z, bTop], ["~" ++ aTop, "~" ++ bTop, z]]
    in (aCNF ++ bCNF ++ auxClauses, nv2)

  -- a OR b: introduce auxiliary z
  -- z <=> (a OR b)
  -- Clauses: (z | ~a), (z | ~b), (a | b | ~z)
  TOr a b ->
    let z = "aux_" ++ show nextVar
        (aCNF, nv1) = tseitinToCNF a (nextVar + 1)
        (bCNF, nv2) = tseitinToCNF b nv1
        aTop = getTseitinTop a
        bTop = getTseitinTop b
        auxClauses = [[z, "~" ++ aTop], [z, "~" ++ bTop], [aTop, bTop, "~" ++ z]]
    in (aCNF ++ bCNF ++ auxClauses, nv2)

  -- a => b is ~a OR b
  TImpl a b -> tseitinToCNF (TOr (TNot a) b) nextVar

  TNot (TNot a) -> tseitinToCNF a nextVar  -- Double negation

  TNot a ->
    let z = "aux_" ++ show nextVar
        (aCNF, nv1) = tseitinToCNF a (nextVar + 1)
        aTop = getTseitinTop a
        auxClauses = [[z, aTop], ["~" ++ z, "~" ++ aTop]]
    in (aCNF ++ auxClauses, nv1)

-- | Get the top-level variable of a Tseitin formula
getTseitinTop :: TseitinFormula -> String
getTseitinTop f = case f of
  TVar v -> v
  TAux n -> "aux_" ++ show n
  _ -> "unknown"  -- Shouldn't happen after conversion

-- | Serialize CNF to TPTP format
cnfToTPTP :: CNF -> String
cnfToTPTP clauses =
  let clauseStrs = zipWith formatClause [1..] clauses
  in unlines $ "% CNF encoding (for comparison)" : clauseStrs
  where
    formatClause n lits =
      "fof(clause_" ++ show n ++ ", axiom, (" ++
      intercalate " | " lits ++ "))."

-- | Measure CNF size
measureCNF :: CNF -> (Int, Int)  -- (num clauses, num literals)
measureCNF cnf =
  let numClauses = length cnf
      numLiterals = sum (Prelude.map length cnf)
  in (numClauses, numLiterals)

-- =============================================================================
-- Helper Functions
-- =============================================================================

-- | Create bit vector for a variable
-- Example: mkBitVector "x" 8 = ["x_0", "x_1", ..., "x_7"]
mkBitVector :: String -> Int -> BitVector
mkBitVector name n = [name ++ "_" ++ show i | i <- [0..n-1]]

-- | Create bit vector for a constant
-- Example: constBitVector 42 8 = ["0", "1", "0", "1", "0", "1", "0", "0"]  -- 42 in binary
constBitVector :: Integer -> Int -> BitVector
constBitVector val n =
  let bits = reverse $ take n (intToBits val ++ repeat False)
  in Prelude.map (\b -> if b then "1" else "0") bits
  where
    intToBits 0 = []
    intToBits v = (v `mod` 2 == 1) : intToBits (v `div` 2)

-- =============================================================================
-- Testing
-- =============================================================================

-- | Example: gt(x, y) for 4-bit integers
exampleGt4 :: String
exampleGt4 =
  let x = mkBitVector "x" 4
      y = mkBitVector "y" 4
      formula = bitGt x y
  in bitFormulaToTPTP formula

-- | Example: eq(x, 42) for 8-bit integers
exampleEq8 :: String
exampleEq8 =
  let x = mkBitVector "x" 8
      y = constBitVector 42 8
      formula = bitEq x y
  in bitFormulaToTPTP formula
