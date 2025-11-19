; Verification Condition for: if-guard
; Classification: Presburger
; Reason: Linear arithmetic with comparisons - Presburger decidable

(set-logic QF_LIA)  ; Quantifier-Free Linear Integer Arithmetic

; Variable declarations
(declare-const x Int)

; uint256 range constraints (0 <= var <= 2^256-1)
(assert (and (>= x 0) (<= x 115792089237316195423570985008687907853269984665640564039457584007913129639935)))

; Verification condition: prove that this is unsatisfiable
; (i.e., the negation should be valid)
(assert (> x 115792089237316195423570985008687907853269984665640564039457584007913129639934))

(check-sat)
(get-model)
