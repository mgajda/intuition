; Verification Condition for: if-guard
; WP Computed: True
; Classification: Presburger
; Reason: Linear arithmetic with comparisons - Presburger decidable

(set-logic QF_LIA)  ; Quantifier-Free Linear Integer Arithmetic

; Variable declarations
(declare-const r Int)
(declare-const s Int)

; uint256 range constraints (0 <= var <= 2^256-1)
(assert (and (>= r 0) (<= r 115792089237316195423570985008687907853269984665640564039457584007913129639935)))
(assert (and (>= s 0) (<= s 115792089237316195423570985008687907853269984665640564039457584007913129639935)))

; Verification condition
(assert (and (not (not (= s 100))) (and (not (not (= r 150))) 1)))

(check-sat)
(get-model)
