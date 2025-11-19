; Verification Condition for: if-guard
; WP Computed: True
; Classification: Presburger
; Reason: Linear arithmetic with comparisons - Presburger decidable

(set-logic QF_LIA)  ; Quantifier-Free Linear Integer Arithmetic

; Variable declarations

; uint256 range constraints (0 <= var <= 2^256-1)

; Verification condition
(assert (and (not (not (> (+ 42 1) 42))) 1))

(check-sat)
(get-model)
