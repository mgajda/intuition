; Verification Condition for: if-guard
; Functions inlined: True
; Classification: QF_BV (Bitvector) - Simple comparison
; Reason: Also works in Presburger, but testing QF_BV encoding
; Converted from: vc_1.smt2

(set-logic QF_BV)  ; Quantifier-Free Bitvectors

; Variable declarations - 256-bit bitvectors (uint256)
(declare-const length (_ BitVec 256))
(declare-const outOfPlaceEncoding (_ BitVec 256))

; No range constraints needed!

; Verification condition
; Original: (= outOfPlaceEncoding (< length 32))
; Note: In SMT, comparison returns Bool, but we're comparing to uint256
; This is checking if outOfPlaceEncoding (as 0 or 1) equals the bool result
(assert (= outOfPlaceEncoding
           (ite (bvult length #x0000000000000000000000000000000000000000000000000000000000000020)
                #x0000000000000000000000000000000000000000000000000000000000000001 ; true = 1
                #x0000000000000000000000000000000000000000000000000000000000000000))) ; false = 0

(check-sat)
(get-model)
