; Verification Condition for: if-guard
; Functions inlined: True
; Classification: QF_BV (Bitvector) - Trivial equality
; Converted from: vc_20.smt2

(set-logic QF_BV)

; Variable declaration
(declare-const y (_ BitVec 256))

; Verification condition - simple equality
(assert (= y #x0000000000000000000000000000000000000000000000000000000000000000))

(check-sat)
(get-model)
