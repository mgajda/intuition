; Verification Condition for: if-guard
; Functions inlined: True
; Classification: QF_BV (Bitvector)
; Reason: Shift operation computed as bitvector
; Converted from: vc_16.smt2 (had unknown from shl)

(set-logic QF_BV)

; Variable declaration
(declare-const newLen (_ BitVec 256))

; Compute the shifted value (assuming shl(64, 1) like in vc_10)
(define-fun max_value () (_ BitVec 256)
  (bvshl #x0000000000000000000000000000000000000000000000000000000000000001
         #x0000000000000000000000000000000000000000000000000000000000000040))

; Verification condition
; Original: (> newLen (- unknown 1))
; With shift: (> newLen (2^64 - 1))
(assert (bvugt newLen (bvsub max_value #x0000000000000000000000000000000000000000000000000000000000000001)))

(check-sat)
(get-model)
