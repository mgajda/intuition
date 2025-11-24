; Verification Condition for: if-guard
; Functions inlined: True
; Classification: QF_BV (Bitvector)
; Reason: Shift left operation - native in bitvectors!
; Converted from: vc_10.smt2 (QF_LIA with shl → unknown)

(set-logic QF_BV)  ; Quantifier-Free Bitvectors

; Variable declarations - 256-bit bitvectors (uint256)
(declare-const memPtr (_ BitVec 256))
(declare-const newFreePtr (_ BitVec 256))

; No range constraints needed!

; Compute shl(64, 1) directly as bitvector shift
; shl(64, 1) = 1 << 64 = 2^64
(define-fun max_64bit () (_ BitVec 256)
  (bvshl #x0000000000000000000000000000000000000000000000000000000000000001
         #x0000000000000000000000000000000000000000000000000000000000000040))

; Verification condition
; Original: (or (> newFreePtr (- unknown 1)) (< newFreePtr memPtr))
; With shl computed: (or (> newFreePtr (2^64 - 1)) (< newFreePtr memPtr))
(assert (or (bvugt newFreePtr (bvsub max_64bit #x0000000000000000000000000000000000000000000000000000000000000001))
            (bvult newFreePtr memPtr)))

(check-sat)
(get-model)
