; Verification Condition for: if-guard
; Functions inlined: True
; Classification: QF_BV (Bitvector)
; Reason: Division as bitvector operation
; Converted from: vc_3.smt2 (QF_LIA with div)

(set-logic QF_BV)  ; Quantifier-Free Bitvectors

; Variable declarations - 256-bit bitvectors (uint256)
(declare-const product (_ BitVec 256))
(declare-const x (_ BitVec 256))
(declare-const y (_ BitVec 256))

; No range constraints needed! Bitvectors have implicit bounds [0, 2^256-1]

; Verification condition
; Original: (not (or (= x 0) (= y (div product x))))
; QF_BV: unsigned division (bvudiv)
(assert (not (or (= x #x0000000000000000000000000000000000000000000000000000000000000000)
                 (= y (bvudiv product x)))))

(check-sat)
(get-model)
