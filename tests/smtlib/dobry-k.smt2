; K combinator: p => (q => p)
; This is valid in both classical and intuitionistic logic
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (not (=> p (=> q p))))
(check-sat)
; Expected: unsat (formula is valid)
