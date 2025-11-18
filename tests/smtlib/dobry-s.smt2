; S combinator: (p => (q => r)) => ((p => q) => (p => r))
; This is valid in both classical and intuitionistic logic
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(assert (not (=> (=> p (=> q r)) (=> (=> p q) (=> p r)))))
(check-sat)
; Expected: unsat (formula is valid)
