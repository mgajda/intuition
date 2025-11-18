; Law of excluded middle: p | ~p
; Valid classically but NOT intuitionistically
(set-logic QF_UF)
(declare-const p Bool)
(assert (not (or p (not p))))
(check-sat)
; Expected for classical: unsat (valid)
; Expected for intuitionistic: sat (not valid)
