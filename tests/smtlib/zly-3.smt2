; Peirce's law: ((p => q) => p) => p
; Valid classically but NOT intuitionistically
(set-logic QF_UF)
(declare-const p Bool)
(declare-const q Bool)
(assert (not (=> (=> (=> p q) p) p)))
(check-sat)
; Expected for classical: unsat (valid)
; Expected for intuitionistic: sat (not valid)
