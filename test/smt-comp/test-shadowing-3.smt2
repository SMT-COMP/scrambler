(set-logic ALL)
(set-info :status sat)
(declare-fun x () Bool)
(assert (let ((x x)) (let ((x x)) x)))
(assert x)
(check-sat)
(exit)
