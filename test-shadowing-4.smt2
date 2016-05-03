(declare-fun x () Bool)
(assert (let ((x x) (y x)) true))
(check-sat)
(exit)
