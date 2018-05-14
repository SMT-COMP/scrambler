; This benchmark is designed to exercise all rules of the SMT-LIB
; grammar (except those not allowed in SMT-COMP).

; Note that this is not a valid script, since some symbols are used
; without declaration. This should perhaps be fixed.

(set-logic AUFBVDTNIRA)

; commands
(assert true)
(check-sat)
(declare-const c Bool)
(declare-datatype Unit ((unit)))
(declare-datatypes ((AnotherUnit 0)) (((anotherunit))))
(declare-fun f () Bool)
(declare-fun g (Int) Bool)
(declare-sort s 0)
(define-fun h () Bool true)
(define-fun i ((x s)) Bool true)
(define-sort t () Bool)
(echo "a string")
(push 1)
(pop 1)
(set-info :keyword)

; terms
(assert (= 1234 1234))
(assert (= 1234.5 1234.5))
(assert (= #x0123456789aBcDeF #x0123456789aBcDeF))
(assert (= #b01 #b01))
(assert (= "a string" "a string"))
(assert c)
(assert (as c Bool))
(assert (g 0))
(assert (let ((x true)) x))
(assert (forall ((x Bool)) (or x (not x))))
(assert (exists ((x Bool)) x))
(assert (match unit ((unit true))))
(assert (! c :keyword))

; datatypes
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-datatypes ((IntList 0)) (((empty) (insert (head Int) (tail IntList)))))
;(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (car T) (cdr (List T)))))))
;(declare-datatypes ((Option 1)) ((par (X) ((none) (some (val X))))))
;(declare-datatypes ((Pair 2)) ((par (X Y) ((pair (first X) (second Y))))))
;(declare-datatypes ((Tree 1) (TreeList 1)) (
;  ; Tree
;  (par (X) ((node (value X) (children (TreeList X)))))
;  ; TreeList
;  (par (Y) ((tl_empty) (tl_insert (tl_head (Tree Y)) (tl_tail (TreeList Y))))))
;)
(declare-datatypes ((IntTree 0) (IntTreeList 0)) (
  ; IntTree
  ((node (value Int) (children IntTreeList)))
  ; IntTreeList
  ((inttl_empty) (inttl_insert (inttl_head IntTree) (inttl_tail IntTreeList)))
))

(assert ((_ is red) red))
(assert ((_ is insert) (insert 1234 empty)))
(assert ((_ is empty) (tail (insert 1234 empty))))
(assert (match (insert 1234 empty) ((empty false) ((insert x y) true) (z false))))

; sorts
(assert (forall ((x Bool)) true))
(assert (forall ((x (Array Int Real))) true))

; attributes
(assert (! c :keyword))
(assert (! c :keyword 1234))
(assert (! c :keyword 1234.5))
(assert (! c :keyword #x0123456789aBcDeF))
(assert (! c :keyword #b01))
(assert (! c :keyword "a string"))
(assert (! c :keyword symbol))
(assert (! c :keyword :anotherkeyword))
(assert (! c :keyword ()))
(assert (! c :keyword (foo ())))
(assert (! c :keyword (foo bar)))
(assert (! c :keyword (foo (bar baz))))

; identifiers
(assert c)
(assert (_ foo 0))
(assert (_ foo bar))

; s-expressions
(set-info :keyword)
(set-info :keyword 1234)
(set-info :keyword 1234.5)
(set-info :keyword #x0123456789aBcDeF)
(set-info :keyword #b01)
(set-info :keyword "a string")
(set-info :keyword symbol)
(set-info :keyword (:anotherkeyword))
(set-info :keyword ())
(set-info :keyword (foo ()))
(set-info :keyword (foo bar))
(set-info :keyword (foo (bar baz)))

; lexicon
(assert c)
(assert |c|)

(exit)
