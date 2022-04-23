package precondition.z3api

object cvc5test {}
/*

 (set-logic ALL)
 (set-option :produce-models true)
 (set-option :incremental true)

(set-logic ALL)
(declare-const x Real)
(assert (< 0 x))
(assert (> 0 x))
(check-sat)

(reset-assertions)

(set-logic ALL)
(declare-const x Real)
(assert (=> (< 0 x)) (> 0 x))
(check-sat)



(declare-fun N () Int)
(assert (=> (>= N 1) (< N 0)))


(declare-fun N () Int)
(assert (>= N 1))
(assert  (< N 0))
(check-sat)

(set-logic ALL)
(reset-assertions)
(declare-const x Real)
(assert (> 0 x))
(assert (not (>= (^ 2 x) 0)))
(check-sat)

(set-logic ALL)

(reset-assertions)
(declare-const x Real)
(declare-const y Int)
(assert (> 0 x))
(assert (> 0 y))
(assert (> 6710886 y))
(assert (not (>= (^ x y) 0)))
(check-sat)

 */
