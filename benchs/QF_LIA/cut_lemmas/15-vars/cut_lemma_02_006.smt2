(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(set-info :source |
Alberto Griggio

|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)
(declare-fun x5 () Int)
(declare-fun x6 () Int)
(declare-fun x7 () Int)
(declare-fun x8 () Int)
(declare-fun x10 () Int)
(declare-fun x11 () Int)
(declare-fun x12 () Int)
(declare-fun x13 () Int)
(declare-fun x14 () Int)
(assert (let ((?v_5 (- x10)) (?v_0 (* x10 1)) (?v_2 (* x4 2)) (?v_1 (* x13 1)) (?v_4 (* x8 (- 1))) (?v_7 (* x11 (- 1))) (?v_3 (* x3 (- 1))) (?v_6 (* x14 (- 1))) (?v_8 (* x12 (- 1)))) (and (not (>= (+ (+ (* x1 (- 9)) (+ (* x0 (- 9)) (+ (* x13 (- 9)) (+ (* x11 45) (+ (* x8 (- 18)) (+ (* x5 (- 36)) (+ (* x10 36) (+ (* x4 54) (+ (* x2 9) (+ (+ (* x7 (- 9)) (+ (* x6 (- 9)) (* x3 36))) (* x14 54))))))))))) (* x12 54)) (- 36))) (and (and (and (and (and (and (and (and (and (and (and (and (and (not (<= 4 x8)) (not (<= x3 (- 1)))) (not (<= 1 x11))) (not (<= x13 (- 3)))) (not (<= 6 x0))) (not (<= (- 1) (+ (+ (+ (+ (+ (+ (* x6 2) (* x2 1)) (* x4 (- 1))) (* x10 (- 1))) (* x5 (- 1))) ?v_4) ?v_7)))) (<= 0 (+ (+ (+ (+ (+ (+ (+ (* x5 (- 2)) x7) x6) x0) ?v_5) (* x13 (- 2))) ?v_2) x2))) (<= 1 (+ (+ (+ (- x5) x8) x10) (* x3 2)))) (not (<= (- 2) (+ (+ (+ (+ (+ (+ ?v_3 ?v_6) (* x2 (- 1))) ?v_0) (* x8 1)) ?v_1) ?v_8)))) (not (<= (+ (+ (+ (+ (* x3 1) ?v_0) (* x11 1)) ?v_1) (* x12 2)) (- 2)))) (not (<= (+ (+ (+ ?v_2 ?v_0) (* x11 2)) (* x1 (- 1))) (- 1)))) (not (<= (+ (+ (* x14 2) ?v_3) ?v_4) (- 2)))) (<= (+ (+ (+ (+ (+ x6 x7) x0) ?v_5) (- x4)) x1) 1)) (not (<= (- 10) (+ (+ (+ (* x7 2) ?v_6) ?v_7) ?v_8)))))))
(check-sat)
(exit)
