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
(declare-fun x9 () Int)
(declare-fun x10 () Int)
(declare-fun x11 () Int)
(declare-fun x12 () Int)
(declare-fun x13 () Int)
(declare-fun x14 () Int)
(assert (let ((?v_4 (- x13)) (?v_1 (- x11)) (?v_13 (+ (- x8) x1)) (?v_3 (- x2))) (let ((?v_12 (+ ?v_3 x1)) (?v_2 (- x3)) (?v_11 (- x6)) (?v_10 (- x0)) (?v_6 (- x7)) (?v_9 (* x5 2)) (?v_8 (- x9))) (let ((?v_5 (+ ?v_10 x2)) (?v_0 (- x4)) (?v_7 (* x13 (- 3)))) (and (not (>= (+ (* x1 (- 238242)) (+ (* x5 160185) (+ (* x9 (- 484272)) (+ (* x12 (- 47967)) (+ (* x2 (- 104430)) (+ (* x0 (- 443562)) (+ (* x13 (- 876858)) (+ (* x6 (- 242136)) (+ (* x8 (- 47967)) (+ (* x10 6195) (+ (* x11 301962) (+ (* x4 (- 52392)) (+ (* x14 (- 170097)) (+ (* x3 119121) (* x7 (- 66021)))))))))))))))) 348159)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= 1 (+ (+ (+ (+ (+ (* x10 2) x2) x0) ?v_0) ?v_4) ?v_11)) (<= (+ (+ (+ (+ (+ (+ x8 x10) ?v_1) ?v_0) x14) ?v_2) ?v_6) (- 1))) (<= (+ (+ (+ (+ (+ ?v_5 x12) ?v_1) x6) ?v_2) (* x7 3)) 0)) (<= 1 (+ (+ (+ ?v_12 ?v_0) ?v_7) x5))) (<= (+ (+ (+ (+ (+ (+ ?v_3 x10) ?v_1) ?v_0) ?v_4) x14) x3) (- 1))) (<= (+ (+ (+ (+ (* x1 2) x8) ?v_1) ?v_0) ?v_2) 0)) (<= 0 (+ (+ (+ ?v_5 ?v_4) x6) x9))) (<= 0 (+ (+ (+ (+ (+ (* x0 (- 2)) x2) (* x8 (- 2))) x5) ?v_8) ?v_6))) (<= 0 (+ (+ (+ x8 x2) x11) ?v_7))) (<= (+ (+ (+ (+ (* x2 2) x10) x0) x14) ?v_6) (- 1))) (<= (- 1) (+ (+ (+ (+ ?v_1 x8) ?v_9) ?v_8) x3))) (<= (+ (+ (+ (+ (+ ?v_13 (- x12)) x11) (* x13 2)) ?v_9) ?v_6) 1)) (<= (- 1) (+ (+ (+ (+ (+ (+ (+ x10 x1) ?v_10) ?v_11) x14) (- x5)) (* x9 (- 2))) ?v_2))) (<= 0 (+ (+ ?v_12 x0) (* x14 (- 2))))) (<= (+ (+ (+ (+ (+ ?v_13 x12) ?v_1) x4) ?v_4) (- x14)) 0)))))))
(check-sat)
(exit)
