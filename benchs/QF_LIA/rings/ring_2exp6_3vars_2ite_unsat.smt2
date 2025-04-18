(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(set-info :source |
show equivalence of the following terms:
(4 * v2 + (1 * v0 + 2 * v1))

v0 + 2 * (v1 + 2 * (v2))

in arithmetic modulo 2exp6
STATUS: unsat

generated by: Alberto Griggio <alberto.griggio@disi.unitn.it>
|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun v0 () Int)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(declare-fun o_0 () Int)
(declare-fun s_1 () Int)
(declare-fun o_1 () Int)
(declare-fun o_2 () Int)
(declare-fun s_3 () Int)
(declare-fun o_3 () Int)
(assert (let ((?v_0 (* v2 2))) (let ((?v_7 (< ?v_0 64)) (?v_8 (< ?v_0 128))) (let ((?v_9 (+ (ite ?v_7 ?v_0 (ite ?v_8 (- ?v_0 64) (- ?v_0 128))) v1))) (let ((?v_10 (- ?v_9 (* o_2 64))) (?v_13 (* v2 4))) (let ((?v_14 (- ?v_13 (* s_1 64))) (?v_2 (* v1 2))) (let ((?v_15 (+ (ite (< ?v_2 64) ?v_2 (ite (< ?v_2 128) (- ?v_2 64) (- ?v_2 128))) v0))) (let ((?v_16 (- ?v_15 (* o_0 64)))) (let ((?v_11 (+ ?v_14 ?v_16))) (let ((?v_12 (- ?v_11 (* o_1 64))) (?v_1 (* 4 v2))) (let ((?v_5 (- (+ (ite ?v_7 ?v_1 (ite ?v_8 (- ?v_1 128) (- ?v_1 256))) (* 2 v1)) (* 128 o_2)))) (let ((?v_6 (- ?v_5 (* s_3 64)))) (let ((?v_3 (+ ?v_6 v0))) (let ((?v_4 (- ?v_3 (* o_3 64)))) (and (not (= ?v_4 ?v_12)) (and (= (> ?v_3 64) (= o_3 1)) (and (and (< ?v_4 64) (<= 0 ?v_4)) (and (and (<= o_3 1) (<= 0 o_3)) (and (= (> ?v_5 64) (>= s_3 1)) (and (and (< ?v_6 64) (<= 0 ?v_6)) (and (and (< s_3 2) (<= 0 s_3)) (and (= (> ?v_9 64) (= o_2 1)) (and (and (< ?v_10 64) (<= 0 ?v_10)) (and (and (<= o_2 1) (<= 0 o_2)) (and (= (> ?v_11 64) (= o_1 1)) (and (and (< ?v_12 64) (<= 0 ?v_12)) (and (and (<= o_1 1) (<= 0 o_1)) (and (= (> ?v_13 64) (>= s_1 1)) (and (and (< ?v_14 64) (<= 0 ?v_14)) (and (and (< s_1 4) (<= 0 s_1)) (and (= (> ?v_15 64) (= o_0 1)) (and (and (< ?v_16 64) (<= 0 ?v_16)) (and (and (<= o_0 1) (<= 0 o_0)) (and (and (< v2 64) (>= v2 0)) (and (and (< v1 64) (>= v1 0)) (and (< v0 64) (>= v0 0)))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
