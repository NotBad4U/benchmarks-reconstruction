(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(set-info :source |
show equivalence of the following terms:
((16 * v4 + 32 * v5) + ((1 * v0 + 2 * v1) + (4 * v2 + 8 * v3)))

v0 + 2 * (v1 + 2 * (v2 + 2 * (v3 + 2 * (v4 + 2 * (v5)))))

in arithmetic modulo 2exp8
STATUS: unsat

generated by: Alberto Griggio <alberto.griggio@disi.unitn.it>
|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun v0 () Int)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(declare-fun v3 () Int)
(declare-fun v4 () Int)
(declare-fun v5 () Int)
(declare-fun s_0 () Int)
(declare-fun o_0 () Int)
(declare-fun s_1 () Int)
(declare-fun s_2 () Int)
(declare-fun o_1 () Int)
(declare-fun s_3 () Int)
(declare-fun s_4 () Int)
(declare-fun o_2 () Int)
(declare-fun o_3 () Int)
(declare-fun o_4 () Int)
(declare-fun o_5 () Int)
(declare-fun s_6 () Int)
(declare-fun o_6 () Int)
(declare-fun s_7 () Int)
(declare-fun o_7 () Int)
(declare-fun s_8 () Int)
(declare-fun o_8 () Int)
(declare-fun s_9 () Int)
(declare-fun o_9 () Int)
(assert (let ((?v_0 (* v5 2))) (let ((?v_6 (< ?v_0 256)) (?v_7 (< ?v_0 512))) (let ((?v_23 (+ (ite ?v_6 ?v_0 (ite ?v_7 (- ?v_0 256) (- ?v_0 512))) v4))) (let ((?v_24 (- ?v_23 (* o_5 256))) (?v_37 (* v3 8))) (let ((?v_38 (- ?v_37 (* s_2 256))) (?v_39 (* v2 4))) (let ((?v_40 (- ?v_39 (* s_1 256)))) (let ((?v_35 (+ ?v_38 ?v_40))) (let ((?v_36 (- ?v_35 (* o_1 256))) (?v_43 (* v1 2))) (let ((?v_44 (- ?v_43 (* s_0 256)))) (let ((?v_41 (+ ?v_44 v0))) (let ((?v_42 (- ?v_41 (* o_0 256)))) (let ((?v_27 (+ ?v_36 ?v_42))) (let ((?v_28 (- ?v_27 (* o_3 256))) (?v_31 (* v5 32))) (let ((?v_32 (- ?v_31 (* s_4 256))) (?v_33 (* v4 16))) (let ((?v_34 (- ?v_33 (* s_3 256)))) (let ((?v_29 (+ ?v_32 ?v_34))) (let ((?v_30 (- ?v_29 (* o_2 256)))) (let ((?v_25 (+ ?v_28 ?v_30))) (let ((?v_26 (- ?v_25 (* o_4 256))) (?v_18 (* 4 v5))) (let ((?v_21 (- (+ (ite ?v_6 ?v_18 (ite ?v_7 (- ?v_18 512) (- ?v_18 1024))) (* 2 v4)) (* 512 o_5)))) (let ((?v_22 (- ?v_21 (* s_6 256)))) (let ((?v_19 (+ ?v_22 v3))) (let ((?v_20 (- ?v_19 (* o_6 256))) (?v_13 (* 8 v5))) (let ((?v_16 (- (+ (- (- (+ (ite ?v_6 ?v_13 (ite ?v_7 (- ?v_13 1024) (- ?v_13 2048))) (* 4 v4)) (* 1024 o_5)) (* 512 s_6)) (* 2 v3)) (* 512 o_6)))) (let ((?v_17 (- ?v_16 (* s_7 256)))) (let ((?v_14 (+ ?v_17 v2))) (let ((?v_15 (- ?v_14 (* o_7 256))) (?v_8 (* 16 v5))) (let ((?v_11 (- (+ (- (- (+ (- (- (+ (ite ?v_6 ?v_8 (ite ?v_7 (- ?v_8 2048) (- ?v_8 4096))) (* 8 v4)) (* 2048 o_5)) (* 1024 s_6)) (* 4 v3)) (* 1024 o_6)) (* 512 s_7)) (* 2 v2)) (* 512 o_7)))) (let ((?v_12 (- ?v_11 (* s_8 256)))) (let ((?v_9 (+ ?v_12 v1))) (let ((?v_10 (- ?v_9 (* o_8 256))) (?v_1 (* 32 v5))) (let ((?v_4 (- (+ (- (- (+ (- (- (+ (- (- (+ (ite ?v_6 ?v_1 (ite ?v_7 (- ?v_1 4096) (- ?v_1 8192))) (* 16 v4)) (* 4096 o_5)) (* 2048 s_6)) (* 8 v3)) (* 2048 o_6)) (* 1024 s_7)) (* 4 v2)) (* 1024 o_7)) (* 512 s_8)) (* 2 v1)) (* 512 o_8)))) (let ((?v_5 (- ?v_4 (* s_9 256)))) (let ((?v_2 (+ ?v_5 v0))) (let ((?v_3 (- ?v_2 (* o_9 256)))) (and (not (= ?v_3 ?v_26)) (and (= (> ?v_2 256) (= o_9 1)) (and (and (< ?v_3 256) (<= 0 ?v_3)) (and (and (<= o_9 1) (<= 0 o_9)) (and (= (> ?v_4 256) (>= s_9 1)) (and (and (< ?v_5 256) (<= 0 ?v_5)) (and (and (< s_9 2) (<= 0 s_9)) (and (= (> ?v_9 256) (= o_8 1)) (and (and (< ?v_10 256) (<= 0 ?v_10)) (and (and (<= o_8 1) (<= 0 o_8)) (and (= (> ?v_11 256) (>= s_8 1)) (and (and (< ?v_12 256) (<= 0 ?v_12)) (and (and (< s_8 2) (<= 0 s_8)) (and (= (> ?v_14 256) (= o_7 1)) (and (and (< ?v_15 256) (<= 0 ?v_15)) (and (and (<= o_7 1) (<= 0 o_7)) (and (= (> ?v_16 256) (>= s_7 1)) (and (and (< ?v_17 256) (<= 0 ?v_17)) (and (and (< s_7 2) (<= 0 s_7)) (and (= (> ?v_19 256) (= o_6 1)) (and (and (< ?v_20 256) (<= 0 ?v_20)) (and (and (<= o_6 1) (<= 0 o_6)) (and (= (> ?v_21 256) (>= s_6 1)) (and (and (< ?v_22 256) (<= 0 ?v_22)) (and (and (< s_6 2) (<= 0 s_6)) (and (= (> ?v_23 256) (= o_5 1)) (and (and (< ?v_24 256) (<= 0 ?v_24)) (and (and (<= o_5 1) (<= 0 o_5)) (and (= (> ?v_25 256) (= o_4 1)) (and (and (< ?v_26 256) (<= 0 ?v_26)) (and (and (<= o_4 1) (<= 0 o_4)) (and (= (> ?v_27 256) (= o_3 1)) (and (and (< ?v_28 256) (<= 0 ?v_28)) (and (and (<= o_3 1) (<= 0 o_3)) (and (= (> ?v_29 256) (= o_2 1)) (and (and (< ?v_30 256) (<= 0 ?v_30)) (and (and (<= o_2 1) (<= 0 o_2)) (and (= (> ?v_31 256) (>= s_4 1)) (and (and (< ?v_32 256) (<= 0 ?v_32)) (and (and (< s_4 32) (<= 0 s_4)) (and (= (> ?v_33 256) (>= s_3 1)) (and (and (< ?v_34 256) (<= 0 ?v_34)) (and (and (< s_3 16) (<= 0 s_3)) (and (= (> ?v_35 256) (= o_1 1)) (and (and (< ?v_36 256) (<= 0 ?v_36)) (and (and (<= o_1 1) (<= 0 o_1)) (and (= (> ?v_37 256) (>= s_2 1)) (and (and (< ?v_38 256) (<= 0 ?v_38)) (and (and (< s_2 8) (<= 0 s_2)) (and (= (> ?v_39 256) (>= s_1 1)) (and (and (< ?v_40 256) (<= 0 ?v_40)) (and (and (< s_1 4) (<= 0 s_1)) (and (= (> ?v_41 256) (= o_0 1)) (and (and (< ?v_42 256) (<= 0 ?v_42)) (and (and (<= o_0 1) (<= 0 o_0)) (and (= (> ?v_43 256) (>= s_0 1)) (and (and (< ?v_44 256) (<= 0 ?v_44)) (and (and (< s_0 2) (<= 0 s_0)) (and (and (< v5 256) (>= v5 0)) (and (and (< v4 256) (>= v4 0)) (and (and (< v3 256) (>= v3 0)) (and (and (< v2 256) (>= v2 0)) (and (and (< v1 256) (>= v1 0)) (and (< v0 256) (>= v0 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
