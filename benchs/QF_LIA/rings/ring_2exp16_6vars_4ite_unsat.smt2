(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(set-info :source |
show equivalence of the following terms:
((16 * v4 + 32 * v5) + ((1 * v0 + 2 * v1) + (4 * v2 + 8 * v3)))

v0 + 2 * (v1 + 2 * (v2 + 2 * (v3 + 2 * (v4 + 2 * (v5)))))

in arithmetic modulo 2exp16
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
(declare-fun o_0 () Int)
(declare-fun s_2 () Int)
(declare-fun o_1 () Int)
(declare-fun s_3 () Int)
(declare-fun s_4 () Int)
(declare-fun o_2 () Int)
(declare-fun o_3 () Int)
(declare-fun o_4 () Int)
(declare-fun o_5 () Int)
(declare-fun o_6 () Int)
(declare-fun s_7 () Int)
(declare-fun o_7 () Int)
(declare-fun s_8 () Int)
(declare-fun o_8 () Int)
(declare-fun s_9 () Int)
(declare-fun o_9 () Int)
(assert (let ((?v_0 (* v5 2))) (let ((?v_2 (< ?v_0 65536)) (?v_3 (< ?v_0 131072))) (let ((?v_29 (+ (ite ?v_2 ?v_0 (ite ?v_3 (- ?v_0 65536) (- ?v_0 131072))) v4))) (let ((?v_30 (- ?v_29 (* o_5 65536))) (?v_43 (* v3 8))) (let ((?v_44 (- ?v_43 (* s_2 65536))) (?v_7 (* v2 4))) (let ((?v_41 (+ ?v_44 (ite (< ?v_7 65536) ?v_7 (ite (< ?v_7 131072) (- ?v_7 65536) (ite (< ?v_7 196608) (- ?v_7 131072) (ite (< ?v_7 262144) (- ?v_7 196608) (- ?v_7 262144)))))))) (let ((?v_42 (- ?v_41 (* o_1 65536))) (?v_8 (* v1 2))) (let ((?v_45 (+ (ite (< ?v_8 65536) ?v_8 (ite (< ?v_8 131072) (- ?v_8 65536) (- ?v_8 131072))) v0))) (let ((?v_46 (- ?v_45 (* o_0 65536)))) (let ((?v_33 (+ ?v_42 ?v_46))) (let ((?v_34 (- ?v_33 (* o_3 65536))) (?v_37 (* v5 32))) (let ((?v_38 (- ?v_37 (* s_4 65536))) (?v_39 (* v4 16))) (let ((?v_40 (- ?v_39 (* s_3 65536)))) (let ((?v_35 (+ ?v_38 ?v_40))) (let ((?v_36 (- ?v_35 (* o_2 65536)))) (let ((?v_31 (+ ?v_34 ?v_36))) (let ((?v_32 (- ?v_31 (* o_4 65536))) (?v_1 (* 4 v5))) (let ((?v_5 (- (+ (ite ?v_2 ?v_1 (ite ?v_3 (- ?v_1 131072) (- ?v_1 262144))) (* 2 v4)) (* 131072 o_5)))) (let ((?v_13 (< ?v_5 65536)) (?v_15 (< ?v_5 131072))) (let ((?v_27 (+ (ite ?v_13 ?v_5 (ite ?v_15 (- ?v_5 65536) (- ?v_5 131072))) v3))) (let ((?v_28 (- ?v_27 (* o_6 65536))) (?v_21 (* 8 v5))) (let ((?v_22 (- (+ (ite ?v_2 ?v_21 (ite ?v_3 (- ?v_21 262144) (- ?v_21 524288))) (* 4 v4)) (* 262144 o_5)))) (let ((?v_25 (- (+ (ite ?v_13 ?v_22 (ite ?v_15 (- ?v_22 131072) (- ?v_22 262144))) (* 2 v3)) (* 131072 o_6)))) (let ((?v_26 (- ?v_25 (* s_7 65536)))) (let ((?v_23 (+ ?v_26 v2))) (let ((?v_24 (- ?v_23 (* o_7 65536))) (?v_14 (* 16 v5))) (let ((?v_16 (- (+ (ite ?v_2 ?v_14 (ite ?v_3 (- ?v_14 524288) (- ?v_14 1048576))) (* 8 v4)) (* 524288 o_5)))) (let ((?v_19 (- (+ (- (- (+ (ite ?v_13 ?v_16 (ite ?v_15 (- ?v_16 262144) (- ?v_16 524288))) (* 4 v3)) (* 262144 o_6)) (* 131072 s_7)) (* 2 v2)) (* 131072 o_7)))) (let ((?v_20 (- ?v_19 (* s_8 65536)))) (let ((?v_17 (+ ?v_20 v1))) (let ((?v_18 (- ?v_17 (* o_8 65536))) (?v_4 (* 32 v5))) (let ((?v_6 (- (+ (ite ?v_2 ?v_4 (ite ?v_3 (- ?v_4 1048576) (- ?v_4 2097152))) (* 16 v4)) (* 1048576 o_5)))) (let ((?v_11 (- (+ (- (- (+ (- (- (+ (ite ?v_13 ?v_6 (ite ?v_15 (- ?v_6 524288) (- ?v_6 1048576))) (* 8 v3)) (* 524288 o_6)) (* 262144 s_7)) (* 4 v2)) (* 262144 o_7)) (* 131072 s_8)) (* 2 v1)) (* 131072 o_8)))) (let ((?v_12 (- ?v_11 (* s_9 65536)))) (let ((?v_9 (+ ?v_12 v0))) (let ((?v_10 (- ?v_9 (* o_9 65536)))) (and (not (= ?v_10 ?v_32)) (and (= (> ?v_9 65536) (= o_9 1)) (and (and (< ?v_10 65536) (<= 0 ?v_10)) (and (and (<= o_9 1) (<= 0 o_9)) (and (= (> ?v_11 65536) (>= s_9 1)) (and (and (< ?v_12 65536) (<= 0 ?v_12)) (and (and (< s_9 2) (<= 0 s_9)) (and (= (> ?v_17 65536) (= o_8 1)) (and (and (< ?v_18 65536) (<= 0 ?v_18)) (and (and (<= o_8 1) (<= 0 o_8)) (and (= (> ?v_19 65536) (>= s_8 1)) (and (and (< ?v_20 65536) (<= 0 ?v_20)) (and (and (< s_8 2) (<= 0 s_8)) (and (= (> ?v_23 65536) (= o_7 1)) (and (and (< ?v_24 65536) (<= 0 ?v_24)) (and (and (<= o_7 1) (<= 0 o_7)) (and (= (> ?v_25 65536) (>= s_7 1)) (and (and (< ?v_26 65536) (<= 0 ?v_26)) (and (and (< s_7 2) (<= 0 s_7)) (and (= (> ?v_27 65536) (= o_6 1)) (and (and (< ?v_28 65536) (<= 0 ?v_28)) (and (and (<= o_6 1) (<= 0 o_6)) (and (= (> ?v_29 65536) (= o_5 1)) (and (and (< ?v_30 65536) (<= 0 ?v_30)) (and (and (<= o_5 1) (<= 0 o_5)) (and (= (> ?v_31 65536) (= o_4 1)) (and (and (< ?v_32 65536) (<= 0 ?v_32)) (and (and (<= o_4 1) (<= 0 o_4)) (and (= (> ?v_33 65536) (= o_3 1)) (and (and (< ?v_34 65536) (<= 0 ?v_34)) (and (and (<= o_3 1) (<= 0 o_3)) (and (= (> ?v_35 65536) (= o_2 1)) (and (and (< ?v_36 65536) (<= 0 ?v_36)) (and (and (<= o_2 1) (<= 0 o_2)) (and (= (> ?v_37 65536) (>= s_4 1)) (and (and (< ?v_38 65536) (<= 0 ?v_38)) (and (and (< s_4 32) (<= 0 s_4)) (and (= (> ?v_39 65536) (>= s_3 1)) (and (and (< ?v_40 65536) (<= 0 ?v_40)) (and (and (< s_3 16) (<= 0 s_3)) (and (= (> ?v_41 65536) (= o_1 1)) (and (and (< ?v_42 65536) (<= 0 ?v_42)) (and (and (<= o_1 1) (<= 0 o_1)) (and (= (> ?v_43 65536) (>= s_2 1)) (and (and (< ?v_44 65536) (<= 0 ?v_44)) (and (and (< s_2 8) (<= 0 s_2)) (and (= (> ?v_45 65536) (= o_0 1)) (and (and (< ?v_46 65536) (<= 0 ?v_46)) (and (and (<= o_0 1) (<= 0 o_0)) (and (and (< v5 65536) (>= v5 0)) (and (and (< v4 65536) (>= v4 0)) (and (and (< v3 65536) (>= v3 0)) (and (and (< v2 65536) (>= v2 0)) (and (and (< v1 65536) (>= v1 0)) (and (< v0 65536) (>= v0 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
