(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(set-info :source |
show equivalence of the following terms:
((64 * v6 + (1 * v0 + 2 * v1)) + ((4 * v2 + 8 * v3) + (16 * v4 + 32 * v5)))

v0 + 2 * (v1 + 2 * (v2 + 2 * (v3 + 2 * (v4 + 2 * (v5 + 2 * (v6))))))

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
(declare-fun v6 () Int)
(declare-fun o_0 () Int)
(declare-fun s_1 () Int)
(declare-fun s_2 () Int)
(declare-fun o_1 () Int)
(declare-fun s_3 () Int)
(declare-fun s_4 () Int)
(declare-fun o_2 () Int)
(declare-fun s_5 () Int)
(declare-fun o_3 () Int)
(declare-fun o_4 () Int)
(declare-fun o_5 () Int)
(declare-fun o_6 () Int)
(declare-fun o_7 () Int)
(declare-fun s_8 () Int)
(declare-fun o_8 () Int)
(declare-fun s_9 () Int)
(declare-fun o_9 () Int)
(declare-fun s_10 () Int)
(declare-fun o_10 () Int)
(declare-fun s_11 () Int)
(declare-fun o_11 () Int)
(assert (let ((?v_0 (* v6 2))) (let ((?v_2 (< ?v_0 256)) (?v_3 (< ?v_0 512))) (let ((?v_34 (+ (ite ?v_2 ?v_0 (ite ?v_3 (- ?v_0 256) (- ?v_0 512))) v5))) (let ((?v_35 (- ?v_34 (* o_6 256))) (?v_46 (* v5 32))) (let ((?v_47 (- ?v_46 (* s_4 256))) (?v_48 (* v4 16))) (let ((?v_49 (- ?v_48 (* s_3 256)))) (let ((?v_44 (+ ?v_47 ?v_49))) (let ((?v_45 (- ?v_44 (* o_2 256))) (?v_52 (* v3 8))) (let ((?v_53 (- ?v_52 (* s_2 256))) (?v_54 (* v2 4))) (let ((?v_55 (- ?v_54 (* s_1 256)))) (let ((?v_50 (+ ?v_53 ?v_55))) (let ((?v_51 (- ?v_50 (* o_1 256)))) (let ((?v_38 (+ ?v_45 ?v_51))) (let ((?v_39 (- ?v_38 (* o_4 256))) (?v_42 (* v6 64))) (let ((?v_43 (- ?v_42 (* s_5 256))) (?v_7 (* v1 2))) (let ((?v_56 (+ (ite (< ?v_7 256) ?v_7 (ite (< ?v_7 512) (- ?v_7 256) (- ?v_7 512))) v0))) (let ((?v_57 (- ?v_56 (* o_0 256)))) (let ((?v_40 (+ ?v_43 ?v_57))) (let ((?v_41 (- ?v_40 (* o_3 256)))) (let ((?v_36 (+ ?v_39 ?v_41))) (let ((?v_37 (- ?v_36 (* o_5 256))) (?v_1 (* 4 v6))) (let ((?v_5 (- (+ (ite ?v_2 ?v_1 (ite ?v_3 (- ?v_1 512) (- ?v_1 1024))) (* 2 v5)) (* 512 o_6)))) (let ((?v_12 (< ?v_5 256)) (?v_14 (< ?v_5 512))) (let ((?v_32 (+ (ite ?v_12 ?v_5 (ite ?v_14 (- ?v_5 256) (- ?v_5 512))) v4))) (let ((?v_33 (- ?v_32 (* o_7 256))) (?v_26 (* 8 v6))) (let ((?v_27 (- (+ (ite ?v_2 ?v_26 (ite ?v_3 (- ?v_26 1024) (- ?v_26 2048))) (* 4 v5)) (* 1024 o_6)))) (let ((?v_30 (- (+ (ite ?v_12 ?v_27 (ite ?v_14 (- ?v_27 512) (- ?v_27 1024))) (* 2 v4)) (* 512 o_7)))) (let ((?v_31 (- ?v_30 (* s_8 256)))) (let ((?v_28 (+ ?v_31 v3))) (let ((?v_29 (- ?v_28 (* o_8 256))) (?v_20 (* 16 v6))) (let ((?v_21 (- (+ (ite ?v_2 ?v_20 (ite ?v_3 (- ?v_20 2048) (- ?v_20 4096))) (* 8 v5)) (* 2048 o_6)))) (let ((?v_24 (- (+ (- (- (+ (ite ?v_12 ?v_21 (ite ?v_14 (- ?v_21 1024) (- ?v_21 2048))) (* 4 v4)) (* 1024 o_7)) (* 512 s_8)) (* 2 v3)) (* 512 o_8)))) (let ((?v_25 (- ?v_24 (* s_9 256)))) (let ((?v_22 (+ ?v_25 v2))) (let ((?v_23 (- ?v_22 (* o_9 256))) (?v_13 (* 32 v6))) (let ((?v_15 (- (+ (ite ?v_2 ?v_13 (ite ?v_3 (- ?v_13 4096) (- ?v_13 8192))) (* 16 v5)) (* 4096 o_6)))) (let ((?v_18 (- (+ (- (- (+ (- (- (+ (ite ?v_12 ?v_15 (ite ?v_14 (- ?v_15 2048) (- ?v_15 4096))) (* 8 v4)) (* 2048 o_7)) (* 1024 s_8)) (* 4 v3)) (* 1024 o_8)) (* 512 s_9)) (* 2 v2)) (* 512 o_9)))) (let ((?v_19 (- ?v_18 (* s_10 256)))) (let ((?v_16 (+ ?v_19 v1))) (let ((?v_17 (- ?v_16 (* o_10 256))) (?v_4 (* 64 v6))) (let ((?v_6 (- (+ (ite ?v_2 ?v_4 (ite ?v_3 (- ?v_4 8192) (- ?v_4 16384))) (* 32 v5)) (* 8192 o_6)))) (let ((?v_10 (- (+ (- (- (+ (- (- (+ (- (- (+ (ite ?v_12 ?v_6 (ite ?v_14 (- ?v_6 4096) (- ?v_6 8192))) (* 16 v4)) (* 4096 o_7)) (* 2048 s_8)) (* 8 v3)) (* 2048 o_8)) (* 1024 s_9)) (* 4 v2)) (* 1024 o_9)) (* 512 s_10)) (* 2 v1)) (* 512 o_10)))) (let ((?v_11 (- ?v_10 (* s_11 256)))) (let ((?v_8 (+ ?v_11 v0))) (let ((?v_9 (- ?v_8 (* o_11 256)))) (and (not (= ?v_9 ?v_37)) (and (= (> ?v_8 256) (= o_11 1)) (and (and (< ?v_9 256) (<= 0 ?v_9)) (and (and (<= o_11 1) (<= 0 o_11)) (and (= (> ?v_10 256) (>= s_11 1)) (and (and (< ?v_11 256) (<= 0 ?v_11)) (and (and (< s_11 2) (<= 0 s_11)) (and (= (> ?v_16 256) (= o_10 1)) (and (and (< ?v_17 256) (<= 0 ?v_17)) (and (and (<= o_10 1) (<= 0 o_10)) (and (= (> ?v_18 256) (>= s_10 1)) (and (and (< ?v_19 256) (<= 0 ?v_19)) (and (and (< s_10 2) (<= 0 s_10)) (and (= (> ?v_22 256) (= o_9 1)) (and (and (< ?v_23 256) (<= 0 ?v_23)) (and (and (<= o_9 1) (<= 0 o_9)) (and (= (> ?v_24 256) (>= s_9 1)) (and (and (< ?v_25 256) (<= 0 ?v_25)) (and (and (< s_9 2) (<= 0 s_9)) (and (= (> ?v_28 256) (= o_8 1)) (and (and (< ?v_29 256) (<= 0 ?v_29)) (and (and (<= o_8 1) (<= 0 o_8)) (and (= (> ?v_30 256) (>= s_8 1)) (and (and (< ?v_31 256) (<= 0 ?v_31)) (and (and (< s_8 2) (<= 0 s_8)) (and (= (> ?v_32 256) (= o_7 1)) (and (and (< ?v_33 256) (<= 0 ?v_33)) (and (and (<= o_7 1) (<= 0 o_7)) (and (= (> ?v_34 256) (= o_6 1)) (and (and (< ?v_35 256) (<= 0 ?v_35)) (and (and (<= o_6 1) (<= 0 o_6)) (and (= (> ?v_36 256) (= o_5 1)) (and (and (< ?v_37 256) (<= 0 ?v_37)) (and (and (<= o_5 1) (<= 0 o_5)) (and (= (> ?v_38 256) (= o_4 1)) (and (and (< ?v_39 256) (<= 0 ?v_39)) (and (and (<= o_4 1) (<= 0 o_4)) (and (= (> ?v_40 256) (= o_3 1)) (and (and (< ?v_41 256) (<= 0 ?v_41)) (and (and (<= o_3 1) (<= 0 o_3)) (and (= (> ?v_42 256) (>= s_5 1)) (and (and (< ?v_43 256) (<= 0 ?v_43)) (and (and (< s_5 64) (<= 0 s_5)) (and (= (> ?v_44 256) (= o_2 1)) (and (and (< ?v_45 256) (<= 0 ?v_45)) (and (and (<= o_2 1) (<= 0 o_2)) (and (= (> ?v_46 256) (>= s_4 1)) (and (and (< ?v_47 256) (<= 0 ?v_47)) (and (and (< s_4 32) (<= 0 s_4)) (and (= (> ?v_48 256) (>= s_3 1)) (and (and (< ?v_49 256) (<= 0 ?v_49)) (and (and (< s_3 16) (<= 0 s_3)) (and (= (> ?v_50 256) (= o_1 1)) (and (and (< ?v_51 256) (<= 0 ?v_51)) (and (and (<= o_1 1) (<= 0 o_1)) (and (= (> ?v_52 256) (>= s_2 1)) (and (and (< ?v_53 256) (<= 0 ?v_53)) (and (and (< s_2 8) (<= 0 s_2)) (and (= (> ?v_54 256) (>= s_1 1)) (and (and (< ?v_55 256) (<= 0 ?v_55)) (and (and (< s_1 4) (<= 0 s_1)) (and (= (> ?v_56 256) (= o_0 1)) (and (and (< ?v_57 256) (<= 0 ?v_57)) (and (and (<= o_0 1) (<= 0 o_0)) (and (and (< v6 256) (>= v6 0)) (and (and (< v5 256) (>= v5 0)) (and (and (< v4 256) (>= v4 0)) (and (and (< v3 256) (>= v3 0)) (and (and (< v2 256) (>= v2 0)) (and (and (< v1 256) (>= v1 0)) (and (< v0 256) (>= v0 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
