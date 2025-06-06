(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(set-info :source |
show equivalence of the following terms:
(((1 * v0 + 2 * v1) + (4 * v2 + 8 * v3)) + ((16 * v4 + 32 * v5) + (64 * v6 + 128 * v7)))

v0 + 2 * (v1 + 2 * (v2 + 2 * (v3 + 2 * (v4 + 2 * (v5 + 2 * (v6 + 2 * (v7)))))))

in arithmetic modulo 2exp12
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
(declare-fun v7 () Int)
(declare-fun s_0 () Int)
(declare-fun o_0 () Int)
(declare-fun s_1 () Int)
(declare-fun s_2 () Int)
(declare-fun o_1 () Int)
(declare-fun s_3 () Int)
(declare-fun s_4 () Int)
(declare-fun o_2 () Int)
(declare-fun s_5 () Int)
(declare-fun s_6 () Int)
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
(declare-fun s_12 () Int)
(declare-fun o_12 () Int)
(declare-fun s_13 () Int)
(declare-fun o_13 () Int)
(assert (let ((?v_0 (* v7 2))) (let ((?v_6 (< ?v_0 4096)) (?v_7 (< ?v_0 8192))) (let ((?v_33 (+ (ite ?v_6 ?v_0 (ite ?v_7 (- ?v_0 4096) (- ?v_0 8192))) v6))) (let ((?v_34 (- ?v_33 (* o_7 4096))) (?v_43 (* v7 128))) (let ((?v_44 (- ?v_43 (* s_6 4096))) (?v_45 (* v6 64))) (let ((?v_46 (- ?v_45 (* s_5 4096)))) (let ((?v_41 (+ ?v_44 ?v_46))) (let ((?v_42 (- ?v_41 (* o_3 4096))) (?v_49 (* v5 32))) (let ((?v_50 (- ?v_49 (* s_4 4096))) (?v_51 (* v4 16))) (let ((?v_52 (- ?v_51 (* s_3 4096)))) (let ((?v_47 (+ ?v_50 ?v_52))) (let ((?v_48 (- ?v_47 (* o_2 4096)))) (let ((?v_37 (+ ?v_42 ?v_48))) (let ((?v_38 (- ?v_37 (* o_5 4096))) (?v_55 (* v3 8))) (let ((?v_56 (- ?v_55 (* s_2 4096))) (?v_57 (* v2 4))) (let ((?v_58 (- ?v_57 (* s_1 4096)))) (let ((?v_53 (+ ?v_56 ?v_58))) (let ((?v_54 (- ?v_53 (* o_1 4096))) (?v_61 (* v1 2))) (let ((?v_62 (- ?v_61 (* s_0 4096)))) (let ((?v_59 (+ ?v_62 v0))) (let ((?v_60 (- ?v_59 (* o_0 4096)))) (let ((?v_39 (+ ?v_54 ?v_60))) (let ((?v_40 (- ?v_39 (* o_4 4096)))) (let ((?v_35 (+ ?v_38 ?v_40))) (let ((?v_36 (- ?v_35 (* o_6 4096))) (?v_28 (* 4 v7))) (let ((?v_31 (- (+ (ite ?v_6 ?v_28 (ite ?v_7 (- ?v_28 8192) (- ?v_28 16384))) (* 2 v6)) (* 8192 o_7)))) (let ((?v_32 (- ?v_31 (* s_8 4096)))) (let ((?v_29 (+ ?v_32 v5))) (let ((?v_30 (- ?v_29 (* o_8 4096))) (?v_23 (* 8 v7))) (let ((?v_26 (- (+ (- (- (+ (ite ?v_6 ?v_23 (ite ?v_7 (- ?v_23 16384) (- ?v_23 32768))) (* 4 v6)) (* 16384 o_7)) (* 8192 s_8)) (* 2 v5)) (* 8192 o_8)))) (let ((?v_27 (- ?v_26 (* s_9 4096)))) (let ((?v_24 (+ ?v_27 v4))) (let ((?v_25 (- ?v_24 (* o_9 4096))) (?v_18 (* 16 v7))) (let ((?v_21 (- (+ (- (- (+ (- (- (+ (ite ?v_6 ?v_18 (ite ?v_7 (- ?v_18 32768) (- ?v_18 65536))) (* 8 v6)) (* 32768 o_7)) (* 16384 s_8)) (* 4 v5)) (* 16384 o_8)) (* 8192 s_9)) (* 2 v4)) (* 8192 o_9)))) (let ((?v_22 (- ?v_21 (* s_10 4096)))) (let ((?v_19 (+ ?v_22 v3))) (let ((?v_20 (- ?v_19 (* o_10 4096))) (?v_13 (* 32 v7))) (let ((?v_16 (- (+ (- (- (+ (- (- (+ (- (- (+ (ite ?v_6 ?v_13 (ite ?v_7 (- ?v_13 65536) (- ?v_13 131072))) (* 16 v6)) (* 65536 o_7)) (* 32768 s_8)) (* 8 v5)) (* 32768 o_8)) (* 16384 s_9)) (* 4 v4)) (* 16384 o_9)) (* 8192 s_10)) (* 2 v3)) (* 8192 o_10)))) (let ((?v_17 (- ?v_16 (* s_11 4096)))) (let ((?v_14 (+ ?v_17 v2))) (let ((?v_15 (- ?v_14 (* o_11 4096))) (?v_8 (* 64 v7))) (let ((?v_11 (- (+ (- (- (+ (- (- (+ (- (- (+ (- (- (+ (ite ?v_6 ?v_8 (ite ?v_7 (- ?v_8 131072) (- ?v_8 262144))) (* 32 v6)) (* 131072 o_7)) (* 65536 s_8)) (* 16 v5)) (* 65536 o_8)) (* 32768 s_9)) (* 8 v4)) (* 32768 o_9)) (* 16384 s_10)) (* 4 v3)) (* 16384 o_10)) (* 8192 s_11)) (* 2 v2)) (* 8192 o_11)))) (let ((?v_12 (- ?v_11 (* s_12 4096)))) (let ((?v_9 (+ ?v_12 v1))) (let ((?v_10 (- ?v_9 (* o_12 4096))) (?v_1 (* 128 v7))) (let ((?v_4 (- (+ (- (- (+ (- (- (+ (- (- (+ (- (- (+ (- (- (+ (ite ?v_6 ?v_1 (ite ?v_7 (- ?v_1 262144) (- ?v_1 524288))) (* 64 v6)) (* 262144 o_7)) (* 131072 s_8)) (* 32 v5)) (* 131072 o_8)) (* 65536 s_9)) (* 16 v4)) (* 65536 o_9)) (* 32768 s_10)) (* 8 v3)) (* 32768 o_10)) (* 16384 s_11)) (* 4 v2)) (* 16384 o_11)) (* 8192 s_12)) (* 2 v1)) (* 8192 o_12)))) (let ((?v_5 (- ?v_4 (* s_13 4096)))) (let ((?v_2 (+ ?v_5 v0))) (let ((?v_3 (- ?v_2 (* o_13 4096)))) (and (not (= ?v_3 ?v_36)) (and (= (> ?v_2 4096) (= o_13 1)) (and (and (< ?v_3 4096) (<= 0 ?v_3)) (and (and (<= o_13 1) (<= 0 o_13)) (and (= (> ?v_4 4096) (>= s_13 1)) (and (and (< ?v_5 4096) (<= 0 ?v_5)) (and (and (< s_13 2) (<= 0 s_13)) (and (= (> ?v_9 4096) (= o_12 1)) (and (and (< ?v_10 4096) (<= 0 ?v_10)) (and (and (<= o_12 1) (<= 0 o_12)) (and (= (> ?v_11 4096) (>= s_12 1)) (and (and (< ?v_12 4096) (<= 0 ?v_12)) (and (and (< s_12 2) (<= 0 s_12)) (and (= (> ?v_14 4096) (= o_11 1)) (and (and (< ?v_15 4096) (<= 0 ?v_15)) (and (and (<= o_11 1) (<= 0 o_11)) (and (= (> ?v_16 4096) (>= s_11 1)) (and (and (< ?v_17 4096) (<= 0 ?v_17)) (and (and (< s_11 2) (<= 0 s_11)) (and (= (> ?v_19 4096) (= o_10 1)) (and (and (< ?v_20 4096) (<= 0 ?v_20)) (and (and (<= o_10 1) (<= 0 o_10)) (and (= (> ?v_21 4096) (>= s_10 1)) (and (and (< ?v_22 4096) (<= 0 ?v_22)) (and (and (< s_10 2) (<= 0 s_10)) (and (= (> ?v_24 4096) (= o_9 1)) (and (and (< ?v_25 4096) (<= 0 ?v_25)) (and (and (<= o_9 1) (<= 0 o_9)) (and (= (> ?v_26 4096) (>= s_9 1)) (and (and (< ?v_27 4096) (<= 0 ?v_27)) (and (and (< s_9 2) (<= 0 s_9)) (and (= (> ?v_29 4096) (= o_8 1)) (and (and (< ?v_30 4096) (<= 0 ?v_30)) (and (and (<= o_8 1) (<= 0 o_8)) (and (= (> ?v_31 4096) (>= s_8 1)) (and (and (< ?v_32 4096) (<= 0 ?v_32)) (and (and (< s_8 2) (<= 0 s_8)) (and (= (> ?v_33 4096) (= o_7 1)) (and (and (< ?v_34 4096) (<= 0 ?v_34)) (and (and (<= o_7 1) (<= 0 o_7)) (and (= (> ?v_35 4096) (= o_6 1)) (and (and (< ?v_36 4096) (<= 0 ?v_36)) (and (and (<= o_6 1) (<= 0 o_6)) (and (= (> ?v_37 4096) (= o_5 1)) (and (and (< ?v_38 4096) (<= 0 ?v_38)) (and (and (<= o_5 1) (<= 0 o_5)) (and (= (> ?v_39 4096) (= o_4 1)) (and (and (< ?v_40 4096) (<= 0 ?v_40)) (and (and (<= o_4 1) (<= 0 o_4)) (and (= (> ?v_41 4096) (= o_3 1)) (and (and (< ?v_42 4096) (<= 0 ?v_42)) (and (and (<= o_3 1) (<= 0 o_3)) (and (= (> ?v_43 4096) (>= s_6 1)) (and (and (< ?v_44 4096) (<= 0 ?v_44)) (and (and (< s_6 128) (<= 0 s_6)) (and (= (> ?v_45 4096) (>= s_5 1)) (and (and (< ?v_46 4096) (<= 0 ?v_46)) (and (and (< s_5 64) (<= 0 s_5)) (and (= (> ?v_47 4096) (= o_2 1)) (and (and (< ?v_48 4096) (<= 0 ?v_48)) (and (and (<= o_2 1) (<= 0 o_2)) (and (= (> ?v_49 4096) (>= s_4 1)) (and (and (< ?v_50 4096) (<= 0 ?v_50)) (and (and (< s_4 32) (<= 0 s_4)) (and (= (> ?v_51 4096) (>= s_3 1)) (and (and (< ?v_52 4096) (<= 0 ?v_52)) (and (and (< s_3 16) (<= 0 s_3)) (and (= (> ?v_53 4096) (= o_1 1)) (and (and (< ?v_54 4096) (<= 0 ?v_54)) (and (and (<= o_1 1) (<= 0 o_1)) (and (= (> ?v_55 4096) (>= s_2 1)) (and (and (< ?v_56 4096) (<= 0 ?v_56)) (and (and (< s_2 8) (<= 0 s_2)) (and (= (> ?v_57 4096) (>= s_1 1)) (and (and (< ?v_58 4096) (<= 0 ?v_58)) (and (and (< s_1 4) (<= 0 s_1)) (and (= (> ?v_59 4096) (= o_0 1)) (and (and (< ?v_60 4096) (<= 0 ?v_60)) (and (and (<= o_0 1) (<= 0 o_0)) (and (= (> ?v_61 4096) (>= s_0 1)) (and (and (< ?v_62 4096) (<= 0 ?v_62)) (and (and (< s_0 2) (<= 0 s_0)) (and (and (< v7 4096) (>= v7 0)) (and (and (< v6 4096) (>= v6 0)) (and (and (< v5 4096) (>= v5 0)) (and (and (< v4 4096) (>= v4 0)) (and (and (< v3 4096) (>= v3 0)) (and (and (< v2 4096) (>= v2 0)) (and (and (< v1 4096) (>= v1 0)) (and (< v0 4096) (>= v0 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
