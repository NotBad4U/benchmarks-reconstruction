(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(set-info :source |
show equivalence of the following terms:
(((4 * v2 + 8 * v3) + (16 * v4 + 32 * v5)) + ((64 * v6 + 128 * v7) + (256 * v8 + (1 * v0 + 2 * v1))))

v0 + 2 * (v1 + 2 * (v2 + 2 * (v3 + 2 * (v4 + 2 * (v5 + 2 * (v6 + 2 * (v7 + 2 * (v8))))))))

in arithmetic modulo 2exp10
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
(declare-fun v8 () Int)
(declare-fun o_0 () Int)
(declare-fun o_1 () Int)
(declare-fun s_3 () Int)
(declare-fun s_4 () Int)
(declare-fun o_2 () Int)
(declare-fun s_5 () Int)
(declare-fun s_6 () Int)
(declare-fun o_3 () Int)
(declare-fun s_7 () Int)
(declare-fun o_4 () Int)
(declare-fun o_5 () Int)
(declare-fun o_6 () Int)
(declare-fun o_7 () Int)
(declare-fun o_8 () Int)
(declare-fun o_9 () Int)
(declare-fun o_10 () Int)
(declare-fun o_11 () Int)
(declare-fun s_12 () Int)
(declare-fun o_12 () Int)
(declare-fun s_13 () Int)
(declare-fun o_13 () Int)
(declare-fun s_14 () Int)
(declare-fun o_14 () Int)
(declare-fun s_15 () Int)
(declare-fun o_15 () Int)
(assert (let ((?v_0 (* v8 2))) (let ((?v_2 (< ?v_0 1024)) (?v_3 (< ?v_0 2048))) (let ((?v_59 (+ (ite ?v_2 ?v_0 (ite ?v_3 (- ?v_0 1024) (- ?v_0 2048))) v7))) (let ((?v_60 (- ?v_59 (* o_8 1024))) (?v_69 (* v8 256))) (let ((?v_70 (- ?v_69 (* s_7 1024))) (?v_20 (* v1 2))) (let ((?v_85 (+ (ite (< ?v_20 1024) ?v_20 (ite (< ?v_20 2048) (- ?v_20 1024) (- ?v_20 2048))) v0))) (let ((?v_86 (- ?v_85 (* o_0 1024)))) (let ((?v_67 (+ ?v_70 ?v_86))) (let ((?v_68 (- ?v_67 (* o_4 1024))) (?v_73 (* v7 128))) (let ((?v_74 (- ?v_73 (* s_6 1024))) (?v_75 (* v6 64))) (let ((?v_76 (- ?v_75 (* s_5 1024)))) (let ((?v_71 (+ ?v_74 ?v_76))) (let ((?v_72 (- ?v_71 (* o_3 1024)))) (let ((?v_63 (+ ?v_68 ?v_72))) (let ((?v_64 (- ?v_63 (* o_6 1024))) (?v_79 (* v5 32))) (let ((?v_80 (- ?v_79 (* s_4 1024))) (?v_81 (* v4 16))) (let ((?v_82 (- ?v_81 (* s_3 1024)))) (let ((?v_77 (+ ?v_80 ?v_82))) (let ((?v_78 (- ?v_77 (* o_2 1024))) (?v_21 (* v3 8)) (?v_22 (* v2 4))) (let ((?v_83 (+ (ite (< ?v_21 1024) ?v_21 (ite (< ?v_21 2048) (- ?v_21 1024) (ite (< ?v_21 3072) (- ?v_21 2048) (ite (< ?v_21 4096) (- ?v_21 3072) (ite (< ?v_21 5120) (- ?v_21 4096) (ite (< ?v_21 6144) (- ?v_21 5120) (ite (< ?v_21 7168) (- ?v_21 6144) (ite (< ?v_21 8192) (- ?v_21 7168) (- ?v_21 8192))))))))) (ite (< ?v_22 1024) ?v_22 (ite (< ?v_22 2048) (- ?v_22 1024) (ite (< ?v_22 3072) (- ?v_22 2048) (ite (< ?v_22 4096) (- ?v_22 3072) (- ?v_22 4096)))))))) (let ((?v_84 (- ?v_83 (* o_1 1024)))) (let ((?v_65 (+ ?v_78 ?v_84))) (let ((?v_66 (- ?v_65 (* o_5 1024)))) (let ((?v_61 (+ ?v_64 ?v_66))) (let ((?v_62 (- ?v_61 (* o_7 1024))) (?v_1 (* 4 v8))) (let ((?v_5 (- (+ (ite ?v_2 ?v_1 (ite ?v_3 (- ?v_1 2048) (- ?v_1 4096))) (* 2 v7)) (* 2048 o_8)))) (let ((?v_7 (< ?v_5 1024)) (?v_9 (< ?v_5 2048))) (let ((?v_57 (+ (ite ?v_7 ?v_5 (ite ?v_9 (- ?v_5 1024) (- ?v_5 2048))) v6))) (let ((?v_58 (- ?v_57 (* o_9 1024))) (?v_4 (* 8 v8))) (let ((?v_6 (- (+ (ite ?v_2 ?v_4 (ite ?v_3 (- ?v_4 4096) (- ?v_4 8192))) (* 4 v7)) (* 4096 o_8)))) (let ((?v_11 (- (+ (ite ?v_7 ?v_6 (ite ?v_9 (- ?v_6 2048) (- ?v_6 4096))) (* 2 v6)) (* 2048 o_9)))) (let ((?v_13 (< ?v_11 1024)) (?v_16 (< ?v_11 2048))) (let ((?v_55 (+ (ite ?v_13 ?v_11 (ite ?v_16 (- ?v_11 1024) (- ?v_11 2048))) v5))) (let ((?v_56 (- ?v_55 (* o_10 1024))) (?v_8 (* 16 v8))) (let ((?v_10 (- (+ (ite ?v_2 ?v_8 (ite ?v_3 (- ?v_8 8192) (- ?v_8 16384))) (* 8 v7)) (* 8192 o_8)))) (let ((?v_12 (- (+ (ite ?v_7 ?v_10 (ite ?v_9 (- ?v_10 4096) (- ?v_10 8192))) (* 4 v6)) (* 4096 o_9)))) (let ((?v_18 (- (+ (ite ?v_13 ?v_12 (ite ?v_16 (- ?v_12 2048) (- ?v_12 4096))) (* 2 v5)) (* 2048 o_10)))) (let ((?v_27 (< ?v_18 1024)) (?v_31 (< ?v_18 2048))) (let ((?v_53 (+ (ite ?v_27 ?v_18 (ite ?v_31 (- ?v_18 1024) (- ?v_18 2048))) v4))) (let ((?v_54 (- ?v_53 (* o_11 1024))) (?v_45 (* 32 v8))) (let ((?v_46 (- (+ (ite ?v_2 ?v_45 (ite ?v_3 (- ?v_45 16384) (- ?v_45 32768))) (* 16 v7)) (* 16384 o_8)))) (let ((?v_47 (- (+ (ite ?v_7 ?v_46 (ite ?v_9 (- ?v_46 8192) (- ?v_46 16384))) (* 8 v6)) (* 8192 o_9)))) (let ((?v_48 (- (+ (ite ?v_13 ?v_47 (ite ?v_16 (- ?v_47 4096) (- ?v_47 8192))) (* 4 v5)) (* 4096 o_10)))) (let ((?v_51 (- (+ (ite ?v_27 ?v_48 (ite ?v_31 (- ?v_48 2048) (- ?v_48 4096))) (* 2 v4)) (* 2048 o_11)))) (let ((?v_52 (- ?v_51 (* s_12 1024)))) (let ((?v_49 (+ ?v_52 v3))) (let ((?v_50 (- ?v_49 (* o_12 1024))) (?v_37 (* 64 v8))) (let ((?v_38 (- (+ (ite ?v_2 ?v_37 (ite ?v_3 (- ?v_37 32768) (- ?v_37 65536))) (* 32 v7)) (* 32768 o_8)))) (let ((?v_39 (- (+ (ite ?v_7 ?v_38 (ite ?v_9 (- ?v_38 16384) (- ?v_38 32768))) (* 16 v6)) (* 16384 o_9)))) (let ((?v_40 (- (+ (ite ?v_13 ?v_39 (ite ?v_16 (- ?v_39 8192) (- ?v_39 16384))) (* 8 v5)) (* 8192 o_10)))) (let ((?v_43 (- (+ (- (- (+ (ite ?v_27 ?v_40 (ite ?v_31 (- ?v_40 4096) (- ?v_40 8192))) (* 4 v4)) (* 4096 o_11)) (* 2048 s_12)) (* 2 v3)) (* 2048 o_12)))) (let ((?v_44 (- ?v_43 (* s_13 1024)))) (let ((?v_41 (+ ?v_44 v2))) (let ((?v_42 (- ?v_41 (* o_13 1024))) (?v_28 (* 128 v8))) (let ((?v_29 (- (+ (ite ?v_2 ?v_28 (ite ?v_3 (- ?v_28 65536) (- ?v_28 131072))) (* 64 v7)) (* 65536 o_8)))) (let ((?v_30 (- (+ (ite ?v_7 ?v_29 (ite ?v_9 (- ?v_29 32768) (- ?v_29 65536))) (* 32 v6)) (* 32768 o_9)))) (let ((?v_32 (- (+ (ite ?v_13 ?v_30 (ite ?v_16 (- ?v_30 16384) (- ?v_30 32768))) (* 16 v5)) (* 16384 o_10)))) (let ((?v_35 (- (+ (- (- (+ (- (- (+ (ite ?v_27 ?v_32 (ite ?v_31 (- ?v_32 8192) (- ?v_32 16384))) (* 8 v4)) (* 8192 o_11)) (* 4096 s_12)) (* 4 v3)) (* 4096 o_12)) (* 2048 s_13)) (* 2 v2)) (* 2048 o_13)))) (let ((?v_36 (- ?v_35 (* s_14 1024)))) (let ((?v_33 (+ ?v_36 v1))) (let ((?v_34 (- ?v_33 (* o_14 1024))) (?v_14 (* 256 v8))) (let ((?v_15 (- (+ (ite ?v_2 ?v_14 (ite ?v_3 (- ?v_14 131072) (- ?v_14 262144))) (* 128 v7)) (* 131072 o_8)))) (let ((?v_17 (- (+ (ite ?v_7 ?v_15 (ite ?v_9 (- ?v_15 65536) (- ?v_15 131072))) (* 64 v6)) (* 65536 o_9)))) (let ((?v_19 (- (+ (ite ?v_13 ?v_17 (ite ?v_16 (- ?v_17 32768) (- ?v_17 65536))) (* 32 v5)) (* 32768 o_10)))) (let ((?v_25 (- (+ (- (- (+ (- (- (+ (- (- (+ (ite ?v_27 ?v_19 (ite ?v_31 (- ?v_19 16384) (- ?v_19 32768))) (* 16 v4)) (* 16384 o_11)) (* 8192 s_12)) (* 8 v3)) (* 8192 o_12)) (* 4096 s_13)) (* 4 v2)) (* 4096 o_13)) (* 2048 s_14)) (* 2 v1)) (* 2048 o_14)))) (let ((?v_26 (- ?v_25 (* s_15 1024)))) (let ((?v_23 (+ ?v_26 v0))) (let ((?v_24 (- ?v_23 (* o_15 1024)))) (and (not (= ?v_24 ?v_62)) (and (= (> ?v_23 1024) (= o_15 1)) (and (and (< ?v_24 1024) (<= 0 ?v_24)) (and (and (<= o_15 1) (<= 0 o_15)) (and (= (> ?v_25 1024) (>= s_15 1)) (and (and (< ?v_26 1024) (<= 0 ?v_26)) (and (and (< s_15 2) (<= 0 s_15)) (and (= (> ?v_33 1024) (= o_14 1)) (and (and (< ?v_34 1024) (<= 0 ?v_34)) (and (and (<= o_14 1) (<= 0 o_14)) (and (= (> ?v_35 1024) (>= s_14 1)) (and (and (< ?v_36 1024) (<= 0 ?v_36)) (and (and (< s_14 2) (<= 0 s_14)) (and (= (> ?v_41 1024) (= o_13 1)) (and (and (< ?v_42 1024) (<= 0 ?v_42)) (and (and (<= o_13 1) (<= 0 o_13)) (and (= (> ?v_43 1024) (>= s_13 1)) (and (and (< ?v_44 1024) (<= 0 ?v_44)) (and (and (< s_13 2) (<= 0 s_13)) (and (= (> ?v_49 1024) (= o_12 1)) (and (and (< ?v_50 1024) (<= 0 ?v_50)) (and (and (<= o_12 1) (<= 0 o_12)) (and (= (> ?v_51 1024) (>= s_12 1)) (and (and (< ?v_52 1024) (<= 0 ?v_52)) (and (and (< s_12 2) (<= 0 s_12)) (and (= (> ?v_53 1024) (= o_11 1)) (and (and (< ?v_54 1024) (<= 0 ?v_54)) (and (and (<= o_11 1) (<= 0 o_11)) (and (= (> ?v_55 1024) (= o_10 1)) (and (and (< ?v_56 1024) (<= 0 ?v_56)) (and (and (<= o_10 1) (<= 0 o_10)) (and (= (> ?v_57 1024) (= o_9 1)) (and (and (< ?v_58 1024) (<= 0 ?v_58)) (and (and (<= o_9 1) (<= 0 o_9)) (and (= (> ?v_59 1024) (= o_8 1)) (and (and (< ?v_60 1024) (<= 0 ?v_60)) (and (and (<= o_8 1) (<= 0 o_8)) (and (= (> ?v_61 1024) (= o_7 1)) (and (and (< ?v_62 1024) (<= 0 ?v_62)) (and (and (<= o_7 1) (<= 0 o_7)) (and (= (> ?v_63 1024) (= o_6 1)) (and (and (< ?v_64 1024) (<= 0 ?v_64)) (and (and (<= o_6 1) (<= 0 o_6)) (and (= (> ?v_65 1024) (= o_5 1)) (and (and (< ?v_66 1024) (<= 0 ?v_66)) (and (and (<= o_5 1) (<= 0 o_5)) (and (= (> ?v_67 1024) (= o_4 1)) (and (and (< ?v_68 1024) (<= 0 ?v_68)) (and (and (<= o_4 1) (<= 0 o_4)) (and (= (> ?v_69 1024) (>= s_7 1)) (and (and (< ?v_70 1024) (<= 0 ?v_70)) (and (and (< s_7 256) (<= 0 s_7)) (and (= (> ?v_71 1024) (= o_3 1)) (and (and (< ?v_72 1024) (<= 0 ?v_72)) (and (and (<= o_3 1) (<= 0 o_3)) (and (= (> ?v_73 1024) (>= s_6 1)) (and (and (< ?v_74 1024) (<= 0 ?v_74)) (and (and (< s_6 128) (<= 0 s_6)) (and (= (> ?v_75 1024) (>= s_5 1)) (and (and (< ?v_76 1024) (<= 0 ?v_76)) (and (and (< s_5 64) (<= 0 s_5)) (and (= (> ?v_77 1024) (= o_2 1)) (and (and (< ?v_78 1024) (<= 0 ?v_78)) (and (and (<= o_2 1) (<= 0 o_2)) (and (= (> ?v_79 1024) (>= s_4 1)) (and (and (< ?v_80 1024) (<= 0 ?v_80)) (and (and (< s_4 32) (<= 0 s_4)) (and (= (> ?v_81 1024) (>= s_3 1)) (and (and (< ?v_82 1024) (<= 0 ?v_82)) (and (and (< s_3 16) (<= 0 s_3)) (and (= (> ?v_83 1024) (= o_1 1)) (and (and (< ?v_84 1024) (<= 0 ?v_84)) (and (and (<= o_1 1) (<= 0 o_1)) (and (= (> ?v_85 1024) (= o_0 1)) (and (and (< ?v_86 1024) (<= 0 ?v_86)) (and (and (<= o_0 1) (<= 0 o_0)) (and (and (< v8 1024) (>= v8 0)) (and (and (< v7 1024) (>= v7 0)) (and (and (< v6 1024) (>= v6 0)) (and (and (< v5 1024) (>= v5 0)) (and (and (< v4 1024) (>= v4 0)) (and (and (< v3 1024) (>= v3 0)) (and (and (< v2 1024) (>= v2 0)) (and (and (< v1 1024) (>= v1 0)) (and (< v0 1024) (>= v0 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
(exit)
