(set-info :smt-lib-version 2.6)
(set-logic QF_LIA)
(set-info :source |
Alberto Griggio

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
(declare-fun s_7 () Int)
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
(assert (let ((?v_66 (- o_5)) (?v_29 (- o_2)) (?v_28 (- s_3)) (?v_10 (- s_4)) (?v_27 (- o_3)) (?v_18 (- s_5)) (?v_17 (- s_6)) (?v_21 (* v1 2)) (?v_33 (* v2 4)) (?v_32 (* v3 8)) (?v_63 (* v4 16)) (?v_62 (* v5 32)) (?v_61 (* v6 64)) (?v_60 (* v7 128)) (?v_53 (* v3 2)) (?v_9 (* v5 2)) (?v_15 (* v6 4)) (?v_16 (* v7 8))) (let ((?v_26 (+ ?v_15 ?v_16))) (let ((?v_31 (+ (+ (+ (+ (+ (+ (+ (+ ?v_26 ?v_9) v4) ?v_17) ?v_18) ?v_27) ?v_10) ?v_28) ?v_29))) (let ((?v_30 (+ ?v_31 ?v_66)) (?v_20 (+ (+ ?v_26 ?v_17) ?v_18))) (let ((?v_19 (+ ?v_20 ?v_27)) (?v_14 (+ ?v_16 ?v_17)) (?v_13 (+ ?v_15 ?v_18)) (?v_12 (+ (+ (+ ?v_9 v4) ?v_10) ?v_28))) (let ((?v_11 (+ ?v_12 ?v_29)) (?v_8 (+ ?v_9 ?v_10)) (?v_0 (+ (* s_0 (- 8)) v1)) (?v_22 (* s_0 (- 16)))) (let ((?v_2 (+ (+ ?v_21 v0) ?v_22)) (?v_23 (* o_0 (- 16)))) (let ((?v_1 (+ ?v_2 ?v_23)) (?v_5 (* s_1 (- 4)))) (let ((?v_3 (+ ?v_5 v2)) (?v_4 (+ (* s_2 (- 2)) v3)) (?v_7 (+ (+ (+ ?v_53 v2) (* s_2 (- 4))) ?v_5))) (let ((?v_6 (+ (* o_1 (- 4)) ?v_7)) (?v_34 (* s_2 (- 16))) (?v_35 (* s_1 (- 16))) (?v_36 (* o_1 (- 16)))) (let ((?v_25 (+ (+ (+ (+ (+ (+ (+ (+ ?v_33 ?v_32) ?v_21) v0) ?v_34) ?v_35) ?v_36) ?v_22) ?v_23)) (?v_37 (* o_4 (- 16)))) (let ((?v_24 (+ ?v_25 ?v_37)) (?v_39 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ ?v_61 ?v_60) ?v_62) ?v_63) ?v_32) ?v_33) ?v_21) v0) (* s_6 (- 16))) (* s_5 (- 16))) (* o_3 (- 16))) (* s_4 (- 16))) (* s_3 (- 16))) (* o_2 (- 16))) (* o_5 (- 16))) ?v_34) ?v_35) ?v_36) ?v_22) ?v_23) ?v_37))) (let ((?v_38 (+ (* o_6 (- 16)) ?v_39)) (?v_40 (+ (* s_7 (- 8)) v7)) (?v_42 (+ (+ (* s_7 (- 16)) (* v7 2)) v6))) (let ((?v_41 (+ ?v_42 (* o_7 (- 16))))) (let ((?v_43 (+ (* s_8 (- 8)) ?v_41)) (?v_45 (+ (+ (+ (+ (+ (* s_7 (- 32)) (* v7 4)) (* v6 2)) (* o_7 (- 32))) (* s_8 (- 16))) v5))) (let ((?v_44 (+ ?v_45 (* o_8 (- 16))))) (let ((?v_46 (+ (* s_9 (- 8)) ?v_44)) (?v_48 (+ (+ (+ (+ (+ (+ (+ (+ (* s_7 (- 64)) ?v_16) ?v_15) (* o_7 (- 64))) (* s_8 (- 32))) ?v_9) (* o_8 (- 32))) (* s_9 (- 16))) v4))) (let ((?v_47 (+ ?v_48 (* o_9 (- 16))))) (let ((?v_49 (+ (* s_10 (- 8)) ?v_47)) (?v_51 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (* s_7 (- 128)) (* v7 16)) (* v6 8)) (* o_7 (- 128))) (* s_8 (- 64))) (* v5 4)) (* o_8 (- 64))) (* s_9 (- 32))) (* v4 2)) (* o_9 (- 32))) (* s_10 (- 16))) v3))) (let ((?v_50 (+ ?v_51 (* o_10 (- 16))))) (let ((?v_52 (+ (* s_11 (- 8)) ?v_50)) (?v_55 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (* s_7 (- 256)) (* v7 32)) (* v6 16)) (* o_7 (- 256))) (* s_8 (- 128))) (* v5 8)) (* o_8 (- 128))) (* s_9 (- 64))) (* v4 4)) (* o_9 (- 64))) (* s_10 (- 32))) ?v_53) (* o_10 (- 32))) (* s_11 (- 16))) v2))) (let ((?v_54 (+ ?v_55 (* o_11 (- 16))))) (let ((?v_56 (+ (* s_12 (- 8)) ?v_54)) (?v_58 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (* s_7 (- 512)) (* v7 64)) (* v6 32)) (* o_7 (- 512))) (* s_8 (- 256))) (* v5 16)) (* o_8 (- 256))) (* s_9 (- 128))) (* v4 8)) (* o_9 (- 128))) (* s_10 (- 64))) (* v3 4)) (* o_10 (- 64))) (* s_11 (- 32))) (* v2 2)) (* o_11 (- 32))) (* s_12 (- 16))) v1))) (let ((?v_57 (+ ?v_58 (* o_12 (- 16))))) (let ((?v_59 (+ (* s_13 (- 8)) ?v_57)) (?v_65 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (* s_7 (- 1024)) ?v_60) ?v_61) (* o_7 (- 1024))) (* s_8 (- 512))) ?v_62) (* o_8 (- 512))) (* s_9 (- 256))) ?v_63) (* o_9 (- 256))) (* s_10 (- 128))) ?v_32) (* o_10 (- 128))) (* s_11 (- 64))) ?v_33) (* o_11 (- 64))) (* s_12 (- 32))) ?v_21) (* o_12 (- 32))) (* s_13 (- 16))) v0))) (let ((?v_64 (+ (* o_13 (- 16)) ?v_65))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= 0 v0) (not (<= 16 v0))) (and (<= 0 v1) (not (<= 16 v1)))) (and (<= 0 v2) (not (<= 16 v2)))) (and (<= 0 v3) (not (<= 16 v3)))) (and (<= 0 v4) (not (<= 16 v4)))) (and (<= 0 v5) (not (<= 16 v5)))) (and (<= 0 v6) (not (<= 16 v6)))) (and (<= 0 v7) (not (<= 16 v7)))) (and (not (<= 2 s_0)) (<= 0 s_0))) (and (<= 0 ?v_0) (not (<= 8 ?v_0)))) (= (<= 1 s_0) (not (<= v1 8)))) (and (<= 0 o_0) (<= o_0 1))) (and (<= 0 ?v_1) (not (<= 16 ?v_1)))) (= (not (<= ?v_2 16)) (= o_0 1))) (and (not (<= 4 s_1)) (<= 0 s_1))) (and (<= 0 ?v_3) (not (<= 4 ?v_3)))) (= (<= 1 s_1) (not (<= v2 4)))) (and (not (<= 8 s_2)) (<= 0 s_2))) (and (<= 0 ?v_4) (not (<= 2 ?v_4)))) (= (<= 1 s_2) (not (<= v3 2)))) (and (<= 0 o_1) (<= o_1 1))) (and (<= 0 ?v_6) (not (<= 4 ?v_6)))) (= (not (<= ?v_7 4)) (= o_1 1))) (and (not (<= 16 s_3)) (<= 0 s_3))) (and (<= s_3 v4) (not (<= 1 (- v4 s_3))))) (= (<= 1 s_3) (not (<= v4 1)))) (and (not (<= 32 s_4)) (<= 0 s_4))) (and (<= 0 ?v_8) (not (<= 1 ?v_8)))) (= (<= 1 s_4) (not (<= v5 0)))) (and (<= 0 o_2) (<= o_2 1))) (and (<= 0 ?v_11) (not (<= 1 ?v_11)))) (= (not (<= ?v_12 1)) (= o_2 1))) (and (not (<= 64 s_5)) (<= 0 s_5))) (and (<= 0 ?v_13) (not (<= 1 ?v_13)))) (= (<= 1 s_5) (not (<= v6 0)))) (and (not (<= 128 s_6)) (<= 0 s_6))) (and (<= 0 ?v_14) (not (<= 1 ?v_14)))) (= (<= 1 s_6) (not (<= v7 0)))) (and (<= 0 o_3) (<= o_3 1))) (and (<= 0 ?v_19) (not (<= 1 ?v_19)))) (= (not (<= ?v_20 1)) (= o_3 1))) (and (<= 0 o_4) (<= o_4 1))) (and (<= 0 ?v_24) (not (<= 16 ?v_24)))) (= (not (<= ?v_25 16)) (= o_4 1))) (and (<= 0 o_5) (<= o_5 1))) (and (<= 0 ?v_30) (not (<= 1 ?v_30)))) (= (not (<= ?v_31 1)) (= o_5 1))) (and (<= 0 o_6) (<= o_6 1))) (and (<= 0 ?v_38) (not (<= 16 ?v_38)))) (= (not (<= ?v_39 16)) (= o_6 1))) (and (not (<= 2 s_7)) (<= 0 s_7))) (and (<= 0 ?v_40) (not (<= 8 ?v_40)))) (= (<= 1 s_7) (not (<= v7 8)))) (and (<= 0 o_7) (<= o_7 1))) (and (<= 0 ?v_41) (not (<= 16 ?v_41)))) (= (not (<= ?v_42 16)) (= o_7 1))) (and (not (<= 2 s_8)) (<= 0 s_8))) (and (<= 0 ?v_43) (not (<= 8 ?v_43)))) (= (<= 1 s_8) (not (<= ?v_41 8)))) (and (<= 0 o_8) (<= o_8 1))) (and (<= 0 ?v_44) (not (<= 16 ?v_44)))) (= (not (<= ?v_45 16)) (= o_8 1))) (and (not (<= 2 s_9)) (<= 0 s_9))) (and (<= 0 ?v_46) (not (<= 8 ?v_46)))) (= (<= 1 s_9) (not (<= ?v_44 8)))) (and (<= 0 o_9) (<= o_9 1))) (and (<= 0 ?v_47) (not (<= 16 ?v_47)))) (= (not (<= ?v_48 16)) (= o_9 1))) (and (not (<= 2 s_10)) (<= 0 s_10))) (and (<= 0 ?v_49) (not (<= 8 ?v_49)))) (= (<= 1 s_10) (not (<= ?v_47 8)))) (and (<= 0 o_10) (<= o_10 1))) (and (<= 0 ?v_50) (not (<= 16 ?v_50)))) (= (not (<= ?v_51 16)) (= o_10 1))) (and (not (<= 2 s_11)) (<= 0 s_11))) (and (<= 0 ?v_52) (not (<= 8 ?v_52)))) (= (<= 1 s_11) (not (<= ?v_50 8)))) (and (<= 0 o_11) (<= o_11 1))) (and (<= 0 ?v_54) (not (<= 16 ?v_54)))) (= (not (<= ?v_55 16)) (= o_11 1))) (and (not (<= 2 s_12)) (<= 0 s_12))) (and (<= 0 ?v_56) (not (<= 8 ?v_56)))) (= (<= 1 s_12) (not (<= ?v_54 8)))) (and (<= 0 o_12) (<= o_12 1))) (and (<= 0 ?v_57) (not (<= 16 ?v_57)))) (= (not (<= ?v_58 16)) (= o_12 1))) (and (not (<= 2 s_13)) (<= 0 s_13))) (and (<= 0 ?v_59) (not (<= 8 ?v_59)))) (= (<= 1 s_13) (not (<= ?v_57 8)))) (and (<= 0 o_13) (<= o_13 1))) (and (<= 0 ?v_64) (not (<= 16 ?v_64)))) (= (not (<= ?v_65 16)) (= o_13 1))) (not (= (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (* o_7 64) (* s_7 64)) (* s_8 32)) (* o_8 32)) (* s_9 16)) (* o_9 16)) (* s_10 8)) (* o_10 8)) (* s_11 4)) (* o_11 4)) (* s_12 2)) (* o_12 2)) s_13) o_13) ?v_17) ?v_18) ?v_27) ?v_10) ?v_28) ?v_29) ?v_66) (- s_2)) (- s_1)) (- o_1)) (- s_0)) (- o_0)) (- o_4)) (- o_6)) 0))))))))))))))))))))))))))))))
(check-sat)
(exit)
