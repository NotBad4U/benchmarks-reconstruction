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
(declare-fun o_6 () Int)
(declare-fun s_7 () Int)
(declare-fun o_7 () Int)
(declare-fun s_8 () Int)
(declare-fun o_8 () Int)
(declare-fun s_9 () Int)
(declare-fun o_9 () Int)
(declare-fun A_itev1 () Int)
(declare-fun A_itev2 () Int)
(declare-fun A_itev3 () Int)
(declare-fun A_itev4 () Int)
(declare-fun A_itev5 () Int)
(declare-fun A_itev6 () Int)
(assert (let ((?v_67 (+ (* v4 16) (* v5 32))) (?v_66 (* A_itev4 8)) (?v_21 (* v1 2)) (?v_42 (* v2 4)) (?v_41 (* v3 8)) (?v_61 (* A_itev4 4)) (?v_56 (* A_itev4 2)) (?v_53 (* v3 2)) (?v_4 (* v5 2)) (?v_1 (<= 4096 v5))) (let ((?v_26 (not ?v_1)) (?v_18 (<= 4096 v1))) (let ((?v_25 (not ?v_18)) (?v_24 (= A_itev6 A_itev5)) (?v_23 (= (+ (- A_itev6) ?v_21) 0)) (?v_22 (<= 2048 v1)) (?v_17 (+ (- A_itev5) ?v_21))) (let ((?v_20 (= ?v_17 4096)) (?v_19 (= ?v_17 8192)) (?v_16 (= A_itev4 A_itev3)) (?v_7 (= A_itev2 A_itev1)) (?v_6 (= (+ (- A_itev2) ?v_4) 0)) (?v_5 (<= 2048 v5)) (?v_0 (+ (- A_itev1) ?v_4))) (let ((?v_3 (= ?v_0 4096)) (?v_2 (= ?v_0 8192)) (?v_13 (+ (+ (* o_5 (- 8192)) (* v4 2)) (* A_itev2 2)))) (let ((?v_8 (+ (- A_itev3) ?v_13))) (let ((?v_11 (= ?v_8 4096)) (?v_12 (+ (+ (* o_5 (- 4096)) v4) A_itev2))) (let ((?v_9 (<= 4096 ?v_12)) (?v_10 (= ?v_8 8192))) (let ((?v_49 (not ?v_9)) (?v_14 (<= 2048 ?v_12)) (?v_15 (= (+ ?v_13 (- A_itev4)) 0)) (?v_38 (* o_0 (- 4096)))) (let ((?v_27 (+ (+ ?v_38 v0) A_itev6)) (?v_30 (* s_1 (- 1024)))) (let ((?v_28 (+ ?v_30 v2)) (?v_29 (+ (* s_2 (- 512)) v3)) (?v_32 (+ (+ (+ ?v_53 v2) (* s_2 (- 1024))) ?v_30))) (let ((?v_31 (+ (* o_1 (- 1024)) ?v_32)) (?v_35 (* s_3 (- 256)))) (let ((?v_33 (+ ?v_35 v4)) (?v_34 (+ (* s_4 (- 128)) v5)) (?v_37 (+ (+ (+ v4 ?v_4) (* s_4 (- 256))) ?v_35))) (let ((?v_36 (+ (* o_2 (- 256)) ?v_37)) (?v_43 (* s_2 (- 4096))) (?v_44 (* s_1 (- 4096))) (?v_45 (* o_1 (- 4096)))) (let ((?v_40 (+ (+ (+ (+ (+ (+ ?v_42 ?v_41) v0) ?v_43) ?v_44) ?v_45) ?v_38)) (?v_46 (* o_3 (- 4096)))) (let ((?v_39 (+ (+ ?v_40 ?v_46) A_itev6)) (?v_68 (* s_4 (- 4096))) (?v_69 (* s_3 (- 4096))) (?v_70 (* o_2 (- 4096)))) (let ((?v_48 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ ?v_67 ?v_41) ?v_42) v0) ?v_43) ?v_44) ?v_45) ?v_38) ?v_46) ?v_68) ?v_69) ?v_70)) (?v_71 (* o_4 (- 4096)))) (let ((?v_47 (+ (+ ?v_48 ?v_71) A_itev6)) (?v_51 (+ (* o_6 (- 4096)) v3))) (let ((?v_50 (+ ?v_51 A_itev4)) (?v_52 (+ (+ (* s_7 (- 2048)) ?v_51) A_itev4)) (?v_55 (+ (+ (+ (* o_6 (- 8192)) ?v_53) (* s_7 (- 4096))) v2))) (let ((?v_57 (+ ?v_55 (* o_7 (- 4096))))) (let ((?v_54 (+ ?v_57 ?v_56)) (?v_58 (+ (+ (* s_8 (- 2048)) ?v_57) ?v_56)) (?v_60 (+ (+ (+ (+ (+ (+ (* o_6 (- 16384)) (* v3 4)) (* s_7 (- 8192))) (* v2 2)) (* o_7 (- 8192))) (* s_8 (- 4096))) v1))) (let ((?v_62 (+ ?v_60 (* o_8 (- 4096))))) (let ((?v_59 (+ ?v_62 ?v_61)) (?v_63 (+ (+ (* s_9 (- 2048)) ?v_62) ?v_61)) (?v_65 (+ (+ (+ (+ (+ (+ (+ (+ (+ (* o_6 (- 32768)) ?v_41) (* s_7 (- 16384))) ?v_42) (* o_7 (- 16384))) (* s_8 (- 8192))) ?v_21) (* o_8 (- 8192))) (* s_9 (- 4096))) v0))) (let ((?v_64 (+ (+ (* o_9 (- 4096)) ?v_65) ?v_66))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (or ?v_2 ?v_26) (or ?v_3 ?v_1)) (or ?v_2 ?v_3)) (or ?v_5 ?v_6)) (or (not ?v_5) ?v_7)) (or ?v_6 ?v_7)) (or ?v_11 ?v_9)) (or ?v_10 ?v_49)) (or ?v_10 ?v_11)) (or ?v_14 ?v_15)) (or (not ?v_14) ?v_16)) (or ?v_15 ?v_16)) (or ?v_20 ?v_18)) (or ?v_19 ?v_25)) (or ?v_19 ?v_20)) (or ?v_22 ?v_23)) (or (not ?v_22) ?v_24)) (or ?v_23 ?v_24)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= 0 v0) (not (<= 4096 v0))) (and (<= 0 v1) ?v_25)) (and (<= 0 v2) (not (<= 4096 v2)))) (and (<= 0 v3) (not (<= 4096 v3)))) (and (<= 0 v4) (not (<= 4096 v4)))) (and (<= 0 v5) ?v_26)) (and (<= 0 o_0) (<= o_0 1))) (and (<= 0 ?v_27) (not (<= 4096 ?v_27)))) (= (not (<= (+ A_itev6 v0) 4096)) (= o_0 1))) (and (not (<= 4 s_1)) (<= 0 s_1))) (and (<= 0 ?v_28) (not (<= 1024 ?v_28)))) (= (<= 1 s_1) (not (<= v2 1024)))) (and (not (<= 8 s_2)) (<= 0 s_2))) (and (<= 0 ?v_29) (not (<= 512 ?v_29)))) (= (<= 1 s_2) (not (<= v3 512)))) (and (<= 0 o_1) (<= o_1 1))) (and (<= 0 ?v_31) (not (<= 1024 ?v_31)))) (= (not (<= ?v_32 1024)) (= o_1 1))) (and (not (<= 16 s_3)) (<= 0 s_3))) (and (<= 0 ?v_33) (not (<= 256 ?v_33)))) (= (<= 1 s_3) (not (<= v4 256)))) (and (not (<= 32 s_4)) (<= 0 s_4))) (and (<= 0 ?v_34) (not (<= 128 ?v_34)))) (= (<= 1 s_4) (not (<= v5 128)))) (and (<= 0 o_2) (<= o_2 1))) (and (<= 0 ?v_36) (not (<= 256 ?v_36)))) (= (not (<= ?v_37 256)) (= o_2 1))) (and (<= 0 o_3) (<= o_3 1))) (and (<= 0 ?v_39) (not (<= 4096 ?v_39)))) (= (not (<= (+ ?v_40 A_itev6) 4096)) (= o_3 1))) (and (<= 0 o_4) (<= o_4 1))) (and (<= 0 ?v_47) (not (<= 4096 ?v_47)))) (= (not (<= (+ ?v_48 A_itev6) 4096)) (= o_4 1))) (and (<= 0 o_5) (<= o_5 1))) (and (<= 0 ?v_12) ?v_49)) (= (not (<= (+ A_itev2 v4) 4096)) (= o_5 1))) (and (<= 0 o_6) (<= o_6 1))) (and (<= 0 ?v_50) (not (<= 4096 ?v_50)))) (= (not (<= (+ A_itev4 v3) 4096)) (= o_6 1))) (and (not (<= 2 s_7)) (<= 0 s_7))) (and (<= 0 ?v_52) (not (<= 2048 ?v_52)))) (= (<= 1 s_7) (not (<= ?v_50 2048)))) (and (<= 0 o_7) (<= o_7 1))) (and (<= 0 ?v_54) (not (<= 4096 ?v_54)))) (= (not (<= (+ ?v_55 ?v_56) 4096)) (= o_7 1))) (and (not (<= 2 s_8)) (<= 0 s_8))) (and (<= 0 ?v_58) (not (<= 2048 ?v_58)))) (= (<= 1 s_8) (not (<= ?v_54 2048)))) (and (<= 0 o_8) (<= o_8 1))) (and (<= 0 ?v_59) (not (<= 4096 ?v_59)))) (= (not (<= (+ ?v_60 ?v_61) 4096)) (= o_8 1))) (and (not (<= 2 s_9)) (<= 0 s_9))) (and (<= 0 ?v_63) (not (<= 2048 ?v_63)))) (= (<= 1 s_9) (not (<= ?v_59 2048)))) (and (<= 0 o_9) (<= o_9 1))) (and (<= 0 ?v_64) (not (<= 4096 ?v_64)))) (= (not (<= (+ ?v_65 ?v_66) 4096)) (= o_9 1))) (not (= (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ ?v_67 (* o_6 32768)) (* s_7 16384)) (* o_7 16384)) (* s_8 8192)) (* v1 (- 2))) (* o_8 8192)) (* s_9 4096)) (* o_9 4096)) ?v_43) ?v_44) ?v_45) ?v_38) ?v_46) ?v_68) ?v_69) ?v_70) ?v_71) (* A_itev4 (- 8))) A_itev6) 0)))))))))))))))))))))))))))))
(check-sat)
(exit)
