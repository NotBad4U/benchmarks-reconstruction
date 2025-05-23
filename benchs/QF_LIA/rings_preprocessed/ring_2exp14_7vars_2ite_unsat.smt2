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
(declare-fun A_itev1 () Int)
(declare-fun A_itev2 () Int)
(declare-fun A_itev3 () Int)
(declare-fun A_itev4 () Int)
(assert (let ((?v_38 (* v6 64)) (?v_75 (* A_itev2 32)) (?v_12 (* v1 2)) (?v_72 (* v2 4)) (?v_71 (* v3 8)) (?v_70 (* v4 16)) (?v_69 (* v5 32)) (?v_66 (* A_itev2 16)) (?v_61 (* A_itev2 8)) (?v_33 (* v3 2)) (?v_58 (* v4 4)) (?v_57 (* v5 8)) (?v_54 (* A_itev2 4)) (?v_49 (* A_itev2 2)) (?v_46 (* v5 2)) (?v_1 (<= 16384 v6))) (let ((?v_17 (not ?v_1)) (?v_9 (<= 16384 v1))) (let ((?v_16 (not ?v_9)) (?v_15 (= A_itev4 A_itev3)) (?v_14 (= (+ (- A_itev4) ?v_12) 0)) (?v_13 (<= 8192 v1)) (?v_8 (+ (- A_itev3) ?v_12))) (let ((?v_11 (= ?v_8 16384)) (?v_10 (= ?v_8 32768)) (?v_7 (= A_itev2 A_itev1)) (?v_4 (* v6 2))) (let ((?v_6 (= (+ (- A_itev2) ?v_4) 0)) (?v_5 (<= 8192 v6)) (?v_0 (+ (- A_itev1) ?v_4))) (let ((?v_3 (= ?v_0 16384)) (?v_2 (= ?v_0 32768)) (?v_30 (* o_0 (- 16384)))) (let ((?v_18 (+ (+ ?v_30 v0) A_itev4)) (?v_21 (* s_1 (- 4096)))) (let ((?v_19 (+ ?v_21 v2)) (?v_20 (+ (* s_2 (- 2048)) v3)) (?v_34 (* s_2 (- 4096)))) (let ((?v_23 (+ (+ (+ ?v_33 v2) ?v_34) ?v_21)) (?v_35 (* o_1 (- 4096)))) (let ((?v_22 (+ ?v_23 ?v_35)) (?v_26 (* s_3 (- 1024)))) (let ((?v_24 (+ ?v_26 v4)) (?v_25 (+ (* s_4 (- 512)) v5)) (?v_28 (+ (+ (+ ?v_46 v4) (* s_4 (- 1024))) ?v_26))) (let ((?v_27 (+ (* o_2 (- 1024)) ?v_28)) (?v_29 (+ (* s_5 (- 256)) v6)) (?v_39 (* s_5 (- 16384)))) (let ((?v_32 (+ (+ (+ ?v_38 v0) ?v_39) ?v_30)) (?v_40 (* o_3 (- 16384)))) (let ((?v_31 (+ (+ ?v_32 ?v_40) A_itev4)) (?v_37 (+ (+ (+ (+ (+ (+ (+ (+ (+ ?v_58 ?v_57) ?v_33) v2) (* s_4 (- 4096))) (* s_3 (- 4096))) (* o_2 (- 4096))) ?v_34) ?v_21) ?v_35))) (let ((?v_36 (+ (* o_4 (- 4096)) ?v_37)) (?v_76 (* s_4 (- 16384))) (?v_77 (* s_3 (- 16384))) (?v_78 (* o_2 (- 16384))) (?v_79 (* s_2 (- 16384))) (?v_80 (* s_1 (- 16384))) (?v_81 (* o_1 (- 16384))) (?v_82 (* o_4 (- 16384)))) (let ((?v_42 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ ?v_38 ?v_69) ?v_70) ?v_71) ?v_72) v0) ?v_76) ?v_77) ?v_78) ?v_79) ?v_80) ?v_81) ?v_82) ?v_39) ?v_30) ?v_40)) (?v_83 (* o_5 (- 16384)))) (let ((?v_41 (+ (+ ?v_42 ?v_83) A_itev4)) (?v_44 (+ (* o_6 (- 16384)) v5))) (let ((?v_43 (+ ?v_44 A_itev2)) (?v_45 (+ (+ (* s_7 (- 8192)) ?v_44) A_itev2)) (?v_48 (+ (+ (+ (* o_6 (- 32768)) ?v_46) (* s_7 (- 16384))) v4))) (let ((?v_50 (+ ?v_48 (* o_7 (- 16384))))) (let ((?v_47 (+ ?v_50 ?v_49)) (?v_51 (+ (+ (* s_8 (- 8192)) ?v_50) ?v_49)) (?v_53 (+ (+ (+ (+ (+ (+ (* o_6 (- 65536)) (* v5 4)) (* s_7 (- 32768))) (* v4 2)) (* o_7 (- 32768))) (* s_8 (- 16384))) v3))) (let ((?v_55 (+ ?v_53 (* o_8 (- 16384))))) (let ((?v_52 (+ ?v_55 ?v_54)) (?v_56 (+ (+ (* s_9 (- 8192)) ?v_55) ?v_54)) (?v_60 (+ (+ (+ (+ (+ (+ (+ (+ (+ (* o_6 (- 131072)) ?v_57) (* s_7 (- 65536))) ?v_58) (* o_7 (- 65536))) (* s_8 (- 32768))) ?v_33) (* o_8 (- 32768))) (* s_9 (- 16384))) v2))) (let ((?v_62 (+ ?v_60 (* o_9 (- 16384))))) (let ((?v_59 (+ ?v_62 ?v_61)) (?v_63 (+ (+ (* s_10 (- 8192)) ?v_62) ?v_61)) (?v_65 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (* o_6 (- 262144)) (* v5 16)) (* s_7 (- 131072))) (* v4 8)) (* o_7 (- 131072))) (* s_8 (- 65536))) (* v3 4)) (* o_8 (- 65536))) (* s_9 (- 32768))) (* v2 2)) (* o_9 (- 32768))) (* s_10 (- 16384))) v1))) (let ((?v_67 (+ ?v_65 (* o_10 (- 16384))))) (let ((?v_64 (+ ?v_67 ?v_66)) (?v_68 (+ (+ (* s_11 (- 8192)) ?v_67) ?v_66)) (?v_74 (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (* o_6 (- 524288)) ?v_69) (* s_7 (- 262144))) ?v_70) (* o_7 (- 262144))) (* s_8 (- 131072))) ?v_71) (* o_8 (- 131072))) (* s_9 (- 65536))) ?v_72) (* o_9 (- 65536))) (* s_10 (- 32768))) ?v_12) (* o_10 (- 32768))) (* s_11 (- 16384))) v0))) (let ((?v_73 (+ (+ (* o_11 (- 16384)) ?v_74) ?v_75))) (and (and (and (and (and (and (and (and (and (and (and (and (or ?v_2 ?v_17) (or ?v_3 ?v_1)) (or ?v_2 ?v_3)) (or ?v_5 ?v_6)) (or (not ?v_5) ?v_7)) (or ?v_6 ?v_7)) (or ?v_11 ?v_9)) (or ?v_10 ?v_16)) (or ?v_10 ?v_11)) (or ?v_13 ?v_14)) (or (not ?v_13) ?v_15)) (or ?v_14 ?v_15)) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= 0 v0) (not (<= 16384 v0))) (and (<= 0 v1) ?v_16)) (and (<= 0 v2) (not (<= 16384 v2)))) (and (<= 0 v3) (not (<= 16384 v3)))) (and (<= 0 v4) (not (<= 16384 v4)))) (and (<= 0 v5) (not (<= 16384 v5)))) (and (<= 0 v6) ?v_17)) (and (<= 0 o_0) (<= o_0 1))) (and (<= 0 ?v_18) (not (<= 16384 ?v_18)))) (= (not (<= (+ A_itev4 v0) 16384)) (= o_0 1))) (and (not (<= 4 s_1)) (<= 0 s_1))) (and (<= 0 ?v_19) (not (<= 4096 ?v_19)))) (= (<= 1 s_1) (not (<= v2 4096)))) (and (not (<= 8 s_2)) (<= 0 s_2))) (and (<= 0 ?v_20) (not (<= 2048 ?v_20)))) (= (<= 1 s_2) (not (<= v3 2048)))) (and (<= 0 o_1) (<= o_1 1))) (and (<= 0 ?v_22) (not (<= 4096 ?v_22)))) (= (not (<= ?v_23 4096)) (= o_1 1))) (and (not (<= 16 s_3)) (<= 0 s_3))) (and (<= 0 ?v_24) (not (<= 1024 ?v_24)))) (= (<= 1 s_3) (not (<= v4 1024)))) (and (not (<= 32 s_4)) (<= 0 s_4))) (and (<= 0 ?v_25) (not (<= 512 ?v_25)))) (= (<= 1 s_4) (not (<= v5 512)))) (and (<= 0 o_2) (<= o_2 1))) (and (<= 0 ?v_27) (not (<= 1024 ?v_27)))) (= (not (<= ?v_28 1024)) (= o_2 1))) (and (not (<= 64 s_5)) (<= 0 s_5))) (and (<= 0 ?v_29) (not (<= 256 ?v_29)))) (= (<= 1 s_5) (not (<= v6 256)))) (and (<= 0 o_3) (<= o_3 1))) (and (<= 0 ?v_31) (not (<= 16384 ?v_31)))) (= (not (<= (+ ?v_32 A_itev4) 16384)) (= o_3 1))) (and (<= 0 o_4) (<= o_4 1))) (and (<= 0 ?v_36) (not (<= 4096 ?v_36)))) (= (not (<= ?v_37 4096)) (= o_4 1))) (and (<= 0 o_5) (<= o_5 1))) (and (<= 0 ?v_41) (not (<= 16384 ?v_41)))) (= (not (<= (+ ?v_42 A_itev4) 16384)) (= o_5 1))) (and (<= 0 o_6) (<= o_6 1))) (and (<= 0 ?v_43) (not (<= 16384 ?v_43)))) (= (not (<= (+ A_itev2 v5) 16384)) (= o_6 1))) (and (not (<= 2 s_7)) (<= 0 s_7))) (and (<= 0 ?v_45) (not (<= 8192 ?v_45)))) (= (<= 1 s_7) (not (<= ?v_43 8192)))) (and (<= 0 o_7) (<= o_7 1))) (and (<= 0 ?v_47) (not (<= 16384 ?v_47)))) (= (not (<= (+ ?v_48 ?v_49) 16384)) (= o_7 1))) (and (not (<= 2 s_8)) (<= 0 s_8))) (and (<= 0 ?v_51) (not (<= 8192 ?v_51)))) (= (<= 1 s_8) (not (<= ?v_47 8192)))) (and (<= 0 o_8) (<= o_8 1))) (and (<= 0 ?v_52) (not (<= 16384 ?v_52)))) (= (not (<= (+ ?v_53 ?v_54) 16384)) (= o_8 1))) (and (not (<= 2 s_9)) (<= 0 s_9))) (and (<= 0 ?v_56) (not (<= 8192 ?v_56)))) (= (<= 1 s_9) (not (<= ?v_52 8192)))) (and (<= 0 o_9) (<= o_9 1))) (and (<= 0 ?v_59) (not (<= 16384 ?v_59)))) (= (not (<= (+ ?v_60 ?v_61) 16384)) (= o_9 1))) (and (not (<= 2 s_10)) (<= 0 s_10))) (and (<= 0 ?v_63) (not (<= 8192 ?v_63)))) (= (<= 1 s_10) (not (<= ?v_59 8192)))) (and (<= 0 o_10) (<= o_10 1))) (and (<= 0 ?v_64) (not (<= 16384 ?v_64)))) (= (not (<= (+ ?v_65 ?v_66) 16384)) (= o_10 1))) (and (not (<= 2 s_11)) (<= 0 s_11))) (and (<= 0 ?v_68) (not (<= 8192 ?v_68)))) (= (<= 1 s_11) (not (<= ?v_64 8192)))) (and (<= 0 o_11) (<= o_11 1))) (and (<= 0 ?v_73) (not (<= 16384 ?v_73)))) (= (not (<= (+ ?v_74 ?v_75) 16384)) (= o_11 1))) (not (= (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (+ (* o_6 524288) ?v_38) (* s_7 262144)) (* o_7 262144)) (* s_8 131072)) (* o_8 131072)) (* s_9 65536)) (* o_9 65536)) (* s_10 32768)) (* v1 (- 2))) (* o_10 32768)) (* s_11 16384)) (* o_11 16384)) ?v_76) ?v_77) ?v_78) ?v_79) ?v_80) ?v_81) ?v_82) ?v_39) ?v_30) ?v_40) ?v_83) (* A_itev2 (- 32))) A_itev4) 0))))))))))))))))))))))))))))))))
(check-sat)
(exit)
