(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
CADE ATP System competition. See http://www.cs.miami.edu/~tptp/CASC
 for more information. 

This benchmark was obtained by trying to find a finite model of a first-order 
formula (Albert Oliveras).
|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f3 (U) U)
(declare-fun f1 (U U) U)
(declare-fun c2 () U)
(declare-fun c5 () U)
(declare-fun c6 () U)
(declare-fun f4 (U U) U)
(declare-fun c7 () U)
(declare-fun c8 () U)
(declare-fun c9 () U)
(declare-fun c10 () U)
(declare-fun c_0 () U)
(declare-fun c_1 () U)
(declare-fun c_2 () U)
(declare-fun c_3 () U)
(declare-fun c_4 () U)
(assert (let ((?v_26 (f3 c_0)) (?v_27 (f3 c_1)) (?v_28 (f3 c_2)) (?v_29 (f3 c_3)) (?v_30 (f3 c_4)) (?v_0 (f1 c_0 c_0)) (?v_1 (f1 c_0 c_1)) (?v_2 (f1 c_0 c_2)) (?v_3 (f1 c_0 c_3)) (?v_4 (f1 c_0 c_4)) (?v_5 (f1 c_1 c_0)) (?v_6 (f1 c_1 c_1)) (?v_7 (f1 c_1 c_2)) (?v_8 (f1 c_1 c_3)) (?v_9 (f1 c_1 c_4)) (?v_10 (f1 c_2 c_0)) (?v_11 (f1 c_2 c_1)) (?v_12 (f1 c_2 c_2)) (?v_13 (f1 c_2 c_3)) (?v_14 (f1 c_2 c_4)) (?v_15 (f1 c_3 c_0)) (?v_16 (f1 c_3 c_1)) (?v_17 (f1 c_3 c_2)) (?v_18 (f1 c_3 c_3)) (?v_19 (f1 c_3 c_4)) (?v_20 (f1 c_4 c_0)) (?v_21 (f1 c_4 c_1)) (?v_22 (f1 c_4 c_2)) (?v_23 (f1 c_4 c_3)) (?v_24 (f1 c_4 c_4)) (?v_31 (= (f4 (f4 c5 c6) c7) (f4 c5 (f4 c6 c7)))) (?v_25 (f4 c8 c9))) (let ((?v_32 (= (f1 ?v_25 c10) (f1 c10 ?v_25))) (?v_33 (f4 c_0 c_0)) (?v_34 (f4 c_0 c_1)) (?v_35 (f4 c_0 c_2)) (?v_36 (f4 c_0 c_3)) (?v_37 (f4 c_0 c_4)) (?v_38 (f4 c_1 c_0)) (?v_39 (f4 c_1 c_1)) (?v_40 (f4 c_1 c_2)) (?v_41 (f4 c_1 c_3)) (?v_42 (f4 c_1 c_4)) (?v_43 (f4 c_2 c_0)) (?v_44 (f4 c_2 c_1)) (?v_45 (f4 c_2 c_2)) (?v_46 (f4 c_2 c_3)) (?v_47 (f4 c_2 c_4)) (?v_48 (f4 c_3 c_0)) (?v_49 (f4 c_3 c_1)) (?v_50 (f4 c_3 c_2)) (?v_51 (f4 c_3 c_3)) (?v_52 (f4 c_3 c_4)) (?v_53 (f4 c_4 c_0)) (?v_54 (f4 c_4 c_1)) (?v_55 (f4 c_4 c_2)) (?v_56 (f4 c_4 c_3)) (?v_57 (f4 c_4 c_4))) (and (distinct c_0 c_1 c_2 c_3 c_4) (= (f1 ?v_26 c_0) c2) (= (f1 ?v_27 c_1) c2) (= (f1 ?v_28 c_2) c2) (= (f1 ?v_29 c_3) c2) (= (f1 ?v_30 c_4) c2) (= (f1 c2 c_0) c_0) (= (f1 c2 c_1) c_1) (= (f1 c2 c_2) c_2) (= (f1 c2 c_3) c_3) (= (f1 c2 c_4) c_4) (= (f1 c_0 c2) c_0) (= (f1 c_1 c2) c_1) (= (f1 c_2 c2) c_2) (= (f1 c_3 c2) c_3) (= (f1 c_4 c2) c_4) (= (f1 ?v_0 c_0) (f1 c_0 ?v_0)) (= (f1 ?v_0 c_1) (f1 c_0 ?v_1)) (= (f1 ?v_0 c_2) (f1 c_0 ?v_2)) (= (f1 ?v_0 c_3) (f1 c_0 ?v_3)) (= (f1 ?v_0 c_4) (f1 c_0 ?v_4)) (= (f1 ?v_1 c_0) (f1 c_0 ?v_5)) (= (f1 ?v_1 c_1) (f1 c_0 ?v_6)) (= (f1 ?v_1 c_2) (f1 c_0 ?v_7)) (= (f1 ?v_1 c_3) (f1 c_0 ?v_8)) (= (f1 ?v_1 c_4) (f1 c_0 ?v_9)) (= (f1 ?v_2 c_0) (f1 c_0 ?v_10)) (= (f1 ?v_2 c_1) (f1 c_0 ?v_11)) (= (f1 ?v_2 c_2) (f1 c_0 ?v_12)) (= (f1 ?v_2 c_3) (f1 c_0 ?v_13)) (= (f1 ?v_2 c_4) (f1 c_0 ?v_14)) (= (f1 ?v_3 c_0) (f1 c_0 ?v_15)) (= (f1 ?v_3 c_1) (f1 c_0 ?v_16)) (= (f1 ?v_3 c_2) (f1 c_0 ?v_17)) (= (f1 ?v_3 c_3) (f1 c_0 ?v_18)) (= (f1 ?v_3 c_4) (f1 c_0 ?v_19)) (= (f1 ?v_4 c_0) (f1 c_0 ?v_20)) (= (f1 ?v_4 c_1) (f1 c_0 ?v_21)) (= (f1 ?v_4 c_2) (f1 c_0 ?v_22)) (= (f1 ?v_4 c_3) (f1 c_0 ?v_23)) (= (f1 ?v_4 c_4) (f1 c_0 ?v_24)) (= (f1 ?v_5 c_0) (f1 c_1 ?v_0)) (= (f1 ?v_5 c_1) (f1 c_1 ?v_1)) (= (f1 ?v_5 c_2) (f1 c_1 ?v_2)) (= (f1 ?v_5 c_3) (f1 c_1 ?v_3)) (= (f1 ?v_5 c_4) (f1 c_1 ?v_4)) (= (f1 ?v_6 c_0) (f1 c_1 ?v_5)) (= (f1 ?v_6 c_1) (f1 c_1 ?v_6)) (= (f1 ?v_6 c_2) (f1 c_1 ?v_7)) (= (f1 ?v_6 c_3) (f1 c_1 ?v_8)) (= (f1 ?v_6 c_4) (f1 c_1 ?v_9)) (= (f1 ?v_7 c_0) (f1 c_1 ?v_10)) (= (f1 ?v_7 c_1) (f1 c_1 ?v_11)) (= (f1 ?v_7 c_2) (f1 c_1 ?v_12)) (= (f1 ?v_7 c_3) (f1 c_1 ?v_13)) (= (f1 ?v_7 c_4) (f1 c_1 ?v_14)) (= (f1 ?v_8 c_0) (f1 c_1 ?v_15)) (= (f1 ?v_8 c_1) (f1 c_1 ?v_16)) (= (f1 ?v_8 c_2) (f1 c_1 ?v_17)) (= (f1 ?v_8 c_3) (f1 c_1 ?v_18)) (= (f1 ?v_8 c_4) (f1 c_1 ?v_19)) (= (f1 ?v_9 c_0) (f1 c_1 ?v_20)) (= (f1 ?v_9 c_1) (f1 c_1 ?v_21)) (= (f1 ?v_9 c_2) (f1 c_1 ?v_22)) (= (f1 ?v_9 c_3) (f1 c_1 ?v_23)) (= (f1 ?v_9 c_4) (f1 c_1 ?v_24)) (= (f1 ?v_10 c_0) (f1 c_2 ?v_0)) (= (f1 ?v_10 c_1) (f1 c_2 ?v_1)) (= (f1 ?v_10 c_2) (f1 c_2 ?v_2)) (= (f1 ?v_10 c_3) (f1 c_2 ?v_3)) (= (f1 ?v_10 c_4) (f1 c_2 ?v_4)) (= (f1 ?v_11 c_0) (f1 c_2 ?v_5)) (= (f1 ?v_11 c_1) (f1 c_2 ?v_6)) (= (f1 ?v_11 c_2) (f1 c_2 ?v_7)) (= (f1 ?v_11 c_3) (f1 c_2 ?v_8)) (= (f1 ?v_11 c_4) (f1 c_2 ?v_9)) (= (f1 ?v_12 c_0) (f1 c_2 ?v_10)) (= (f1 ?v_12 c_1) (f1 c_2 ?v_11)) (= (f1 ?v_12 c_2) (f1 c_2 ?v_12)) (= (f1 ?v_12 c_3) (f1 c_2 ?v_13)) (= (f1 ?v_12 c_4) (f1 c_2 ?v_14)) (= (f1 ?v_13 c_0) (f1 c_2 ?v_15)) (= (f1 ?v_13 c_1) (f1 c_2 ?v_16)) (= (f1 ?v_13 c_2) (f1 c_2 ?v_17)) (= (f1 ?v_13 c_3) (f1 c_2 ?v_18)) (= (f1 ?v_13 c_4) (f1 c_2 ?v_19)) (= (f1 ?v_14 c_0) (f1 c_2 ?v_20)) (= (f1 ?v_14 c_1) (f1 c_2 ?v_21)) (= (f1 ?v_14 c_2) (f1 c_2 ?v_22)) (= (f1 ?v_14 c_3) (f1 c_2 ?v_23)) (= (f1 ?v_14 c_4) (f1 c_2 ?v_24)) (= (f1 ?v_15 c_0) (f1 c_3 ?v_0)) (= (f1 ?v_15 c_1) (f1 c_3 ?v_1)) (= (f1 ?v_15 c_2) (f1 c_3 ?v_2)) (= (f1 ?v_15 c_3) (f1 c_3 ?v_3)) (= (f1 ?v_15 c_4) (f1 c_3 ?v_4)) (= (f1 ?v_16 c_0) (f1 c_3 ?v_5)) (= (f1 ?v_16 c_1) (f1 c_3 ?v_6)) (= (f1 ?v_16 c_2) (f1 c_3 ?v_7)) (= (f1 ?v_16 c_3) (f1 c_3 ?v_8)) (= (f1 ?v_16 c_4) (f1 c_3 ?v_9)) (= (f1 ?v_17 c_0) (f1 c_3 ?v_10)) (= (f1 ?v_17 c_1) (f1 c_3 ?v_11)) (= (f1 ?v_17 c_2) (f1 c_3 ?v_12)) (= (f1 ?v_17 c_3) (f1 c_3 ?v_13)) (= (f1 ?v_17 c_4) (f1 c_3 ?v_14)) (= (f1 ?v_18 c_0) (f1 c_3 ?v_15)) (= (f1 ?v_18 c_1) (f1 c_3 ?v_16)) (= (f1 ?v_18 c_2) (f1 c_3 ?v_17)) (= (f1 ?v_18 c_3) (f1 c_3 ?v_18)) (= (f1 ?v_18 c_4) (f1 c_3 ?v_19)) (= (f1 ?v_19 c_0) (f1 c_3 ?v_20)) (= (f1 ?v_19 c_1) (f1 c_3 ?v_21)) (= (f1 ?v_19 c_2) (f1 c_3 ?v_22)) (= (f1 ?v_19 c_3) (f1 c_3 ?v_23)) (= (f1 ?v_19 c_4) (f1 c_3 ?v_24)) (= (f1 ?v_20 c_0) (f1 c_4 ?v_0)) (= (f1 ?v_20 c_1) (f1 c_4 ?v_1)) (= (f1 ?v_20 c_2) (f1 c_4 ?v_2)) (= (f1 ?v_20 c_3) (f1 c_4 ?v_3)) (= (f1 ?v_20 c_4) (f1 c_4 ?v_4)) (= (f1 ?v_21 c_0) (f1 c_4 ?v_5)) (= (f1 ?v_21 c_1) (f1 c_4 ?v_6)) (= (f1 ?v_21 c_2) (f1 c_4 ?v_7)) (= (f1 ?v_21 c_3) (f1 c_4 ?v_8)) (= (f1 ?v_21 c_4) (f1 c_4 ?v_9)) (= (f1 ?v_22 c_0) (f1 c_4 ?v_10)) (= (f1 ?v_22 c_1) (f1 c_4 ?v_11)) (= (f1 ?v_22 c_2) (f1 c_4 ?v_12)) (= (f1 ?v_22 c_3) (f1 c_4 ?v_13)) (= (f1 ?v_22 c_4) (f1 c_4 ?v_14)) (= (f1 ?v_23 c_0) (f1 c_4 ?v_15)) (= (f1 ?v_23 c_1) (f1 c_4 ?v_16)) (= (f1 ?v_23 c_2) (f1 c_4 ?v_17)) (= (f1 ?v_23 c_3) (f1 c_4 ?v_18)) (= (f1 ?v_23 c_4) (f1 c_4 ?v_19)) (= (f1 ?v_24 c_0) (f1 c_4 ?v_20)) (= (f1 ?v_24 c_1) (f1 c_4 ?v_21)) (= (f1 ?v_24 c_2) (f1 c_4 ?v_22)) (= (f1 ?v_24 c_3) (f1 c_4 ?v_23)) (= (f1 ?v_24 c_4) (f1 c_4 ?v_24)) (or ?v_31 ?v_32) (= ?v_33 (f1 c_0 (f1 c_0 (f1 ?v_26 ?v_26)))) (= ?v_34 (f1 c_0 (f1 c_1 (f1 ?v_26 ?v_27)))) (= ?v_35 (f1 c_0 (f1 c_2 (f1 ?v_26 ?v_28)))) (= ?v_36 (f1 c_0 (f1 c_3 (f1 ?v_26 ?v_29)))) (= ?v_37 (f1 c_0 (f1 c_4 (f1 ?v_26 ?v_30)))) (= ?v_38 (f1 c_1 (f1 c_0 (f1 ?v_27 ?v_26)))) (= ?v_39 (f1 c_1 (f1 c_1 (f1 ?v_27 ?v_27)))) (= ?v_40 (f1 c_1 (f1 c_2 (f1 ?v_27 ?v_28)))) (= ?v_41 (f1 c_1 (f1 c_3 (f1 ?v_27 ?v_29)))) (= ?v_42 (f1 c_1 (f1 c_4 (f1 ?v_27 ?v_30)))) (= ?v_43 (f1 c_2 (f1 c_0 (f1 ?v_28 ?v_26)))) (= ?v_44 (f1 c_2 (f1 c_1 (f1 ?v_28 ?v_27)))) (= ?v_45 (f1 c_2 (f1 c_2 (f1 ?v_28 ?v_28)))) (= ?v_46 (f1 c_2 (f1 c_3 (f1 ?v_28 ?v_29)))) (= ?v_47 (f1 c_2 (f1 c_4 (f1 ?v_28 ?v_30)))) (= ?v_48 (f1 c_3 (f1 c_0 (f1 ?v_29 ?v_26)))) (= ?v_49 (f1 c_3 (f1 c_1 (f1 ?v_29 ?v_27)))) (= ?v_50 (f1 c_3 (f1 c_2 (f1 ?v_29 ?v_28)))) (= ?v_51 (f1 c_3 (f1 c_3 (f1 ?v_29 ?v_29)))) (= ?v_52 (f1 c_3 (f1 c_4 (f1 ?v_29 ?v_30)))) (= ?v_53 (f1 c_4 (f1 c_0 (f1 ?v_30 ?v_26)))) (= ?v_54 (f1 c_4 (f1 c_1 (f1 ?v_30 ?v_27)))) (= ?v_55 (f1 c_4 (f1 c_2 (f1 ?v_30 ?v_28)))) (= ?v_56 (f1 c_4 (f1 c_3 (f1 ?v_30 ?v_29)))) (= ?v_57 (f1 c_4 (f1 c_4 (f1 ?v_30 ?v_30)))) (= (f1 c_0 ?v_26) c2) (= (f1 c_1 ?v_27) c2) (= (f1 c_2 ?v_28) c2) (= (f1 c_3 ?v_29) c2) (= (f1 c_4 ?v_30) c2) (or (not ?v_31) (not ?v_32)) (or (= ?v_0 c_0) (= ?v_0 c_1) (= ?v_0 c_2) (= ?v_0 c_3) (= ?v_0 c_4)) (or (= ?v_1 c_0) (= ?v_1 c_1) (= ?v_1 c_2) (= ?v_1 c_3) (= ?v_1 c_4)) (or (= ?v_2 c_0) (= ?v_2 c_1) (= ?v_2 c_2) (= ?v_2 c_3) (= ?v_2 c_4)) (or (= ?v_3 c_0) (= ?v_3 c_1) (= ?v_3 c_2) (= ?v_3 c_3) (= ?v_3 c_4)) (or (= ?v_4 c_0) (= ?v_4 c_1) (= ?v_4 c_2) (= ?v_4 c_3) (= ?v_4 c_4)) (or (= ?v_5 c_0) (= ?v_5 c_1) (= ?v_5 c_2) (= ?v_5 c_3) (= ?v_5 c_4)) (or (= ?v_6 c_0) (= ?v_6 c_1) (= ?v_6 c_2) (= ?v_6 c_3) (= ?v_6 c_4)) (or (= ?v_7 c_0) (= ?v_7 c_1) (= ?v_7 c_2) (= ?v_7 c_3) (= ?v_7 c_4)) (or (= ?v_8 c_0) (= ?v_8 c_1) (= ?v_8 c_2) (= ?v_8 c_3) (= ?v_8 c_4)) (or (= ?v_9 c_0) (= ?v_9 c_1) (= ?v_9 c_2) (= ?v_9 c_3) (= ?v_9 c_4)) (or (= ?v_10 c_0) (= ?v_10 c_1) (= ?v_10 c_2) (= ?v_10 c_3) (= ?v_10 c_4)) (or (= ?v_11 c_0) (= ?v_11 c_1) (= ?v_11 c_2) (= ?v_11 c_3) (= ?v_11 c_4)) (or (= ?v_12 c_0) (= ?v_12 c_1) (= ?v_12 c_2) (= ?v_12 c_3) (= ?v_12 c_4)) (or (= ?v_13 c_0) (= ?v_13 c_1) (= ?v_13 c_2) (= ?v_13 c_3) (= ?v_13 c_4)) (or (= ?v_14 c_0) (= ?v_14 c_1) (= ?v_14 c_2) (= ?v_14 c_3) (= ?v_14 c_4)) (or (= ?v_15 c_0) (= ?v_15 c_1) (= ?v_15 c_2) (= ?v_15 c_3) (= ?v_15 c_4)) (or (= ?v_16 c_0) (= ?v_16 c_1) (= ?v_16 c_2) (= ?v_16 c_3) (= ?v_16 c_4)) (or (= ?v_17 c_0) (= ?v_17 c_1) (= ?v_17 c_2) (= ?v_17 c_3) (= ?v_17 c_4)) (or (= ?v_18 c_0) (= ?v_18 c_1) (= ?v_18 c_2) (= ?v_18 c_3) (= ?v_18 c_4)) (or (= ?v_19 c_0) (= ?v_19 c_1) (= ?v_19 c_2) (= ?v_19 c_3) (= ?v_19 c_4)) (or (= ?v_20 c_0) (= ?v_20 c_1) (= ?v_20 c_2) (= ?v_20 c_3) (= ?v_20 c_4)) (or (= ?v_21 c_0) (= ?v_21 c_1) (= ?v_21 c_2) (= ?v_21 c_3) (= ?v_21 c_4)) (or (= ?v_22 c_0) (= ?v_22 c_1) (= ?v_22 c_2) (= ?v_22 c_3) (= ?v_22 c_4)) (or (= ?v_23 c_0) (= ?v_23 c_1) (= ?v_23 c_2) (= ?v_23 c_3) (= ?v_23 c_4)) (or (= ?v_24 c_0) (= ?v_24 c_1) (= ?v_24 c_2) (= ?v_24 c_3) (= ?v_24 c_4)) (or (= ?v_33 c_0) (= ?v_33 c_1) (= ?v_33 c_2) (= ?v_33 c_3) (= ?v_33 c_4)) (or (= ?v_34 c_0) (= ?v_34 c_1) (= ?v_34 c_2) (= ?v_34 c_3) (= ?v_34 c_4)) (or (= ?v_35 c_0) (= ?v_35 c_1) (= ?v_35 c_2) (= ?v_35 c_3) (= ?v_35 c_4)) (or (= ?v_36 c_0) (= ?v_36 c_1) (= ?v_36 c_2) (= ?v_36 c_3) (= ?v_36 c_4)) (or (= ?v_37 c_0) (= ?v_37 c_1) (= ?v_37 c_2) (= ?v_37 c_3) (= ?v_37 c_4)) (or (= ?v_38 c_0) (= ?v_38 c_1) (= ?v_38 c_2) (= ?v_38 c_3) (= ?v_38 c_4)) (or (= ?v_39 c_0) (= ?v_39 c_1) (= ?v_39 c_2) (= ?v_39 c_3) (= ?v_39 c_4)) (or (= ?v_40 c_0) (= ?v_40 c_1) (= ?v_40 c_2) (= ?v_40 c_3) (= ?v_40 c_4)) (or (= ?v_41 c_0) (= ?v_41 c_1) (= ?v_41 c_2) (= ?v_41 c_3) (= ?v_41 c_4)) (or (= ?v_42 c_0) (= ?v_42 c_1) (= ?v_42 c_2) (= ?v_42 c_3) (= ?v_42 c_4)) (or (= ?v_43 c_0) (= ?v_43 c_1) (= ?v_43 c_2) (= ?v_43 c_3) (= ?v_43 c_4)) (or (= ?v_44 c_0) (= ?v_44 c_1) (= ?v_44 c_2) (= ?v_44 c_3) (= ?v_44 c_4)) (or (= ?v_45 c_0) (= ?v_45 c_1) (= ?v_45 c_2) (= ?v_45 c_3) (= ?v_45 c_4)) (or (= ?v_46 c_0) (= ?v_46 c_1) (= ?v_46 c_2) (= ?v_46 c_3) (= ?v_46 c_4)) (or (= ?v_47 c_0) (= ?v_47 c_1) (= ?v_47 c_2) (= ?v_47 c_3) (= ?v_47 c_4)) (or (= ?v_48 c_0) (= ?v_48 c_1) (= ?v_48 c_2) (= ?v_48 c_3) (= ?v_48 c_4)) (or (= ?v_49 c_0) (= ?v_49 c_1) (= ?v_49 c_2) (= ?v_49 c_3) (= ?v_49 c_4)) (or (= ?v_50 c_0) (= ?v_50 c_1) (= ?v_50 c_2) (= ?v_50 c_3) (= ?v_50 c_4)) (or (= ?v_51 c_0) (= ?v_51 c_1) (= ?v_51 c_2) (= ?v_51 c_3) (= ?v_51 c_4)) (or (= ?v_52 c_0) (= ?v_52 c_1) (= ?v_52 c_2) (= ?v_52 c_3) (= ?v_52 c_4)) (or (= ?v_53 c_0) (= ?v_53 c_1) (= ?v_53 c_2) (= ?v_53 c_3) (= ?v_53 c_4)) (or (= ?v_54 c_0) (= ?v_54 c_1) (= ?v_54 c_2) (= ?v_54 c_3) (= ?v_54 c_4)) (or (= ?v_55 c_0) (= ?v_55 c_1) (= ?v_55 c_2) (= ?v_55 c_3) (= ?v_55 c_4)) (or (= ?v_56 c_0) (= ?v_56 c_1) (= ?v_56 c_2) (= ?v_56 c_3) (= ?v_56 c_4)) (or (= ?v_57 c_0) (= ?v_57 c_1) (= ?v_57 c_2) (= ?v_57 c_3) (= ?v_57 c_4)) (or (= ?v_26 c_0) (= ?v_26 c_1) (= ?v_26 c_2) (= ?v_26 c_3) (= ?v_26 c_4)) (or (= ?v_27 c_0) (= ?v_27 c_1) (= ?v_27 c_2) (= ?v_27 c_3) (= ?v_27 c_4)) (or (= ?v_28 c_0) (= ?v_28 c_1) (= ?v_28 c_2) (= ?v_28 c_3) (= ?v_28 c_4)) (or (= ?v_29 c_0) (= ?v_29 c_1) (= ?v_29 c_2) (= ?v_29 c_3) (= ?v_29 c_4)) (or (= ?v_30 c_0) (= ?v_30 c_1) (= ?v_30 c_2) (= ?v_30 c_3) (= ?v_30 c_4)) (or (= c2 c_0) (= c2 c_1) (= c2 c_2) (= c2 c_3) (= c2 c_4)) (or (= c5 c_0) (= c5 c_1) (= c5 c_2) (= c5 c_3) (= c5 c_4)) (or (= c6 c_0) (= c6 c_1) (= c6 c_2) (= c6 c_3) (= c6 c_4)) (or (= c7 c_0) (= c7 c_1) (= c7 c_2) (= c7 c_3) (= c7 c_4)) (or (= c8 c_0) (= c8 c_1) (= c8 c_2) (= c8 c_3) (= c8 c_4)) (or (= c9 c_0) (= c9 c_1) (= c9 c_2) (= c9 c_3) (= c9 c_4)) (or (= c10 c_0) (= c10 c_1) (= c10 c_2) (= c10 c_3) (= c10 c_4))))))
(check-sat)
(exit)