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
(declare-fun p2 (U) Bool)
(declare-fun f1 (U U) U)
(declare-fun p4 (U) Bool)
(declare-fun p3 (U) Bool)
(declare-fun c6 () U)
(declare-fun c5 () U)
(declare-fun c7 () U)
(declare-fun c_0 () U)
(declare-fun c_1 () U)
(declare-fun c_2 () U)
(declare-fun c_3 () U)
(declare-fun c_4 () U)
(assert (let ((?v_31 (p2 c_0))) (let ((?v_0 (not ?v_31)) (?v_1 (f1 c_0 c_0)) (?v_33 (p2 c_1))) (let ((?v_6 (not ?v_33)) (?v_2 (f1 c_1 c_0)) (?v_35 (p2 c_2))) (let ((?v_9 (not ?v_35)) (?v_3 (f1 c_2 c_0)) (?v_37 (p2 c_3))) (let ((?v_11 (not ?v_37)) (?v_4 (f1 c_3 c_0)) (?v_39 (p2 c_4))) (let ((?v_13 (not ?v_39)) (?v_5 (f1 c_4 c_0)) (?v_7 (f1 c_0 c_1)) (?v_8 (f1 c_1 c_1)) (?v_10 (f1 c_2 c_1)) (?v_12 (f1 c_3 c_1)) (?v_14 (f1 c_4 c_1)) (?v_15 (f1 c_0 c_2)) (?v_16 (f1 c_1 c_2)) (?v_17 (f1 c_2 c_2)) (?v_18 (f1 c_3 c_2)) (?v_19 (f1 c_4 c_2)) (?v_20 (f1 c_0 c_3)) (?v_21 (f1 c_1 c_3)) (?v_22 (f1 c_2 c_3)) (?v_23 (f1 c_3 c_3)) (?v_24 (f1 c_4 c_3)) (?v_25 (f1 c_0 c_4)) (?v_26 (f1 c_1 c_4)) (?v_27 (f1 c_2 c_4)) (?v_28 (f1 c_3 c_4)) (?v_29 (f1 c_4 c_4)) (?v_30 (p3 c_0))) (let ((?v_51 (not ?v_30)) (?v_32 (p3 c_1))) (let ((?v_53 (not ?v_32)) (?v_34 (p3 c_2))) (let ((?v_55 (not ?v_34)) (?v_36 (p3 c_3))) (let ((?v_57 (not ?v_36)) (?v_38 (p3 c_4))) (let ((?v_59 (not ?v_38)) (?v_40 (p4 c_0)) (?v_42 (p4 c_1)) (?v_43 (p4 c_2)) (?v_44 (p4 c_3)) (?v_45 (p4 c_4))) (let ((?v_41 (not ?v_40)) (?v_50 (p2 ?v_1)) (?v_46 (not ?v_42)) (?v_60 (p2 ?v_2)) (?v_47 (not ?v_43)) (?v_65 (p2 ?v_3)) (?v_48 (not ?v_44)) (?v_70 (p2 ?v_4)) (?v_49 (not ?v_45)) (?v_75 (p2 ?v_5)) (?v_52 (p2 ?v_7)) (?v_61 (p2 ?v_8)) (?v_66 (p2 ?v_10)) (?v_71 (p2 ?v_12)) (?v_76 (p2 ?v_14)) (?v_54 (p2 ?v_15)) (?v_62 (p2 ?v_16)) (?v_67 (p2 ?v_17)) (?v_72 (p2 ?v_18)) (?v_77 (p2 ?v_19)) (?v_56 (p2 ?v_20)) (?v_63 (p2 ?v_21)) (?v_68 (p2 ?v_22)) (?v_73 (p2 ?v_23)) (?v_78 (p2 ?v_24)) (?v_58 (p2 ?v_25)) (?v_64 (p2 ?v_26)) (?v_69 (p2 ?v_27)) (?v_74 (p2 ?v_28)) (?v_79 (p2 ?v_29))) (and (distinct c_0 c_1 c_2 c_3 c_4) (or ?v_0 ?v_0 (p4 ?v_1) (p3 ?v_1)) (or ?v_0 ?v_6 (p4 ?v_2) (p3 ?v_2)) (or ?v_0 ?v_9 (p4 ?v_3) (p3 ?v_3)) (or ?v_0 ?v_11 (p4 ?v_4) (p3 ?v_4)) (or ?v_0 ?v_13 (p4 ?v_5) (p3 ?v_5)) (or ?v_6 ?v_0 (p4 ?v_7) (p3 ?v_7)) (or ?v_6 ?v_6 (p4 ?v_8) (p3 ?v_8)) (or ?v_6 ?v_9 (p4 ?v_10) (p3 ?v_10)) (or ?v_6 ?v_11 (p4 ?v_12) (p3 ?v_12)) (or ?v_6 ?v_13 (p4 ?v_14) (p3 ?v_14)) (or ?v_9 ?v_0 (p4 ?v_15) (p3 ?v_15)) (or ?v_9 ?v_6 (p4 ?v_16) (p3 ?v_16)) (or ?v_9 ?v_9 (p4 ?v_17) (p3 ?v_17)) (or ?v_9 ?v_11 (p4 ?v_18) (p3 ?v_18)) (or ?v_9 ?v_13 (p4 ?v_19) (p3 ?v_19)) (or ?v_11 ?v_0 (p4 ?v_20) (p3 ?v_20)) (or ?v_11 ?v_6 (p4 ?v_21) (p3 ?v_21)) (or ?v_11 ?v_9 (p4 ?v_22) (p3 ?v_22)) (or ?v_11 ?v_11 (p4 ?v_23) (p3 ?v_23)) (or ?v_11 ?v_13 (p4 ?v_24) (p3 ?v_24)) (or ?v_13 ?v_0 (p4 ?v_25) (p3 ?v_25)) (or ?v_13 ?v_6 (p4 ?v_26) (p3 ?v_26)) (or ?v_13 ?v_9 (p4 ?v_27) (p3 ?v_27)) (or ?v_13 ?v_11 (p4 ?v_28) (p3 ?v_28)) (or ?v_13 ?v_13 (p4 ?v_29) (p3 ?v_29)) (or ?v_0 ?v_51) (or ?v_6 ?v_53) (or ?v_9 ?v_55) (or ?v_11 ?v_57) (or ?v_13 ?v_59) (or ?v_40 ?v_30 ?v_31) (or ?v_42 ?v_32 ?v_33) (or ?v_43 ?v_34 ?v_35) (or ?v_44 ?v_36 ?v_37) (or ?v_45 ?v_38 ?v_39) (p3 c6) (p2 c5) (or ?v_41 ?v_41 ?v_50) (or ?v_41 ?v_46 ?v_60) (or ?v_41 ?v_47 ?v_65) (or ?v_41 ?v_48 ?v_70) (or ?v_41 ?v_49 ?v_75) (or ?v_46 ?v_41 ?v_52) (or ?v_46 ?v_46 ?v_61) (or ?v_46 ?v_47 ?v_66) (or ?v_46 ?v_48 ?v_71) (or ?v_46 ?v_49 ?v_76) (or ?v_47 ?v_41 ?v_54) (or ?v_47 ?v_46 ?v_62) (or ?v_47 ?v_47 ?v_67) (or ?v_47 ?v_48 ?v_72) (or ?v_47 ?v_49 ?v_77) (or ?v_48 ?v_41 ?v_56) (or ?v_48 ?v_46 ?v_63) (or ?v_48 ?v_47 ?v_68) (or ?v_48 ?v_48 ?v_73) (or ?v_48 ?v_49 ?v_78) (or ?v_49 ?v_41 ?v_58) (or ?v_49 ?v_46 ?v_64) (or ?v_49 ?v_47 ?v_69) (or ?v_49 ?v_48 ?v_74) (or ?v_49 ?v_49 ?v_79) (= (f1 c_0 ?v_1) (f1 ?v_1 c_0)) (= (f1 c_0 ?v_7) (f1 ?v_1 c_1)) (= (f1 c_0 ?v_15) (f1 ?v_1 c_2)) (= (f1 c_0 ?v_20) (f1 ?v_1 c_3)) (= (f1 c_0 ?v_25) (f1 ?v_1 c_4)) (= (f1 c_0 ?v_2) (f1 ?v_7 c_0)) (= (f1 c_0 ?v_8) (f1 ?v_7 c_1)) (= (f1 c_0 ?v_16) (f1 ?v_7 c_2)) (= (f1 c_0 ?v_21) (f1 ?v_7 c_3)) (= (f1 c_0 ?v_26) (f1 ?v_7 c_4)) (= (f1 c_0 ?v_3) (f1 ?v_15 c_0)) (= (f1 c_0 ?v_10) (f1 ?v_15 c_1)) (= (f1 c_0 ?v_17) (f1 ?v_15 c_2)) (= (f1 c_0 ?v_22) (f1 ?v_15 c_3)) (= (f1 c_0 ?v_27) (f1 ?v_15 c_4)) (= (f1 c_0 ?v_4) (f1 ?v_20 c_0)) (= (f1 c_0 ?v_12) (f1 ?v_20 c_1)) (= (f1 c_0 ?v_18) (f1 ?v_20 c_2)) (= (f1 c_0 ?v_23) (f1 ?v_20 c_3)) (= (f1 c_0 ?v_28) (f1 ?v_20 c_4)) (= (f1 c_0 ?v_5) (f1 ?v_25 c_0)) (= (f1 c_0 ?v_14) (f1 ?v_25 c_1)) (= (f1 c_0 ?v_19) (f1 ?v_25 c_2)) (= (f1 c_0 ?v_24) (f1 ?v_25 c_3)) (= (f1 c_0 ?v_29) (f1 ?v_25 c_4)) (= (f1 c_1 ?v_1) (f1 ?v_2 c_0)) (= (f1 c_1 ?v_7) (f1 ?v_2 c_1)) (= (f1 c_1 ?v_15) (f1 ?v_2 c_2)) (= (f1 c_1 ?v_20) (f1 ?v_2 c_3)) (= (f1 c_1 ?v_25) (f1 ?v_2 c_4)) (= (f1 c_1 ?v_2) (f1 ?v_8 c_0)) (= (f1 c_1 ?v_8) (f1 ?v_8 c_1)) (= (f1 c_1 ?v_16) (f1 ?v_8 c_2)) (= (f1 c_1 ?v_21) (f1 ?v_8 c_3)) (= (f1 c_1 ?v_26) (f1 ?v_8 c_4)) (= (f1 c_1 ?v_3) (f1 ?v_16 c_0)) (= (f1 c_1 ?v_10) (f1 ?v_16 c_1)) (= (f1 c_1 ?v_17) (f1 ?v_16 c_2)) (= (f1 c_1 ?v_22) (f1 ?v_16 c_3)) (= (f1 c_1 ?v_27) (f1 ?v_16 c_4)) (= (f1 c_1 ?v_4) (f1 ?v_21 c_0)) (= (f1 c_1 ?v_12) (f1 ?v_21 c_1)) (= (f1 c_1 ?v_18) (f1 ?v_21 c_2)) (= (f1 c_1 ?v_23) (f1 ?v_21 c_3)) (= (f1 c_1 ?v_28) (f1 ?v_21 c_4)) (= (f1 c_1 ?v_5) (f1 ?v_26 c_0)) (= (f1 c_1 ?v_14) (f1 ?v_26 c_1)) (= (f1 c_1 ?v_19) (f1 ?v_26 c_2)) (= (f1 c_1 ?v_24) (f1 ?v_26 c_3)) (= (f1 c_1 ?v_29) (f1 ?v_26 c_4)) (= (f1 c_2 ?v_1) (f1 ?v_3 c_0)) (= (f1 c_2 ?v_7) (f1 ?v_3 c_1)) (= (f1 c_2 ?v_15) (f1 ?v_3 c_2)) (= (f1 c_2 ?v_20) (f1 ?v_3 c_3)) (= (f1 c_2 ?v_25) (f1 ?v_3 c_4)) (= (f1 c_2 ?v_2) (f1 ?v_10 c_0)) (= (f1 c_2 ?v_8) (f1 ?v_10 c_1)) (= (f1 c_2 ?v_16) (f1 ?v_10 c_2)) (= (f1 c_2 ?v_21) (f1 ?v_10 c_3)) (= (f1 c_2 ?v_26) (f1 ?v_10 c_4)) (= (f1 c_2 ?v_3) (f1 ?v_17 c_0)) (= (f1 c_2 ?v_10) (f1 ?v_17 c_1)) (= (f1 c_2 ?v_17) (f1 ?v_17 c_2)) (= (f1 c_2 ?v_22) (f1 ?v_17 c_3)) (= (f1 c_2 ?v_27) (f1 ?v_17 c_4)) (= (f1 c_2 ?v_4) (f1 ?v_22 c_0)) (= (f1 c_2 ?v_12) (f1 ?v_22 c_1)) (= (f1 c_2 ?v_18) (f1 ?v_22 c_2)) (= (f1 c_2 ?v_23) (f1 ?v_22 c_3)) (= (f1 c_2 ?v_28) (f1 ?v_22 c_4)) (= (f1 c_2 ?v_5) (f1 ?v_27 c_0)) (= (f1 c_2 ?v_14) (f1 ?v_27 c_1)) (= (f1 c_2 ?v_19) (f1 ?v_27 c_2)) (= (f1 c_2 ?v_24) (f1 ?v_27 c_3)) (= (f1 c_2 ?v_29) (f1 ?v_27 c_4)) (= (f1 c_3 ?v_1) (f1 ?v_4 c_0)) (= (f1 c_3 ?v_7) (f1 ?v_4 c_1)) (= (f1 c_3 ?v_15) (f1 ?v_4 c_2)) (= (f1 c_3 ?v_20) (f1 ?v_4 c_3)) (= (f1 c_3 ?v_25) (f1 ?v_4 c_4)) (= (f1 c_3 ?v_2) (f1 ?v_12 c_0)) (= (f1 c_3 ?v_8) (f1 ?v_12 c_1)) (= (f1 c_3 ?v_16) (f1 ?v_12 c_2)) (= (f1 c_3 ?v_21) (f1 ?v_12 c_3)) (= (f1 c_3 ?v_26) (f1 ?v_12 c_4)) (= (f1 c_3 ?v_3) (f1 ?v_18 c_0)) (= (f1 c_3 ?v_10) (f1 ?v_18 c_1)) (= (f1 c_3 ?v_17) (f1 ?v_18 c_2)) (= (f1 c_3 ?v_22) (f1 ?v_18 c_3)) (= (f1 c_3 ?v_27) (f1 ?v_18 c_4)) (= (f1 c_3 ?v_4) (f1 ?v_23 c_0)) (= (f1 c_3 ?v_12) (f1 ?v_23 c_1)) (= (f1 c_3 ?v_18) (f1 ?v_23 c_2)) (= (f1 c_3 ?v_23) (f1 ?v_23 c_3)) (= (f1 c_3 ?v_28) (f1 ?v_23 c_4)) (= (f1 c_3 ?v_5) (f1 ?v_28 c_0)) (= (f1 c_3 ?v_14) (f1 ?v_28 c_1)) (= (f1 c_3 ?v_19) (f1 ?v_28 c_2)) (= (f1 c_3 ?v_24) (f1 ?v_28 c_3)) (= (f1 c_3 ?v_29) (f1 ?v_28 c_4)) (= (f1 c_4 ?v_1) (f1 ?v_5 c_0)) (= (f1 c_4 ?v_7) (f1 ?v_5 c_1)) (= (f1 c_4 ?v_15) (f1 ?v_5 c_2)) (= (f1 c_4 ?v_20) (f1 ?v_5 c_3)) (= (f1 c_4 ?v_25) (f1 ?v_5 c_4)) (= (f1 c_4 ?v_2) (f1 ?v_14 c_0)) (= (f1 c_4 ?v_8) (f1 ?v_14 c_1)) (= (f1 c_4 ?v_16) (f1 ?v_14 c_2)) (= (f1 c_4 ?v_21) (f1 ?v_14 c_3)) (= (f1 c_4 ?v_26) (f1 ?v_14 c_4)) (= (f1 c_4 ?v_3) (f1 ?v_19 c_0)) (= (f1 c_4 ?v_10) (f1 ?v_19 c_1)) (= (f1 c_4 ?v_17) (f1 ?v_19 c_2)) (= (f1 c_4 ?v_22) (f1 ?v_19 c_3)) (= (f1 c_4 ?v_27) (f1 ?v_19 c_4)) (= (f1 c_4 ?v_4) (f1 ?v_24 c_0)) (= (f1 c_4 ?v_12) (f1 ?v_24 c_1)) (= (f1 c_4 ?v_18) (f1 ?v_24 c_2)) (= (f1 c_4 ?v_23) (f1 ?v_24 c_3)) (= (f1 c_4 ?v_28) (f1 ?v_24 c_4)) (= (f1 c_4 ?v_5) (f1 ?v_29 c_0)) (= (f1 c_4 ?v_14) (f1 ?v_29 c_1)) (= (f1 c_4 ?v_19) (f1 ?v_29 c_2)) (= (f1 c_4 ?v_24) (f1 ?v_29 c_3)) (= (f1 c_4 ?v_29) (f1 ?v_29 c_4)) (or ?v_50 ?v_51 ?v_51) (or ?v_52 ?v_51 ?v_53) (or ?v_54 ?v_51 ?v_55) (or ?v_56 ?v_51 ?v_57) (or ?v_58 ?v_51 ?v_59) (or ?v_60 ?v_53 ?v_51) (or ?v_61 ?v_53 ?v_53) (or ?v_62 ?v_53 ?v_55) (or ?v_63 ?v_53 ?v_57) (or ?v_64 ?v_53 ?v_59) (or ?v_65 ?v_55 ?v_51) (or ?v_66 ?v_55 ?v_53) (or ?v_67 ?v_55 ?v_55) (or ?v_68 ?v_55 ?v_57) (or ?v_69 ?v_55 ?v_59) (or ?v_70 ?v_57 ?v_51) (or ?v_71 ?v_57 ?v_53) (or ?v_72 ?v_57 ?v_55) (or ?v_73 ?v_57 ?v_57) (or ?v_74 ?v_57 ?v_59) (or ?v_75 ?v_59 ?v_51) (or ?v_76 ?v_59 ?v_53) (or ?v_77 ?v_59 ?v_55) (or ?v_78 ?v_59 ?v_57) (or ?v_79 ?v_59 ?v_59) (p4 c7) (or ?v_41 ?v_0) (or ?v_46 ?v_6) (or ?v_47 ?v_9) (or ?v_48 ?v_11) (or ?v_49 ?v_13) (or ?v_51 ?v_41) (or ?v_53 ?v_46) (or ?v_55 ?v_47) (or ?v_57 ?v_48) (or ?v_59 ?v_49) (or (= ?v_1 c_0) (= ?v_1 c_1) (= ?v_1 c_2) (= ?v_1 c_3) (= ?v_1 c_4)) (or (= ?v_7 c_0) (= ?v_7 c_1) (= ?v_7 c_2) (= ?v_7 c_3) (= ?v_7 c_4)) (or (= ?v_15 c_0) (= ?v_15 c_1) (= ?v_15 c_2) (= ?v_15 c_3) (= ?v_15 c_4)) (or (= ?v_20 c_0) (= ?v_20 c_1) (= ?v_20 c_2) (= ?v_20 c_3) (= ?v_20 c_4)) (or (= ?v_25 c_0) (= ?v_25 c_1) (= ?v_25 c_2) (= ?v_25 c_3) (= ?v_25 c_4)) (or (= ?v_2 c_0) (= ?v_2 c_1) (= ?v_2 c_2) (= ?v_2 c_3) (= ?v_2 c_4)) (or (= ?v_8 c_0) (= ?v_8 c_1) (= ?v_8 c_2) (= ?v_8 c_3) (= ?v_8 c_4)) (or (= ?v_16 c_0) (= ?v_16 c_1) (= ?v_16 c_2) (= ?v_16 c_3) (= ?v_16 c_4)) (or (= ?v_21 c_0) (= ?v_21 c_1) (= ?v_21 c_2) (= ?v_21 c_3) (= ?v_21 c_4)) (or (= ?v_26 c_0) (= ?v_26 c_1) (= ?v_26 c_2) (= ?v_26 c_3) (= ?v_26 c_4)) (or (= ?v_3 c_0) (= ?v_3 c_1) (= ?v_3 c_2) (= ?v_3 c_3) (= ?v_3 c_4)) (or (= ?v_10 c_0) (= ?v_10 c_1) (= ?v_10 c_2) (= ?v_10 c_3) (= ?v_10 c_4)) (or (= ?v_17 c_0) (= ?v_17 c_1) (= ?v_17 c_2) (= ?v_17 c_3) (= ?v_17 c_4)) (or (= ?v_22 c_0) (= ?v_22 c_1) (= ?v_22 c_2) (= ?v_22 c_3) (= ?v_22 c_4)) (or (= ?v_27 c_0) (= ?v_27 c_1) (= ?v_27 c_2) (= ?v_27 c_3) (= ?v_27 c_4)) (or (= ?v_4 c_0) (= ?v_4 c_1) (= ?v_4 c_2) (= ?v_4 c_3) (= ?v_4 c_4)) (or (= ?v_12 c_0) (= ?v_12 c_1) (= ?v_12 c_2) (= ?v_12 c_3) (= ?v_12 c_4)) (or (= ?v_18 c_0) (= ?v_18 c_1) (= ?v_18 c_2) (= ?v_18 c_3) (= ?v_18 c_4)) (or (= ?v_23 c_0) (= ?v_23 c_1) (= ?v_23 c_2) (= ?v_23 c_3) (= ?v_23 c_4)) (or (= ?v_28 c_0) (= ?v_28 c_1) (= ?v_28 c_2) (= ?v_28 c_3) (= ?v_28 c_4)) (or (= ?v_5 c_0) (= ?v_5 c_1) (= ?v_5 c_2) (= ?v_5 c_3) (= ?v_5 c_4)) (or (= ?v_14 c_0) (= ?v_14 c_1) (= ?v_14 c_2) (= ?v_14 c_3) (= ?v_14 c_4)) (or (= ?v_19 c_0) (= ?v_19 c_1) (= ?v_19 c_2) (= ?v_19 c_3) (= ?v_19 c_4)) (or (= ?v_24 c_0) (= ?v_24 c_1) (= ?v_24 c_2) (= ?v_24 c_3) (= ?v_24 c_4)) (or (= ?v_29 c_0) (= ?v_29 c_1) (= ?v_29 c_2) (= ?v_29 c_3) (= ?v_29 c_4)) (or (= c6 c_0) (= c6 c_1) (= c6 c_2) (= c6 c_3) (= c6 c_4)) (or (= c5 c_0) (= c5 c_1) (= c5 c_2) (= c5 c_3) (= c5 c_4)) (or (= c7 c_0) (= c7 c_1) (= c7 c_2) (= c7 c_3) (= c7 c_4))))))))))))))))
(check-sat)
(exit)