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
(declare-fun f2 (U U) U)
(declare-fun f1 (U U) U)
(declare-fun f3 (U) U)
(declare-fun c5 () U)
(declare-fun c6 () U)
(declare-fun c7 () U)
(declare-fun c4 () U)
(declare-fun c_0 () U)
(declare-fun c_1 () U)
(declare-fun c_2 () U)
(declare-fun c_3 () U)
(declare-fun c_4 () U)
(assert (let ((?v_25 (f2 c_0 c_0)) (?v_26 (f2 c_0 c_1)) (?v_27 (f2 c_0 c_2)) (?v_28 (f2 c_0 c_3)) (?v_29 (f2 c_0 c_4)) (?v_30 (f2 c_1 c_0)) (?v_31 (f2 c_1 c_1)) (?v_32 (f2 c_1 c_2)) (?v_33 (f2 c_1 c_3)) (?v_34 (f2 c_1 c_4)) (?v_35 (f2 c_2 c_0)) (?v_36 (f2 c_2 c_1)) (?v_37 (f2 c_2 c_2)) (?v_38 (f2 c_2 c_3)) (?v_39 (f2 c_2 c_4)) (?v_40 (f2 c_3 c_0)) (?v_41 (f2 c_3 c_1)) (?v_42 (f2 c_3 c_2)) (?v_43 (f2 c_3 c_3)) (?v_44 (f2 c_3 c_4)) (?v_45 (f2 c_4 c_0)) (?v_46 (f2 c_4 c_1)) (?v_47 (f2 c_4 c_2)) (?v_48 (f2 c_4 c_3)) (?v_49 (f2 c_4 c_4)) (?v_0 (f1 c_0 c_0)) (?v_2 (f1 c_0 c_1)) (?v_1 (f1 c_1 c_0)) (?v_5 (f1 c_0 c_2)) (?v_4 (f1 c_2 c_0)) (?v_10 (f1 c_0 c_3)) (?v_9 (f1 c_3 c_0)) (?v_17 (f1 c_0 c_4)) (?v_16 (f1 c_4 c_0)) (?v_3 (f1 c_1 c_1)) (?v_7 (f1 c_1 c_2)) (?v_6 (f1 c_2 c_1)) (?v_12 (f1 c_1 c_3)) (?v_11 (f1 c_3 c_1)) (?v_19 (f1 c_1 c_4)) (?v_18 (f1 c_4 c_1)) (?v_8 (f1 c_2 c_2)) (?v_14 (f1 c_2 c_3)) (?v_13 (f1 c_3 c_2)) (?v_21 (f1 c_2 c_4)) (?v_20 (f1 c_4 c_2)) (?v_15 (f1 c_3 c_3)) (?v_23 (f1 c_3 c_4)) (?v_22 (f1 c_4 c_3)) (?v_24 (f1 c_4 c_4)) (?v_51 (f3 c_0)) (?v_52 (f3 c_1)) (?v_53 (f3 c_2)) (?v_54 (f3 c_3)) (?v_55 (f3 c_4)) (?v_50 (f2 c6 c7))) (let ((?v_61 (= ?v_0 c_0)) (?v_62 (= ?v_3 c_1)) (?v_63 (= ?v_8 c_2)) (?v_64 (= ?v_15 c_3)) (?v_65 (= ?v_24 c_4)) (?v_56 (= ?v_25 c_0)) (?v_57 (= ?v_31 c_1)) (?v_58 (= ?v_37 c_2)) (?v_59 (= ?v_43 c_3)) (?v_60 (= ?v_49 c_4))) (and (distinct c_0 c_1 c_2 c_3 c_4) (= (f1 c_0 ?v_25) c_0) (= (f1 c_0 ?v_26) c_0) (= (f1 c_0 ?v_27) c_0) (= (f1 c_0 ?v_28) c_0) (= (f1 c_0 ?v_29) c_0) (= (f1 c_1 ?v_30) c_1) (= (f1 c_1 ?v_31) c_1) (= (f1 c_1 ?v_32) c_1) (= (f1 c_1 ?v_33) c_1) (= (f1 c_1 ?v_34) c_1) (= (f1 c_2 ?v_35) c_2) (= (f1 c_2 ?v_36) c_2) (= (f1 c_2 ?v_37) c_2) (= (f1 c_2 ?v_38) c_2) (= (f1 c_2 ?v_39) c_2) (= (f1 c_3 ?v_40) c_3) (= (f1 c_3 ?v_41) c_3) (= (f1 c_3 ?v_42) c_3) (= (f1 c_3 ?v_43) c_3) (= (f1 c_3 ?v_44) c_3) (= (f1 c_4 ?v_45) c_4) (= (f1 c_4 ?v_46) c_4) (= (f1 c_4 ?v_47) c_4) (= (f1 c_4 ?v_48) c_4) (= (f1 c_4 ?v_49) c_4) (= ?v_0 ?v_0) (= ?v_2 ?v_1) (= ?v_5 ?v_4) (= ?v_10 ?v_9) (= ?v_17 ?v_16) (= ?v_1 ?v_2) (= ?v_3 ?v_3) (= ?v_7 ?v_6) (= ?v_12 ?v_11) (= ?v_19 ?v_18) (= ?v_4 ?v_5) (= ?v_6 ?v_7) (= ?v_8 ?v_8) (= ?v_14 ?v_13) (= ?v_21 ?v_20) (= ?v_9 ?v_10) (= ?v_11 ?v_12) (= ?v_13 ?v_14) (= ?v_15 ?v_15) (= ?v_23 ?v_22) (= ?v_16 ?v_17) (= ?v_18 ?v_19) (= ?v_20 ?v_21) (= ?v_22 ?v_23) (= ?v_24 ?v_24) (= (f2 ?v_25 c_0) (f2 c_0 ?v_25)) (= (f2 ?v_25 c_1) (f2 c_0 ?v_26)) (= (f2 ?v_25 c_2) (f2 c_0 ?v_27)) (= (f2 ?v_25 c_3) (f2 c_0 ?v_28)) (= (f2 ?v_25 c_4) (f2 c_0 ?v_29)) (= (f2 ?v_26 c_0) (f2 c_0 ?v_30)) (= (f2 ?v_26 c_1) (f2 c_0 ?v_31)) (= (f2 ?v_26 c_2) (f2 c_0 ?v_32)) (= (f2 ?v_26 c_3) (f2 c_0 ?v_33)) (= (f2 ?v_26 c_4) (f2 c_0 ?v_34)) (= (f2 ?v_27 c_0) (f2 c_0 ?v_35)) (= (f2 ?v_27 c_1) (f2 c_0 ?v_36)) (= (f2 ?v_27 c_2) (f2 c_0 ?v_37)) (= (f2 ?v_27 c_3) (f2 c_0 ?v_38)) (= (f2 ?v_27 c_4) (f2 c_0 ?v_39)) (= (f2 ?v_28 c_0) (f2 c_0 ?v_40)) (= (f2 ?v_28 c_1) (f2 c_0 ?v_41)) (= (f2 ?v_28 c_2) (f2 c_0 ?v_42)) (= (f2 ?v_28 c_3) (f2 c_0 ?v_43)) (= (f2 ?v_28 c_4) (f2 c_0 ?v_44)) (= (f2 ?v_29 c_0) (f2 c_0 ?v_45)) (= (f2 ?v_29 c_1) (f2 c_0 ?v_46)) (= (f2 ?v_29 c_2) (f2 c_0 ?v_47)) (= (f2 ?v_29 c_3) (f2 c_0 ?v_48)) (= (f2 ?v_29 c_4) (f2 c_0 ?v_49)) (= (f2 ?v_30 c_0) (f2 c_1 ?v_25)) (= (f2 ?v_30 c_1) (f2 c_1 ?v_26)) (= (f2 ?v_30 c_2) (f2 c_1 ?v_27)) (= (f2 ?v_30 c_3) (f2 c_1 ?v_28)) (= (f2 ?v_30 c_4) (f2 c_1 ?v_29)) (= (f2 ?v_31 c_0) (f2 c_1 ?v_30)) (= (f2 ?v_31 c_1) (f2 c_1 ?v_31)) (= (f2 ?v_31 c_2) (f2 c_1 ?v_32)) (= (f2 ?v_31 c_3) (f2 c_1 ?v_33)) (= (f2 ?v_31 c_4) (f2 c_1 ?v_34)) (= (f2 ?v_32 c_0) (f2 c_1 ?v_35)) (= (f2 ?v_32 c_1) (f2 c_1 ?v_36)) (= (f2 ?v_32 c_2) (f2 c_1 ?v_37)) (= (f2 ?v_32 c_3) (f2 c_1 ?v_38)) (= (f2 ?v_32 c_4) (f2 c_1 ?v_39)) (= (f2 ?v_33 c_0) (f2 c_1 ?v_40)) (= (f2 ?v_33 c_1) (f2 c_1 ?v_41)) (= (f2 ?v_33 c_2) (f2 c_1 ?v_42)) (= (f2 ?v_33 c_3) (f2 c_1 ?v_43)) (= (f2 ?v_33 c_4) (f2 c_1 ?v_44)) (= (f2 ?v_34 c_0) (f2 c_1 ?v_45)) (= (f2 ?v_34 c_1) (f2 c_1 ?v_46)) (= (f2 ?v_34 c_2) (f2 c_1 ?v_47)) (= (f2 ?v_34 c_3) (f2 c_1 ?v_48)) (= (f2 ?v_34 c_4) (f2 c_1 ?v_49)) (= (f2 ?v_35 c_0) (f2 c_2 ?v_25)) (= (f2 ?v_35 c_1) (f2 c_2 ?v_26)) (= (f2 ?v_35 c_2) (f2 c_2 ?v_27)) (= (f2 ?v_35 c_3) (f2 c_2 ?v_28)) (= (f2 ?v_35 c_4) (f2 c_2 ?v_29)) (= (f2 ?v_36 c_0) (f2 c_2 ?v_30)) (= (f2 ?v_36 c_1) (f2 c_2 ?v_31)) (= (f2 ?v_36 c_2) (f2 c_2 ?v_32)) (= (f2 ?v_36 c_3) (f2 c_2 ?v_33)) (= (f2 ?v_36 c_4) (f2 c_2 ?v_34)) (= (f2 ?v_37 c_0) (f2 c_2 ?v_35)) (= (f2 ?v_37 c_1) (f2 c_2 ?v_36)) (= (f2 ?v_37 c_2) (f2 c_2 ?v_37)) (= (f2 ?v_37 c_3) (f2 c_2 ?v_38)) (= (f2 ?v_37 c_4) (f2 c_2 ?v_39)) (= (f2 ?v_38 c_0) (f2 c_2 ?v_40)) (= (f2 ?v_38 c_1) (f2 c_2 ?v_41)) (= (f2 ?v_38 c_2) (f2 c_2 ?v_42)) (= (f2 ?v_38 c_3) (f2 c_2 ?v_43)) (= (f2 ?v_38 c_4) (f2 c_2 ?v_44)) (= (f2 ?v_39 c_0) (f2 c_2 ?v_45)) (= (f2 ?v_39 c_1) (f2 c_2 ?v_46)) (= (f2 ?v_39 c_2) (f2 c_2 ?v_47)) (= (f2 ?v_39 c_3) (f2 c_2 ?v_48)) (= (f2 ?v_39 c_4) (f2 c_2 ?v_49)) (= (f2 ?v_40 c_0) (f2 c_3 ?v_25)) (= (f2 ?v_40 c_1) (f2 c_3 ?v_26)) (= (f2 ?v_40 c_2) (f2 c_3 ?v_27)) (= (f2 ?v_40 c_3) (f2 c_3 ?v_28)) (= (f2 ?v_40 c_4) (f2 c_3 ?v_29)) (= (f2 ?v_41 c_0) (f2 c_3 ?v_30)) (= (f2 ?v_41 c_1) (f2 c_3 ?v_31)) (= (f2 ?v_41 c_2) (f2 c_3 ?v_32)) (= (f2 ?v_41 c_3) (f2 c_3 ?v_33)) (= (f2 ?v_41 c_4) (f2 c_3 ?v_34)) (= (f2 ?v_42 c_0) (f2 c_3 ?v_35)) (= (f2 ?v_42 c_1) (f2 c_3 ?v_36)) (= (f2 ?v_42 c_2) (f2 c_3 ?v_37)) (= (f2 ?v_42 c_3) (f2 c_3 ?v_38)) (= (f2 ?v_42 c_4) (f2 c_3 ?v_39)) (= (f2 ?v_43 c_0) (f2 c_3 ?v_40)) (= (f2 ?v_43 c_1) (f2 c_3 ?v_41)) (= (f2 ?v_43 c_2) (f2 c_3 ?v_42)) (= (f2 ?v_43 c_3) (f2 c_3 ?v_43)) (= (f2 ?v_43 c_4) (f2 c_3 ?v_44)) (= (f2 ?v_44 c_0) (f2 c_3 ?v_45)) (= (f2 ?v_44 c_1) (f2 c_3 ?v_46)) (= (f2 ?v_44 c_2) (f2 c_3 ?v_47)) (= (f2 ?v_44 c_3) (f2 c_3 ?v_48)) (= (f2 ?v_44 c_4) (f2 c_3 ?v_49)) (= (f2 ?v_45 c_0) (f2 c_4 ?v_25)) (= (f2 ?v_45 c_1) (f2 c_4 ?v_26)) (= (f2 ?v_45 c_2) (f2 c_4 ?v_27)) (= (f2 ?v_45 c_3) (f2 c_4 ?v_28)) (= (f2 ?v_45 c_4) (f2 c_4 ?v_29)) (= (f2 ?v_46 c_0) (f2 c_4 ?v_30)) (= (f2 ?v_46 c_1) (f2 c_4 ?v_31)) (= (f2 ?v_46 c_2) (f2 c_4 ?v_32)) (= (f2 ?v_46 c_3) (f2 c_4 ?v_33)) (= (f2 ?v_46 c_4) (f2 c_4 ?v_34)) (= (f2 ?v_47 c_0) (f2 c_4 ?v_35)) (= (f2 ?v_47 c_1) (f2 c_4 ?v_36)) (= (f2 ?v_47 c_2) (f2 c_4 ?v_37)) (= (f2 ?v_47 c_3) (f2 c_4 ?v_38)) (= (f2 ?v_47 c_4) (f2 c_4 ?v_39)) (= (f2 ?v_48 c_0) (f2 c_4 ?v_40)) (= (f2 ?v_48 c_1) (f2 c_4 ?v_41)) (= (f2 ?v_48 c_2) (f2 c_4 ?v_42)) (= (f2 ?v_48 c_3) (f2 c_4 ?v_43)) (= (f2 ?v_48 c_4) (f2 c_4 ?v_44)) (= (f2 ?v_49 c_0) (f2 c_4 ?v_45)) (= (f2 ?v_49 c_1) (f2 c_4 ?v_46)) (= (f2 ?v_49 c_2) (f2 c_4 ?v_47)) (= (f2 ?v_49 c_3) (f2 c_4 ?v_48)) (= (f2 ?v_49 c_4) (f2 c_4 ?v_49)) (= (f1 ?v_51 c_0) c5) (= (f1 ?v_52 c_1) c5) (= (f1 ?v_53 c_2) c5) (= (f1 ?v_54 c_3) c5) (= (f1 ?v_55 c_4) c5) (= (f1 ?v_0 c_0) (f1 c_0 ?v_0)) (= (f1 ?v_0 c_1) (f1 c_0 ?v_2)) (= (f1 ?v_0 c_2) (f1 c_0 ?v_5)) (= (f1 ?v_0 c_3) (f1 c_0 ?v_10)) (= (f1 ?v_0 c_4) (f1 c_0 ?v_17)) (= (f1 ?v_2 c_0) (f1 c_0 ?v_1)) (= (f1 ?v_2 c_1) (f1 c_0 ?v_3)) (= (f1 ?v_2 c_2) (f1 c_0 ?v_7)) (= (f1 ?v_2 c_3) (f1 c_0 ?v_12)) (= (f1 ?v_2 c_4) (f1 c_0 ?v_19)) (= (f1 ?v_5 c_0) (f1 c_0 ?v_4)) (= (f1 ?v_5 c_1) (f1 c_0 ?v_6)) (= (f1 ?v_5 c_2) (f1 c_0 ?v_8)) (= (f1 ?v_5 c_3) (f1 c_0 ?v_14)) (= (f1 ?v_5 c_4) (f1 c_0 ?v_21)) (= (f1 ?v_10 c_0) (f1 c_0 ?v_9)) (= (f1 ?v_10 c_1) (f1 c_0 ?v_11)) (= (f1 ?v_10 c_2) (f1 c_0 ?v_13)) (= (f1 ?v_10 c_3) (f1 c_0 ?v_15)) (= (f1 ?v_10 c_4) (f1 c_0 ?v_23)) (= (f1 ?v_17 c_0) (f1 c_0 ?v_16)) (= (f1 ?v_17 c_1) (f1 c_0 ?v_18)) (= (f1 ?v_17 c_2) (f1 c_0 ?v_20)) (= (f1 ?v_17 c_3) (f1 c_0 ?v_22)) (= (f1 ?v_17 c_4) (f1 c_0 ?v_24)) (= (f1 ?v_1 c_0) (f1 c_1 ?v_0)) (= (f1 ?v_1 c_1) (f1 c_1 ?v_2)) (= (f1 ?v_1 c_2) (f1 c_1 ?v_5)) (= (f1 ?v_1 c_3) (f1 c_1 ?v_10)) (= (f1 ?v_1 c_4) (f1 c_1 ?v_17)) (= (f1 ?v_3 c_0) (f1 c_1 ?v_1)) (= (f1 ?v_3 c_1) (f1 c_1 ?v_3)) (= (f1 ?v_3 c_2) (f1 c_1 ?v_7)) (= (f1 ?v_3 c_3) (f1 c_1 ?v_12)) (= (f1 ?v_3 c_4) (f1 c_1 ?v_19)) (= (f1 ?v_7 c_0) (f1 c_1 ?v_4)) (= (f1 ?v_7 c_1) (f1 c_1 ?v_6)) (= (f1 ?v_7 c_2) (f1 c_1 ?v_8)) (= (f1 ?v_7 c_3) (f1 c_1 ?v_14)) (= (f1 ?v_7 c_4) (f1 c_1 ?v_21)) (= (f1 ?v_12 c_0) (f1 c_1 ?v_9)) (= (f1 ?v_12 c_1) (f1 c_1 ?v_11)) (= (f1 ?v_12 c_2) (f1 c_1 ?v_13)) (= (f1 ?v_12 c_3) (f1 c_1 ?v_15)) (= (f1 ?v_12 c_4) (f1 c_1 ?v_23)) (= (f1 ?v_19 c_0) (f1 c_1 ?v_16)) (= (f1 ?v_19 c_1) (f1 c_1 ?v_18)) (= (f1 ?v_19 c_2) (f1 c_1 ?v_20)) (= (f1 ?v_19 c_3) (f1 c_1 ?v_22)) (= (f1 ?v_19 c_4) (f1 c_1 ?v_24)) (= (f1 ?v_4 c_0) (f1 c_2 ?v_0)) (= (f1 ?v_4 c_1) (f1 c_2 ?v_2)) (= (f1 ?v_4 c_2) (f1 c_2 ?v_5)) (= (f1 ?v_4 c_3) (f1 c_2 ?v_10)) (= (f1 ?v_4 c_4) (f1 c_2 ?v_17)) (= (f1 ?v_6 c_0) (f1 c_2 ?v_1)) (= (f1 ?v_6 c_1) (f1 c_2 ?v_3)) (= (f1 ?v_6 c_2) (f1 c_2 ?v_7)) (= (f1 ?v_6 c_3) (f1 c_2 ?v_12)) (= (f1 ?v_6 c_4) (f1 c_2 ?v_19)) (= (f1 ?v_8 c_0) (f1 c_2 ?v_4)) (= (f1 ?v_8 c_1) (f1 c_2 ?v_6)) (= (f1 ?v_8 c_2) (f1 c_2 ?v_8)) (= (f1 ?v_8 c_3) (f1 c_2 ?v_14)) (= (f1 ?v_8 c_4) (f1 c_2 ?v_21)) (= (f1 ?v_14 c_0) (f1 c_2 ?v_9)) (= (f1 ?v_14 c_1) (f1 c_2 ?v_11)) (= (f1 ?v_14 c_2) (f1 c_2 ?v_13)) (= (f1 ?v_14 c_3) (f1 c_2 ?v_15)) (= (f1 ?v_14 c_4) (f1 c_2 ?v_23)) (= (f1 ?v_21 c_0) (f1 c_2 ?v_16)) (= (f1 ?v_21 c_1) (f1 c_2 ?v_18)) (= (f1 ?v_21 c_2) (f1 c_2 ?v_20)) (= (f1 ?v_21 c_3) (f1 c_2 ?v_22)) (= (f1 ?v_21 c_4) (f1 c_2 ?v_24)) (= (f1 ?v_9 c_0) (f1 c_3 ?v_0)) (= (f1 ?v_9 c_1) (f1 c_3 ?v_2)) (= (f1 ?v_9 c_2) (f1 c_3 ?v_5)) (= (f1 ?v_9 c_3) (f1 c_3 ?v_10)) (= (f1 ?v_9 c_4) (f1 c_3 ?v_17)) (= (f1 ?v_11 c_0) (f1 c_3 ?v_1)) (= (f1 ?v_11 c_1) (f1 c_3 ?v_3)) (= (f1 ?v_11 c_2) (f1 c_3 ?v_7)) (= (f1 ?v_11 c_3) (f1 c_3 ?v_12)) (= (f1 ?v_11 c_4) (f1 c_3 ?v_19)) (= (f1 ?v_13 c_0) (f1 c_3 ?v_4)) (= (f1 ?v_13 c_1) (f1 c_3 ?v_6)) (= (f1 ?v_13 c_2) (f1 c_3 ?v_8)) (= (f1 ?v_13 c_3) (f1 c_3 ?v_14)) (= (f1 ?v_13 c_4) (f1 c_3 ?v_21)) (= (f1 ?v_15 c_0) (f1 c_3 ?v_9)) (= (f1 ?v_15 c_1) (f1 c_3 ?v_11)) (= (f1 ?v_15 c_2) (f1 c_3 ?v_13)) (= (f1 ?v_15 c_3) (f1 c_3 ?v_15)) (= (f1 ?v_15 c_4) (f1 c_3 ?v_23)) (= (f1 ?v_23 c_0) (f1 c_3 ?v_16)) (= (f1 ?v_23 c_1) (f1 c_3 ?v_18)) (= (f1 ?v_23 c_2) (f1 c_3 ?v_20)) (= (f1 ?v_23 c_3) (f1 c_3 ?v_22)) (= (f1 ?v_23 c_4) (f1 c_3 ?v_24)) (= (f1 ?v_16 c_0) (f1 c_4 ?v_0)) (= (f1 ?v_16 c_1) (f1 c_4 ?v_2)) (= (f1 ?v_16 c_2) (f1 c_4 ?v_5)) (= (f1 ?v_16 c_3) (f1 c_4 ?v_10)) (= (f1 ?v_16 c_4) (f1 c_4 ?v_17)) (= (f1 ?v_18 c_0) (f1 c_4 ?v_1)) (= (f1 ?v_18 c_1) (f1 c_4 ?v_3)) (= (f1 ?v_18 c_2) (f1 c_4 ?v_7)) (= (f1 ?v_18 c_3) (f1 c_4 ?v_12)) (= (f1 ?v_18 c_4) (f1 c_4 ?v_19)) (= (f1 ?v_20 c_0) (f1 c_4 ?v_4)) (= (f1 ?v_20 c_1) (f1 c_4 ?v_6)) (= (f1 ?v_20 c_2) (f1 c_4 ?v_8)) (= (f1 ?v_20 c_3) (f1 c_4 ?v_14)) (= (f1 ?v_20 c_4) (f1 c_4 ?v_21)) (= (f1 ?v_22 c_0) (f1 c_4 ?v_9)) (= (f1 ?v_22 c_1) (f1 c_4 ?v_11)) (= (f1 ?v_22 c_2) (f1 c_4 ?v_13)) (= (f1 ?v_22 c_3) (f1 c_4 ?v_15)) (= (f1 ?v_22 c_4) (f1 c_4 ?v_23)) (= (f1 ?v_24 c_0) (f1 c_4 ?v_16)) (= (f1 ?v_24 c_1) (f1 c_4 ?v_18)) (= (f1 ?v_24 c_2) (f1 c_4 ?v_20)) (= (f1 ?v_24 c_3) (f1 c_4 ?v_22)) (= (f1 ?v_24 c_4) (f1 c_4 ?v_24)) (= ?v_25 ?v_25) (= ?v_26 ?v_30) (= ?v_27 ?v_35) (= ?v_28 ?v_40) (= ?v_29 ?v_45) (= ?v_30 ?v_26) (= ?v_31 ?v_31) (= ?v_32 ?v_36) (= ?v_33 ?v_41) (= ?v_34 ?v_46) (= ?v_35 ?v_27) (= ?v_36 ?v_32) (= ?v_37 ?v_37) (= ?v_38 ?v_42) (= ?v_39 ?v_47) (= ?v_40 ?v_28) (= ?v_41 ?v_33) (= ?v_42 ?v_38) (= ?v_43 ?v_43) (= ?v_44 ?v_48) (= ?v_45 ?v_29) (= ?v_46 ?v_34) (= ?v_47 ?v_39) (= ?v_48 ?v_44) (= ?v_49 ?v_49) (not (= (f2 c6 (f1 (f3 c6) ?v_50)) ?v_50)) (= (f2 (f1 ?v_51 ?v_25) (f2 ?v_51 ?v_0)) c4) (= (f2 (f1 ?v_51 ?v_26) (f2 ?v_52 ?v_2)) c4) (= (f2 (f1 ?v_51 ?v_27) (f2 ?v_53 ?v_5)) c4) (= (f2 (f1 ?v_51 ?v_28) (f2 ?v_54 ?v_10)) c4) (= (f2 (f1 ?v_51 ?v_29) (f2 ?v_55 ?v_17)) c4) (= (f2 (f1 ?v_52 ?v_30) (f2 ?v_51 ?v_1)) c4) (= (f2 (f1 ?v_52 ?v_31) (f2 ?v_52 ?v_3)) c4) (= (f2 (f1 ?v_52 ?v_32) (f2 ?v_53 ?v_7)) c4) (= (f2 (f1 ?v_52 ?v_33) (f2 ?v_54 ?v_12)) c4) (= (f2 (f1 ?v_52 ?v_34) (f2 ?v_55 ?v_19)) c4) (= (f2 (f1 ?v_53 ?v_35) (f2 ?v_51 ?v_4)) c4) (= (f2 (f1 ?v_53 ?v_36) (f2 ?v_52 ?v_6)) c4) (= (f2 (f1 ?v_53 ?v_37) (f2 ?v_53 ?v_8)) c4) (= (f2 (f1 ?v_53 ?v_38) (f2 ?v_54 ?v_14)) c4) (= (f2 (f1 ?v_53 ?v_39) (f2 ?v_55 ?v_21)) c4) (= (f2 (f1 ?v_54 ?v_40) (f2 ?v_51 ?v_9)) c4) (= (f2 (f1 ?v_54 ?v_41) (f2 ?v_52 ?v_11)) c4) (= (f2 (f1 ?v_54 ?v_42) (f2 ?v_53 ?v_13)) c4) (= (f2 (f1 ?v_54 ?v_43) (f2 ?v_54 ?v_15)) c4) (= (f2 (f1 ?v_54 ?v_44) (f2 ?v_55 ?v_23)) c4) (= (f2 (f1 ?v_55 ?v_45) (f2 ?v_51 ?v_16)) c4) (= (f2 (f1 ?v_55 ?v_46) (f2 ?v_52 ?v_18)) c4) (= (f2 (f1 ?v_55 ?v_47) (f2 ?v_53 ?v_20)) c4) (= (f2 (f1 ?v_55 ?v_48) (f2 ?v_54 ?v_22)) c4) (= (f2 (f1 ?v_55 ?v_49) (f2 ?v_55 ?v_24)) c4) (= (f2 c_0 ?v_0) c_0) (= (f2 c_0 ?v_2) c_0) (= (f2 c_0 ?v_5) c_0) (= (f2 c_0 ?v_10) c_0) (= (f2 c_0 ?v_17) c_0) (= (f2 c_1 ?v_1) c_1) (= (f2 c_1 ?v_3) c_1) (= (f2 c_1 ?v_7) c_1) (= (f2 c_1 ?v_12) c_1) (= (f2 c_1 ?v_19) c_1) (= (f2 c_2 ?v_4) c_2) (= (f2 c_2 ?v_6) c_2) (= (f2 c_2 ?v_8) c_2) (= (f2 c_2 ?v_14) c_2) (= (f2 c_2 ?v_21) c_2) (= (f2 c_3 ?v_9) c_3) (= (f2 c_3 ?v_11) c_3) (= (f2 c_3 ?v_13) c_3) (= (f2 c_3 ?v_15) c_3) (= (f2 c_3 ?v_23) c_3) (= (f2 c_4 ?v_16) c_4) (= (f2 c_4 ?v_18) c_4) (= (f2 c_4 ?v_20) c_4) (= (f2 c_4 ?v_22) c_4) (= (f2 c_4 ?v_24) c_4) (= (f3 ?v_0) (f2 ?v_51 ?v_51)) (= (f3 ?v_2) (f2 ?v_51 ?v_52)) (= (f3 ?v_5) (f2 ?v_51 ?v_53)) (= (f3 ?v_10) (f2 ?v_51 ?v_54)) (= (f3 ?v_17) (f2 ?v_51 ?v_55)) (= (f3 ?v_1) (f2 ?v_52 ?v_51)) (= (f3 ?v_3) (f2 ?v_52 ?v_52)) (= (f3 ?v_7) (f2 ?v_52 ?v_53)) (= (f3 ?v_12) (f2 ?v_52 ?v_54)) (= (f3 ?v_19) (f2 ?v_52 ?v_55)) (= (f3 ?v_4) (f2 ?v_53 ?v_51)) (= (f3 ?v_6) (f2 ?v_53 ?v_52)) (= (f3 ?v_8) (f2 ?v_53 ?v_53)) (= (f3 ?v_14) (f2 ?v_53 ?v_54)) (= (f3 ?v_21) (f2 ?v_53 ?v_55)) (= (f3 ?v_9) (f2 ?v_54 ?v_51)) (= (f3 ?v_11) (f2 ?v_54 ?v_52)) (= (f3 ?v_13) (f2 ?v_54 ?v_53)) (= (f3 ?v_15) (f2 ?v_54 ?v_54)) (= (f3 ?v_23) (f2 ?v_54 ?v_55)) (= (f3 ?v_16) (f2 ?v_55 ?v_51)) (= (f3 ?v_18) (f2 ?v_55 ?v_52)) (= (f3 ?v_20) (f2 ?v_55 ?v_53)) (= (f3 ?v_22) (f2 ?v_55 ?v_54)) (= (f3 ?v_24) (f2 ?v_55 ?v_55)) ?v_61 ?v_62 ?v_63 ?v_64 ?v_65 (= (f3 ?v_51) c_0) (= (f3 ?v_52) c_1) (= (f3 ?v_53) c_2) (= (f3 ?v_54) c_3) (= (f3 ?v_55) c_4) (= (f3 ?v_25) (f1 ?v_51 ?v_51)) (= (f3 ?v_26) (f1 ?v_51 ?v_52)) (= (f3 ?v_27) (f1 ?v_51 ?v_53)) (= (f3 ?v_28) (f1 ?v_51 ?v_54)) (= (f3 ?v_29) (f1 ?v_51 ?v_55)) (= (f3 ?v_30) (f1 ?v_52 ?v_51)) (= (f3 ?v_31) (f1 ?v_52 ?v_52)) (= (f3 ?v_32) (f1 ?v_52 ?v_53)) (= (f3 ?v_33) (f1 ?v_52 ?v_54)) (= (f3 ?v_34) (f1 ?v_52 ?v_55)) (= (f3 ?v_35) (f1 ?v_53 ?v_51)) (= (f3 ?v_36) (f1 ?v_53 ?v_52)) (= (f3 ?v_37) (f1 ?v_53 ?v_53)) (= (f3 ?v_38) (f1 ?v_53 ?v_54)) (= (f3 ?v_39) (f1 ?v_53 ?v_55)) (= (f3 ?v_40) (f1 ?v_54 ?v_51)) (= (f3 ?v_41) (f1 ?v_54 ?v_52)) (= (f3 ?v_42) (f1 ?v_54 ?v_53)) (= (f3 ?v_43) (f1 ?v_54 ?v_54)) (= (f3 ?v_44) (f1 ?v_54 ?v_55)) (= (f3 ?v_45) (f1 ?v_55 ?v_51)) (= (f3 ?v_46) (f1 ?v_55 ?v_52)) (= (f3 ?v_47) (f1 ?v_55 ?v_53)) (= (f3 ?v_48) (f1 ?v_55 ?v_54)) (= (f3 ?v_49) (f1 ?v_55 ?v_55)) ?v_56 ?v_57 ?v_58 ?v_59 ?v_60 (= (f2 ?v_51 c_0) c4) (= (f2 ?v_52 c_1) c4) (= (f2 ?v_53 c_2) c4) (= (f2 ?v_54 c_3) c4) (= (f2 ?v_55 c_4) c4) (or ?v_56 (= ?v_25 c_1) (= ?v_25 c_2) (= ?v_25 c_3) (= ?v_25 c_4)) (or (= ?v_26 c_0) (= ?v_26 c_1) (= ?v_26 c_2) (= ?v_26 c_3) (= ?v_26 c_4)) (or (= ?v_27 c_0) (= ?v_27 c_1) (= ?v_27 c_2) (= ?v_27 c_3) (= ?v_27 c_4)) (or (= ?v_28 c_0) (= ?v_28 c_1) (= ?v_28 c_2) (= ?v_28 c_3) (= ?v_28 c_4)) (or (= ?v_29 c_0) (= ?v_29 c_1) (= ?v_29 c_2) (= ?v_29 c_3) (= ?v_29 c_4)) (or (= ?v_30 c_0) (= ?v_30 c_1) (= ?v_30 c_2) (= ?v_30 c_3) (= ?v_30 c_4)) (or (= ?v_31 c_0) ?v_57 (= ?v_31 c_2) (= ?v_31 c_3) (= ?v_31 c_4)) (or (= ?v_32 c_0) (= ?v_32 c_1) (= ?v_32 c_2) (= ?v_32 c_3) (= ?v_32 c_4)) (or (= ?v_33 c_0) (= ?v_33 c_1) (= ?v_33 c_2) (= ?v_33 c_3) (= ?v_33 c_4)) (or (= ?v_34 c_0) (= ?v_34 c_1) (= ?v_34 c_2) (= ?v_34 c_3) (= ?v_34 c_4)) (or (= ?v_35 c_0) (= ?v_35 c_1) (= ?v_35 c_2) (= ?v_35 c_3) (= ?v_35 c_4)) (or (= ?v_36 c_0) (= ?v_36 c_1) (= ?v_36 c_2) (= ?v_36 c_3) (= ?v_36 c_4)) (or (= ?v_37 c_0) (= ?v_37 c_1) ?v_58 (= ?v_37 c_3) (= ?v_37 c_4)) (or (= ?v_38 c_0) (= ?v_38 c_1) (= ?v_38 c_2) (= ?v_38 c_3) (= ?v_38 c_4)) (or (= ?v_39 c_0) (= ?v_39 c_1) (= ?v_39 c_2) (= ?v_39 c_3) (= ?v_39 c_4)) (or (= ?v_40 c_0) (= ?v_40 c_1) (= ?v_40 c_2) (= ?v_40 c_3) (= ?v_40 c_4)) (or (= ?v_41 c_0) (= ?v_41 c_1) (= ?v_41 c_2) (= ?v_41 c_3) (= ?v_41 c_4)) (or (= ?v_42 c_0) (= ?v_42 c_1) (= ?v_42 c_2) (= ?v_42 c_3) (= ?v_42 c_4)) (or (= ?v_43 c_0) (= ?v_43 c_1) (= ?v_43 c_2) ?v_59 (= ?v_43 c_4)) (or (= ?v_44 c_0) (= ?v_44 c_1) (= ?v_44 c_2) (= ?v_44 c_3) (= ?v_44 c_4)) (or (= ?v_45 c_0) (= ?v_45 c_1) (= ?v_45 c_2) (= ?v_45 c_3) (= ?v_45 c_4)) (or (= ?v_46 c_0) (= ?v_46 c_1) (= ?v_46 c_2) (= ?v_46 c_3) (= ?v_46 c_4)) (or (= ?v_47 c_0) (= ?v_47 c_1) (= ?v_47 c_2) (= ?v_47 c_3) (= ?v_47 c_4)) (or (= ?v_48 c_0) (= ?v_48 c_1) (= ?v_48 c_2) (= ?v_48 c_3) (= ?v_48 c_4)) (or (= ?v_49 c_0) (= ?v_49 c_1) (= ?v_49 c_2) (= ?v_49 c_3) ?v_60) (or ?v_61 (= ?v_0 c_1) (= ?v_0 c_2) (= ?v_0 c_3) (= ?v_0 c_4)) (or (= ?v_2 c_0) (= ?v_2 c_1) (= ?v_2 c_2) (= ?v_2 c_3) (= ?v_2 c_4)) (or (= ?v_5 c_0) (= ?v_5 c_1) (= ?v_5 c_2) (= ?v_5 c_3) (= ?v_5 c_4)) (or (= ?v_10 c_0) (= ?v_10 c_1) (= ?v_10 c_2) (= ?v_10 c_3) (= ?v_10 c_4)) (or (= ?v_17 c_0) (= ?v_17 c_1) (= ?v_17 c_2) (= ?v_17 c_3) (= ?v_17 c_4)) (or (= ?v_1 c_0) (= ?v_1 c_1) (= ?v_1 c_2) (= ?v_1 c_3) (= ?v_1 c_4)) (or (= ?v_3 c_0) ?v_62 (= ?v_3 c_2) (= ?v_3 c_3) (= ?v_3 c_4)) (or (= ?v_7 c_0) (= ?v_7 c_1) (= ?v_7 c_2) (= ?v_7 c_3) (= ?v_7 c_4)) (or (= ?v_12 c_0) (= ?v_12 c_1) (= ?v_12 c_2) (= ?v_12 c_3) (= ?v_12 c_4)) (or (= ?v_19 c_0) (= ?v_19 c_1) (= ?v_19 c_2) (= ?v_19 c_3) (= ?v_19 c_4)) (or (= ?v_4 c_0) (= ?v_4 c_1) (= ?v_4 c_2) (= ?v_4 c_3) (= ?v_4 c_4)) (or (= ?v_6 c_0) (= ?v_6 c_1) (= ?v_6 c_2) (= ?v_6 c_3) (= ?v_6 c_4)) (or (= ?v_8 c_0) (= ?v_8 c_1) ?v_63 (= ?v_8 c_3) (= ?v_8 c_4)) (or (= ?v_14 c_0) (= ?v_14 c_1) (= ?v_14 c_2) (= ?v_14 c_3) (= ?v_14 c_4)) (or (= ?v_21 c_0) (= ?v_21 c_1) (= ?v_21 c_2) (= ?v_21 c_3) (= ?v_21 c_4)) (or (= ?v_9 c_0) (= ?v_9 c_1) (= ?v_9 c_2) (= ?v_9 c_3) (= ?v_9 c_4)) (or (= ?v_11 c_0) (= ?v_11 c_1) (= ?v_11 c_2) (= ?v_11 c_3) (= ?v_11 c_4)) (or (= ?v_13 c_0) (= ?v_13 c_1) (= ?v_13 c_2) (= ?v_13 c_3) (= ?v_13 c_4)) (or (= ?v_15 c_0) (= ?v_15 c_1) (= ?v_15 c_2) ?v_64 (= ?v_15 c_4)) (or (= ?v_23 c_0) (= ?v_23 c_1) (= ?v_23 c_2) (= ?v_23 c_3) (= ?v_23 c_4)) (or (= ?v_16 c_0) (= ?v_16 c_1) (= ?v_16 c_2) (= ?v_16 c_3) (= ?v_16 c_4)) (or (= ?v_18 c_0) (= ?v_18 c_1) (= ?v_18 c_2) (= ?v_18 c_3) (= ?v_18 c_4)) (or (= ?v_20 c_0) (= ?v_20 c_1) (= ?v_20 c_2) (= ?v_20 c_3) (= ?v_20 c_4)) (or (= ?v_22 c_0) (= ?v_22 c_1) (= ?v_22 c_2) (= ?v_22 c_3) (= ?v_22 c_4)) (or (= ?v_24 c_0) (= ?v_24 c_1) (= ?v_24 c_2) (= ?v_24 c_3) ?v_65) (or (= ?v_51 c_0) (= ?v_51 c_1) (= ?v_51 c_2) (= ?v_51 c_3) (= ?v_51 c_4)) (or (= ?v_52 c_0) (= ?v_52 c_1) (= ?v_52 c_2) (= ?v_52 c_3) (= ?v_52 c_4)) (or (= ?v_53 c_0) (= ?v_53 c_1) (= ?v_53 c_2) (= ?v_53 c_3) (= ?v_53 c_4)) (or (= ?v_54 c_0) (= ?v_54 c_1) (= ?v_54 c_2) (= ?v_54 c_3) (= ?v_54 c_4)) (or (= ?v_55 c_0) (= ?v_55 c_1) (= ?v_55 c_2) (= ?v_55 c_3) (= ?v_55 c_4)) (or (= c5 c_0) (= c5 c_1) (= c5 c_2) (= c5 c_3) (= c5 c_4)) (or (= c6 c_0) (= c6 c_1) (= c6 c_2) (= c6 c_3) (= c6 c_4)) (or (= c7 c_0) (= c7 c_1) (= c7 c_2) (= c7 c_3) (= c7 c_4)) (or (= c4 c_0) (= c4 c_1) (= c4 c_2) (= c4 c_3) (= c4 c_4))))))
(check-sat)
(exit)