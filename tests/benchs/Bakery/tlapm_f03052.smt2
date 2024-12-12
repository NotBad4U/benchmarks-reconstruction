;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_N_,
;;	       NEW VARIABLE VARIABLE_num_,
;;	       NEW VARIABLE VARIABLE_flag_,
;;	       NEW VARIABLE VARIABLE_pc_,
;;	       NEW VARIABLE VARIABLE_unread_,
;;	       NEW VARIABLE VARIABLE_max_,
;;	       NEW VARIABLE VARIABLE_nxt_,
;;	       CONSTANT_N_ \in Nat 
;;	PROVE  (/\ VARIABLE_num_ = [CONSTANT_i_ \in 1..CONSTANT_N_ |-> 0]
;;	        /\ VARIABLE_flag_ = [CONSTANT_i_ \in 1..CONSTANT_N_ |-> FALSE]
;;	        /\ VARIABLE_unread_ \in [1..CONSTANT_N_ -> SUBSET 1..CONSTANT_N_]
;;	        /\ VARIABLE_max_ \in [1..CONSTANT_N_ -> Nat]
;;	        /\ VARIABLE_nxt_ \in [1..CONSTANT_N_ -> 1..CONSTANT_N_]
;;	        /\ VARIABLE_pc_ = [CONSTANT_self_ \in 1..CONSTANT_N_ |-> "p1"])
;;	       => (/\ VARIABLE_num_ \in [1..CONSTANT_N_ -> Nat]
;;	           /\ VARIABLE_flag_ \in [1..CONSTANT_N_ -> BOOLEAN]
;;	           /\ VARIABLE_unread_ \in [1..CONSTANT_N_ -> SUBSET 1..CONSTANT_N_]
;;	           /\ \A CONSTANT_i_ \in 1..CONSTANT_N_ :
;;	                 VARIABLE_pc_[CONSTANT_i_] \in {"p2", "p5", "p6"}
;;	                 => CONSTANT_i_ \notin VARIABLE_unread_[CONSTANT_i_]
;;	           /\ VARIABLE_max_ \in [1..CONSTANT_N_ -> Nat]
;;	           /\ VARIABLE_nxt_ \in [1..CONSTANT_N_ -> 1..CONSTANT_N_]
;;	           /\ \A CONSTANT_i_ \in 1..CONSTANT_N_ :
;;	                 VARIABLE_pc_[CONSTANT_i_] = "p6"
;;	                 => VARIABLE_nxt_[CONSTANT_i_] # CONSTANT_i_
;;	           /\ VARIABLE_pc_
;;	              \in [1..CONSTANT_N_ ->
;;	                     {"p1", "p2", "p3", "p4", "p5", "p6", "cs", "p7"}])
;;	          /\ (\A CONSTANT_i_ \in 1..CONSTANT_N_ :
;;	                 /\ /\ VARIABLE_pc_[CONSTANT_i_] \in {"p1", "p2"}
;;	                       => VARIABLE_num_[CONSTANT_i_] = 0
;;	                    /\ VARIABLE_num_[CONSTANT_i_] = 0
;;	                       => VARIABLE_pc_[CONSTANT_i_]
;;	                          \in {"p1", "p2", "p3", "p7"}
;;	                 /\ /\ VARIABLE_flag_[CONSTANT_i_]
;;	                       => VARIABLE_pc_[CONSTANT_i_]
;;	                          \in {"p1", "p2", "p3", "p4"}
;;	                    /\ VARIABLE_pc_[CONSTANT_i_] \in {"p2", "p3"}
;;	                       => VARIABLE_flag_[CONSTANT_i_]
;;	                 /\ VARIABLE_pc_[CONSTANT_i_] \in {"p5", "p6"}
;;	                    => (\A CONSTANT_j_
;;	                           \in (1..CONSTANT_N_
;;	                                \ VARIABLE_unread_[CONSTANT_i_])
;;	                               \ {CONSTANT_i_} :
;;	                           /\ VARIABLE_num_[CONSTANT_i_] > 0
;;	                           /\ \/ VARIABLE_pc_[CONSTANT_j_] = "p1"
;;	                              \/ /\ VARIABLE_pc_[CONSTANT_j_] = "p2"
;;	                                 /\ \/ CONSTANT_i_
;;	                                       \in VARIABLE_unread_[CONSTANT_j_]
;;	                                    \/ VARIABLE_max_[CONSTANT_j_]
;;	                                       >= VARIABLE_num_[CONSTANT_i_]
;;	                              \/ /\ VARIABLE_pc_[CONSTANT_j_] = "p3"
;;	                                 /\ VARIABLE_max_[CONSTANT_j_]
;;	                                    >= VARIABLE_num_[CONSTANT_i_]
;;	                              \/ /\ VARIABLE_pc_[CONSTANT_j_]
;;	                                    \in {"p4", "p5", "p6"}
;;	                                 /\ \/ VARIABLE_num_[CONSTANT_i_]
;;	                                       < VARIABLE_num_[CONSTANT_j_]
;;	                                    \/ /\ VARIABLE_num_[CONSTANT_j_]
;;	                                          = VARIABLE_num_[CONSTANT_i_]
;;	                                       /\ CONSTANT_i_ =< CONSTANT_j_
;;	                                 /\ VARIABLE_pc_[CONSTANT_j_]
;;	                                    \in {"p5", "p6"}
;;	                                    => CONSTANT_i_
;;	                                       \in VARIABLE_unread_[CONSTANT_j_]
;;	                              \/ VARIABLE_pc_[CONSTANT_j_] = "p7")
;;	                 /\ (/\ VARIABLE_pc_[CONSTANT_i_] = "p6"
;;	                     /\ \/ VARIABLE_pc_[VARIABLE_nxt_[CONSTANT_i_]] = "p2"
;;	                           /\ CONSTANT_i_
;;	                              \notin VARIABLE_unread_[VARIABLE_nxt_[CONSTANT_i_]]
;;	                        \/ VARIABLE_pc_[VARIABLE_nxt_[CONSTANT_i_]] = "p3")
;;	                    => VARIABLE_max_[VARIABLE_nxt_[CONSTANT_i_]]
;;	                       >= VARIABLE_num_[CONSTANT_i_]
;;	                 /\ VARIABLE_pc_[CONSTANT_i_] = "cs"
;;	                    => (\A CONSTANT_j_ \in 1..CONSTANT_N_ \ {CONSTANT_i_} :
;;	                           /\ VARIABLE_num_[CONSTANT_i_] > 0
;;	                           /\ \/ VARIABLE_pc_[CONSTANT_j_] = "p1"
;;	                              \/ /\ VARIABLE_pc_[CONSTANT_j_] = "p2"
;;	                                 /\ \/ CONSTANT_i_
;;	                                       \in VARIABLE_unread_[CONSTANT_j_]
;;	                                    \/ VARIABLE_max_[CONSTANT_j_]
;;	                                       >= VARIABLE_num_[CONSTANT_i_]
;;	                              \/ /\ VARIABLE_pc_[CONSTANT_j_] = "p3"
;;	                                 /\ VARIABLE_max_[CONSTANT_j_]
;;	                                    >= VARIABLE_num_[CONSTANT_i_]
;;	                              \/ /\ VARIABLE_pc_[CONSTANT_j_]
;;	                                    \in {"p4", "p5", "p6"}
;;	                                 /\ \/ VARIABLE_num_[CONSTANT_i_]
;;	                                       < VARIABLE_num_[CONSTANT_j_]
;;	                                    \/ /\ VARIABLE_num_[CONSTANT_j_]
;;	                                          = VARIABLE_num_[CONSTANT_i_]
;;	                                       /\ CONSTANT_i_ =< CONSTANT_j_
;;	                                 /\ VARIABLE_pc_[CONSTANT_j_]
;;	                                    \in {"p5", "p6"}
;;	                                    => CONSTANT_i_
;;	                                       \in VARIABLE_unread_[CONSTANT_j_]
;;	                              \/ VARIABLE_pc_[CONSTANT_j_] = "p7"))
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #7
;; Generated from file "./examples/Bakery.tla", line 310, characters 3-4

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_BoolSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Castunderscore_Bool (Bool) Idv)

(declare-fun smt__TLAunderscore_underscore_Castunderscore_Int (Int) Idv)

(declare-fun smt__TLAunderscore_underscore_FunApp (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLAunderscore_underscore_FunIsafcn (Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_FunSet (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntLteq (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntRange (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_NatSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Projunderscore_Int (Idv) Int)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_1 (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_2 (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_3 (Idv Idv
  Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_4 (Idv Idv Idv
  Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_8 (Idv Idv Idv
  Idv Idv Idv Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_SetMinus (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_cs () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_p1 () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_p2 () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_p3 () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_p4 () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_p5 () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_p6 () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_p7 () Idv)

(declare-fun smt__TLAunderscore_underscore_StrSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Subset (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SubsetEq (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_TrigEqunderscore_Idv (Idv
  Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_Ttunderscore_Idv () Idv)

;; Axiom: SetExt
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (= (smt__TLAunderscore_underscore_Mem smt__z smt__x)
              (smt__TLAunderscore_underscore_Mem smt__z smt__y)))
          (= smt__x smt__y))
        :pattern ((smt__TLAunderscore_underscore_SetExtTrigger smt__x smt__y))))
    :named |SetExt|))

;; Axiom: SubsetEqIntro
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (=> (smt__TLAunderscore_underscore_Mem smt__z smt__x)
              (smt__TLAunderscore_underscore_Mem smt__z smt__y)))
          (smt__TLAunderscore_underscore_SubsetEq smt__x smt__y))
        :pattern ((smt__TLAunderscore_underscore_SubsetEq smt__x smt__y))))
    :named |SubsetEqIntro|))

;; Axiom: SubsetEqElim
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv) (smt__z Idv))
      (!
        (=>
          (and (smt__TLAunderscore_underscore_SubsetEq smt__x smt__y)
            (smt__TLAunderscore_underscore_Mem smt__z smt__x))
          (smt__TLAunderscore_underscore_Mem smt__z smt__y))
        :pattern ((smt__TLAunderscore_underscore_SubsetEq smt__x smt__y)
                   (smt__TLAunderscore_underscore_Mem smt__z smt__x))))
    :named |SubsetEqElim|))

;; Axiom: SubsetDefAlt
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_Subset smt__a))
          (smt__TLAunderscore_underscore_SubsetEq smt__x smt__a))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_Subset smt__a)))
        :pattern ((smt__TLAunderscore_underscore_SubsetEq smt__x smt__a)
                   (smt__TLAunderscore_underscore_Subset smt__a))))
    :named |SubsetDefAlt|))

;; Axiom: SetMinusDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetMinus smt__a smt__b))
          (and (smt__TLAunderscore_underscore_Mem smt__x smt__a)
            (not (smt__TLAunderscore_underscore_Mem smt__x smt__b))))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetMinus smt__a smt__b)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__a)
                   (smt__TLAunderscore_underscore_SetMinus smt__a smt__b))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__b)
                   (smt__TLAunderscore_underscore_SetMinus smt__a smt__b))))
    :named |SetMinusDef|))

;; Axiom: NatSetDef
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_Mem smt__x
            smt__TLAunderscore_underscore_NatSet)
          (and
            (smt__TLAunderscore_underscore_Mem smt__x
              smt__TLAunderscore_underscore_IntSet)
            (smt__TLAunderscore_underscore_IntLteq
              (smt__TLAunderscore_underscore_Castunderscore_Int 0) smt__x)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    smt__TLAunderscore_underscore_NatSet))))
    :named |NatSetDef|))

;; Axiom: IntRangeDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_IntRange smt__a smt__b))
          (and
            (smt__TLAunderscore_underscore_Mem smt__x
              smt__TLAunderscore_underscore_IntSet)
            (smt__TLAunderscore_underscore_IntLteq smt__a smt__x)
            (smt__TLAunderscore_underscore_IntLteq smt__x smt__b)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_IntRange smt__a smt__b)))))
    :named |IntRangeDef|))

;; Axiom: FunExt
(assert
  (!
    (forall ((smt__f Idv) (smt__g Idv))
      (!
        (=>
          (and (smt__TLAunderscore_underscore_FunIsafcn smt__f)
            (smt__TLAunderscore_underscore_FunIsafcn smt__g)
            (= (smt__TLAunderscore_underscore_FunDom smt__f)
              (smt__TLAunderscore_underscore_FunDom smt__g))
            (forall ((smt__x Idv))
              (=>
                (smt__TLAunderscore_underscore_Mem smt__x
                  (smt__TLAunderscore_underscore_FunDom smt__f))
                (= (smt__TLAunderscore_underscore_FunApp smt__f smt__x)
                  (smt__TLAunderscore_underscore_FunApp smt__g smt__x)))))
          (= smt__f smt__g))
        :pattern ((smt__TLAunderscore_underscore_FunIsafcn smt__f)
                   (smt__TLAunderscore_underscore_FunIsafcn smt__g))))
    :named |FunExt|))

; omitted fact (second-order)

;; Axiom: FunSetIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (and (smt__TLAunderscore_underscore_FunIsafcn smt__f)
            (= (smt__TLAunderscore_underscore_FunDom smt__f) smt__a)
            (forall ((smt__x Idv))
              (=> (smt__TLAunderscore_underscore_Mem smt__x smt__a)
                (smt__TLAunderscore_underscore_Mem
                  (smt__TLAunderscore_underscore_FunApp smt__f smt__x) 
                  smt__b))))
          (smt__TLAunderscore_underscore_Mem smt__f
            (smt__TLAunderscore_underscore_FunSet smt__a smt__b)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__f
                    (smt__TLAunderscore_underscore_FunSet smt__a smt__b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__f
            (smt__TLAunderscore_underscore_FunSet smt__a smt__b))
          (and (smt__TLAunderscore_underscore_FunIsafcn smt__f)
            (= (smt__TLAunderscore_underscore_FunDom smt__f) smt__a)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__f
                    (smt__TLAunderscore_underscore_FunSet smt__a smt__b)))))
    :named |FunSetElim1|))

;; Axiom: FunSetElim2
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv) (smt__x Idv))
      (!
        (=>
          (and
            (smt__TLAunderscore_underscore_Mem smt__f
              (smt__TLAunderscore_underscore_FunSet smt__a smt__b))
            (smt__TLAunderscore_underscore_Mem smt__x smt__a))
          (smt__TLAunderscore_underscore_Mem
            (smt__TLAunderscore_underscore_FunApp smt__f smt__x) smt__b))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__f
                    (smt__TLAunderscore_underscore_FunSet smt__a smt__b))
                   (smt__TLAunderscore_underscore_Mem smt__x smt__a))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__f
                    (smt__TLAunderscore_underscore_FunSet smt__a smt__b))
                   (smt__TLAunderscore_underscore_FunApp smt__f smt__x))))
    :named |FunSetElim2|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (!
        (smt__TLAunderscore_underscore_Mem smt__a1
          (smt__TLAunderscore_underscore_SetEnumunderscore_1 smt__a1))
        :pattern ((smt__TLAunderscore_underscore_SetEnumunderscore_1 smt__a1))))
    :named |EnumDefIntro 1|))

;; Axiom: EnumDefIntro 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv))
      (!
        (and
          (smt__TLAunderscore_underscore_Mem smt__a1
            (smt__TLAunderscore_underscore_SetEnumunderscore_2 smt__a1
              smt__a2))
          (smt__TLAunderscore_underscore_Mem smt__a2
            (smt__TLAunderscore_underscore_SetEnumunderscore_2 smt__a1
              smt__a2)))
        :pattern ((smt__TLAunderscore_underscore_SetEnumunderscore_2 
                    smt__a1 smt__a2)))) :named |EnumDefIntro 2|))

;; Axiom: EnumDefIntro 3
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv))
      (!
        (and
          (smt__TLAunderscore_underscore_Mem smt__a1
            (smt__TLAunderscore_underscore_SetEnumunderscore_3 smt__a1
              smt__a2 smt__a3))
          (smt__TLAunderscore_underscore_Mem smt__a2
            (smt__TLAunderscore_underscore_SetEnumunderscore_3 smt__a1
              smt__a2 smt__a3))
          (smt__TLAunderscore_underscore_Mem smt__a3
            (smt__TLAunderscore_underscore_SetEnumunderscore_3 smt__a1
              smt__a2 smt__a3)))
        :pattern ((smt__TLAunderscore_underscore_SetEnumunderscore_3 
                    smt__a1 smt__a2 smt__a3)))) :named |EnumDefIntro 3|))

;; Axiom: EnumDefIntro 4
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv))
      (!
        (and
          (smt__TLAunderscore_underscore_Mem smt__a1
            (smt__TLAunderscore_underscore_SetEnumunderscore_4 smt__a1
              smt__a2 smt__a3 smt__a4))
          (smt__TLAunderscore_underscore_Mem smt__a2
            (smt__TLAunderscore_underscore_SetEnumunderscore_4 smt__a1
              smt__a2 smt__a3 smt__a4))
          (smt__TLAunderscore_underscore_Mem smt__a3
            (smt__TLAunderscore_underscore_SetEnumunderscore_4 smt__a1
              smt__a2 smt__a3 smt__a4))
          (smt__TLAunderscore_underscore_Mem smt__a4
            (smt__TLAunderscore_underscore_SetEnumunderscore_4 smt__a1
              smt__a2 smt__a3 smt__a4)))
        :pattern ((smt__TLAunderscore_underscore_SetEnumunderscore_4 
                    smt__a1 smt__a2 smt__a3 smt__a4))))
    :named |EnumDefIntro 4|))

;; Axiom: EnumDefIntro 8
(assert
  (!
    (forall
      ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv) (smt__a5 Idv)
        (smt__a6 Idv) (smt__a7 Idv) (smt__a8 Idv))
      (!
        (and
          (smt__TLAunderscore_underscore_Mem smt__a1
            (smt__TLAunderscore_underscore_SetEnumunderscore_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (smt__TLAunderscore_underscore_Mem smt__a2
            (smt__TLAunderscore_underscore_SetEnumunderscore_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (smt__TLAunderscore_underscore_Mem smt__a3
            (smt__TLAunderscore_underscore_SetEnumunderscore_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (smt__TLAunderscore_underscore_Mem smt__a4
            (smt__TLAunderscore_underscore_SetEnumunderscore_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (smt__TLAunderscore_underscore_Mem smt__a5
            (smt__TLAunderscore_underscore_SetEnumunderscore_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (smt__TLAunderscore_underscore_Mem smt__a6
            (smt__TLAunderscore_underscore_SetEnumunderscore_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (smt__TLAunderscore_underscore_Mem smt__a7
            (smt__TLAunderscore_underscore_SetEnumunderscore_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (smt__TLAunderscore_underscore_Mem smt__a8
            (smt__TLAunderscore_underscore_SetEnumunderscore_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8)))
        :pattern ((smt__TLAunderscore_underscore_SetEnumunderscore_8 
                    smt__a1 smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7
                    smt__a8)))) :named |EnumDefIntro 8|))

;; Axiom: EnumDefElim 1
(assert
  (!
    (forall ((smt__a1 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetEnumunderscore_1 smt__a1))
          (= smt__x smt__a1))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetEnumunderscore_1
                      smt__a1))))) :named |EnumDefElim 1|))

;; Axiom: EnumDefElim 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetEnumunderscore_2 smt__a1
              smt__a2)) (or (= smt__x smt__a1) (= smt__x smt__a2)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetEnumunderscore_2
                      smt__a1 smt__a2))))) :named |EnumDefElim 2|))

;; Axiom: EnumDefElim 3
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetEnumunderscore_3 smt__a1
              smt__a2 smt__a3))
          (or (= smt__x smt__a1) (= smt__x smt__a2) (= smt__x smt__a3)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetEnumunderscore_3
                      smt__a1 smt__a2 smt__a3))))) :named |EnumDefElim 3|))

;; Axiom: EnumDefElim 4
(assert
  (!
    (forall
      ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetEnumunderscore_4 smt__a1
              smt__a2 smt__a3 smt__a4))
          (or (= smt__x smt__a1) (= smt__x smt__a2) (= smt__x smt__a3)
            (= smt__x smt__a4)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetEnumunderscore_4
                      smt__a1 smt__a2 smt__a3 smt__a4)))))
    :named |EnumDefElim 4|))

;; Axiom: EnumDefElim 8
(assert
  (!
    (forall
      ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv) (smt__a5 Idv)
        (smt__a6 Idv) (smt__a7 Idv) (smt__a8 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetEnumunderscore_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (or (= smt__x smt__a1) (= smt__x smt__a2) (= smt__x smt__a3)
            (= smt__x smt__a4) (= smt__x smt__a5) (= smt__x smt__a6)
            (= smt__x smt__a7) (= smt__x smt__a8)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetEnumunderscore_8
                      smt__a1 smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 
                      smt__a7 smt__a8))))) :named |EnumDefElim 8|))

;; Axiom: StrLitIsstr cs
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_cs
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr cs|))

;; Axiom: StrLitIsstr p1
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_p1
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr p1|))

;; Axiom: StrLitIsstr p2
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_p2
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr p2|))

;; Axiom: StrLitIsstr p3
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_p3
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr p3|))

;; Axiom: StrLitIsstr p4
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_p4
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr p4|))

;; Axiom: StrLitIsstr p5
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_p5
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr p5|))

;; Axiom: StrLitIsstr p6
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_p6
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr p6|))

;; Axiom: StrLitIsstr p7
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_p7
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr p7|))

;; Axiom: StrLitDistinct cs p1
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_cs
      smt__TLAunderscore_underscore_StrLitunderscore_p1)
    :named |StrLitDistinct cs p1|))

;; Axiom: StrLitDistinct cs p2
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_cs
      smt__TLAunderscore_underscore_StrLitunderscore_p2)
    :named |StrLitDistinct cs p2|))

;; Axiom: StrLitDistinct cs p3
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_cs
      smt__TLAunderscore_underscore_StrLitunderscore_p3)
    :named |StrLitDistinct cs p3|))

;; Axiom: StrLitDistinct cs p4
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_cs
      smt__TLAunderscore_underscore_StrLitunderscore_p4)
    :named |StrLitDistinct cs p4|))

;; Axiom: StrLitDistinct cs p5
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_cs
      smt__TLAunderscore_underscore_StrLitunderscore_p5)
    :named |StrLitDistinct cs p5|))

;; Axiom: StrLitDistinct cs p6
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_cs
      smt__TLAunderscore_underscore_StrLitunderscore_p6)
    :named |StrLitDistinct cs p6|))

;; Axiom: StrLitDistinct p2 p1
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p2
      smt__TLAunderscore_underscore_StrLitunderscore_p1)
    :named |StrLitDistinct p2 p1|))

;; Axiom: StrLitDistinct p3 p1
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p3
      smt__TLAunderscore_underscore_StrLitunderscore_p1)
    :named |StrLitDistinct p3 p1|))

;; Axiom: StrLitDistinct p3 p2
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p3
      smt__TLAunderscore_underscore_StrLitunderscore_p2)
    :named |StrLitDistinct p3 p2|))

;; Axiom: StrLitDistinct p3 p5
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p3
      smt__TLAunderscore_underscore_StrLitunderscore_p5)
    :named |StrLitDistinct p3 p5|))

;; Axiom: StrLitDistinct p3 p6
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p3
      smt__TLAunderscore_underscore_StrLitunderscore_p6)
    :named |StrLitDistinct p3 p6|))

;; Axiom: StrLitDistinct p4 p1
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p4
      smt__TLAunderscore_underscore_StrLitunderscore_p1)
    :named |StrLitDistinct p4 p1|))

;; Axiom: StrLitDistinct p4 p2
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p4
      smt__TLAunderscore_underscore_StrLitunderscore_p2)
    :named |StrLitDistinct p4 p2|))

;; Axiom: StrLitDistinct p4 p3
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p4
      smt__TLAunderscore_underscore_StrLitunderscore_p3)
    :named |StrLitDistinct p4 p3|))

;; Axiom: StrLitDistinct p4 p5
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p4
      smt__TLAunderscore_underscore_StrLitunderscore_p5)
    :named |StrLitDistinct p4 p5|))

;; Axiom: StrLitDistinct p4 p6
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p4
      smt__TLAunderscore_underscore_StrLitunderscore_p6)
    :named |StrLitDistinct p4 p6|))

;; Axiom: StrLitDistinct p5 p1
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p5
      smt__TLAunderscore_underscore_StrLitunderscore_p1)
    :named |StrLitDistinct p5 p1|))

;; Axiom: StrLitDistinct p5 p2
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p5
      smt__TLAunderscore_underscore_StrLitunderscore_p2)
    :named |StrLitDistinct p5 p2|))

;; Axiom: StrLitDistinct p6 p1
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p6
      smt__TLAunderscore_underscore_StrLitunderscore_p1)
    :named |StrLitDistinct p6 p1|))

;; Axiom: StrLitDistinct p6 p2
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p6
      smt__TLAunderscore_underscore_StrLitunderscore_p2)
    :named |StrLitDistinct p6 p2|))

;; Axiom: StrLitDistinct p6 p5
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p6
      smt__TLAunderscore_underscore_StrLitunderscore_p5)
    :named |StrLitDistinct p6 p5|))

;; Axiom: StrLitDistinct p7 cs
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p7
      smt__TLAunderscore_underscore_StrLitunderscore_cs)
    :named |StrLitDistinct p7 cs|))

;; Axiom: StrLitDistinct p7 p1
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p7
      smt__TLAunderscore_underscore_StrLitunderscore_p1)
    :named |StrLitDistinct p7 p1|))

;; Axiom: StrLitDistinct p7 p2
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p7
      smt__TLAunderscore_underscore_StrLitunderscore_p2)
    :named |StrLitDistinct p7 p2|))

;; Axiom: StrLitDistinct p7 p3
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p7
      smt__TLAunderscore_underscore_StrLitunderscore_p3)
    :named |StrLitDistinct p7 p3|))

;; Axiom: StrLitDistinct p7 p4
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p7
      smt__TLAunderscore_underscore_StrLitunderscore_p4)
    :named |StrLitDistinct p7 p4|))

;; Axiom: StrLitDistinct p7 p5
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p7
      smt__TLAunderscore_underscore_StrLitunderscore_p5)
    :named |StrLitDistinct p7 p5|))

;; Axiom: StrLitDistinct p7 p6
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_p7
      smt__TLAunderscore_underscore_StrLitunderscore_p6)
    :named |StrLitDistinct p7 p6|))

;; Axiom: CastInjAlt Bool
(assert
  (!
    (and
      (= (smt__TLAunderscore_underscore_Castunderscore_Bool true)
        smt__TLAunderscore_underscore_Ttunderscore_Idv)
      (distinct (smt__TLAunderscore_underscore_Castunderscore_Bool false)
        smt__TLAunderscore_underscore_Ttunderscore_Idv))
    :named |CastInjAlt Bool|))

;; Axiom: CastInjAlt Int
(assert
  (!
    (forall ((smt__x Int))
      (!
        (= smt__x
          (smt__TLAunderscore_underscore_Projunderscore_Int
            (smt__TLAunderscore_underscore_Castunderscore_Int smt__x)))
        :pattern ((smt__TLAunderscore_underscore_Castunderscore_Int smt__x))))
    :named |CastInjAlt Int|))

;; Axiom: TypeGuardIntro Bool
(assert
  (!
    (forall ((smt__z Bool))
      (!
        (smt__TLAunderscore_underscore_Mem
          (smt__TLAunderscore_underscore_Castunderscore_Bool smt__z)
          smt__TLAunderscore_underscore_BoolSet)
        :pattern ((smt__TLAunderscore_underscore_Castunderscore_Bool smt__z))))
    :named |TypeGuardIntro Bool|))

;; Axiom: TypeGuardIntro Int
(assert
  (!
    (forall ((smt__z Int))
      (!
        (smt__TLAunderscore_underscore_Mem
          (smt__TLAunderscore_underscore_Castunderscore_Int smt__z)
          smt__TLAunderscore_underscore_IntSet)
        :pattern ((smt__TLAunderscore_underscore_Castunderscore_Int smt__z))))
    :named |TypeGuardIntro Int|))

;; Axiom: TypeGuardElim Bool
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__x
            smt__TLAunderscore_underscore_BoolSet)
          (or
            (= smt__x
              (smt__TLAunderscore_underscore_Castunderscore_Bool true))
            (= smt__x
              (smt__TLAunderscore_underscore_Castunderscore_Bool false))))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    smt__TLAunderscore_underscore_BoolSet))))
    :named |TypeGuardElim Bool|))

;; Axiom: TypeGuardElim Int
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__x
            smt__TLAunderscore_underscore_IntSet)
          (= smt__x
            (smt__TLAunderscore_underscore_Castunderscore_Int
              (smt__TLAunderscore_underscore_Projunderscore_Int smt__x))))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    smt__TLAunderscore_underscore_IntSet))))
    :named |TypeGuardElim Int|))

;; Axiom: Typing TIntLteq
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLAunderscore_underscore_IntLteq
            (smt__TLAunderscore_underscore_Castunderscore_Int smt__x1)
            (smt__TLAunderscore_underscore_Castunderscore_Int smt__x2))
          (<= smt__x1 smt__x2))
        :pattern ((smt__TLAunderscore_underscore_IntLteq
                    (smt__TLAunderscore_underscore_Castunderscore_Int smt__x1)
                    (smt__TLAunderscore_underscore_Castunderscore_Int smt__x2)))))
    :named |Typing TIntLteq|))

;; Axiom: ExtTrigEqDef Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (= (smt__TLAunderscore_underscore_TrigEqunderscore_Idv smt__x smt__y)
          (= smt__x smt__y))
        :pattern ((smt__TLAunderscore_underscore_TrigEqunderscore_Idv 
                    smt__x smt__y)))) :named |ExtTrigEqDef Idv|))

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

(declare-fun smt__CONSTANTunderscore_Nunderscore_ () Idv)

; hidden fact

(declare-fun smt__VARIABLEunderscore_numunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_numunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_flagunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_flagunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_pcunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_pcunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_unreadunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_unreadunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_maxunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_maxunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_nxtunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_nxtunderscore_underscore_prime () Idv)

(declare-fun smt__STATEunderscore_varsunderscore_ () Idv)

(declare-fun smt__ACTIONunderscore_p1underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_p2underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_p3underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_p4underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_p5underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_p6underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_csunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_p7underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_punderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Nextunderscore_ () Idv)

(declare-fun smt__TEMPORALunderscore_Specunderscore_ () Idv)

(declare-fun smt__STATEunderscore_MutualExclusionunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_Nunderscore_
    smt__TLAunderscore_underscore_NatSet))

; hidden fact

; hidden fact

(declare-fun smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_1 (Idv) Idv)

;; Axiom: FunConstrIsafcn TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv))
      (!
        (smt__TLAunderscore_underscore_FunIsafcn
          (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_1
            smt__a))
        :pattern ((smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_1
                    smt__a)))) :named |FunConstrIsafcn TLA__FunFcn_flatnd_1|))

;; Axiom: FunDomDef TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunDom
            (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_1
              smt__a)) smt__a)
        :pattern ((smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_1
                    smt__a)))) :named |FunDomDef TLA__FunFcn_flatnd_1|))

;; Axiom: FunAppDef TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=> (smt__TLAunderscore_underscore_Mem smt__x smt__a)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_1
                smt__a) smt__x)
            (smt__TLAunderscore_underscore_Castunderscore_Int 0)))
        :pattern ((smt__TLAunderscore_underscore_FunApp
                    (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_1
                      smt__a) smt__x))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__a)
                   (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_1
                     smt__a)))) :named |FunAppDef TLA__FunFcn_flatnd_1|))

;; Axiom: FunTyping TLA__FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv))
      (!
        (=>
          (forall ((smt__x Idv))
            (=> (smt__TLAunderscore_underscore_Mem smt__x smt__a)
              (smt__TLAunderscore_underscore_Mem
                (smt__TLAunderscore_underscore_Castunderscore_Int 0) 
                smt__b)))
          (smt__TLAunderscore_underscore_Mem
            (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_1
              smt__a) (smt__TLAunderscore_underscore_FunSet smt__a smt__b)))
        :pattern ((smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_1
                    smt__a)
                   (smt__TLAunderscore_underscore_FunSet smt__a smt__b))))
    :named |FunTyping TLA__FunFcn_flatnd_1|))

(declare-fun smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_2 (Idv) Idv)

;; Axiom: FunConstrIsafcn TLA__FunFcn_flatnd_2
(assert
  (!
    (forall ((smt__a Idv))
      (!
        (smt__TLAunderscore_underscore_FunIsafcn
          (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_2
            smt__a))
        :pattern ((smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_2
                    smt__a)))) :named |FunConstrIsafcn TLA__FunFcn_flatnd_2|))

;; Axiom: FunDomDef TLA__FunFcn_flatnd_2
(assert
  (!
    (forall ((smt__a Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunDom
            (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_2
              smt__a)) smt__a)
        :pattern ((smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_2
                    smt__a)))) :named |FunDomDef TLA__FunFcn_flatnd_2|))

;; Axiom: FunAppDef TLA__FunFcn_flatnd_2
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=> (smt__TLAunderscore_underscore_Mem smt__x smt__a)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_2
                smt__a) smt__x)
            (smt__TLAunderscore_underscore_Castunderscore_Bool false)))
        :pattern ((smt__TLAunderscore_underscore_FunApp
                    (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_2
                      smt__a) smt__x))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__a)
                   (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_2
                     smt__a)))) :named |FunAppDef TLA__FunFcn_flatnd_2|))

;; Axiom: FunTyping TLA__FunFcn_flatnd_2
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv))
      (!
        (=>
          (forall ((smt__x Idv))
            (=> (smt__TLAunderscore_underscore_Mem smt__x smt__a)
              (smt__TLAunderscore_underscore_Mem
                (smt__TLAunderscore_underscore_Castunderscore_Bool false)
                smt__b)))
          (smt__TLAunderscore_underscore_Mem
            (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_2
              smt__a) (smt__TLAunderscore_underscore_FunSet smt__a smt__b)))
        :pattern ((smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_2
                    smt__a)
                   (smt__TLAunderscore_underscore_FunSet smt__a smt__b))))
    :named |FunTyping TLA__FunFcn_flatnd_2|))

(declare-fun smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_3 (Idv) Idv)

;; Axiom: FunConstrIsafcn TLA__FunFcn_flatnd_3
(assert
  (!
    (forall ((smt__a Idv))
      (!
        (smt__TLAunderscore_underscore_FunIsafcn
          (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_3
            smt__a))
        :pattern ((smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_3
                    smt__a)))) :named |FunConstrIsafcn TLA__FunFcn_flatnd_3|))

;; Axiom: FunDomDef TLA__FunFcn_flatnd_3
(assert
  (!
    (forall ((smt__a Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunDom
            (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_3
              smt__a)) smt__a)
        :pattern ((smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_3
                    smt__a)))) :named |FunDomDef TLA__FunFcn_flatnd_3|))

;; Axiom: FunAppDef TLA__FunFcn_flatnd_3
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=> (smt__TLAunderscore_underscore_Mem smt__x smt__a)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_3
                smt__a) smt__x)
            smt__TLAunderscore_underscore_StrLitunderscore_p1))
        :pattern ((smt__TLAunderscore_underscore_FunApp
                    (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_3
                      smt__a) smt__x))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__a)
                   (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_3
                     smt__a)))) :named |FunAppDef TLA__FunFcn_flatnd_3|))

;; Axiom: FunTyping TLA__FunFcn_flatnd_3
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv))
      (!
        (=>
          (forall ((smt__x Idv))
            (=> (smt__TLAunderscore_underscore_Mem smt__x smt__a)
              (smt__TLAunderscore_underscore_Mem
                smt__TLAunderscore_underscore_StrLitunderscore_p1 smt__b)))
          (smt__TLAunderscore_underscore_Mem
            (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_3
              smt__a) (smt__TLAunderscore_underscore_FunSet smt__a smt__b)))
        :pattern ((smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_3
                    smt__a)
                   (smt__TLAunderscore_underscore_FunSet smt__a smt__b))))
    :named |FunTyping TLA__FunFcn_flatnd_3|))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            smt__VARIABLEunderscore_numunderscore_
            (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_1
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                smt__CONSTANTunderscore_Nunderscore_)))
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            smt__VARIABLEunderscore_flagunderscore_
            (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_2
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                smt__CONSTANTunderscore_Nunderscore_)))
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_unreadunderscore_
            (smt__TLAunderscore_underscore_FunSet
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                smt__CONSTANTunderscore_Nunderscore_)
              (smt__TLAunderscore_underscore_Subset
                (smt__TLAunderscore_underscore_IntRange
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                  smt__CONSTANTunderscore_Nunderscore_))))
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_maxunderscore_
            (smt__TLAunderscore_underscore_FunSet
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                smt__CONSTANTunderscore_Nunderscore_)
              smt__TLAunderscore_underscore_NatSet))
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_nxtunderscore_
            (smt__TLAunderscore_underscore_FunSet
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                smt__CONSTANTunderscore_Nunderscore_)
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                smt__CONSTANTunderscore_Nunderscore_)))
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            smt__VARIABLEunderscore_pcunderscore_
            (smt__TLAunderscore_underscore_FunFcnunderscore_flatndunderscore_3
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                smt__CONSTANTunderscore_Nunderscore_))))
        (and
          (and
            (smt__TLAunderscore_underscore_Mem
              smt__VARIABLEunderscore_numunderscore_
              (smt__TLAunderscore_underscore_FunSet
                (smt__TLAunderscore_underscore_IntRange
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                  smt__CONSTANTunderscore_Nunderscore_)
                smt__TLAunderscore_underscore_NatSet))
            (smt__TLAunderscore_underscore_Mem
              smt__VARIABLEunderscore_flagunderscore_
              (smt__TLAunderscore_underscore_FunSet
                (smt__TLAunderscore_underscore_IntRange
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                  smt__CONSTANTunderscore_Nunderscore_)
                smt__TLAunderscore_underscore_BoolSet))
            (smt__TLAunderscore_underscore_Mem
              smt__VARIABLEunderscore_unreadunderscore_
              (smt__TLAunderscore_underscore_FunSet
                (smt__TLAunderscore_underscore_IntRange
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                  smt__CONSTANTunderscore_Nunderscore_)
                (smt__TLAunderscore_underscore_Subset
                  (smt__TLAunderscore_underscore_IntRange
                    (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                    smt__CONSTANTunderscore_Nunderscore_))))
            (forall ((smt__CONSTANTunderscore_iunderscore_ Idv))
              (=>
                (smt__TLAunderscore_underscore_Mem
                  smt__CONSTANTunderscore_iunderscore_
                  (smt__TLAunderscore_underscore_IntRange
                    (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                    smt__CONSTANTunderscore_Nunderscore_))
                (=>
                  (smt__TLAunderscore_underscore_Mem
                    (smt__TLAunderscore_underscore_FunApp
                      smt__VARIABLEunderscore_pcunderscore_
                      smt__CONSTANTunderscore_iunderscore_)
                    (smt__TLAunderscore_underscore_SetEnumunderscore_3
                      smt__TLAunderscore_underscore_StrLitunderscore_p2
                      smt__TLAunderscore_underscore_StrLitunderscore_p5
                      smt__TLAunderscore_underscore_StrLitunderscore_p6))
                  (not
                    (smt__TLAunderscore_underscore_Mem
                      smt__CONSTANTunderscore_iunderscore_
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_unreadunderscore_
                        smt__CONSTANTunderscore_iunderscore_))))))
            (smt__TLAunderscore_underscore_Mem
              smt__VARIABLEunderscore_maxunderscore_
              (smt__TLAunderscore_underscore_FunSet
                (smt__TLAunderscore_underscore_IntRange
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                  smt__CONSTANTunderscore_Nunderscore_)
                smt__TLAunderscore_underscore_NatSet))
            (smt__TLAunderscore_underscore_Mem
              smt__VARIABLEunderscore_nxtunderscore_
              (smt__TLAunderscore_underscore_FunSet
                (smt__TLAunderscore_underscore_IntRange
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                  smt__CONSTANTunderscore_Nunderscore_)
                (smt__TLAunderscore_underscore_IntRange
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                  smt__CONSTANTunderscore_Nunderscore_)))
            (forall ((smt__CONSTANTunderscore_iunderscore_ Idv))
              (=>
                (smt__TLAunderscore_underscore_Mem
                  smt__CONSTANTunderscore_iunderscore_
                  (smt__TLAunderscore_underscore_IntRange
                    (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                    smt__CONSTANTunderscore_Nunderscore_))
                (=>
                  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                    (smt__TLAunderscore_underscore_FunApp
                      smt__VARIABLEunderscore_pcunderscore_
                      smt__CONSTANTunderscore_iunderscore_)
                    smt__TLAunderscore_underscore_StrLitunderscore_p6)
                  (not
                    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_nxtunderscore_
                        smt__CONSTANTunderscore_iunderscore_)
                      smt__CONSTANTunderscore_iunderscore_)))))
            (smt__TLAunderscore_underscore_Mem
              smt__VARIABLEunderscore_pcunderscore_
              (smt__TLAunderscore_underscore_FunSet
                (smt__TLAunderscore_underscore_IntRange
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                  smt__CONSTANTunderscore_Nunderscore_)
                (smt__TLAunderscore_underscore_SetEnumunderscore_8
                  smt__TLAunderscore_underscore_StrLitunderscore_p1
                  smt__TLAunderscore_underscore_StrLitunderscore_p2
                  smt__TLAunderscore_underscore_StrLitunderscore_p3
                  smt__TLAunderscore_underscore_StrLitunderscore_p4
                  smt__TLAunderscore_underscore_StrLitunderscore_p5
                  smt__TLAunderscore_underscore_StrLitunderscore_p6
                  smt__TLAunderscore_underscore_StrLitunderscore_cs
                  smt__TLAunderscore_underscore_StrLitunderscore_p7))))
          (forall ((smt__CONSTANTunderscore_iunderscore_ Idv))
            (=>
              (smt__TLAunderscore_underscore_Mem
                smt__CONSTANTunderscore_iunderscore_
                (smt__TLAunderscore_underscore_IntRange
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                  smt__CONSTANTunderscore_Nunderscore_))
              (and
                (and
                  (=>
                    (smt__TLAunderscore_underscore_Mem
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_pcunderscore_
                        smt__CONSTANTunderscore_iunderscore_)
                      (smt__TLAunderscore_underscore_SetEnumunderscore_2
                        smt__TLAunderscore_underscore_StrLitunderscore_p1
                        smt__TLAunderscore_underscore_StrLitunderscore_p2))
                    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_numunderscore_
                        smt__CONSTANTunderscore_iunderscore_)
                      (smt__TLAunderscore_underscore_Castunderscore_Int 0)))
                  (=>
                    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_numunderscore_
                        smt__CONSTANTunderscore_iunderscore_)
                      (smt__TLAunderscore_underscore_Castunderscore_Int 0))
                    (smt__TLAunderscore_underscore_Mem
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_pcunderscore_
                        smt__CONSTANTunderscore_iunderscore_)
                      (smt__TLAunderscore_underscore_SetEnumunderscore_4
                        smt__TLAunderscore_underscore_StrLitunderscore_p1
                        smt__TLAunderscore_underscore_StrLitunderscore_p2
                        smt__TLAunderscore_underscore_StrLitunderscore_p3
                        smt__TLAunderscore_underscore_StrLitunderscore_p7))))
                (and
                  (=>
                    (=
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_flagunderscore_
                        smt__CONSTANTunderscore_iunderscore_)
                      smt__TLAunderscore_underscore_Ttunderscore_Idv)
                    (smt__TLAunderscore_underscore_Mem
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_pcunderscore_
                        smt__CONSTANTunderscore_iunderscore_)
                      (smt__TLAunderscore_underscore_SetEnumunderscore_4
                        smt__TLAunderscore_underscore_StrLitunderscore_p1
                        smt__TLAunderscore_underscore_StrLitunderscore_p2
                        smt__TLAunderscore_underscore_StrLitunderscore_p3
                        smt__TLAunderscore_underscore_StrLitunderscore_p4)))
                  (=>
                    (smt__TLAunderscore_underscore_Mem
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_pcunderscore_
                        smt__CONSTANTunderscore_iunderscore_)
                      (smt__TLAunderscore_underscore_SetEnumunderscore_2
                        smt__TLAunderscore_underscore_StrLitunderscore_p2
                        smt__TLAunderscore_underscore_StrLitunderscore_p3))
                    (=
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_flagunderscore_
                        smt__CONSTANTunderscore_iunderscore_)
                      smt__TLAunderscore_underscore_Ttunderscore_Idv)))
                (=>
                  (smt__TLAunderscore_underscore_Mem
                    (smt__TLAunderscore_underscore_FunApp
                      smt__VARIABLEunderscore_pcunderscore_
                      smt__CONSTANTunderscore_iunderscore_)
                    (smt__TLAunderscore_underscore_SetEnumunderscore_2
                      smt__TLAunderscore_underscore_StrLitunderscore_p5
                      smt__TLAunderscore_underscore_StrLitunderscore_p6))
                  (forall ((smt__CONSTANTunderscore_junderscore_ Idv))
                    (=>
                      (smt__TLAunderscore_underscore_Mem
                        smt__CONSTANTunderscore_junderscore_
                        (smt__TLAunderscore_underscore_SetMinus
                          (smt__TLAunderscore_underscore_SetMinus
                            (smt__TLAunderscore_underscore_IntRange
                              (smt__TLAunderscore_underscore_Castunderscore_Int
                                1) smt__CONSTANTunderscore_Nunderscore_)
                            (smt__TLAunderscore_underscore_FunApp
                              smt__VARIABLEunderscore_unreadunderscore_
                              smt__CONSTANTunderscore_iunderscore_))
                          (smt__TLAunderscore_underscore_SetEnumunderscore_1
                            smt__CONSTANTunderscore_iunderscore_)))
                      (and
                        (and
                          (smt__TLAunderscore_underscore_IntLteq
                            (smt__TLAunderscore_underscore_Castunderscore_Int
                              0)
                            (smt__TLAunderscore_underscore_FunApp
                              smt__VARIABLEunderscore_numunderscore_
                              smt__CONSTANTunderscore_iunderscore_))
                          (not
                            (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                              (smt__TLAunderscore_underscore_Castunderscore_Int
                                0)
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_numunderscore_
                                smt__CONSTANTunderscore_iunderscore_))))
                        (or
                          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                            (smt__TLAunderscore_underscore_FunApp
                              smt__VARIABLEunderscore_pcunderscore_
                              smt__CONSTANTunderscore_junderscore_)
                            smt__TLAunderscore_underscore_StrLitunderscore_p1)
                          (and
                            (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_pcunderscore_
                                smt__CONSTANTunderscore_junderscore_)
                              smt__TLAunderscore_underscore_StrLitunderscore_p2)
                            (or
                              (smt__TLAunderscore_underscore_Mem
                                smt__CONSTANTunderscore_iunderscore_
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__VARIABLEunderscore_unreadunderscore_
                                  smt__CONSTANTunderscore_junderscore_))
                              (smt__TLAunderscore_underscore_IntLteq
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__VARIABLEunderscore_numunderscore_
                                  smt__CONSTANTunderscore_iunderscore_)
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__VARIABLEunderscore_maxunderscore_
                                  smt__CONSTANTunderscore_junderscore_))))
                          (and
                            (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_pcunderscore_
                                smt__CONSTANTunderscore_junderscore_)
                              smt__TLAunderscore_underscore_StrLitunderscore_p3)
                            (smt__TLAunderscore_underscore_IntLteq
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_numunderscore_
                                smt__CONSTANTunderscore_iunderscore_)
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_maxunderscore_
                                smt__CONSTANTunderscore_junderscore_)))
                          (and
                            (smt__TLAunderscore_underscore_Mem
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_pcunderscore_
                                smt__CONSTANTunderscore_junderscore_)
                              (smt__TLAunderscore_underscore_SetEnumunderscore_3
                                smt__TLAunderscore_underscore_StrLitunderscore_p4
                                smt__TLAunderscore_underscore_StrLitunderscore_p5
                                smt__TLAunderscore_underscore_StrLitunderscore_p6))
                            (or
                              (and
                                (smt__TLAunderscore_underscore_IntLteq
                                  (smt__TLAunderscore_underscore_FunApp
                                    smt__VARIABLEunderscore_numunderscore_
                                    smt__CONSTANTunderscore_iunderscore_)
                                  (smt__TLAunderscore_underscore_FunApp
                                    smt__VARIABLEunderscore_numunderscore_
                                    smt__CONSTANTunderscore_junderscore_))
                                (not
                                  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                    (smt__TLAunderscore_underscore_FunApp
                                      smt__VARIABLEunderscore_numunderscore_
                                      smt__CONSTANTunderscore_iunderscore_)
                                    (smt__TLAunderscore_underscore_FunApp
                                      smt__VARIABLEunderscore_numunderscore_
                                      smt__CONSTANTunderscore_junderscore_))))
                              (and
                                (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                  (smt__TLAunderscore_underscore_FunApp
                                    smt__VARIABLEunderscore_numunderscore_
                                    smt__CONSTANTunderscore_junderscore_)
                                  (smt__TLAunderscore_underscore_FunApp
                                    smt__VARIABLEunderscore_numunderscore_
                                    smt__CONSTANTunderscore_iunderscore_))
                                (smt__TLAunderscore_underscore_IntLteq
                                  smt__CONSTANTunderscore_iunderscore_
                                  smt__CONSTANTunderscore_junderscore_)))
                            (=>
                              (smt__TLAunderscore_underscore_Mem
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__VARIABLEunderscore_pcunderscore_
                                  smt__CONSTANTunderscore_junderscore_)
                                (smt__TLAunderscore_underscore_SetEnumunderscore_2
                                  smt__TLAunderscore_underscore_StrLitunderscore_p5
                                  smt__TLAunderscore_underscore_StrLitunderscore_p6))
                              (smt__TLAunderscore_underscore_Mem
                                smt__CONSTANTunderscore_iunderscore_
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__VARIABLEunderscore_unreadunderscore_
                                  smt__CONSTANTunderscore_junderscore_))))
                          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                            (smt__TLAunderscore_underscore_FunApp
                              smt__VARIABLEunderscore_pcunderscore_
                              smt__CONSTANTunderscore_junderscore_)
                            smt__TLAunderscore_underscore_StrLitunderscore_p7))))))
                (=>
                  (and
                    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_pcunderscore_
                        smt__CONSTANTunderscore_iunderscore_)
                      smt__TLAunderscore_underscore_StrLitunderscore_p6)
                    (or
                      (and
                        (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                          (smt__TLAunderscore_underscore_FunApp
                            smt__VARIABLEunderscore_pcunderscore_
                            (smt__TLAunderscore_underscore_FunApp
                              smt__VARIABLEunderscore_nxtunderscore_
                              smt__CONSTANTunderscore_iunderscore_))
                          smt__TLAunderscore_underscore_StrLitunderscore_p2)
                        (not
                          (smt__TLAunderscore_underscore_Mem
                            smt__CONSTANTunderscore_iunderscore_
                            (smt__TLAunderscore_underscore_FunApp
                              smt__VARIABLEunderscore_unreadunderscore_
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_nxtunderscore_
                                smt__CONSTANTunderscore_iunderscore_)))))
                      (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                        (smt__TLAunderscore_underscore_FunApp
                          smt__VARIABLEunderscore_pcunderscore_
                          (smt__TLAunderscore_underscore_FunApp
                            smt__VARIABLEunderscore_nxtunderscore_
                            smt__CONSTANTunderscore_iunderscore_))
                        smt__TLAunderscore_underscore_StrLitunderscore_p3)))
                  (smt__TLAunderscore_underscore_IntLteq
                    (smt__TLAunderscore_underscore_FunApp
                      smt__VARIABLEunderscore_numunderscore_
                      smt__CONSTANTunderscore_iunderscore_)
                    (smt__TLAunderscore_underscore_FunApp
                      smt__VARIABLEunderscore_maxunderscore_
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_nxtunderscore_
                        smt__CONSTANTunderscore_iunderscore_))))
                (=>
                  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                    (smt__TLAunderscore_underscore_FunApp
                      smt__VARIABLEunderscore_pcunderscore_
                      smt__CONSTANTunderscore_iunderscore_)
                    smt__TLAunderscore_underscore_StrLitunderscore_cs)
                  (forall ((smt__CONSTANTunderscore_junderscore_ Idv))
                    (=>
                      (smt__TLAunderscore_underscore_Mem
                        smt__CONSTANTunderscore_junderscore_
                        (smt__TLAunderscore_underscore_SetMinus
                          (smt__TLAunderscore_underscore_IntRange
                            (smt__TLAunderscore_underscore_Castunderscore_Int
                              1) smt__CONSTANTunderscore_Nunderscore_)
                          (smt__TLAunderscore_underscore_SetEnumunderscore_1
                            smt__CONSTANTunderscore_iunderscore_)))
                      (and
                        (and
                          (smt__TLAunderscore_underscore_IntLteq
                            (smt__TLAunderscore_underscore_Castunderscore_Int
                              0)
                            (smt__TLAunderscore_underscore_FunApp
                              smt__VARIABLEunderscore_numunderscore_
                              smt__CONSTANTunderscore_iunderscore_))
                          (not
                            (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                              (smt__TLAunderscore_underscore_Castunderscore_Int
                                0)
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_numunderscore_
                                smt__CONSTANTunderscore_iunderscore_))))
                        (or
                          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                            (smt__TLAunderscore_underscore_FunApp
                              smt__VARIABLEunderscore_pcunderscore_
                              smt__CONSTANTunderscore_junderscore_)
                            smt__TLAunderscore_underscore_StrLitunderscore_p1)
                          (and
                            (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_pcunderscore_
                                smt__CONSTANTunderscore_junderscore_)
                              smt__TLAunderscore_underscore_StrLitunderscore_p2)
                            (or
                              (smt__TLAunderscore_underscore_Mem
                                smt__CONSTANTunderscore_iunderscore_
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__VARIABLEunderscore_unreadunderscore_
                                  smt__CONSTANTunderscore_junderscore_))
                              (smt__TLAunderscore_underscore_IntLteq
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__VARIABLEunderscore_numunderscore_
                                  smt__CONSTANTunderscore_iunderscore_)
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__VARIABLEunderscore_maxunderscore_
                                  smt__CONSTANTunderscore_junderscore_))))
                          (and
                            (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_pcunderscore_
                                smt__CONSTANTunderscore_junderscore_)
                              smt__TLAunderscore_underscore_StrLitunderscore_p3)
                            (smt__TLAunderscore_underscore_IntLteq
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_numunderscore_
                                smt__CONSTANTunderscore_iunderscore_)
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_maxunderscore_
                                smt__CONSTANTunderscore_junderscore_)))
                          (and
                            (smt__TLAunderscore_underscore_Mem
                              (smt__TLAunderscore_underscore_FunApp
                                smt__VARIABLEunderscore_pcunderscore_
                                smt__CONSTANTunderscore_junderscore_)
                              (smt__TLAunderscore_underscore_SetEnumunderscore_3
                                smt__TLAunderscore_underscore_StrLitunderscore_p4
                                smt__TLAunderscore_underscore_StrLitunderscore_p5
                                smt__TLAunderscore_underscore_StrLitunderscore_p6))
                            (or
                              (and
                                (smt__TLAunderscore_underscore_IntLteq
                                  (smt__TLAunderscore_underscore_FunApp
                                    smt__VARIABLEunderscore_numunderscore_
                                    smt__CONSTANTunderscore_iunderscore_)
                                  (smt__TLAunderscore_underscore_FunApp
                                    smt__VARIABLEunderscore_numunderscore_
                                    smt__CONSTANTunderscore_junderscore_))
                                (not
                                  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                    (smt__TLAunderscore_underscore_FunApp
                                      smt__VARIABLEunderscore_numunderscore_
                                      smt__CONSTANTunderscore_iunderscore_)
                                    (smt__TLAunderscore_underscore_FunApp
                                      smt__VARIABLEunderscore_numunderscore_
                                      smt__CONSTANTunderscore_junderscore_))))
                              (and
                                (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                  (smt__TLAunderscore_underscore_FunApp
                                    smt__VARIABLEunderscore_numunderscore_
                                    smt__CONSTANTunderscore_junderscore_)
                                  (smt__TLAunderscore_underscore_FunApp
                                    smt__VARIABLEunderscore_numunderscore_
                                    smt__CONSTANTunderscore_iunderscore_))
                                (smt__TLAunderscore_underscore_IntLteq
                                  smt__CONSTANTunderscore_iunderscore_
                                  smt__CONSTANTunderscore_junderscore_)))
                            (=>
                              (smt__TLAunderscore_underscore_Mem
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__VARIABLEunderscore_pcunderscore_
                                  smt__CONSTANTunderscore_junderscore_)
                                (smt__TLAunderscore_underscore_SetEnumunderscore_2
                                  smt__TLAunderscore_underscore_StrLitunderscore_p5
                                  smt__TLAunderscore_underscore_StrLitunderscore_p6))
                              (smt__TLAunderscore_underscore_Mem
                                smt__CONSTANTunderscore_iunderscore_
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__VARIABLEunderscore_unreadunderscore_
                                  smt__CONSTANTunderscore_junderscore_))))
                          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                            (smt__TLAunderscore_underscore_FunApp
                              smt__VARIABLEunderscore_pcunderscore_
                              smt__CONSTANTunderscore_junderscore_)
                            smt__TLAunderscore_underscore_StrLitunderscore_p7))))))))))))
    :named |Goal|))

(check-sat)
(exit)
