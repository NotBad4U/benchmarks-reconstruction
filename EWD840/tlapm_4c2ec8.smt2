;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_N_,
;;	       NEW VARIABLE VARIABLE_active_,
;;	       NEW VARIABLE VARIABLE_color_,
;;	       NEW VARIABLE VARIABLE_tpos_,
;;	       NEW VARIABLE VARIABLE_tcolor_,
;;	       CONSTANT_N_ \in Nat \ {0} ,
;;	       ASSUME /\ VARIABLE_active_ \in [0..CONSTANT_N_ - 1 -> BOOLEAN]
;;	              /\ VARIABLE_color_
;;	                 \in [0..CONSTANT_N_ - 1 -> {"white", "black"}]
;;	              /\ VARIABLE_tpos_ \in 0..CONSTANT_N_ - 1
;;	              /\ VARIABLE_tcolor_ \in {"white", "black"} ,
;;	              ACTION_Next_ \/ ?h6fbaa = STATE_vars_ 
;;	       PROVE  /\ ?VARIABLE_active_#prime \in [0..CONSTANT_N_ - 1 -> BOOLEAN]
;;	              /\ ?VARIABLE_color_#prime
;;	                 \in [0..CONSTANT_N_ - 1 -> {"white", "black"}]
;;	              /\ ?VARIABLE_tpos_#prime \in 0..CONSTANT_N_ - 1
;;	              /\ ?VARIABLE_tcolor_#prime \in {"white", "black"} 
;;	PROVE  (/\ VARIABLE_active_ \in [0..CONSTANT_N_ - 1 -> BOOLEAN]
;;	        /\ VARIABLE_color_ \in [0..CONSTANT_N_ - 1 -> {"white", "black"}]
;;	        /\ VARIABLE_tpos_ \in 0..CONSTANT_N_ - 1
;;	        /\ VARIABLE_tcolor_ \in {"white", "black"})
;;	       /\ (ACTION_Next_ \/ ?h6fbaa = STATE_vars_)
;;	       => (/\ ?VARIABLE_active_#prime \in [0..CONSTANT_N_ - 1 -> BOOLEAN]
;;	           /\ ?VARIABLE_color_#prime
;;	              \in [0..CONSTANT_N_ - 1 -> {"white", "black"}]
;;	           /\ ?VARIABLE_tpos_#prime \in 0..CONSTANT_N_ - 1
;;	           /\ ?VARIABLE_tcolor_#prime \in {"white", "black"})
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #13
;; Generated from file "./examples/EWD840.tla", line 146, characters 5-11

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA__Anon_OPAQUE_h6fbaa () Idv)

(declare-fun smt__TLA__BoolSet () Idv)

(declare-fun smt__TLA__Cast_Int (Int) Idv)

(declare-fun smt__TLA__FunApp (Idv Idv) Idv)

(declare-fun smt__TLA__FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA__FunIsafcn (Idv) Bool)

(declare-fun smt__TLA__FunSet (Idv Idv) Idv)

(declare-fun smt__TLA__IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA__IntMinus (Idv Idv) Idv)

(declare-fun smt__TLA__IntRange (Idv Idv) Idv)

(declare-fun smt__TLA__IntSet () Idv)

(declare-fun smt__TLA__Mem (Idv Idv) Bool)

(declare-fun smt__TLA__NatSet () Idv)

(declare-fun smt__TLA__Proj_Int (Idv) Int)

(declare-fun smt__TLA__SetEnum_1 (Idv) Idv)

(declare-fun smt__TLA__SetEnum_2 (Idv Idv) Idv)

(declare-fun smt__TLA__SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA__SetMinus (Idv Idv) Idv)

(declare-fun smt__TLA__StrLit_black () Idv)

(declare-fun smt__TLA__StrLit_white () Idv)

(declare-fun smt__TLA__StrSet () Idv)

(declare-fun smt__TLA__TrigEq_Idv (Idv
  Idv) Bool)

(declare-fun smt__TLA__Tt_Idv () Idv)

;; Axiom: SetExt
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (= (smt__TLA__Mem smt__z smt__x)
              (smt__TLA__Mem smt__z smt__y)))
          (= smt__x smt__y))
        :pattern ((smt__TLA__SetExtTrigger smt__x smt__y))))
    :named |SetExt|))

;; Axiom: SetMinusDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (=
          (smt__TLA__Mem smt__x
            (smt__TLA__SetMinus smt__a smt__b))
          (and (smt__TLA__Mem smt__x smt__a)
            (not (smt__TLA__Mem smt__x smt__b))))
        :pattern ((smt__TLA__Mem smt__x
                    (smt__TLA__SetMinus smt__a smt__b)))
        :pattern ((smt__TLA__Mem smt__x smt__a)
                   (smt__TLA__SetMinus smt__a smt__b))
        :pattern ((smt__TLA__Mem smt__x smt__b)
                   (smt__TLA__SetMinus smt__a smt__b))))
    :named |SetMinusDef|))

;; Axiom: NatSetDef
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=
          (smt__TLA__Mem smt__x
            smt__TLA__NatSet)
          (and
            (smt__TLA__Mem smt__x
              smt__TLA__IntSet)
            (smt__TLA__IntLteq
              (smt__TLA__Cast_Int 0) smt__x)))
        :pattern ((smt__TLA__Mem smt__x
                    smt__TLA__NatSet))))
    :named |NatSetDef|))

;; Axiom: IntRangeDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (=
          (smt__TLA__Mem smt__x
            (smt__TLA__IntRange smt__a smt__b))
          (and
            (smt__TLA__Mem smt__x
              smt__TLA__IntSet)
            (smt__TLA__IntLteq smt__a smt__x)
            (smt__TLA__IntLteq smt__x smt__b)))
        :pattern ((smt__TLA__Mem smt__x
                    (smt__TLA__IntRange smt__a smt__b)))))
    :named |IntRangeDef|))

;; Axiom: FunExt
(assert
  (!
    (forall ((smt__f Idv) (smt__g Idv))
      (!
        (=>
          (and (smt__TLA__FunIsafcn smt__f)
            (smt__TLA__FunIsafcn smt__g)
            (= (smt__TLA__FunDom smt__f)
              (smt__TLA__FunDom smt__g))
            (forall ((smt__x Idv))
              (=>
                (smt__TLA__Mem smt__x
                  (smt__TLA__FunDom smt__f))
                (= (smt__TLA__FunApp smt__f smt__x)
                  (smt__TLA__FunApp smt__g smt__x)))))
          (= smt__f smt__g))
        :pattern ((smt__TLA__FunIsafcn smt__f)
                   (smt__TLA__FunIsafcn smt__g))))
    :named |FunExt|))

; omitted fact (second-order)

;; Axiom: FunSetIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (and (smt__TLA__FunIsafcn smt__f)
            (= (smt__TLA__FunDom smt__f) smt__a)
            (forall ((smt__x Idv))
              (=> (smt__TLA__Mem smt__x smt__a)
                (smt__TLA__Mem
                  (smt__TLA__FunApp smt__f smt__x) 
                  smt__b))))
          (smt__TLA__Mem smt__f
            (smt__TLA__FunSet smt__a smt__b)))
        :pattern ((smt__TLA__Mem smt__f
                    (smt__TLA__FunSet smt__a smt__b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (smt__TLA__Mem smt__f
            (smt__TLA__FunSet smt__a smt__b))
          (and (smt__TLA__FunIsafcn smt__f)
            (= (smt__TLA__FunDom smt__f) smt__a)))
        :pattern ((smt__TLA__Mem smt__f
                    (smt__TLA__FunSet smt__a smt__b)))))
    :named |FunSetElim1|))

;; Axiom: FunSetElim2
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv) (smt__x Idv))
      (!
        (=>
          (and
            (smt__TLA__Mem smt__f
              (smt__TLA__FunSet smt__a smt__b))
            (smt__TLA__Mem smt__x smt__a))
          (smt__TLA__Mem
            (smt__TLA__FunApp smt__f smt__x) smt__b))
        :pattern ((smt__TLA__Mem smt__f
                    (smt__TLA__FunSet smt__a smt__b))
                   (smt__TLA__Mem smt__x smt__a))
        :pattern ((smt__TLA__Mem smt__f
                    (smt__TLA__FunSet smt__a smt__b))
                   (smt__TLA__FunApp smt__f smt__x))))
    :named |FunSetElim2|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (!
        (smt__TLA__Mem smt__a1
          (smt__TLA__SetEnum_1 smt__a1))
        :pattern ((smt__TLA__SetEnum_1 smt__a1))))
    :named |EnumDefIntro 1|))

;; Axiom: EnumDefIntro 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv))
      (!
        (and
          (smt__TLA__Mem smt__a1
            (smt__TLA__SetEnum_2 smt__a1
              smt__a2))
          (smt__TLA__Mem smt__a2
            (smt__TLA__SetEnum_2 smt__a1
              smt__a2)))
        :pattern ((smt__TLA__SetEnum_2 
                    smt__a1 smt__a2)))) :named |EnumDefIntro 2|))

;; Axiom: EnumDefElim 1
(assert
  (!
    (forall ((smt__a1 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLA__Mem smt__x
            (smt__TLA__SetEnum_1 smt__a1))
          (= smt__x smt__a1))
        :pattern ((smt__TLA__Mem smt__x
                    (smt__TLA__SetEnum_1
                      smt__a1))))) :named |EnumDefElim 1|))

;; Axiom: EnumDefElim 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLA__Mem smt__x
            (smt__TLA__SetEnum_2 smt__a1
              smt__a2)) (or (= smt__x smt__a1) (= smt__x smt__a2)))
        :pattern ((smt__TLA__Mem smt__x
                    (smt__TLA__SetEnum_2
                      smt__a1 smt__a2))))) :named |EnumDefElim 2|))

;; Axiom: StrLitIsstr black
(assert
  (!
    (smt__TLA__Mem
      smt__TLA__StrLit_black
      smt__TLA__StrSet) :named |StrLitIsstr black|))

;; Axiom: StrLitIsstr white
(assert
  (!
    (smt__TLA__Mem
      smt__TLA__StrLit_white
      smt__TLA__StrSet) :named |StrLitIsstr white|))

;; Axiom: StrLitDistinct black white
(assert
  (!
    (distinct smt__TLA__StrLit_black
      smt__TLA__StrLit_white)
    :named |StrLitDistinct black white|))

;; Axiom: CastInjAlt Int
(assert
  (!
    (forall ((smt__x Int))
      (!
        (= smt__x
          (smt__TLA__Proj_Int
            (smt__TLA__Cast_Int smt__x)))
        :pattern ((smt__TLA__Cast_Int smt__x))))
    :named |CastInjAlt Int|))

;; Axiom: TypeGuardIntro Int
(assert
  (!
    (forall ((smt__z Int))
      (!
        (smt__TLA__Mem
          (smt__TLA__Cast_Int smt__z)
          smt__TLA__IntSet)
        :pattern ((smt__TLA__Cast_Int smt__z))))
    :named |TypeGuardIntro Int|))

;; Axiom: TypeGuardElim Int
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=>
          (smt__TLA__Mem smt__x
            smt__TLA__IntSet)
          (= smt__x
            (smt__TLA__Cast_Int
              (smt__TLA__Proj_Int smt__x))))
        :pattern ((smt__TLA__Mem smt__x
                    smt__TLA__IntSet))))
    :named |TypeGuardElim Int|))

;; Axiom: Typing TIntMinus
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLA__IntMinus
            (smt__TLA__Cast_Int smt__x1)
            (smt__TLA__Cast_Int smt__x2))
          (smt__TLA__Cast_Int
            (- smt__x1 smt__x2)))
        :pattern ((smt__TLA__IntMinus
                    (smt__TLA__Cast_Int smt__x1)
                    (smt__TLA__Cast_Int smt__x2)))))
    :named |Typing TIntMinus|))

;; Axiom: Typing TIntLteq
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLA__IntLteq
            (smt__TLA__Cast_Int smt__x1)
            (smt__TLA__Cast_Int smt__x2))
          (<= smt__x1 smt__x2))
        :pattern ((smt__TLA__IntLteq
                    (smt__TLA__Cast_Int smt__x1)
                    (smt__TLA__Cast_Int smt__x2)))))
    :named |Typing TIntLteq|))

;; Axiom: ExtTrigEqDef Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (= (smt__TLA__TrigEq_Idv smt__x smt__y)
          (= smt__x smt__y))
        :pattern ((smt__TLA__TrigEq_Idv 
                    smt__x smt__y)))) :named |ExtTrigEqDef Idv|))

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

(declare-fun smt__CONSTANT_N_ () Idv)

; hidden fact

(declare-fun smt__VARIABLE_active_ () Idv)

(declare-fun smt__VARIABLE_active__prime () Idv)

(declare-fun smt__VARIABLE_color_ () Idv)

(declare-fun smt__VARIABLE_color__prime () Idv)

(declare-fun smt__VARIABLE_tpos_ () Idv)

(declare-fun smt__VARIABLE_tpos__prime () Idv)

(declare-fun smt__VARIABLE_tcolor_ () Idv)

(declare-fun smt__VARIABLE_tcolor__prime () Idv)

(declare-fun smt__STATE_Init_ () Idv)

(declare-fun smt__ACTION_InitiateProbe_ () Idv)

(declare-fun smt__ACTION_PassToken_ (Idv) Idv)

(declare-fun smt__ACTION_SendMsg_ (Idv) Idv)

(declare-fun smt__ACTION_Deactivate_ (Idv) Idv)

(declare-fun smt__ACTION_Controlled_ () Idv)

(declare-fun smt__ACTION_Environment_ () Idv)

(declare-fun smt__ACTION_Next_ () Idv)

(declare-fun smt__STATE_vars_ () Idv)

(declare-fun smt__TEMPORAL_Fairness_ () Idv)

(declare-fun smt__TEMPORAL_Spec_ () Idv)

(declare-fun smt__STATE_NeverBlack_ () Idv)

(declare-fun smt__TEMPORAL_NeverChangeColor_ () Idv)

(declare-fun smt__STATE_terminationDetected_ () Idv)

(declare-fun smt__STATE_TerminationDetection_ () Idv)

(declare-fun smt__TEMPORAL_Liveness_ () Idv)

(declare-fun smt__TEMPORAL_AllNodesTerminateIfNoMessages_ () Idv)

(declare-fun smt__STATE_Inv_ () Idv)

(assert
  (smt__TLA__Mem smt__CONSTANT_N_
    (smt__TLA__SetMinus
      smt__TLA__NatSet
      (smt__TLA__SetEnum_1
        (smt__TLA__Cast_Int 0)))))

; hidden fact

; hidden fact

; hidden fact

(assert
  (=>
    (and
      (smt__TLA__Mem
        smt__VARIABLE_active_
        (smt__TLA__FunSet
          (smt__TLA__IntRange
            (smt__TLA__Cast_Int 0)
            (smt__TLA__IntMinus
              smt__CONSTANT_N_
              (smt__TLA__Cast_Int 1)))
          smt__TLA__BoolSet))
      (smt__TLA__Mem
        smt__VARIABLE_color_
        (smt__TLA__FunSet
          (smt__TLA__IntRange
            (smt__TLA__Cast_Int 0)
            (smt__TLA__IntMinus
              smt__CONSTANT_N_
              (smt__TLA__Cast_Int 1)))
          (smt__TLA__SetEnum_2
            smt__TLA__StrLit_white
            smt__TLA__StrLit_black)))
      (smt__TLA__Mem
        smt__VARIABLE_tpos_
        (smt__TLA__IntRange
          (smt__TLA__Cast_Int 0)
          (smt__TLA__IntMinus
            smt__CONSTANT_N_
            (smt__TLA__Cast_Int 1))))
      (smt__TLA__Mem
        smt__VARIABLE_tcolor_
        (smt__TLA__SetEnum_2
          smt__TLA__StrLit_white
          smt__TLA__StrLit_black)))
    (=>
      (or
        (= smt__ACTION_Next_
          smt__TLA__Tt_Idv)
        (smt__TLA__TrigEq_Idv
          smt__TLA__Anon_OPAQUE_h6fbaa
          smt__STATE_vars_))
      (and
        (smt__TLA__Mem
          smt__VARIABLE_active__prime
          (smt__TLA__FunSet
            (smt__TLA__IntRange
              (smt__TLA__Cast_Int 0)
              (smt__TLA__IntMinus
                smt__CONSTANT_N_
                (smt__TLA__Cast_Int 1)))
            smt__TLA__BoolSet))
        (smt__TLA__Mem
          smt__VARIABLE_color__prime
          (smt__TLA__FunSet
            (smt__TLA__IntRange
              (smt__TLA__Cast_Int 0)
              (smt__TLA__IntMinus
                smt__CONSTANT_N_
                (smt__TLA__Cast_Int 1)))
            (smt__TLA__SetEnum_2
              smt__TLA__StrLit_white
              smt__TLA__StrLit_black)))
        (smt__TLA__Mem
          smt__VARIABLE_tpos__prime
          (smt__TLA__IntRange
            (smt__TLA__Cast_Int 0)
            (smt__TLA__IntMinus
              smt__CONSTANT_N_
              (smt__TLA__Cast_Int 1))))
        (smt__TLA__Mem
          smt__VARIABLE_tcolor__prime
          (smt__TLA__SetEnum_2
            smt__TLA__StrLit_white
            smt__TLA__StrLit_black))))))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and
            (smt__TLA__Mem
              smt__VARIABLE_active_
              (smt__TLA__FunSet
                (smt__TLA__IntRange
                  (smt__TLA__Cast_Int 0)
                  (smt__TLA__IntMinus
                    smt__CONSTANT_N_
                    (smt__TLA__Cast_Int 1)))
                smt__TLA__BoolSet))
            (smt__TLA__Mem
              smt__VARIABLE_color_
              (smt__TLA__FunSet
                (smt__TLA__IntRange
                  (smt__TLA__Cast_Int 0)
                  (smt__TLA__IntMinus
                    smt__CONSTANT_N_
                    (smt__TLA__Cast_Int 1)))
                (smt__TLA__SetEnum_2
                  smt__TLA__StrLit_white
                  smt__TLA__StrLit_black)))
            (smt__TLA__Mem
              smt__VARIABLE_tpos_
              (smt__TLA__IntRange
                (smt__TLA__Cast_Int 0)
                (smt__TLA__IntMinus
                  smt__CONSTANT_N_
                  (smt__TLA__Cast_Int 1))))
            (smt__TLA__Mem
              smt__VARIABLE_tcolor_
              (smt__TLA__SetEnum_2
                smt__TLA__StrLit_white
                smt__TLA__StrLit_black)))
          (or
            (= smt__ACTION_Next_
              smt__TLA__Tt_Idv)
            (smt__TLA__TrigEq_Idv
              smt__TLA__Anon_OPAQUE_h6fbaa
              smt__STATE_vars_)))
        (and
          (smt__TLA__Mem
            smt__VARIABLE_active__prime
            (smt__TLA__FunSet
              (smt__TLA__IntRange
                (smt__TLA__Cast_Int 0)
                (smt__TLA__IntMinus
                  smt__CONSTANT_N_
                  (smt__TLA__Cast_Int 1)))
              smt__TLA__BoolSet))
          (smt__TLA__Mem
            smt__VARIABLE_color__prime
            (smt__TLA__FunSet
              (smt__TLA__IntRange
                (smt__TLA__Cast_Int 0)
                (smt__TLA__IntMinus
                  smt__CONSTANT_N_
                  (smt__TLA__Cast_Int 1)))
              (smt__TLA__SetEnum_2
                smt__TLA__StrLit_white
                smt__TLA__StrLit_black)))
          (smt__TLA__Mem
            smt__VARIABLE_tpos__prime
            (smt__TLA__IntRange
              (smt__TLA__Cast_Int 0)
              (smt__TLA__IntMinus
                smt__CONSTANT_N_
                (smt__TLA__Cast_Int 1))))
          (smt__TLA__Mem
            smt__VARIABLE_tcolor__prime
            (smt__TLA__SetEnum_2
              smt__TLA__StrLit_white
              smt__TLA__StrLit_black)))))
    :named |Goal|))

(check-sat)
(exit)
