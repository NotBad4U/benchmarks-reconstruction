;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_N_,
;;	       NEW VARIABLE VARIABLE_active_,
;;	       NEW VARIABLE VARIABLE_color_,
;;	       NEW VARIABLE VARIABLE_tpos_,
;;	       NEW VARIABLE VARIABLE_tcolor_,
;;	       CONSTANT_N_ \in Nat \ {0} ,
;;	       /\ VARIABLE_active_ \in [0..CONSTANT_N_ - 1 -> BOOLEAN]
;;	       /\ VARIABLE_color_ \in [0..CONSTANT_N_ - 1 -> {"white", "black"}]
;;	       /\ VARIABLE_tpos_ \in 0..CONSTANT_N_ - 1
;;	       /\ VARIABLE_tcolor_ \in {"white", "black"} ,
;;	       ACTION_Next_ \/ ?h6fbaa = STATE_vars_ ,
;;	       NEW CONSTANT CONSTANT_i_ \in 0..CONSTANT_N_ - 1 \ {0},
;;	       ~VARIABLE_active_[CONSTANT_i_]
;;	       \/ VARIABLE_color_[CONSTANT_i_] = "black"
;;	       \/ VARIABLE_tcolor_ = "black" ,
;;	       VARIABLE_tpos_ = CONSTANT_i_ ,
;;	       ?VARIABLE_tpos_#prime = CONSTANT_i_ - 1 ,
;;	       ?VARIABLE_tcolor_#prime
;;	       = (IF VARIABLE_color_[CONSTANT_i_] = "black"
;;	            THEN "black"
;;	            ELSE VARIABLE_tcolor_) ,
;;	       ?VARIABLE_active_#prime = VARIABLE_active_ ,
;;	       ?VARIABLE_color_#prime
;;	       = [VARIABLE_color_ EXCEPT ![CONSTANT_i_] = "white"] 
;;	PROVE  /\ ?VARIABLE_active_#prime \in [0..CONSTANT_N_ - 1 -> BOOLEAN]
;;	       /\ ?VARIABLE_color_#prime
;;	          \in [0..CONSTANT_N_ - 1 -> {"white", "black"}]
;;	       /\ ?VARIABLE_tpos_#prime \in 0..CONSTANT_N_ - 1
;;	       /\ ?VARIABLE_tcolor_#prime \in {"white", "black"}
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #16
;; Generated from file "./examples/EWD840.tla", line 152, characters 5-6

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA_Anon_OPAQUE_h6fbaa () Idv)

(declare-fun smt__TLA_BoolSet () Idv)

(declare-fun smt__TLA_Cast_Int (Int) Idv)

(declare-fun smt__TLA_FunApp (Idv Idv) Idv)

(declare-fun smt__TLA_FunDom (Idv) Idv)

(declare-fun smt__TLA_FunExcept (Idv Idv Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA_FunIsafcn (Idv) Bool)

(declare-fun smt__TLA_FunSet (Idv Idv) Idv)

(declare-fun smt__TLA_IntLteq (Idv Idv) Bool)

(declare-fun smt__TLA_IntMinus (Idv Idv) Idv)

(declare-fun smt__TLA_IntRange (Idv Idv) Idv)

(declare-fun smt__TLA_IntSet () Idv)

(declare-fun smt__TLA_Mem (Idv Idv) Bool)

(declare-fun smt__TLA_NatSet () Idv)

(declare-fun smt__TLA_Proj_Int (Idv) Int)

(declare-fun smt__TLA_SetEnum_1 (Idv) Idv)

(declare-fun smt__TLA_SetEnum_2 (Idv Idv) Idv)

(declare-fun smt__TLA_SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLA_SetMinus (Idv Idv) Idv)

(declare-fun smt__TLA_StrLit_black () Idv)

(declare-fun smt__TLA_StrLit_white () Idv)

(declare-fun smt__TLA_StrSet () Idv)

(declare-fun smt__TLA_TrigEq_Idv (Idv
  Idv) Bool)

(declare-fun smt__TLA_Tt_Idv () Idv)

;; Axiom: SetExt
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (= (smt__TLA_Mem smt__z smt__x)
              (smt__TLA_Mem smt__z smt__y)))
          (= smt__x smt__y))
        :pattern ((smt__TLA_SetExtTrigger smt__x smt__y))))
    :named |SetExt|))

;; Axiom: SetMinusDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (=
          (smt__TLA_Mem smt__x
            (smt__TLA_SetMinus smt__a smt__b))
          (and (smt__TLA_Mem smt__x smt__a)
            (not (smt__TLA_Mem smt__x smt__b))))
        :pattern ((smt__TLA_Mem smt__x
                    (smt__TLA_SetMinus smt__a smt__b)))
        :pattern ((smt__TLA_Mem smt__x smt__a)
                   (smt__TLA_SetMinus smt__a smt__b))
        :pattern ((smt__TLA_Mem smt__x smt__b)
                   (smt__TLA_SetMinus smt__a smt__b))))
    :named |SetMinusDef|))

;; Axiom: NatSetDef
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=
          (smt__TLA_Mem smt__x
            smt__TLA_NatSet)
          (and
            (smt__TLA_Mem smt__x
              smt__TLA_IntSet)
            (smt__TLA_IntLteq
              (smt__TLA_Cast_Int 0) smt__x)))
        :pattern ((smt__TLA_Mem smt__x
                    smt__TLA_NatSet))))
    :named |NatSetDef|))

;; Axiom: IntRangeDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (=
          (smt__TLA_Mem smt__x
            (smt__TLA_IntRange smt__a smt__b))
          (and
            (smt__TLA_Mem smt__x
              smt__TLA_IntSet)
            (smt__TLA_IntLteq smt__a smt__x)
            (smt__TLA_IntLteq smt__x smt__b)))
        :pattern ((smt__TLA_Mem smt__x
                    (smt__TLA_IntRange smt__a smt__b)))))
    :named |IntRangeDef|))

;; Axiom: FunExt
(assert
  (!
    (forall ((smt__f Idv) (smt__g Idv))
      (!
        (=>
          (and (smt__TLA_FunIsafcn smt__f)
            (smt__TLA_FunIsafcn smt__g)
            (= (smt__TLA_FunDom smt__f)
              (smt__TLA_FunDom smt__g))
            (forall ((smt__x Idv))
              (=>
                (smt__TLA_Mem smt__x
                  (smt__TLA_FunDom smt__f))
                (= (smt__TLA_FunApp smt__f smt__x)
                  (smt__TLA_FunApp smt__g smt__x)))))
          (= smt__f smt__g))
        :pattern ((smt__TLA_FunIsafcn smt__f)
                   (smt__TLA_FunIsafcn smt__g))))
    :named |FunExt|))

; omitted fact (second-order)

;; Axiom: FunSetIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (and (smt__TLA_FunIsafcn smt__f)
            (= (smt__TLA_FunDom smt__f) smt__a)
            (forall ((smt__x Idv))
              (=> (smt__TLA_Mem smt__x smt__a)
                (smt__TLA_Mem
                  (smt__TLA_FunApp smt__f smt__x) 
                  smt__b))))
          (smt__TLA_Mem smt__f
            (smt__TLA_FunSet smt__a smt__b)))
        :pattern ((smt__TLA_Mem smt__f
                    (smt__TLA_FunSet smt__a smt__b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (smt__TLA_Mem smt__f
            (smt__TLA_FunSet smt__a smt__b))
          (and (smt__TLA_FunIsafcn smt__f)
            (= (smt__TLA_FunDom smt__f) smt__a)))
        :pattern ((smt__TLA_Mem smt__f
                    (smt__TLA_FunSet smt__a smt__b)))))
    :named |FunSetElim1|))

;; Axiom: FunSetElim2
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv) (smt__x Idv))
      (!
        (=>
          (and
            (smt__TLA_Mem smt__f
              (smt__TLA_FunSet smt__a smt__b))
            (smt__TLA_Mem smt__x smt__a))
          (smt__TLA_Mem
            (smt__TLA_FunApp smt__f smt__x) smt__b))
        :pattern ((smt__TLA_Mem smt__f
                    (smt__TLA_FunSet smt__a smt__b))
                   (smt__TLA_Mem smt__x smt__a))
        :pattern ((smt__TLA_Mem smt__f
                    (smt__TLA_FunSet smt__a smt__b))
                   (smt__TLA_FunApp smt__f smt__x))))
    :named |FunSetElim2|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: FunExceptIsafcn
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (smt__TLA_FunIsafcn
          (smt__TLA_FunExcept smt__f smt__x smt__y))
        :pattern ((smt__TLA_FunExcept smt__f smt__x
                    smt__y)))) :named |FunExceptIsafcn|))

;; Axiom: FunExceptDomDef
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (=
          (smt__TLA_FunDom
            (smt__TLA_FunExcept smt__f smt__x smt__y))
          (smt__TLA_FunDom smt__f))
        :pattern ((smt__TLA_FunExcept smt__f smt__x
                    smt__y)))) :named |FunExceptDomDef|))

;; Axiom: FunExceptAppDef1
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (=>
          (smt__TLA_Mem smt__x
            (smt__TLA_FunDom smt__f))
          (=
            (smt__TLA_FunApp
              (smt__TLA_FunExcept smt__f smt__x smt__y)
              smt__x) smt__y))
        :pattern ((smt__TLA_FunExcept smt__f smt__x
                    smt__y)))) :named |FunExceptAppDef1|))

;; Axiom: FunExceptAppDef2
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv) (smt__z Idv))
      (!
        (=>
          (smt__TLA_Mem smt__z
            (smt__TLA_FunDom smt__f))
          (and
            (=> (= smt__z smt__x)
              (=
                (smt__TLA_FunApp
                  (smt__TLA_FunExcept smt__f smt__x
                    smt__y) smt__z) smt__y))
            (=> (distinct smt__z smt__x)
              (=
                (smt__TLA_FunApp
                  (smt__TLA_FunExcept smt__f smt__x
                    smt__y) smt__z)
                (smt__TLA_FunApp smt__f smt__z)))))
        :pattern ((smt__TLA_FunApp
                    (smt__TLA_FunExcept smt__f smt__x
                      smt__y) smt__z))
        :pattern ((smt__TLA_FunExcept smt__f smt__x
                    smt__y)
                   (smt__TLA_FunApp smt__f smt__z))))
    :named |FunExceptAppDef2|))

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (!
        (smt__TLA_Mem smt__a1
          (smt__TLA_SetEnum_1 smt__a1))
        :pattern ((smt__TLA_SetEnum_1 smt__a1))))
    :named |EnumDefIntro 1|))

;; Axiom: EnumDefIntro 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv))
      (!
        (and
          (smt__TLA_Mem smt__a1
            (smt__TLA_SetEnum_2 smt__a1
              smt__a2))
          (smt__TLA_Mem smt__a2
            (smt__TLA_SetEnum_2 smt__a1
              smt__a2)))
        :pattern ((smt__TLA_SetEnum_2 
                    smt__a1 smt__a2)))) :named |EnumDefIntro 2|))

;; Axiom: EnumDefElim 1
(assert
  (!
    (forall ((smt__a1 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLA_Mem smt__x
            (smt__TLA_SetEnum_1 smt__a1))
          (= smt__x smt__a1))
        :pattern ((smt__TLA_Mem smt__x
                    (smt__TLA_SetEnum_1
                      smt__a1))))) :named |EnumDefElim 1|))

;; Axiom: EnumDefElim 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLA_Mem smt__x
            (smt__TLA_SetEnum_2 smt__a1
              smt__a2)) (or (= smt__x smt__a1) (= smt__x smt__a2)))
        :pattern ((smt__TLA_Mem smt__x
                    (smt__TLA_SetEnum_2
                      smt__a1 smt__a2))))) :named |EnumDefElim 2|))

;; Axiom: StrLitIsstr black
(assert
  (!
    (smt__TLA_Mem
      smt__TLA_StrLit_black
      smt__TLA_StrSet) :named |StrLitIsstr black|))

;; Axiom: StrLitIsstr white
(assert
  (!
    (smt__TLA_Mem
      smt__TLA_StrLit_white
      smt__TLA_StrSet) :named |StrLitIsstr white|))

;; Axiom: StrLitDistinct black white
(assert
  (!
    (distinct smt__TLA_StrLit_black
      smt__TLA_StrLit_white)
    :named |StrLitDistinct black white|))

;; Axiom: CastInjAlt Int
(assert
  (!
    (forall ((smt__x Int))
      (!
        (= smt__x
          (smt__TLA_Proj_Int
            (smt__TLA_Cast_Int smt__x)))
        :pattern ((smt__TLA_Cast_Int smt__x))))
    :named |CastInjAlt Int|))

;; Axiom: TypeGuardIntro Int
(assert
  (!
    (forall ((smt__z Int))
      (!
        (smt__TLA_Mem
          (smt__TLA_Cast_Int smt__z)
          smt__TLA_IntSet)
        :pattern ((smt__TLA_Cast_Int smt__z))))
    :named |TypeGuardIntro Int|))

;; Axiom: TypeGuardElim Int
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=>
          (smt__TLA_Mem smt__x
            smt__TLA_IntSet)
          (= smt__x
            (smt__TLA_Cast_Int
              (smt__TLA_Proj_Int smt__x))))
        :pattern ((smt__TLA_Mem smt__x
                    smt__TLA_IntSet))))
    :named |TypeGuardElim Int|))

;; Axiom: Typing TIntMinus
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLA_IntMinus
            (smt__TLA_Cast_Int smt__x1)
            (smt__TLA_Cast_Int smt__x2))
          (smt__TLA_Cast_Int
            (- smt__x1 smt__x2)))
        :pattern ((smt__TLA_IntMinus
                    (smt__TLA_Cast_Int smt__x1)
                    (smt__TLA_Cast_Int smt__x2)))))
    :named |Typing TIntMinus|))

;; Axiom: Typing TIntLteq
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLA_IntLteq
            (smt__TLA_Cast_Int smt__x1)
            (smt__TLA_Cast_Int smt__x2))
          (<= smt__x1 smt__x2))
        :pattern ((smt__TLA_IntLteq
                    (smt__TLA_Cast_Int smt__x1)
                    (smt__TLA_Cast_Int smt__x2)))))
    :named |Typing TIntLteq|))

;; Axiom: ExtTrigEqDef Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (= (smt__TLA_TrigEq_Idv smt__x smt__y)
          (= smt__x smt__y))
        :pattern ((smt__TLA_TrigEq_Idv 
                    smt__x smt__y)))) :named |ExtTrigEqDef Idv|))

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

(declare-fun smt__CONSTANT_N_ () Idv)

; hidden fact

(declare-fun smt__VARIABLE_active_ () Idv)

(declare-fun smt__VARIABLE_active_prime () Idv)

(declare-fun smt__VARIABLE_color_ () Idv)

(declare-fun smt__VARIABLE_color_prime () Idv)

(declare-fun smt__VARIABLE_tpos_ () Idv)

(declare-fun smt__VARIABLE_tpos_prime () Idv)

(declare-fun smt__VARIABLE_tcolor_ () Idv)

(declare-fun smt__VARIABLE_tcolor_prime () Idv)

(declare-fun smt__STATE_Init_ () Idv)

(declare-fun smt__ACTION_InitiateProbe_ () Idv)

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
  (smt__TLA_Mem smt__CONSTANT_N_
    (smt__TLA_SetMinus
      smt__TLA_NatSet
      (smt__TLA_SetEnum_1
        (smt__TLA_Cast_Int 0)))))

; hidden fact

; hidden fact

; hidden fact

(assert
  (and
    (smt__TLA_Mem
      smt__VARIABLE_active_
      (smt__TLA_FunSet
        (smt__TLA_IntRange
          (smt__TLA_Cast_Int 0)
          (smt__TLA_IntMinus
            smt__CONSTANT_N_
            (smt__TLA_Cast_Int 1)))
        smt__TLA_BoolSet))
    (smt__TLA_Mem
      smt__VARIABLE_color_
      (smt__TLA_FunSet
        (smt__TLA_IntRange
          (smt__TLA_Cast_Int 0)
          (smt__TLA_IntMinus
            smt__CONSTANT_N_
            (smt__TLA_Cast_Int 1)))
        (smt__TLA_SetEnum_2
          smt__TLA_StrLit_white
          smt__TLA_StrLit_black)))
    (smt__TLA_Mem
      smt__VARIABLE_tpos_
      (smt__TLA_IntRange
        (smt__TLA_Cast_Int 0)
        (smt__TLA_IntMinus
          smt__CONSTANT_N_
          (smt__TLA_Cast_Int 1))))
    (smt__TLA_Mem
      smt__VARIABLE_tcolor_
      (smt__TLA_SetEnum_2
        smt__TLA_StrLit_white
        smt__TLA_StrLit_black))))

(assert
  (or
    (= smt__ACTION_Next_
      smt__TLA_Tt_Idv)
    (smt__TLA_TrigEq_Idv
      smt__TLA_Anon_OPAQUE_h6fbaa
      smt__STATE_vars_)))

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANT_i () Idv)

(assert
  (smt__TLA_Mem smt__CONSTANT_i
    (smt__TLA_SetMinus
      (smt__TLA_IntRange
        (smt__TLA_Cast_Int 0)
        (smt__TLA_IntMinus
          smt__CONSTANT_N_
          (smt__TLA_Cast_Int 1)))
      (smt__TLA_SetEnum_1
        (smt__TLA_Cast_Int 0)))))

; hidden fact

; hidden fact

; hidden fact

(assert
  (or
    (or
      (not
        (=
          (smt__TLA_FunApp
            smt__VARIABLE_active_
            smt__CONSTANT_i)
          smt__TLA_Tt_Idv))
      (smt__TLA_TrigEq_Idv
        (smt__TLA_FunApp
          smt__VARIABLE_color_
          smt__CONSTANT_i)
        smt__TLA_StrLit_black))
    (smt__TLA_TrigEq_Idv
      smt__VARIABLE_tcolor_
      smt__TLA_StrLit_black)))

(assert
  (smt__TLA_TrigEq_Idv
    smt__VARIABLE_tpos_
    smt__CONSTANT_i))

(assert
  (smt__TLA_TrigEq_Idv
    smt__VARIABLE_tpos_prime
    (smt__TLA_IntMinus
      smt__CONSTANT_i
      (smt__TLA_Cast_Int 1))))

(assert
  (smt__TLA_TrigEq_Idv
    smt__VARIABLE_tcolor_prime
    (ite
      (smt__TLA_TrigEq_Idv
        (smt__TLA_FunApp
          smt__VARIABLE_color_
          smt__CONSTANT_i)
        smt__TLA_StrLit_black)
      smt__TLA_StrLit_black
      smt__VARIABLE_tcolor_)))

(assert
  (smt__TLA_TrigEq_Idv
    smt__VARIABLE_active_prime
    smt__VARIABLE_active_))

(assert
  (smt__TLA_TrigEq_Idv
    smt__VARIABLE_color_prime
    (smt__TLA_FunExcept
      smt__VARIABLE_color_
      smt__CONSTANT_i
      smt__TLA_StrLit_white)))

;; Goal
(assert
  (!
    (not
      (and
        (smt__TLA_Mem
          smt__VARIABLE_active_prime
          (smt__TLA_FunSet
            (smt__TLA_IntRange
              (smt__TLA_Cast_Int 0)
              (smt__TLA_IntMinus
                smt__CONSTANT_N_
                (smt__TLA_Cast_Int 1)))
            smt__TLA_BoolSet))
        (smt__TLA_Mem
          smt__VARIABLE_color_prime
          (smt__TLA_FunSet
            (smt__TLA_IntRange
              (smt__TLA_Cast_Int 0)
              (smt__TLA_IntMinus
                smt__CONSTANT_N_
                (smt__TLA_Cast_Int 1)))
            (smt__TLA_SetEnum_2
              smt__TLA_StrLit_white
              smt__TLA_StrLit_black)))
        (smt__TLA_Mem
          smt__VARIABLE_tpos_prime
          (smt__TLA_IntRange
            (smt__TLA_Cast_Int 0)
            (smt__TLA_IntMinus
              smt__CONSTANT_N_
              (smt__TLA_Cast_Int 1))))
        (smt__TLA_Mem
          smt__VARIABLE_tcolor_prime
          (smt__TLA_SetEnum_2
            smt__TLA_StrLit_white
            smt__TLA_StrLit_black))))
    :named |Goal|))

(check-sat)
(exit)
