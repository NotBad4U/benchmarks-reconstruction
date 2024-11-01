;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_N_,
;;	       NEW VARIABLE VARIABLE_active_,
;;	       NEW VARIABLE VARIABLE_color_,
;;	       NEW VARIABLE VARIABLE_tpos_,
;;	       NEW VARIABLE VARIABLE_tcolor_,
;;	       /\ ~VARIABLE_active_[0]
;;	       /\ STATE_Inv_ ,
;;	       VARIABLE_tpos_ = 0 ,
;;	       VARIABLE_tcolor_ = "white" ,
;;	       VARIABLE_color_[0] = "white" 
;;	PROVE  ~VARIABLE_tcolor_ = "black"
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #39
;; Generated from file "./examples/EWD840.tla", line 203, characters 9-10

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLA_Cast_Int (Int) Idv)

(declare-fun smt__TLA_FunApp (Idv Idv) Idv)

(declare-fun smt__TLA_FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLA_FunIsafcn (Idv) Bool)

(declare-fun smt__TLA_IntSet () Idv)

(declare-fun smt__TLA_Mem (Idv Idv) Bool)

(declare-fun smt__TLA_Proj_Int (Idv) Int)

(declare-fun smt__TLA_SetExtTrigger (Idv Idv) Bool)

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

; omitted fact (second-order)

; omitted fact (second-order)

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

(declare-fun smt__CONSTANT_Nodes_ () Idv)

(declare-fun smt__CONSTANT_Color_ () Idv)

(declare-fun smt__STATE_TypeOK_ () Idv)

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

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (and
    (not
      (=
        (smt__TLA_FunApp
          smt__VARIABLE_active_
          (smt__TLA_Cast_Int 0))
        smt__TLA_Tt_Idv))
    (= smt__STATE_Inv_
      smt__TLA_Tt_Idv)))

(assert
  (smt__TLA_TrigEq_Idv
    smt__VARIABLE_tpos_
    (smt__TLA_Cast_Int 0)))

(assert
  (smt__TLA_TrigEq_Idv
    smt__VARIABLE_tcolor_
    smt__TLA_StrLit_white))

(assert
  (smt__TLA_TrigEq_Idv
    (smt__TLA_FunApp
      smt__VARIABLE_color_
      (smt__TLA_Cast_Int 0))
    smt__TLA_StrLit_white))

;; Goal
(assert
  (!
    (not
      (not
        (smt__TLA_TrigEq_Idv
          smt__VARIABLE_tcolor_
          smt__TLA_StrLit_black)))
    :named |Goal|))

(check-sat)
(exit)
