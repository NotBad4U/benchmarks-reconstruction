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

(declare-fun TLA_Cast_Int (Int) Idv)

(declare-fun TLA_FunApp (Idv Idv) Idv)

(declare-fun TLA_FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun TLA_FunIsafcn (Idv) Bool)

(declare-fun TLA_IntSet () Idv)

(declare-fun TLA_Mem (Idv Idv) Bool)

(declare-fun TLA_Proj_Int (Idv) Int)

(declare-fun TLA_SetExtTrigger (Idv Idv) Bool)

(declare-fun TLA_StrLit_black () Idv)

(declare-fun TLA_StrLit_white () Idv)

(declare-fun TLA_StrSet () Idv)

(declare-fun TLA_TrigEq_Idv (Idv
  Idv) Bool)

(declare-fun TLA_Tt_Idv () Idv)

;; Axiom: SetExt
(assert
  (!
    (forall ((x Idv) (y Idv))
      (!
        (=>
          (forall ((z Idv))
            (= (TLA_Mem z x)
              (TLA_Mem z y)))
          (= x y))
        :pattern ((TLA_SetExtTrigger x y))))
    :named |SetExt|))

;; Axiom: FunExt
(assert
  (!
    (forall ((f Idv) (g Idv))
      (!
        (=>
          (and (TLA_FunIsafcn f)
            (TLA_FunIsafcn g)
            (= (TLA_FunDom f)
              (TLA_FunDom g))
            (forall ((x Idv))
              (=>
                (TLA_Mem x
                  (TLA_FunDom f))
                (= (TLA_FunApp f x)
                  (TLA_FunApp g x)))))
          (= f g))
        :pattern ((TLA_FunIsafcn f)
                   (TLA_FunIsafcn g))))
    :named |FunExt|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: StrLitIsstr black
(assert
  (!
    (TLA_Mem
      TLA_StrLit_black
      TLA_StrSet) :named |StrLitIsstr black|))

;; Axiom: StrLitIsstr white
(assert
  (!
    (TLA_Mem
      TLA_StrLit_white
      TLA_StrSet) :named |StrLitIsstr white|))

;; Axiom: StrLitDistinct black white
(assert
  (!
    (distinct TLA_StrLit_black
      TLA_StrLit_white)
    :named |StrLitDistinct black white|))

;; Axiom: CastInjAlt Int
(assert
  (!
    (forall ((x Int))
      (!
        (= x
          (TLA_Proj_Int
            (TLA_Cast_Int x)))
        :pattern ((TLA_Cast_Int x))))
    :named |CastInjAlt Int|))

;; Axiom: TypeGuardIntro Int
(assert
  (!
    (forall ((z Int))
      (!
        (TLA_Mem
          (TLA_Cast_Int z)
          TLA_IntSet)
        :pattern ((TLA_Cast_Int z))))
    :named |TypeGuardIntro Int|))

;; Axiom: TypeGuardElim Int
(assert
  (!
    (forall ((x Idv))
      (!
        (=>
          (TLA_Mem x
            TLA_IntSet)
          (= x
            (TLA_Cast_Int
              (TLA_Proj_Int x))))
        :pattern ((TLA_Mem x
                    TLA_IntSet))))
    :named |TypeGuardElim Int|))

;; Axiom: ExtTrigEqDef Idv
(assert
  (!
    (forall ((x Idv) (y Idv))
      (!
        (= (TLA_TrigEq_Idv x y)
          (= x y))
        :pattern ((TLA_TrigEq_Idv 
                    x y)))) :named |ExtTrigEqDef Idv|))

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

(declare-fun CONSTANT_N_ () Idv)

; hidden fact

(declare-fun VARIABLE_active_ () Idv)

(declare-fun VARIABLE_active_prime () Idv)

(declare-fun VARIABLE_color_ () Idv)

(declare-fun VARIABLE_color_prime () Idv)

(declare-fun VARIABLE_tpos_ () Idv)

(declare-fun VARIABLE_tpos_prime () Idv)

(declare-fun VARIABLE_tcolor_ () Idv)

(declare-fun VARIABLE_tcolor_prime () Idv)

(declare-fun CONSTANT_Nodes_ () Idv)

(declare-fun CONSTANT_Color_ () Idv)

(declare-fun STATE_TypeOK_ () Idv)

(declare-fun STATE_Init_ () Idv)

(declare-fun ACTION_InitiateProbe_ () Idv)

(declare-fun ACTION_PassToken_ (Idv) Idv)

(declare-fun ACTION_SendMsg_ (Idv) Idv)

(declare-fun ACTION_Deactivate_ (Idv) Idv)

(declare-fun ACTION_Controlled_ () Idv)

(declare-fun ACTION_Environment_ () Idv)

(declare-fun ACTION_Next_ () Idv)

(declare-fun STATE_vars_ () Idv)

(declare-fun TEMPORAL_Fairness_ () Idv)

(declare-fun TEMPORAL_Spec_ () Idv)

(declare-fun STATE_NeverBlack_ () Idv)

(declare-fun TEMPORAL_NeverChangeColor_ () Idv)

(declare-fun STATE_terminationDetected_ () Idv)

(declare-fun STATE_TerminationDetection_ () Idv)

(declare-fun TEMPORAL_Liveness_ () Idv)

(declare-fun TEMPORAL_AllNodesTerminateIfNoMessages_ () Idv)

(declare-fun STATE_Inv_ () Idv)

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
        (TLA_FunApp
          VARIABLE_active_
          (TLA_Cast_Int 0))
        TLA_Tt_Idv))
    (= STATE_Inv_
      TLA_Tt_Idv)))

(assert
  (TLA_TrigEq_Idv
    VARIABLE_tpos_
    (TLA_Cast_Int 0)))

(assert
  (TLA_TrigEq_Idv
    VARIABLE_tcolor_
    TLA_StrLit_white))

(assert
  (TLA_TrigEq_Idv
    (TLA_FunApp
      VARIABLE_color_
      (TLA_Cast_Int 0))
    TLA_StrLit_white))

;; Goal
(assert
  (!
    (not
      (not
        (TLA_TrigEq_Idv
          VARIABLE_tcolor_
          TLA_StrLit_black)))
    :named |Goal|))

(check-sat)
(exit)