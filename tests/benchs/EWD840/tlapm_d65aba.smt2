;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_N_,
;;	       NEW VARIABLE VARIABLE_active_,
;;	       NEW VARIABLE VARIABLE_color_,
;;	       NEW VARIABLE VARIABLE_tpos_,
;;	       NEW VARIABLE VARIABLE_tcolor_,
;;	       NEW CONSTANT CONSTANT_i_ \in 0..CONSTANT_N_ - 1,
;;	       ASSUME CONSTANT_i_ = 0 
;;	       PROVE  ~VARIABLE_active_[CONSTANT_i_] ,
;;	       ASSUME CONSTANT_i_ \in 1..CONSTANT_N_ - 1 
;;	       PROVE  ~VARIABLE_active_[CONSTANT_i_] 
;;	PROVE  ~VARIABLE_active_[CONSTANT_i_]
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #36
;; Generated from file "./examples/EWD840.tla", line 217, characters 15-16

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun TLA_Cast_Int (Int) Idv)

(declare-fun TLA_FunApp (Idv Idv) Idv)

(declare-fun TLA_FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun TLA_FunIsafcn (Idv) Bool)

(declare-fun TLA_IntLteq (Idv Idv) Bool)

(declare-fun TLA_IntMinus (Idv Idv) Idv)

(declare-fun TLA_IntRange (Idv Idv) Idv)

(declare-fun TLA_IntSet () Idv)

(declare-fun TLA_Mem (Idv Idv) Bool)

(declare-fun TLA_Proj_Int (Idv) Int)

(declare-fun TLA_SetExtTrigger (Idv Idv) Bool)

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

;; Axiom: IntRangeDef
(assert
  (!
    (forall ((a Idv) (b Idv) (x Idv))
      (!
        (=
          (TLA_Mem x
            (TLA_IntRange a b))
          (and
            (TLA_Mem x
              TLA_IntSet)
            (TLA_IntLteq a x)
            (TLA_IntLteq x b)))
        :pattern ((TLA_Mem x
                    (TLA_IntRange a b)))))
    :named |IntRangeDef|))

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

;; Axiom: Typing TIntMinus
(assert
  (!
    (forall ((x1 Int) (x2 Int))
      (!
        (=
          (TLA_IntMinus
            (TLA_Cast_Int x1)
            (TLA_Cast_Int x2))
          (TLA_Cast_Int
            (- x1 x2)))
        :pattern ((TLA_IntMinus
                    (TLA_Cast_Int x1)
                    (TLA_Cast_Int x2)))))
    :named |Typing TIntMinus|))

;; Axiom: Typing TIntLteq
(assert
  (!
    (forall ((x1 Int) (x2 Int))
      (!
        (=
          (TLA_IntLteq
            (TLA_Cast_Int x1)
            (TLA_Cast_Int x2))
          (<= x1 x2))
        :pattern ((TLA_IntLteq
                    (TLA_Cast_Int x1)
                    (TLA_Cast_Int x2)))))
    :named |Typing TIntLteq|))

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

; hidden fact

(declare-fun CONSTANT_i_ () Idv)

(assert
  (TLA_Mem CONSTANT_i_
    (TLA_IntRange
      (TLA_Cast_Int 0)
      (TLA_IntMinus
        CONSTANT_N_
        (TLA_Cast_Int 1)))))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (=>
    (TLA_TrigEq_Idv
      CONSTANT_i_
      (TLA_Cast_Int 0))
    (not
      (=
        (TLA_FunApp
          VARIABLE_active_
          CONSTANT_i_)
        TLA_Tt_Idv))))

(assert
  (=>
    (TLA_Mem CONSTANT_i_
      (TLA_IntRange
        (TLA_Cast_Int 1)
        (TLA_IntMinus
          CONSTANT_N_
          (TLA_Cast_Int 1))))
    (not
      (=
        (TLA_FunApp
          VARIABLE_active_
          CONSTANT_i_)
        TLA_Tt_Idv))))

;; Goal
(assert
  (!
    (not
      (not
        (=
          (TLA_FunApp
            VARIABLE_active_
            CONSTANT_i_)
          TLA_Tt_Idv))) :named |Goal|))

(check-sat)
(exit)