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

(declare-fun TLA_Anon_OPAQUE_h6fbaa () Idv)

(declare-fun TLA_BoolSet () Idv)

(declare-fun TLA_Cast_Int (Int) Idv)

(declare-fun TLA_FunApp (Idv Idv) Idv)

(declare-fun TLA_FunDom (Idv) Idv)

(declare-fun TLA_FunExcept (Idv Idv Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun TLA_FunIsafcn (Idv) Bool)

(declare-fun TLA_FunSet (Idv Idv) Idv)

(declare-fun TLA_IntLteq (Idv Idv) Bool)

(declare-fun TLA_IntMinus (Idv Idv) Idv)

(declare-fun TLA_IntRange (Idv Idv) Idv)

(declare-fun TLA_IntSet () Idv)

(declare-fun TLA_Mem (Idv Idv) Bool)

(declare-fun TLA_NatSet () Idv)

(declare-fun TLA_Proj_Int (Idv) Int)

(declare-fun TLA_SetEnum_1 (Idv) Idv)

(declare-fun TLA_SetEnum_2 (Idv Idv) Idv)

(declare-fun TLA_SetExtTrigger (Idv Idv) Bool)

(declare-fun TLA_SetMinus (Idv Idv) Idv)

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

;; Axiom: SetMinusDef
(assert
  (!
    (forall ((a Idv) (b Idv) (x Idv))
      (!
        (=
          (TLA_Mem x
            (TLA_SetMinus a b))
          (and (TLA_Mem x a)
            (not (TLA_Mem x b))))
        :pattern ((TLA_Mem x
                    (TLA_SetMinus a b)))
        :pattern ((TLA_Mem x a)
                   (TLA_SetMinus a b))
        :pattern ((TLA_Mem x b)
                   (TLA_SetMinus a b))))
    :named |SetMinusDef|))

;; Axiom: NatSetDef
(assert
  (!
    (forall ((x Idv))
      (!
        (=
          (TLA_Mem x
            TLA_NatSet)
          (and
            (TLA_Mem x
              TLA_IntSet)
            (TLA_IntLteq
              (TLA_Cast_Int 0) x)))
        :pattern ((TLA_Mem x
                    TLA_NatSet))))
    :named |NatSetDef|))

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

;; Axiom: FunSetIntro
(assert
  (!
    (forall ((a Idv) (b Idv) (f Idv))
      (!
        (=>
          (and (TLA_FunIsafcn f)
            (= (TLA_FunDom f) a)
            (forall ((x Idv))
              (=> (TLA_Mem x a)
                (TLA_Mem
                  (TLA_FunApp f x) 
                  b))))
          (TLA_Mem f
            (TLA_FunSet a b)))
        :pattern ((TLA_Mem f
                    (TLA_FunSet a b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((a Idv) (b Idv) (f Idv))
      (!
        (=>
          (TLA_Mem f
            (TLA_FunSet a b))
          (and (TLA_FunIsafcn f)
            (= (TLA_FunDom f) a)))
        :pattern ((TLA_Mem f
                    (TLA_FunSet a b)))))
    :named |FunSetElim1|))

;; Axiom: FunSetElim2
(assert
  (!
    (forall ((a Idv) (b Idv) (f Idv) (x Idv))
      (!
        (=>
          (and
            (TLA_Mem f
              (TLA_FunSet a b))
            (TLA_Mem x a))
          (TLA_Mem
            (TLA_FunApp f x) b))
        :pattern ((TLA_Mem f
                    (TLA_FunSet a b))
                   (TLA_Mem x a))
        :pattern ((TLA_Mem f
                    (TLA_FunSet a b))
                   (TLA_FunApp f x))))
    :named |FunSetElim2|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: FunExceptIsafcn
(assert
  (!
    (forall ((f Idv) (x Idv) (y Idv))
      (!
        (TLA_FunIsafcn
          (TLA_FunExcept f x y))
        :pattern ((TLA_FunExcept f x
                    y)))) :named |FunExceptIsafcn|))

;; Axiom: FunExceptDomDef
(assert
  (!
    (forall ((f Idv) (x Idv) (y Idv))
      (!
        (=
          (TLA_FunDom
            (TLA_FunExcept f x y))
          (TLA_FunDom f))
        :pattern ((TLA_FunExcept f x
                    y)))) :named |FunExceptDomDef|))

;; Axiom: FunExceptAppDef1
(assert
  (!
    (forall ((f Idv) (x Idv) (y Idv))
      (!
        (=>
          (TLA_Mem x
            (TLA_FunDom f))
          (=
            (TLA_FunApp
              (TLA_FunExcept f x y)
              x) y))
        :pattern ((TLA_FunExcept f x
                    y)))) :named |FunExceptAppDef1|))

;; Axiom: FunExceptAppDef2
(assert
  (!
    (forall ((f Idv) (x Idv) (y Idv) (z Idv))
      (!
        (=>
          (TLA_Mem z
            (TLA_FunDom f))
          (and
            (=> (= z x)
              (=
                (TLA_FunApp
                  (TLA_FunExcept f x
                    y) z) y))
            (=> (distinct z x)
              (=
                (TLA_FunApp
                  (TLA_FunExcept f x
                    y) z)
                (TLA_FunApp f z)))))
        :pattern ((TLA_FunApp
                    (TLA_FunExcept f x
                      y) z))
        :pattern ((TLA_FunExcept f x
                    y)
                   (TLA_FunApp f z))))
    :named |FunExceptAppDef2|))

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((a1 Idv))
      (!
        (TLA_Mem a1
          (TLA_SetEnum_1 a1))
        :pattern ((TLA_SetEnum_1 a1))))
    :named |EnumDefIntro 1|))

;; Axiom: EnumDefIntro 2
(assert
  (!
    (forall ((a1 Idv) (a2 Idv))
      (!
        (and
          (TLA_Mem a1
            (TLA_SetEnum_2 a1
              a2))
          (TLA_Mem a2
            (TLA_SetEnum_2 a1
              a2)))
        :pattern ((TLA_SetEnum_2 
                    a1 a2)))) :named |EnumDefIntro 2|))

;; Axiom: EnumDefElim 1
(assert
  (!
    (forall ((a1 Idv) (x Idv))
      (!
        (=>
          (TLA_Mem x
            (TLA_SetEnum_1 a1))
          (= x a1))
        :pattern ((TLA_Mem x
                    (TLA_SetEnum_1
                      a1))))) :named |EnumDefElim 1|))

;; Axiom: EnumDefElim 2
(assert
  (!
    (forall ((a1 Idv) (a2 Idv) (x Idv))
      (!
        (=>
          (TLA_Mem x
            (TLA_SetEnum_2 a1
              a2)) (or (= x a1) (= x a2)))
        :pattern ((TLA_Mem x
                    (TLA_SetEnum_2
                      a1 a2))))) :named |EnumDefElim 2|))

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

(declare-fun STATE_Init_ () Idv)

(declare-fun ACTION_InitiateProbe_ () Idv)

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

(assert
  (TLA_Mem CONSTANT_N_
    (TLA_SetMinus
      TLA_NatSet
      (TLA_SetEnum_1
        (TLA_Cast_Int 0)))))

; hidden fact

; hidden fact

; hidden fact

(assert
  (and
    (TLA_Mem
      VARIABLE_active_
      (TLA_FunSet
        (TLA_IntRange
          (TLA_Cast_Int 0)
          (TLA_IntMinus
            CONSTANT_N_
            (TLA_Cast_Int 1)))
        TLA_BoolSet))
    (TLA_Mem
      VARIABLE_color_
      (TLA_FunSet
        (TLA_IntRange
          (TLA_Cast_Int 0)
          (TLA_IntMinus
            CONSTANT_N_
            (TLA_Cast_Int 1)))
        (TLA_SetEnum_2
          TLA_StrLit_white
          TLA_StrLit_black)))
    (TLA_Mem
      VARIABLE_tpos_
      (TLA_IntRange
        (TLA_Cast_Int 0)
        (TLA_IntMinus
          CONSTANT_N_
          (TLA_Cast_Int 1))))
    (TLA_Mem
      VARIABLE_tcolor_
      (TLA_SetEnum_2
        TLA_StrLit_white
        TLA_StrLit_black))))

(assert
  (or
    (= ACTION_Next_
      TLA_Tt_Idv)
    (TLA_TrigEq_Idv
      TLA_Anon_OPAQUE_h6fbaa
      STATE_vars_)))

; hidden fact

; hidden fact

; hidden fact

(declare-fun CONSTANT_i_ () Idv)

(assert
  (TLA_Mem CONSTANT_i_
    (TLA_SetMinus
      (TLA_IntRange
        (TLA_Cast_Int 0)
        (TLA_IntMinus
          CONSTANT_N_
          (TLA_Cast_Int 1)))
      (TLA_SetEnum_1
        (TLA_Cast_Int 0)))))

; hidden fact

; hidden fact

; hidden fact

(assert
  (or
    (or
      (not
        (=
          (TLA_FunApp
            VARIABLE_active_
            CONSTANT_i_)
          TLA_Tt_Idv))
      (TLA_TrigEq_Idv
        (TLA_FunApp
          VARIABLE_color_
          CONSTANT_i_)
        TLA_StrLit_black))
    (TLA_TrigEq_Idv
      VARIABLE_tcolor_
      TLA_StrLit_black)))

(assert
  (TLA_TrigEq_Idv
    VARIABLE_tpos_
    CONSTANT_i_))

(assert
  (TLA_TrigEq_Idv
    VARIABLE_tpos_prime
    (TLA_IntMinus
      CONSTANT_i_
      (TLA_Cast_Int 1))))

(assert
  (TLA_TrigEq_Idv
    VARIABLE_tcolor_prime
    (ite
      (TLA_TrigEq_Idv
        (TLA_FunApp
          VARIABLE_color_
          CONSTANT_i_)
        TLA_StrLit_black)
      TLA_StrLit_black
      VARIABLE_tcolor_)))

(assert
  (TLA_TrigEq_Idv
    VARIABLE_active_prime
    VARIABLE_active_))

(assert
  (TLA_TrigEq_Idv
    VARIABLE_color_prime
    (TLA_FunExcept
      VARIABLE_color_
      CONSTANT_i_
      TLA_StrLit_white)))

;; Goal
(assert
  (!
    (not
      (and
        (TLA_Mem
          VARIABLE_active_prime
          (TLA_FunSet
            (TLA_IntRange
              (TLA_Cast_Int 0)
              (TLA_IntMinus
                CONSTANT_N_
                (TLA_Cast_Int 1)))
            TLA_BoolSet))
        (TLA_Mem
          VARIABLE_color_prime
          (TLA_FunSet
            (TLA_IntRange
              (TLA_Cast_Int 0)
              (TLA_IntMinus
                CONSTANT_N_
                (TLA_Cast_Int 1)))
            (TLA_SetEnum_2
              TLA_StrLit_white
              TLA_StrLit_black)))
        (TLA_Mem
          VARIABLE_tpos_prime
          (TLA_IntRange
            (TLA_Cast_Int 0)
            (TLA_IntMinus
              CONSTANT_N_
              (TLA_Cast_Int 1))))
        (TLA_Mem
          VARIABLE_tcolor_prime
          (TLA_SetEnum_2
            TLA_StrLit_white
            TLA_StrLit_black))))
    :named |Goal|))

(check-sat)
(exit)
