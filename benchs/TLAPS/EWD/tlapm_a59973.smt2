;; Proof obligation:
;;	ASSUME NEW CONSTANT CST_N_,
;;	       NEW VARIABLE VAR_active_,
;;	       NEW VARIABLE VAR_color_,
;;	       NEW VARIABLE VAR_tpos_,
;;	       NEW VARIABLE VAR_tcolor_,
;;	       CST_N_ \in Nat \ {0} ,
;;	       /\ VAR_active_ \in [0..CST_N_ - 1 -> BOOLEAN]
;;	       /\ VAR_color_ \in [0..CST_N_ - 1 -> {"white", "black"}]
;;	       /\ VAR_tpos_ \in 0..CST_N_ - 1
;;	       /\ VAR_tcolor_ \in {"white", "black"} ,
;;	       ACTION_Next_ \/ ?h6fbaa = STATE_vars_ ,
;;	       NEW CONSTANT CST_i_ \in 0..CST_N_ - 1,
;;	       VAR_active_[CST_i_] ,
;;	       ?VAR_active_#prime
;;	       = [VAR_active_ EXCEPT ![CST_i_] = FALSE] ,
;;	       ?VAR_color_#prime = VAR_color_ ,
;;	       ?VAR_tpos_#prime = VAR_tpos_ ,
;;	       ?VAR_tcolor_#prime = VAR_tcolor_ 
;;	PROVE  /\ ?VAR_active_#prime \in [0..CST_N_ - 1 -> BOOLEAN]
;;	       /\ ?VAR_color_#prime
;;	          \in [0..CST_N_ - 1 -> {"white", "black"}]
;;	       /\ ?VAR_tpos_#prime \in 0..CST_N_ - 1
;;	       /\ ?VAR_tcolor_#prime \in {"white", "black"}
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #18
;; Generated from file "./examples/EWD840.tla", line 156, characters 5-6

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun Anon_OPAQUE_h6fbaa () Idv)

(declare-fun BoolSet () Idv)

(declare-fun Cast_Bool (Bool) Idv)

(declare-fun Cast_Int (Int) Idv)

(declare-fun FunApp (Idv Idv) Idv)

(declare-fun FunDom (Idv) Idv)

(declare-fun FunExcept (Idv Idv Idv) Idv)

; omitted declaration of '_FunFcn' (second-order)

(declare-fun FunIsafcn (Idv) Bool)

(declare-fun FunSet (Idv Idv) Idv)

(declare-fun IntLteq (Idv Idv) Bool)

(declare-fun IntMinus (Idv Idv) Idv)

(declare-fun IntRange (Idv Idv) Idv)

(declare-fun IntSet () Idv)

(declare-fun Mem (Idv Idv) Bool)

(declare-fun NatSet () Idv)

(declare-fun Proj_Int (Idv) Int)

(declare-fun SetEnum_1 (Idv) Idv)

(declare-fun SetEnum_2 (Idv Idv) Idv)

(declare-fun SetExtTrigger (Idv Idv) Bool)

(declare-fun SetMinus (Idv Idv) Idv)

(declare-fun StrLit_black () Idv)

(declare-fun StrLit_white () Idv)

(declare-fun StrSet () Idv)

(declare-fun TrigEq_Idv (Idv
  Idv) Bool)

(declare-fun Tt_Idv () Idv)

;; Axiom: SetExt
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (= (Mem smt__z smt__x)
              (Mem smt__z smt__y)))
          (= smt__x smt__y))
        :pattern ((SetExtTrigger smt__x smt__y))))
    :named |SetExt|))

;; Axiom: SetMinusDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (=
          (Mem smt__x
            (SetMinus smt__a smt__b))
          (and (Mem smt__x smt__a)
            (not (Mem smt__x smt__b))))
        :pattern ((Mem smt__x
                    (SetMinus smt__a smt__b)))
        :pattern ((Mem smt__x smt__a)
                   (SetMinus smt__a smt__b))
        :pattern ((Mem smt__x smt__b)
                   (SetMinus smt__a smt__b))))
    :named |SetMinusDef|))

;; Axiom: NatSetDef
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=
          (Mem smt__x
            NatSet)
          (and
            (Mem smt__x
              IntSet)
            (IntLteq
              (Cast_Int 0) smt__x)))
        :pattern ((Mem smt__x
                    NatSet))))
    :named |NatSetDef|))

;; Axiom: IntRangeDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (=
          (Mem smt__x
            (IntRange smt__a smt__b))
          (and
            (Mem smt__x
              IntSet)
            (IntLteq smt__a smt__x)
            (IntLteq smt__x smt__b)))
        :pattern ((Mem smt__x
                    (IntRange smt__a smt__b)))))
    :named |IntRangeDef|))

;; Axiom: FunExt
(assert
  (!
    (forall ((smt__f Idv) (smt__g Idv))
      (!
        (=>
          (and (FunIsafcn smt__f)
            (FunIsafcn smt__g)
            (= (FunDom smt__f)
              (FunDom smt__g))
            (forall ((smt__x Idv))
              (=>
                (Mem smt__x
                  (FunDom smt__f))
                (= (FunApp smt__f smt__x)
                  (FunApp smt__g smt__x)))))
          (= smt__f smt__g))
        :pattern ((FunIsafcn smt__f)
                   (FunIsafcn smt__g))))
    :named |FunExt|))

; omitted fact (second-order)

;; Axiom: FunSetIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (and (FunIsafcn smt__f)
            (= (FunDom smt__f) smt__a)
            (forall ((smt__x Idv))
              (=> (Mem smt__x smt__a)
                (Mem
                  (FunApp smt__f smt__x) 
                  smt__b))))
          (Mem smt__f
            (FunSet smt__a smt__b)))
        :pattern ((Mem smt__f
                    (FunSet smt__a smt__b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (Mem smt__f
            (FunSet smt__a smt__b))
          (and (FunIsafcn smt__f)
            (= (FunDom smt__f) smt__a)))
        :pattern ((Mem smt__f
                    (FunSet smt__a smt__b)))))
    :named |FunSetElim1|))

;; Axiom: FunSetElim2
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv) (smt__x Idv))
      (!
        (=>
          (and
            (Mem smt__f
              (FunSet smt__a smt__b))
            (Mem smt__x smt__a))
          (Mem
            (FunApp smt__f smt__x) smt__b))
        :pattern ((Mem smt__f
                    (FunSet smt__a smt__b))
                   (Mem smt__x smt__a))
        :pattern ((Mem smt__f
                    (FunSet smt__a smt__b))
                   (FunApp smt__f smt__x))))
    :named |FunSetElim2|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: FunExceptIsafcn
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (FunIsafcn
          (FunExcept smt__f smt__x smt__y))
        :pattern ((FunExcept smt__f smt__x
                    smt__y)))) :named |FunExceptIsafcn|))

;; Axiom: FunExceptDomDef
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (=
          (FunDom
            (FunExcept smt__f smt__x smt__y))
          (FunDom smt__f))
        :pattern ((FunExcept smt__f smt__x
                    smt__y)))) :named |FunExceptDomDef|))

;; Axiom: FunExceptAppDef1
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (=>
          (Mem smt__x
            (FunDom smt__f))
          (=
            (FunApp
              (FunExcept smt__f smt__x smt__y)
              smt__x) smt__y))
        :pattern ((FunExcept smt__f smt__x
                    smt__y)))) :named |FunExceptAppDef1|))

;; Axiom: FunExceptAppDef2
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv) (smt__z Idv))
      (!
        (=>
          (Mem smt__z
            (FunDom smt__f))
          (and
            (=> (= smt__z smt__x)
              (=
                (FunApp
                  (FunExcept smt__f smt__x
                    smt__y) smt__z) smt__y))
            (=> (distinct smt__z smt__x)
              (=
                (FunApp
                  (FunExcept smt__f smt__x
                    smt__y) smt__z)
                (FunApp smt__f smt__z)))))
        :pattern ((FunApp
                    (FunExcept smt__f smt__x
                      smt__y) smt__z))
        :pattern ((FunExcept smt__f smt__x
                    smt__y)
                   (FunApp smt__f smt__z))))
    :named |FunExceptAppDef2|))

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (!
        (Mem smt__a1
          (SetEnum_1 smt__a1))
        :pattern ((SetEnum_1 smt__a1))))
    :named |EnumDefIntro 1|))

;; Axiom: EnumDefIntro 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv))
      (!
        (and
          (Mem smt__a1
            (SetEnum_2 smt__a1
              smt__a2))
          (Mem smt__a2
            (SetEnum_2 smt__a1
              smt__a2)))
        :pattern ((SetEnum_2 
                    smt__a1 smt__a2)))) :named |EnumDefIntro 2|))

;; Axiom: EnumDefElim 1
(assert
  (!
    (forall ((smt__a1 Idv) (smt__x Idv))
      (!
        (=>
          (Mem smt__x
            (SetEnum_1 smt__a1))
          (= smt__x smt__a1))
        :pattern ((Mem smt__x
                    (SetEnum_1
                      smt__a1))))) :named |EnumDefElim 1|))

;; Axiom: EnumDefElim 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv))
      (!
        (=>
          (Mem smt__x
            (SetEnum_2 smt__a1
              smt__a2)) (or (= smt__x smt__a1) (= smt__x smt__a2)))
        :pattern ((Mem smt__x
                    (SetEnum_2
                      smt__a1 smt__a2))))) :named |EnumDefElim 2|))

;; Axiom: StrLitIsstr black
(assert
  (!
    (Mem
      StrLit_black
      StrSet) :named |StrLitIsstr black|))

;; Axiom: StrLitIsstr white
(assert
  (!
    (Mem
      StrLit_white
      StrSet) :named |StrLitIsstr white|))

;; Axiom: StrLitDistinct black white
(assert
  (!
    (distinct StrLit_black
      StrLit_white)
    :named |StrLitDistinct black white|))

;; Axiom: CastInjAlt Bool
(assert
  (!
    (and
      (= (Cast_Bool true)
        Tt_Idv)
      (distinct (Cast_Bool false)
        Tt_Idv))
    :named |CastInjAlt Bool|))

;; Axiom: CastInjAlt Int
(assert
  (!
    (forall ((smt__x Int))
      (!
        (= smt__x
          (Proj_Int
            (Cast_Int smt__x)))
        :pattern ((Cast_Int smt__x))))
    :named |CastInjAlt Int|))

;; Axiom: TypeGuardIntro Bool
(assert
  (!
    (forall ((smt__z Bool))
      (!
        (Mem
          (Cast_Bool smt__z)
          BoolSet)
        :pattern ((Cast_Bool smt__z))))
    :named |TypeGuardIntro Bool|))

;; Axiom: TypeGuardIntro Int
(assert
  (!
    (forall ((smt__z Int))
      (!
        (Mem
          (Cast_Int smt__z)
          IntSet)
        :pattern ((Cast_Int smt__z))))
    :named |TypeGuardIntro Int|))

;; Axiom: TypeGuardElim Bool
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=>
          (Mem smt__x
            BoolSet)
          (or
            (= smt__x
              (Cast_Bool true))
            (= smt__x
              (Cast_Bool false))))
        :pattern ((Mem smt__x
                    BoolSet))))
    :named |TypeGuardElim Bool|))

;; Axiom: TypeGuardElim Int
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=>
          (Mem smt__x
            IntSet)
          (= smt__x
            (Cast_Int
              (Proj_Int smt__x))))
        :pattern ((Mem smt__x
                    IntSet))))
    :named |TypeGuardElim Int|))

;; Axiom: Typing TIntMinus
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (IntMinus
            (Cast_Int smt__x1)
            (Cast_Int smt__x2))
          (Cast_Int
            (- smt__x1 smt__x2)))
        :pattern ((IntMinus
                    (Cast_Int smt__x1)
                    (Cast_Int smt__x2)))))
    :named |Typing TIntMinus|))

;; Axiom: Typing TIntLteq
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (IntLteq
            (Cast_Int smt__x1)
            (Cast_Int smt__x2))
          (<= smt__x1 smt__x2))
        :pattern ((IntLteq
                    (Cast_Int smt__x1)
                    (Cast_Int smt__x2)))))
    :named |Typing TIntLteq|))

;; Axiom: ExtTrigEqDef Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (= (TrigEq_Idv smt__x smt__y)
          (= smt__x smt__y))
        :pattern ((TrigEq_Idv 
                    smt__x smt__y)))) :named |ExtTrigEqDef Idv|))

; hidden fact

; hidden fact

; omitted declaration of 'CST_EnabledWrapper_' (second-order)

; omitted declaration of 'CST_CdotWrapper_' (second-order)

(declare-fun CST_N_ () Idv)

; hidden fact

(declare-fun VAR_active_ () Idv)

(declare-fun VAR_active_prime () Idv)

(declare-fun VAR_color_ () Idv)

(declare-fun VAR_color_prime () Idv)

(declare-fun VAR_tpos_ () Idv)

(declare-fun VAR_tpos_prime () Idv)

(declare-fun VAR_tcolor_ () Idv)

(declare-fun VAR_tcolor_prime () Idv)

(declare-fun STATE_Init_ () Idv)

(declare-fun ACTION_InitiateProbe_ () Idv)

(declare-fun ACTION_PassToken_ (Idv) Idv)

(declare-fun ACTION_SendMsg_ (Idv) Idv)

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
  (Mem CST_N_
    (SetMinus
      NatSet
      (SetEnum_1
        (Cast_Int 0)))))

; hidden fact

; hidden fact

; hidden fact

(assert
  (and
    (Mem
      VAR_active_
      (FunSet
        (IntRange
          (Cast_Int 0)
          (IntMinus
            CST_N_
            (Cast_Int 1)))
        BoolSet))
    (Mem
      VAR_color_
      (FunSet
        (IntRange
          (Cast_Int 0)
          (IntMinus
            CST_N_
            (Cast_Int 1)))
        (SetEnum_2
          StrLit_white
          StrLit_black)))
    (Mem
      VAR_tpos_
      (IntRange
        (Cast_Int 0)
        (IntMinus
          CST_N_
          (Cast_Int 1))))
    (Mem
      VAR_tcolor_
      (SetEnum_2
        StrLit_white
        StrLit_black))))

(assert
  (or
    (= ACTION_Next_
      Tt_Idv)
    (TrigEq_Idv
      Anon_OPAQUE_h6fbaa
      STATE_vars_)))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun CST_i_ () Idv)

(assert
  (Mem CST_i_
    (IntRange
      (Cast_Int 0)
      (IntMinus
        CST_N_
        (Cast_Int 1)))))

; hidden fact

; hidden fact

; hidden fact

(assert
  (=
    (FunApp
      VAR_active_
      CST_i_)
    Tt_Idv))

(assert
  (TrigEq_Idv
    VAR_active_prime
    (FunExcept
      VAR_active_
      CST_i_
      (Cast_Bool false))))

(assert
  (TrigEq_Idv
    VAR_color_prime
    VAR_color_))

(assert
  (TrigEq_Idv
    VAR_tpos_prime
    VAR_tpos_))

(assert
  (TrigEq_Idv
    VAR_tcolor_prime
    VAR_tcolor_))

;; Goal
(assert
  (!
    (not
      (and
        (Mem
          VAR_active_prime
          (FunSet
            (IntRange
              (Cast_Int 0)
              (IntMinus
                CST_N_
                (Cast_Int 1)))
            BoolSet))
        (Mem
          VAR_color_prime
          (FunSet
            (IntRange
              (Cast_Int 0)
              (IntMinus
                CST_N_
                (Cast_Int 1)))
            (SetEnum_2
              StrLit_white
              StrLit_black)))
        (Mem
          VAR_tpos_prime
          (IntRange
            (Cast_Int 0)
            (IntMinus
              CST_N_
              (Cast_Int 1))))
        (Mem
          VAR_tcolor_prime
          (SetEnum_2
            StrLit_white
            StrLit_black))))
    :named |Goal|))

(check-sat)
(exit)
