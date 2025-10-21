;; Proof obligation:
;;	ASSUME NEW CONSTANT CST_N_,
;;	       NEW VARIABLE VAR_active_,
;;	       NEW VARIABLE VAR_color_,
;;	       NEW VARIABLE VAR_tpos_,
;;	       NEW VARIABLE VAR_tcolor_,
;;	       CST_N_ \in Nat \ {0} 
;;	PROVE  (\/ P0::\A CST_i_ \in 0..CST_N_ - 1 :
;;	                  VAR_tpos_ < CST_i_
;;	                  => ~VAR_active_[CST_i_]
;;	        \/ P1::\E CST_j_ \in 0..VAR_tpos_ :
;;	                  VAR_color_[CST_j_] = "black"
;;	        \/ P2::(VAR_tcolor_ = "black"))
;;	       => ((/\ VAR_tpos_ = 0 /\ VAR_tcolor_ = "white"
;;	            /\ VAR_color_[0] = "white" /\ ~VAR_active_[0])
;;	           => (\A CST_i_ \in 0..CST_N_ - 1 :
;;	                  ~VAR_active_[CST_i_]))
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #31
;; Generated from file "./examples/EWD840.tla", line 175, characters 3-4

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun Cast_Int (Int) Idv)

(declare-fun FunApp (Idv Idv) Idv)

(declare-fun FunDom (Idv) Idv)

; omitted declaration of '_FunFcn' (second-order)

(declare-fun FunIsafcn (Idv) Bool)

(declare-fun IntLteq (Idv Idv) Bool)

(declare-fun IntMinus (Idv Idv) Idv)

(declare-fun IntRange (Idv Idv) Idv)

(declare-fun IntSet () Idv)

(declare-fun Mem (Idv Idv) Bool)

(declare-fun NatSet () Idv)

(declare-fun Proj_Int (Idv) Int)

(declare-fun SetEnum_1 (Idv) Idv)

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

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (!
        (Mem smt__a1
          (SetEnum_1 smt__a1))
        :pattern ((SetEnum_1 smt__a1))))
    :named |EnumDefIntro 1|))

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

;; Axiom: StrLitDistinct white black
(assert
  (!
    (distinct StrLit_white
      StrLit_black)
    :named |StrLitDistinct white black|))

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

(declare-fun CST_Color_ () Idv)

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

(declare-fun TEMPORAL_Liveness_ () Idv)

(declare-fun TEMPORAL_AllNodesTerminateIfNoMessages_ () Idv)

; hidden fact

(assert
  (Mem CST_N_
    (SetMinus
      NatSet
      (SetEnum_1
        (Cast_Int 0)))))

; hidden fact

; hidden fact

;; Goal
(assert
  (!
    (not
      (=>
        (or
          (forall ((CST_i_ Idv))
            (=>
              (Mem
                CST_i_
                (IntRange
                  (Cast_Int 0)
                  (IntMinus
                    CST_N_
                    (Cast_Int 1))))
              (=>
                (and
                  (IntLteq
                    VAR_tpos_
                    CST_i_)
                  (not
                    (TrigEq_Idv
                      VAR_tpos_
                      CST_i_)))
                (not
                  (=
                    (FunApp
                      VAR_active_
                      CST_i_)
                    Tt_Idv)))))
          (exists ((CST_j_ Idv))
            (and
              (Mem
                CST_j_
                (IntRange
                  (Cast_Int 0)
                  VAR_tpos_))
              (TrigEq_Idv
                (FunApp
                  VAR_color_
                  CST_j_)
                StrLit_black)))
          (TrigEq_Idv
            VAR_tcolor_
            StrLit_black))
        (=>
          (and
            (and
              (TrigEq_Idv
                VAR_tpos_
                (Cast_Int 0))
              (TrigEq_Idv
                VAR_tcolor_
                StrLit_white))
            (and
              (TrigEq_Idv
                (FunApp
                  VAR_color_
                  (Cast_Int 0))
                StrLit_white)
              (not
                (=
                  (FunApp
                    VAR_active_
                    (Cast_Int 0))
                  Tt_Idv))))
          (forall ((CST_i_ Idv))
            (=>
              (Mem
                CST_i_
                (IntRange
                  (Cast_Int 0)
                  (IntMinus
                    CST_N_
                    (Cast_Int 1))))
              (not
                (=
                  (FunApp
                    VAR_active_
                    CST_i_)
                  Tt_Idv)))))))
    :named |Goal|))

(check-sat)
(exit)
