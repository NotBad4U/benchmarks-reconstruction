;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_N_,
;;	       NEW VARIABLE VARIABLE_active_,
;;	       NEW VARIABLE VARIABLE_color_,
;;	       NEW VARIABLE VARIABLE_tpos_,
;;	       NEW VARIABLE VARIABLE_tcolor_,
;;	       NEW CONSTANT CONSTANT_i_ \in CONSTANT_Nodes_,
;;	       VARIABLE_tpos_ = 0 ,
;;	       CONSTANT_i_ \in 1..CONSTANT_N_ - 1 ,
;;	       CONSTANT_N_ \in Nat \ {0} 
;;	PROVE  VARIABLE_tpos_ < CONSTANT_i_
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #55
;; Generated from file "./examples/EWD840.tla", line 214, characters 25-26

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_Castunderscore_Int (Int) Idv)

(declare-fun smt__TLAunderscore_underscore_IntLteq (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntMinus (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntRange (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_NatSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Projunderscore_Int (Idv) Int)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_1 (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_SetMinus (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_TrigEqunderscore_Idv (Idv
  Idv) Bool)

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

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (!
        (smt__TLAunderscore_underscore_Mem smt__a1
          (smt__TLAunderscore_underscore_SetEnumunderscore_1 smt__a1))
        :pattern ((smt__TLAunderscore_underscore_SetEnumunderscore_1 smt__a1))))
    :named |EnumDefIntro 1|))

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

;; Axiom: Typing TIntMinus
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLAunderscore_underscore_IntMinus
            (smt__TLAunderscore_underscore_Castunderscore_Int smt__x1)
            (smt__TLAunderscore_underscore_Castunderscore_Int smt__x2))
          (smt__TLAunderscore_underscore_Castunderscore_Int
            (- smt__x1 smt__x2)))
        :pattern ((smt__TLAunderscore_underscore_IntMinus
                    (smt__TLAunderscore_underscore_Castunderscore_Int smt__x1)
                    (smt__TLAunderscore_underscore_Castunderscore_Int smt__x2)))))
    :named |Typing TIntMinus|))

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

(declare-fun smt__VARIABLEunderscore_activeunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_activeunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_colorunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_colorunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_tposunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_tposunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_tcolorunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_tcolorunderscore_underscore_prime () Idv)

(declare-fun smt__CONSTANTunderscore_Nodesunderscore_ () Idv)

(declare-fun smt__CONSTANTunderscore_Colorunderscore_ () Idv)

(declare-fun smt__STATEunderscore_TypeOKunderscore_ () Idv)

(declare-fun smt__STATEunderscore_Initunderscore_ () Idv)

(declare-fun smt__ACTIONunderscore_InitiateProbeunderscore_ () Idv)

(declare-fun smt__ACTIONunderscore_PassTokenunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_SendMsgunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Deactivateunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Controlledunderscore_ () Idv)

(declare-fun smt__ACTIONunderscore_Environmentunderscore_ () Idv)

(declare-fun smt__ACTIONunderscore_Nextunderscore_ () Idv)

(declare-fun smt__STATEunderscore_varsunderscore_ () Idv)

(declare-fun smt__TEMPORALunderscore_Fairnessunderscore_ () Idv)

(declare-fun smt__TEMPORALunderscore_Specunderscore_ () Idv)

(declare-fun smt__STATEunderscore_NeverBlackunderscore_ () Idv)

(declare-fun smt__TEMPORALunderscore_NeverChangeColorunderscore_ () Idv)

(declare-fun smt__STATEunderscore_terminationDetectedunderscore_ () Idv)

(declare-fun smt__STATEunderscore_TerminationDetectionunderscore_ () Idv)

(declare-fun smt__TEMPORALunderscore_Livenessunderscore_ () Idv)

(declare-fun smt__TEMPORALunderscore_AllNodesTerminateIfNoMessagesunderscore_ () Idv)

(declare-fun smt__STATEunderscore_Invunderscore_ () Idv)

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

(declare-fun smt__CONSTANT_i () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANT_i
    smt__CONSTANTunderscore_Nodesunderscore_))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
    smt__VARIABLEunderscore_tposunderscore_
    (smt__TLAunderscore_underscore_Castunderscore_Int 0)))

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANT_i
    (smt__TLAunderscore_underscore_IntRange
      (smt__TLAunderscore_underscore_Castunderscore_Int 1)
      (smt__TLAunderscore_underscore_IntMinus
        smt__CONSTANTunderscore_Nunderscore_
        (smt__TLAunderscore_underscore_Castunderscore_Int 1)))))

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_Nunderscore_
    (smt__TLAunderscore_underscore_SetMinus
      smt__TLAunderscore_underscore_NatSet
      (smt__TLAunderscore_underscore_SetEnumunderscore_1
        (smt__TLAunderscore_underscore_Castunderscore_Int 0)))))

;; Goal
(assert
  (!
    (not
      (and
        (smt__TLAunderscore_underscore_IntLteq
          smt__VARIABLEunderscore_tposunderscore_
          smt__CONSTANT_i)
        (not
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            smt__VARIABLEunderscore_tposunderscore_
            smt__CONSTANT_i)))) :named |Goal|))

(check-sat)
(exit)
