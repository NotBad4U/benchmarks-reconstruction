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
;;	       (\/ ACTION_InitiateProbe_
;;	        \/ \E CONSTANT_i_ \in 0..CONSTANT_N_ - 1 \ {0} :
;;	              ACTION_PassToken_(CONSTANT_i_))
;;	       \/ (\E CONSTANT_i_ \in 0..CONSTANT_N_ - 1 :
;;	              ACTION_Deactivate_(CONSTANT_i_) \/ ACTION_SendMsg_(CONSTANT_i_))
;;	       \/ ?h6fbaa = STATE_vars_ ,
;;	       ASSUME ACTION_InitiateProbe_ 
;;	       PROVE  /\ ?VARIABLE_active_#prime \in [0..CONSTANT_N_ - 1 -> BOOLEAN]
;;	              /\ ?VARIABLE_color_#prime
;;	                 \in [0..CONSTANT_N_ - 1 -> {"white", "black"}]
;;	              /\ ?VARIABLE_tpos_#prime \in 0..CONSTANT_N_ - 1
;;	              /\ ?VARIABLE_tcolor_#prime \in {"white", "black"} ,
;;	       ASSUME NEW CONSTANT CONSTANT_i_ \in 0..CONSTANT_N_ - 1 \ {0},
;;	              ACTION_PassToken_(CONSTANT_i_) 
;;	       PROVE  /\ ?VARIABLE_active_#prime \in [0..CONSTANT_N_ - 1 -> BOOLEAN]
;;	              /\ ?VARIABLE_color_#prime
;;	                 \in [0..CONSTANT_N_ - 1 -> {"white", "black"}]
;;	              /\ ?VARIABLE_tpos_#prime \in 0..CONSTANT_N_ - 1
;;	              /\ ?VARIABLE_tcolor_#prime \in {"white", "black"} ,
;;	       ASSUME NEW CONSTANT CONSTANT_i_ \in 0..CONSTANT_N_ - 1,
;;	              ACTION_Deactivate_(CONSTANT_i_) 
;;	       PROVE  /\ ?VARIABLE_active_#prime \in [0..CONSTANT_N_ - 1 -> BOOLEAN]
;;	              /\ ?VARIABLE_color_#prime
;;	                 \in [0..CONSTANT_N_ - 1 -> {"white", "black"}]
;;	              /\ ?VARIABLE_tpos_#prime \in 0..CONSTANT_N_ - 1
;;	              /\ ?VARIABLE_tcolor_#prime \in {"white", "black"} ,
;;	       ASSUME NEW CONSTANT CONSTANT_i_ \in 0..CONSTANT_N_ - 1,
;;	              ACTION_SendMsg_(CONSTANT_i_) 
;;	       PROVE  /\ ?VARIABLE_active_#prime \in [0..CONSTANT_N_ - 1 -> BOOLEAN]
;;	              /\ ?VARIABLE_color_#prime
;;	                 \in [0..CONSTANT_N_ - 1 -> {"white", "black"}]
;;	              /\ ?VARIABLE_tpos_#prime \in 0..CONSTANT_N_ - 1
;;	              /\ ?VARIABLE_tcolor_#prime \in {"white", "black"} ,
;;	       ASSUME ?h6fbaa = STATE_vars_ 
;;	       PROVE  /\ ?VARIABLE_active_#prime \in [0..CONSTANT_N_ - 1 -> BOOLEAN]
;;	              /\ ?VARIABLE_color_#prime
;;	                 \in [0..CONSTANT_N_ - 1 -> {"white", "black"}]
;;	              /\ ?VARIABLE_tpos_#prime \in 0..CONSTANT_N_ - 1
;;	              /\ ?VARIABLE_tcolor_#prime \in {"white", "black"} 
;;	PROVE  /\ ?VARIABLE_active_#prime \in [0..CONSTANT_N_ - 1 -> BOOLEAN]
;;	       /\ ?VARIABLE_color_#prime
;;	          \in [0..CONSTANT_N_ - 1 -> {"white", "black"}]
;;	       /\ ?VARIABLE_tpos_#prime \in 0..CONSTANT_N_ - 1
;;	       /\ ?VARIABLE_tcolor_#prime \in {"white", "black"}
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #7
;; Generated from file "./examples/EWD840.tla", line 164, characters 5-6

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h6fbaa () Idv)

(declare-fun smt__TLAunderscore_underscore_BoolSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Castunderscore_Int (Int) Idv)

(declare-fun smt__TLAunderscore_underscore_FunApp (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLAunderscore_underscore_FunIsafcn (Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_FunSet (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntLteq (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntMinus (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntRange (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_NatSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Projunderscore_Int (Idv) Int)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_1 (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_2 (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_SetMinus (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_black () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_white () Idv)

(declare-fun smt__TLAunderscore_underscore_StrSet () Idv)

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

;; Axiom: StrLitIsstr black
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_black
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr black|))

;; Axiom: StrLitIsstr white
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_white
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr white|))

;; Axiom: StrLitDistinct black white
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_black
      smt__TLAunderscore_underscore_StrLitunderscore_white)
    :named |StrLitDistinct black white|))

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

(declare-fun smt__STATEunderscore_Initunderscore_ () Idv)

(declare-fun smt__ACTIONunderscore_InitiateProbeunderscore_ () Idv)

(declare-fun smt__ACTIONunderscore_PassTokenunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_SendMsgunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Deactivateunderscore_ (Idv) Idv)

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

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_Nunderscore_
    (smt__TLAunderscore_underscore_SetMinus
      smt__TLAunderscore_underscore_NatSet
      (smt__TLAunderscore_underscore_SetEnumunderscore_1
        (smt__TLAunderscore_underscore_Castunderscore_Int 0)))))

; hidden fact

; hidden fact

; hidden fact

(assert
  (and
    (smt__TLAunderscore_underscore_Mem
      smt__VARIABLEunderscore_activeunderscore_
      (smt__TLAunderscore_underscore_FunSet
        (smt__TLAunderscore_underscore_IntRange
          (smt__TLAunderscore_underscore_Castunderscore_Int 0)
          (smt__TLAunderscore_underscore_IntMinus
            smt__CONSTANTunderscore_Nunderscore_
            (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
        smt__TLAunderscore_underscore_BoolSet))
    (smt__TLAunderscore_underscore_Mem
      smt__VARIABLEunderscore_colorunderscore_
      (smt__TLAunderscore_underscore_FunSet
        (smt__TLAunderscore_underscore_IntRange
          (smt__TLAunderscore_underscore_Castunderscore_Int 0)
          (smt__TLAunderscore_underscore_IntMinus
            smt__CONSTANTunderscore_Nunderscore_
            (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
        (smt__TLAunderscore_underscore_SetEnumunderscore_2
          smt__TLAunderscore_underscore_StrLitunderscore_white
          smt__TLAunderscore_underscore_StrLitunderscore_black)))
    (smt__TLAunderscore_underscore_Mem
      smt__VARIABLEunderscore_tposunderscore_
      (smt__TLAunderscore_underscore_IntRange
        (smt__TLAunderscore_underscore_Castunderscore_Int 0)
        (smt__TLAunderscore_underscore_IntMinus
          smt__CONSTANTunderscore_Nunderscore_
          (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
    (smt__TLAunderscore_underscore_Mem
      smt__VARIABLEunderscore_tcolorunderscore_
      (smt__TLAunderscore_underscore_SetEnumunderscore_2
        smt__TLAunderscore_underscore_StrLitunderscore_white
        smt__TLAunderscore_underscore_StrLitunderscore_black))))

(assert
  (or
    (or
      (or
        (= smt__ACTIONunderscore_InitiateProbeunderscore_
          smt__TLAunderscore_underscore_Ttunderscore_Idv)
        (exists ((smt__CONSTANT_i Idv))
          (and
            (smt__TLAunderscore_underscore_Mem
              smt__CONSTANT_i
              (smt__TLAunderscore_underscore_SetMinus
                (smt__TLAunderscore_underscore_IntRange
                  (smt__TLAunderscore_underscore_Castunderscore_Int 0)
                  (smt__TLAunderscore_underscore_IntMinus
                    smt__CONSTANTunderscore_Nunderscore_
                    (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
                (smt__TLAunderscore_underscore_SetEnumunderscore_1
                  (smt__TLAunderscore_underscore_Castunderscore_Int 0))))
            (=
              (smt__ACTIONunderscore_PassTokenunderscore_
                smt__CONSTANT_i)
              smt__TLAunderscore_underscore_Ttunderscore_Idv))))
      (exists ((smt__CONSTANT_i Idv))
        (and
          (smt__TLAunderscore_underscore_Mem
            smt__CONSTANT_i
            (smt__TLAunderscore_underscore_IntRange
              (smt__TLAunderscore_underscore_Castunderscore_Int 0)
              (smt__TLAunderscore_underscore_IntMinus
                smt__CONSTANTunderscore_Nunderscore_
                (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
          (or
            (=
              (smt__ACTIONunderscore_Deactivateunderscore_
                smt__CONSTANT_i)
              smt__TLAunderscore_underscore_Ttunderscore_Idv)
            (=
              (smt__ACTIONunderscore_SendMsgunderscore_
                smt__CONSTANT_i)
              smt__TLAunderscore_underscore_Ttunderscore_Idv)))))
    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
      smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h6fbaa
      smt__STATEunderscore_varsunderscore_)))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (=>
    (= smt__ACTIONunderscore_InitiateProbeunderscore_
      smt__TLAunderscore_underscore_Ttunderscore_Idv)
    (and
      (smt__TLAunderscore_underscore_Mem
        smt__VARIABLEunderscore_activeunderscore_underscore_prime
        (smt__TLAunderscore_underscore_FunSet
          (smt__TLAunderscore_underscore_IntRange
            (smt__TLAunderscore_underscore_Castunderscore_Int 0)
            (smt__TLAunderscore_underscore_IntMinus
              smt__CONSTANTunderscore_Nunderscore_
              (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
          smt__TLAunderscore_underscore_BoolSet))
      (smt__TLAunderscore_underscore_Mem
        smt__VARIABLEunderscore_colorunderscore_underscore_prime
        (smt__TLAunderscore_underscore_FunSet
          (smt__TLAunderscore_underscore_IntRange
            (smt__TLAunderscore_underscore_Castunderscore_Int 0)
            (smt__TLAunderscore_underscore_IntMinus
              smt__CONSTANTunderscore_Nunderscore_
              (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
          (smt__TLAunderscore_underscore_SetEnumunderscore_2
            smt__TLAunderscore_underscore_StrLitunderscore_white
            smt__TLAunderscore_underscore_StrLitunderscore_black)))
      (smt__TLAunderscore_underscore_Mem
        smt__VARIABLEunderscore_tposunderscore_underscore_prime
        (smt__TLAunderscore_underscore_IntRange
          (smt__TLAunderscore_underscore_Castunderscore_Int 0)
          (smt__TLAunderscore_underscore_IntMinus
            smt__CONSTANTunderscore_Nunderscore_
            (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
      (smt__TLAunderscore_underscore_Mem
        smt__VARIABLEunderscore_tcolorunderscore_underscore_prime
        (smt__TLAunderscore_underscore_SetEnumunderscore_2
          smt__TLAunderscore_underscore_StrLitunderscore_white
          smt__TLAunderscore_underscore_StrLitunderscore_black)))))

(assert
  (forall ((smt__CONSTANT_i Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem smt__CONSTANT_i
        (smt__TLAunderscore_underscore_SetMinus
          (smt__TLAunderscore_underscore_IntRange
            (smt__TLAunderscore_underscore_Castunderscore_Int 0)
            (smt__TLAunderscore_underscore_IntMinus
              smt__CONSTANTunderscore_Nunderscore_
              (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
          (smt__TLAunderscore_underscore_SetEnumunderscore_1
            (smt__TLAunderscore_underscore_Castunderscore_Int 0))))
      (=>
        (=
          (smt__ACTIONunderscore_PassTokenunderscore_
            smt__CONSTANT_i)
          smt__TLAunderscore_underscore_Ttunderscore_Idv)
        (and
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_activeunderscore_underscore_prime
            (smt__TLAunderscore_underscore_FunSet
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 0)
                (smt__TLAunderscore_underscore_IntMinus
                  smt__CONSTANTunderscore_Nunderscore_
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
              smt__TLAunderscore_underscore_BoolSet))
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_colorunderscore_underscore_prime
            (smt__TLAunderscore_underscore_FunSet
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 0)
                (smt__TLAunderscore_underscore_IntMinus
                  smt__CONSTANTunderscore_Nunderscore_
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
              (smt__TLAunderscore_underscore_SetEnumunderscore_2
                smt__TLAunderscore_underscore_StrLitunderscore_white
                smt__TLAunderscore_underscore_StrLitunderscore_black)))
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_tposunderscore_underscore_prime
            (smt__TLAunderscore_underscore_IntRange
              (smt__TLAunderscore_underscore_Castunderscore_Int 0)
              (smt__TLAunderscore_underscore_IntMinus
                smt__CONSTANTunderscore_Nunderscore_
                (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_tcolorunderscore_underscore_prime
            (smt__TLAunderscore_underscore_SetEnumunderscore_2
              smt__TLAunderscore_underscore_StrLitunderscore_white
              smt__TLAunderscore_underscore_StrLitunderscore_black)))))))

(assert
  (forall ((smt__CONSTANT_i Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem smt__CONSTANT_i
        (smt__TLAunderscore_underscore_IntRange
          (smt__TLAunderscore_underscore_Castunderscore_Int 0)
          (smt__TLAunderscore_underscore_IntMinus
            smt__CONSTANTunderscore_Nunderscore_
            (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
      (=>
        (=
          (smt__ACTIONunderscore_Deactivateunderscore_
            smt__CONSTANT_i)
          smt__TLAunderscore_underscore_Ttunderscore_Idv)
        (and
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_activeunderscore_underscore_prime
            (smt__TLAunderscore_underscore_FunSet
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 0)
                (smt__TLAunderscore_underscore_IntMinus
                  smt__CONSTANTunderscore_Nunderscore_
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
              smt__TLAunderscore_underscore_BoolSet))
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_colorunderscore_underscore_prime
            (smt__TLAunderscore_underscore_FunSet
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 0)
                (smt__TLAunderscore_underscore_IntMinus
                  smt__CONSTANTunderscore_Nunderscore_
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
              (smt__TLAunderscore_underscore_SetEnumunderscore_2
                smt__TLAunderscore_underscore_StrLitunderscore_white
                smt__TLAunderscore_underscore_StrLitunderscore_black)))
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_tposunderscore_underscore_prime
            (smt__TLAunderscore_underscore_IntRange
              (smt__TLAunderscore_underscore_Castunderscore_Int 0)
              (smt__TLAunderscore_underscore_IntMinus
                smt__CONSTANTunderscore_Nunderscore_
                (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_tcolorunderscore_underscore_prime
            (smt__TLAunderscore_underscore_SetEnumunderscore_2
              smt__TLAunderscore_underscore_StrLitunderscore_white
              smt__TLAunderscore_underscore_StrLitunderscore_black)))))))

(assert
  (forall ((smt__CONSTANT_i Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem smt__CONSTANT_i
        (smt__TLAunderscore_underscore_IntRange
          (smt__TLAunderscore_underscore_Castunderscore_Int 0)
          (smt__TLAunderscore_underscore_IntMinus
            smt__CONSTANTunderscore_Nunderscore_
            (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
      (=>
        (=
          (smt__ACTIONunderscore_SendMsgunderscore_
            smt__CONSTANT_i)
          smt__TLAunderscore_underscore_Ttunderscore_Idv)
        (and
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_activeunderscore_underscore_prime
            (smt__TLAunderscore_underscore_FunSet
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 0)
                (smt__TLAunderscore_underscore_IntMinus
                  smt__CONSTANTunderscore_Nunderscore_
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
              smt__TLAunderscore_underscore_BoolSet))
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_colorunderscore_underscore_prime
            (smt__TLAunderscore_underscore_FunSet
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 0)
                (smt__TLAunderscore_underscore_IntMinus
                  smt__CONSTANTunderscore_Nunderscore_
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
              (smt__TLAunderscore_underscore_SetEnumunderscore_2
                smt__TLAunderscore_underscore_StrLitunderscore_white
                smt__TLAunderscore_underscore_StrLitunderscore_black)))
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_tposunderscore_underscore_prime
            (smt__TLAunderscore_underscore_IntRange
              (smt__TLAunderscore_underscore_Castunderscore_Int 0)
              (smt__TLAunderscore_underscore_IntMinus
                smt__CONSTANTunderscore_Nunderscore_
                (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
          (smt__TLAunderscore_underscore_Mem
            smt__VARIABLEunderscore_tcolorunderscore_underscore_prime
            (smt__TLAunderscore_underscore_SetEnumunderscore_2
              smt__TLAunderscore_underscore_StrLitunderscore_white
              smt__TLAunderscore_underscore_StrLitunderscore_black)))))))

(assert
  (=>
    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
      smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h6fbaa
      smt__STATEunderscore_varsunderscore_)
    (and
      (smt__TLAunderscore_underscore_Mem
        smt__VARIABLEunderscore_activeunderscore_underscore_prime
        (smt__TLAunderscore_underscore_FunSet
          (smt__TLAunderscore_underscore_IntRange
            (smt__TLAunderscore_underscore_Castunderscore_Int 0)
            (smt__TLAunderscore_underscore_IntMinus
              smt__CONSTANTunderscore_Nunderscore_
              (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
          smt__TLAunderscore_underscore_BoolSet))
      (smt__TLAunderscore_underscore_Mem
        smt__VARIABLEunderscore_colorunderscore_underscore_prime
        (smt__TLAunderscore_underscore_FunSet
          (smt__TLAunderscore_underscore_IntRange
            (smt__TLAunderscore_underscore_Castunderscore_Int 0)
            (smt__TLAunderscore_underscore_IntMinus
              smt__CONSTANTunderscore_Nunderscore_
              (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
          (smt__TLAunderscore_underscore_SetEnumunderscore_2
            smt__TLAunderscore_underscore_StrLitunderscore_white
            smt__TLAunderscore_underscore_StrLitunderscore_black)))
      (smt__TLAunderscore_underscore_Mem
        smt__VARIABLEunderscore_tposunderscore_underscore_prime
        (smt__TLAunderscore_underscore_IntRange
          (smt__TLAunderscore_underscore_Castunderscore_Int 0)
          (smt__TLAunderscore_underscore_IntMinus
            smt__CONSTANTunderscore_Nunderscore_
            (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
      (smt__TLAunderscore_underscore_Mem
        smt__VARIABLEunderscore_tcolorunderscore_underscore_prime
        (smt__TLAunderscore_underscore_SetEnumunderscore_2
          smt__TLAunderscore_underscore_StrLitunderscore_white
          smt__TLAunderscore_underscore_StrLitunderscore_black)))))

;; Goal
(assert
  (!
    (not
      (and
        (smt__TLAunderscore_underscore_Mem
          smt__VARIABLEunderscore_activeunderscore_underscore_prime
          (smt__TLAunderscore_underscore_FunSet
            (smt__TLAunderscore_underscore_IntRange
              (smt__TLAunderscore_underscore_Castunderscore_Int 0)
              (smt__TLAunderscore_underscore_IntMinus
                smt__CONSTANTunderscore_Nunderscore_
                (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
            smt__TLAunderscore_underscore_BoolSet))
        (smt__TLAunderscore_underscore_Mem
          smt__VARIABLEunderscore_colorunderscore_underscore_prime
          (smt__TLAunderscore_underscore_FunSet
            (smt__TLAunderscore_underscore_IntRange
              (smt__TLAunderscore_underscore_Castunderscore_Int 0)
              (smt__TLAunderscore_underscore_IntMinus
                smt__CONSTANTunderscore_Nunderscore_
                (smt__TLAunderscore_underscore_Castunderscore_Int 1)))
            (smt__TLAunderscore_underscore_SetEnumunderscore_2
              smt__TLAunderscore_underscore_StrLitunderscore_white
              smt__TLAunderscore_underscore_StrLitunderscore_black)))
        (smt__TLAunderscore_underscore_Mem
          smt__VARIABLEunderscore_tposunderscore_underscore_prime
          (smt__TLAunderscore_underscore_IntRange
            (smt__TLAunderscore_underscore_Castunderscore_Int 0)
            (smt__TLAunderscore_underscore_IntMinus
              smt__CONSTANTunderscore_Nunderscore_
              (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
        (smt__TLAunderscore_underscore_Mem
          smt__VARIABLEunderscore_tcolorunderscore_underscore_prime
          (smt__TLAunderscore_underscore_SetEnumunderscore_2
            smt__TLAunderscore_underscore_StrLitunderscore_white
            smt__TLAunderscore_underscore_StrLitunderscore_black))))
    :named |Goal|))

(check-sat)
(exit)
