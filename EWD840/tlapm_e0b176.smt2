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
;;	PROVE  ~(\E CONSTANT_j_ \in 0..VARIABLE_tpos_ :
;;	            VARIABLE_color_[CONSTANT_j_] = "black")
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #41
;; Generated from file "./examples/EWD840.tla", line 205, characters 9-10

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_Castunderscore_Int (Int) Idv)

(declare-fun smt__TLAunderscore_underscore_FunApp (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLAunderscore_underscore_FunIsafcn (Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntLteq (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntRange (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_Projunderscore_Int (Idv) Int)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

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

; omitted fact (second-order)

; omitted fact (second-order)

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

(assert
  (and
    (not
      (=
        (smt__TLAunderscore_underscore_FunApp
          smt__VARIABLEunderscore_activeunderscore_
          (smt__TLAunderscore_underscore_Castunderscore_Int 0))
        smt__TLAunderscore_underscore_Ttunderscore_Idv))
    (= smt__STATEunderscore_Invunderscore_
      smt__TLAunderscore_underscore_Ttunderscore_Idv)))

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
    smt__VARIABLEunderscore_tposunderscore_
    (smt__TLAunderscore_underscore_Castunderscore_Int 0)))

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
    smt__VARIABLEunderscore_tcolorunderscore_
    smt__TLAunderscore_underscore_StrLitunderscore_white))

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
    (smt__TLAunderscore_underscore_FunApp
      smt__VARIABLEunderscore_colorunderscore_
      (smt__TLAunderscore_underscore_Castunderscore_Int 0))
    smt__TLAunderscore_underscore_StrLitunderscore_white))

;; Goal
(assert
  (!
    (not
      (not
        (exists ((smt__CONSTANTunderscore_junderscore_ Idv))
          (and
            (smt__TLAunderscore_underscore_Mem
              smt__CONSTANTunderscore_junderscore_
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 0)
                smt__VARIABLEunderscore_tposunderscore_))
            (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
              (smt__TLAunderscore_underscore_FunApp
                smt__VARIABLEunderscore_colorunderscore_
                smt__CONSTANTunderscore_junderscore_)
              smt__TLAunderscore_underscore_StrLitunderscore_black)))))
    :named |Goal|))

(check-sat)
(exit)
