;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_N_,
;;	       NEW VARIABLE VARIABLE_active_,
;;	       NEW VARIABLE VARIABLE_color_,
;;	       NEW VARIABLE VARIABLE_tpos_,
;;	       NEW VARIABLE VARIABLE_tcolor_,
;;	       ASSUME NEW CONSTANT CONSTANT_i_ \in CONSTANT_Nodes_
;;	       PROVE  ~VARIABLE_active_[CONSTANT_i_] 
;;	PROVE  \A CONSTANT_i_ \in CONSTANT_Nodes_ : ~VARIABLE_active_[CONSTANT_i_]
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #47
;; Generated from file "./examples/EWD840.tla", line 209, characters 5-26

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_FunApp (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLAunderscore_underscore_FunIsafcn (Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

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

; hidden fact

(assert
  (forall ((smt__CONSTANT_i Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem smt__CONSTANT_i
        smt__CONSTANTunderscore_Nodesunderscore_)
      (not
        (=
          (smt__TLAunderscore_underscore_FunApp
            smt__VARIABLEunderscore_activeunderscore_
            smt__CONSTANT_i)
          smt__TLAunderscore_underscore_Ttunderscore_Idv)))))

;; Goal
(assert
  (!
    (not
      (forall ((smt__CONSTANT_i Idv))
        (=>
          (smt__TLAunderscore_underscore_Mem
            smt__CONSTANT_i
            smt__CONSTANTunderscore_Nodesunderscore_)
          (not
            (=
              (smt__TLAunderscore_underscore_FunApp
                smt__VARIABLEunderscore_activeunderscore_
                smt__CONSTANT_i)
              smt__TLAunderscore_underscore_Ttunderscore_Idv)))))
    :named |Goal|))

(check-sat)
(exit)
