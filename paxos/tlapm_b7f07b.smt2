;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_Quorums_,
;;	       NEW VARIABLE VARIABLE_msgs_,
;;	       NEW VARIABLE VARIABLE_maxBal_,
;;	       NEW VARIABLE VARIABLE_maxVBal_,
;;	       NEW VARIABLE VARIABLE_maxVal_,
;;	       \A CONSTANT_S_ : \E CONSTANT_x_ : CONSTANT_x_ \notin CONSTANT_S_ 
;;	PROVE  (CHOOSE CONSTANT_v_ : CONSTANT_v_ \notin CONSTANT_Values_)
;;	       \notin CONSTANT_Values_
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #3
;; Generated from file "./Paxos.tla", line 42, characters 1-2

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

; omitted declaration of 'TLA__Choose' (second-order)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

; omitted fact (second-order)

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

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

(declare-fun smt__CONSTANTunderscore_Acceptorsunderscore_ () Idv)

(declare-fun smt__CONSTANTunderscore_Valuesunderscore_ () Idv)

(declare-fun smt__CONSTANTunderscore_Quorumsunderscore_ () Idv)

; hidden fact

; hidden fact

(declare-fun smt__CONSTANTunderscore_Ballotsunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_msgsunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_msgsunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_maxBalunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_maxBalunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_maxVBalunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_maxValunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_maxValunderscore_underscore_prime () Idv)

(declare-fun smt__STATEunderscore_varsunderscore_ () Idv)

(declare-fun smt__ACTIONunderscore_Sendunderscore_ (Idv) Idv)

(assert
  (forall ((smt__CONSTANTunderscore_Sunderscore_ Idv))
    (exists ((smt__CONSTANTunderscore_xunderscore_ Idv))
      (not
        (smt__TLAunderscore_underscore_Mem
          smt__CONSTANTunderscore_xunderscore_
          smt__CONSTANTunderscore_Sunderscore_)))))

(declare-fun smt__TLAunderscore_underscore_Chooseunderscore_flatndunderscore_1 () Idv)

;; Axiom: ChooseDef TLA__Choose_flatnd_1
(assert
  (!
    (forall ((smt__x Idv))
      (=>
        (not
          (smt__TLAunderscore_underscore_Mem smt__x
            smt__CONSTANTunderscore_Valuesunderscore_))
        (not
          (smt__TLAunderscore_underscore_Mem
            smt__TLAunderscore_underscore_Chooseunderscore_flatndunderscore_1
            smt__CONSTANTunderscore_Valuesunderscore_))))
    :named |ChooseDef TLA__Choose_flatnd_1|))

;; Goal
(assert
  (!
    (not
      (not
        (smt__TLAunderscore_underscore_Mem
          smt__TLAunderscore_underscore_Chooseunderscore_flatndunderscore_1
          smt__CONSTANTunderscore_Valuesunderscore_))) :named |Goal|))

(check-sat)
(exit)
