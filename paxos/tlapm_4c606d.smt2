;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_Quorums_,
;;	       NEW VARIABLE VARIABLE_msgs_,
;;	       NEW VARIABLE VARIABLE_maxBal_,
;;	       NEW VARIABLE VARIABLE_maxVBal_,
;;	       NEW VARIABLE VARIABLE_maxVal_,
;;	       ?h15bf9 ,
;;	       CONSTANT_Consistency_ ,
;;	       ACTION_Next_ ,
;;	       {CONSTANT_v_ \in CONSTANT_Values_ : CONSTANT_Chosen_(CONSTANT_v_)}
;;	       # {CONSTANT_v_ \in CONSTANT_Values_ : CONSTANT_Chosen_(CONSTANT_v_)} ,
;;	       {CONSTANT_v_ \in CONSTANT_Values_ : CONSTANT_Chosen_(CONSTANT_v_)}
;;	       \subseteq {CONSTANT_v_ \in CONSTANT_Values_ :
;;	                    CONSTANT_Chosen_(CONSTANT_v_)} ,
;;	       \A CONSTANT_v_, CONSTANT_w_
;;	          \in {CONSTANT_v_ \in CONSTANT_Values_ :
;;	                 CONSTANT_Chosen_(CONSTANT_v_)} :
;;	          CONSTANT_v_ = CONSTANT_w_ ,
;;	       {CONSTANT_v_ \in CONSTANT_Values_ : CONSTANT_Chosen_(CONSTANT_v_)}
;;	       = {} 
;;	PROVE  /\ {CONSTANT_v_ \in CONSTANT_Values_ : CONSTANT_Chosen_(CONSTANT_v_)}
;;	          = {}
;;	       /\ \E CONSTANT_v_ \in CONSTANT_Values_ :
;;	             {CONSTANT_v__1 \in CONSTANT_Values_ :
;;	                CONSTANT_Chosen_(CONSTANT_v__1)}
;;	             = {CONSTANT_v__1 \in CONSTANT_Values_ :
;;	                  CONSTANT_Chosen_(CONSTANT_v__1)}
;;	               \cup {CONSTANT_v_}
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #253
;; Generated from file "./Paxos.tla", line 513, characters 5-6

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9 () Idv)

(declare-fun smt__TLAunderscore_underscore_Cup (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_0 () Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_1 (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

; omitted declaration of 'TLA__SetSt' (second-order)

(declare-fun smt__TLAunderscore_underscore_SubsetEq (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_TrigEqunderscore_Idv (Idv
  Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_TrigEqunderscore_Setdollarsignunderscore_Idvdollarsignunderscore_ (Idv
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

;; Axiom: SubsetEqIntro
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (=> (smt__TLAunderscore_underscore_Mem smt__z smt__x)
              (smt__TLAunderscore_underscore_Mem smt__z smt__y)))
          (smt__TLAunderscore_underscore_SubsetEq smt__x smt__y))
        :pattern ((smt__TLAunderscore_underscore_SubsetEq smt__x smt__y))))
    :named |SubsetEqIntro|))

;; Axiom: SubsetEqElim
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv) (smt__z Idv))
      (!
        (=>
          (and (smt__TLAunderscore_underscore_SubsetEq smt__x smt__y)
            (smt__TLAunderscore_underscore_Mem smt__z smt__x))
          (smt__TLAunderscore_underscore_Mem smt__z smt__y))
        :pattern ((smt__TLAunderscore_underscore_SubsetEq smt__x smt__y)
                   (smt__TLAunderscore_underscore_Mem smt__z smt__x))))
    :named |SubsetEqElim|))

;; Axiom: CupDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_Cup smt__a smt__b))
          (or (smt__TLAunderscore_underscore_Mem smt__x smt__a)
            (smt__TLAunderscore_underscore_Mem smt__x smt__b)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_Cup smt__a smt__b)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__a)
                   (smt__TLAunderscore_underscore_Cup smt__a smt__b))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__b)
                   (smt__TLAunderscore_underscore_Cup smt__a smt__b))))
    :named |CupDef|))

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

;; Axiom: EnumDefElim 0
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (not
          (smt__TLAunderscore_underscore_Mem smt__x
            smt__TLAunderscore_underscore_SetEnumunderscore_0))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    smt__TLAunderscore_underscore_SetEnumunderscore_0))))
    :named |EnumDefElim 0|))

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

;; Axiom: ExtTrigEqDef Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (= (smt__TLAunderscore_underscore_TrigEqunderscore_Idv smt__x smt__y)
          (= smt__x smt__y))
        :pattern ((smt__TLAunderscore_underscore_TrigEqunderscore_Idv 
                    smt__x smt__y)))) :named |ExtTrigEqDef Idv|))

;; Axiom: ExtTrigEqDef Set$Idv$
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_TrigEqunderscore_Setdollarsignunderscore_Idvdollarsignunderscore_
            smt__x smt__y) (= smt__x smt__y))
        :pattern ((smt__TLAunderscore_underscore_TrigEqunderscore_Setdollarsignunderscore_Idvdollarsignunderscore_
                    smt__x smt__y)))) :named |ExtTrigEqDef Set$Idv$|))

;; Axiom: ExtTrigEqTrigger Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (! (smt__TLAunderscore_underscore_SetExtTrigger smt__x smt__y)
        :pattern ((smt__TLAunderscore_underscore_TrigEqunderscore_Setdollarsignunderscore_Idvdollarsignunderscore_
                    smt__x smt__y)))) :named |ExtTrigEqTrigger Idv|))

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

(declare-fun smt__CONSTANTunderscore_Noneunderscore_ () Idv)

; hidden fact

(declare-fun smt__STATEunderscore_Initunderscore_ () Idv)

(declare-fun smt__ACTIONunderscore_Phase1aunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Phase1bunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Phase2aunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Phase2bunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Nextunderscore_ () Idv)

(declare-fun smt__TEMPORALunderscore_Specunderscore_ () Idv)

(declare-fun smt__CONSTANTunderscore_VotedForInunderscore_ (Idv Idv Idv) Idv)

(declare-fun smt__CONSTANTunderscore_ChosenInunderscore_ (Idv Idv) Idv)

(declare-fun smt__CONSTANTunderscore_Chosenunderscore_ (Idv) Idv)

(declare-fun smt__CONSTANTunderscore_Consistencyunderscore_ () Idv)

(declare-fun smt__CONSTANTunderscore_Messagesunderscore_ () Idv)

(declare-fun smt__STATEunderscore_TypeOKunderscore_ () Idv)

(declare-fun smt__STATEunderscore_WontVoteInunderscore_ (Idv Idv) Idv)

(declare-fun smt__STATEunderscore_SafeAtunderscore_ (Idv Idv) Idv)

(declare-fun smt__STATEunderscore_MsgInvunderscore_ () Idv)

; hidden fact

; hidden fact

(declare-fun smt__STATEunderscore_AccInvunderscore_ () Idv)

(declare-fun smt__STATEunderscore_Invunderscore_ () Idv)

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANTunderscore_Cexclamationmarkunderscore_Initunderscore_ () Idv)

(declare-fun smt__TEMPORALunderscore_Cexclamationmarkunderscore_Specunderscore_ () Idv)

; hidden fact

; hidden fact

; hidden fact

(assert
  (= smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9
    smt__TLAunderscore_underscore_Ttunderscore_Idv))

(assert
  (= smt__CONSTANTunderscore_Consistencyunderscore_
    smt__TLAunderscore_underscore_Ttunderscore_Idv))

(assert
  (= smt__ACTIONunderscore_Nextunderscore_
    smt__TLAunderscore_underscore_Ttunderscore_Idv))

(declare-fun smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1 (Idv) Idv)

;; Axiom: SetStDef TLA__SetSt_flatnd_1
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
              smt__a))
          (and (smt__TLAunderscore_underscore_Mem smt__x smt__a)
            (= (smt__CONSTANTunderscore_Chosenunderscore_ smt__x)
              smt__TLAunderscore_underscore_Ttunderscore_Idv)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
                      smt__a)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__a)
                   (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
                     smt__a)))) :named |SetStDef TLA__SetSt_flatnd_1|))

(assert
  (not
    (smt__TLAunderscore_underscore_TrigEqunderscore_Setdollarsignunderscore_Idvdollarsignunderscore_
      (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
        smt__CONSTANTunderscore_Valuesunderscore_)
      (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
        smt__CONSTANTunderscore_Valuesunderscore_))))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (smt__TLAunderscore_underscore_SubsetEq
    (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
      smt__CONSTANTunderscore_Valuesunderscore_)
    (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
      smt__CONSTANTunderscore_Valuesunderscore_)))

(assert
  (forall
    ((smt__CONSTANTunderscore_vunderscore_ Idv)
      (smt__CONSTANTunderscore_wunderscore_ Idv))
    (=>
      (and
        (smt__TLAunderscore_underscore_Mem
          smt__CONSTANTunderscore_vunderscore_
          (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
            smt__CONSTANTunderscore_Valuesunderscore_))
        (smt__TLAunderscore_underscore_Mem
          smt__CONSTANTunderscore_wunderscore_
          (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
            smt__CONSTANTunderscore_Valuesunderscore_)))
      (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
        smt__CONSTANTunderscore_vunderscore_
        smt__CONSTANTunderscore_wunderscore_))))

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Setdollarsignunderscore_Idvdollarsignunderscore_
    (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
      smt__CONSTANTunderscore_Valuesunderscore_)
    smt__TLAunderscore_underscore_SetEnumunderscore_0))

;; Goal
(assert
  (!
    (not
      (and
        (smt__TLAunderscore_underscore_TrigEqunderscore_Setdollarsignunderscore_Idvdollarsignunderscore_
          (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
            smt__CONSTANTunderscore_Valuesunderscore_)
          smt__TLAunderscore_underscore_SetEnumunderscore_0)
        (exists ((smt__CONSTANTunderscore_vunderscore_ Idv))
          (and
            (smt__TLAunderscore_underscore_Mem
              smt__CONSTANTunderscore_vunderscore_
              smt__CONSTANTunderscore_Valuesunderscore_)
            (smt__TLAunderscore_underscore_TrigEqunderscore_Setdollarsignunderscore_Idvdollarsignunderscore_
              (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
                smt__CONSTANTunderscore_Valuesunderscore_)
              (smt__TLAunderscore_underscore_Cup
                (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
                  smt__CONSTANTunderscore_Valuesunderscore_)
                (smt__TLAunderscore_underscore_SetEnumunderscore_1
                  smt__CONSTANTunderscore_vunderscore_))))))) :named |Goal|))

(check-sat)
(exit)
