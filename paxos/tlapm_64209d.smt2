;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_Quorums_,
;;	       NEW VARIABLE VARIABLE_msgs_,
;;	       NEW VARIABLE VARIABLE_maxBal_,
;;	       NEW VARIABLE VARIABLE_maxVBal_,
;;	       NEW VARIABLE VARIABLE_maxVal_,
;;	       STATE_Inv_ ,
;;	       NEW CONSTANT CONSTANT_v1_ \in CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_v2_ \in CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_b1_ \in Nat,
;;	       NEW CONSTANT CONSTANT_b2_ \in Nat,
;;	       CONSTANT_ChosenIn_(CONSTANT_v1_, CONSTANT_b1_) ,
;;	       CONSTANT_ChosenIn_(CONSTANT_v2_, CONSTANT_b2_) ,
;;	       CONSTANT_b1_ =< CONSTANT_b2_ ,
;;	       ASSUME CONSTANT_b1_ = CONSTANT_b2_ 
;;	       PROVE  CONSTANT_v1_ = CONSTANT_v2_ ,
;;	       ASSUME CONSTANT_b1_ < CONSTANT_b2_ 
;;	       PROVE  CONSTANT_v1_ = CONSTANT_v2_ 
;;	PROVE  CONSTANT_v1_ = CONSTANT_v2_
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #223
;; Generated from file "./Paxos.tla", line 485, characters 13-14

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_Castunderscore_Int (Int) Idv)

(declare-fun smt__TLAunderscore_underscore_IntLteq (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_NatSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Projunderscore_Int (Idv) Int)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

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

(declare-fun smt__CONSTANTunderscore_Acceptorsunderscore_ () Idv)

(declare-fun smt__CONSTANTunderscore_Valuesunderscore_ () Idv)

(declare-fun smt__CONSTANTunderscore_Quorumsunderscore_ () Idv)

; hidden fact

; hidden fact

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

; hidden fact

(assert
  (= smt__STATEunderscore_Invunderscore_
    smt__TLAunderscore_underscore_Ttunderscore_Idv))

(declare-fun smt__CONSTANTunderscore_v1underscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_v1underscore_
    smt__CONSTANTunderscore_Valuesunderscore_))

(declare-fun smt__CONSTANTunderscore_v2underscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_v2underscore_
    smt__CONSTANTunderscore_Valuesunderscore_))

(declare-fun smt__CONSTANTunderscore_b1underscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_b1underscore_
    smt__TLAunderscore_underscore_NatSet))

(declare-fun smt__CONSTANTunderscore_b2underscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_b2underscore_
    smt__TLAunderscore_underscore_NatSet))

(assert
  (=
    (smt__CONSTANTunderscore_ChosenInunderscore_
      smt__CONSTANTunderscore_v1underscore_
      smt__CONSTANTunderscore_b1underscore_)
    smt__TLAunderscore_underscore_Ttunderscore_Idv))

(assert
  (=
    (smt__CONSTANTunderscore_ChosenInunderscore_
      smt__CONSTANTunderscore_v2underscore_
      smt__CONSTANTunderscore_b2underscore_)
    smt__TLAunderscore_underscore_Ttunderscore_Idv))

(assert
  (smt__TLAunderscore_underscore_IntLteq
    smt__CONSTANTunderscore_b1underscore_
    smt__CONSTANTunderscore_b2underscore_))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (=>
    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
      smt__CONSTANTunderscore_b1underscore_
      smt__CONSTANTunderscore_b2underscore_)
    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
      smt__CONSTANTunderscore_v1underscore_
      smt__CONSTANTunderscore_v2underscore_)))

(assert
  (=>
    (and
      (smt__TLAunderscore_underscore_IntLteq
        smt__CONSTANTunderscore_b1underscore_
        smt__CONSTANTunderscore_b2underscore_)
      (not
        (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
          smt__CONSTANTunderscore_b1underscore_
          smt__CONSTANTunderscore_b2underscore_)))
    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
      smt__CONSTANTunderscore_v1underscore_
      smt__CONSTANTunderscore_v2underscore_)))

;; Goal
(assert
  (!
    (not
      (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
        smt__CONSTANTunderscore_v1underscore_
        smt__CONSTANTunderscore_v2underscore_)) :named |Goal|))

(check-sat)
(exit)
