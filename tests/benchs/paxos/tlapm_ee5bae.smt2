;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_Quorums_,
;;	       NEW VARIABLE VARIABLE_msgs_,
;;	       NEW VARIABLE VARIABLE_maxBal_,
;;	       NEW VARIABLE VARIABLE_maxVBal_,
;;	       NEW VARIABLE VARIABLE_maxVal_,
;;	       STATE_TypeOK_ /\ STATE_MsgInv_ /\ STATE_AccInv_ ,
;;	       \/ \E CONSTANT_b_ \in Nat :
;;	             ACTION_Phase1a_(CONSTANT_b_) \/ ACTION_Phase2a_(CONSTANT_b_)
;;	       \/ \E CONSTANT_a_ \in CONSTANT_Acceptors_ :
;;	             ACTION_Phase1b_(CONSTANT_a_) \/ ACTION_Phase2b_(CONSTANT_a_) ,
;;	       ASSUME NEW CONSTANT CONSTANT_b_ \in Nat,
;;	              ACTION_Phase1a_(CONSTANT_b_) 
;;	       PROVE  ?h6d380 ,
;;	       ASSUME NEW CONSTANT CONSTANT_b_ \in Nat,
;;	              ACTION_Phase2a_(CONSTANT_b_) 
;;	       PROVE  ?h6d380 ,
;;	       ASSUME NEW CONSTANT CONSTANT_a_ \in CONSTANT_Acceptors_,
;;	              ACTION_Phase1b_(CONSTANT_a_) 
;;	       PROVE  ?h6d380 ,
;;	       ASSUME NEW CONSTANT CONSTANT_a_ \in CONSTANT_Acceptors_,
;;	              ACTION_Phase2b_(CONSTANT_a_) 
;;	       PROVE  ?h6d380 
;;	PROVE  ?h6d380
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #80
;; Generated from file "./Paxos.tla", line 336, characters 15-16

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h6d380 () Idv)

(declare-fun smt__TLAunderscore_underscore_Castunderscore_Int (Int) Idv)

(declare-fun smt__TLAunderscore_underscore_IntLteq (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_NatSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Projunderscore_Int (Idv) Int)

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

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (and
    (and
      (= smt__STATEunderscore_TypeOKunderscore_
        smt__TLAunderscore_underscore_Ttunderscore_Idv)
      (= smt__STATEunderscore_MsgInvunderscore_
        smt__TLAunderscore_underscore_Ttunderscore_Idv))
    (= smt__STATEunderscore_AccInvunderscore_
      smt__TLAunderscore_underscore_Ttunderscore_Idv)))

(assert
  (or
    (exists ((smt__CONSTANTunderscore_bunderscore_ Idv))
      (and
        (smt__TLAunderscore_underscore_Mem
          smt__CONSTANTunderscore_bunderscore_
          smt__TLAunderscore_underscore_NatSet)
        (or
          (=
            (smt__ACTIONunderscore_Phase1aunderscore_
              smt__CONSTANTunderscore_bunderscore_)
            smt__TLAunderscore_underscore_Ttunderscore_Idv)
          (=
            (smt__ACTIONunderscore_Phase2aunderscore_
              smt__CONSTANTunderscore_bunderscore_)
            smt__TLAunderscore_underscore_Ttunderscore_Idv))))
    (exists ((smt__CONSTANTunderscore_aunderscore_ Idv))
      (and
        (smt__TLAunderscore_underscore_Mem
          smt__CONSTANTunderscore_aunderscore_
          smt__CONSTANTunderscore_Acceptorsunderscore_)
        (or
          (=
            (smt__ACTIONunderscore_Phase1bunderscore_
              smt__CONSTANTunderscore_aunderscore_)
            smt__TLAunderscore_underscore_Ttunderscore_Idv)
          (=
            (smt__ACTIONunderscore_Phase2bunderscore_
              smt__CONSTANTunderscore_aunderscore_)
            smt__TLAunderscore_underscore_Ttunderscore_Idv))))))

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
  (forall ((smt__CONSTANTunderscore_bunderscore_ Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_bunderscore_
        smt__TLAunderscore_underscore_NatSet)
      (=>
        (=
          (smt__ACTIONunderscore_Phase1aunderscore_
            smt__CONSTANTunderscore_bunderscore_)
          smt__TLAunderscore_underscore_Ttunderscore_Idv)
        (=
          smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h6d380
          smt__TLAunderscore_underscore_Ttunderscore_Idv)))))

(assert
  (forall ((smt__CONSTANTunderscore_bunderscore_ Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_bunderscore_
        smt__TLAunderscore_underscore_NatSet)
      (=>
        (=
          (smt__ACTIONunderscore_Phase2aunderscore_
            smt__CONSTANTunderscore_bunderscore_)
          smt__TLAunderscore_underscore_Ttunderscore_Idv)
        (=
          smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h6d380
          smt__TLAunderscore_underscore_Ttunderscore_Idv)))))

(assert
  (forall ((smt__CONSTANTunderscore_aunderscore_ Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_aunderscore_
        smt__CONSTANTunderscore_Acceptorsunderscore_)
      (=>
        (=
          (smt__ACTIONunderscore_Phase1bunderscore_
            smt__CONSTANTunderscore_aunderscore_)
          smt__TLAunderscore_underscore_Ttunderscore_Idv)
        (=
          smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h6d380
          smt__TLAunderscore_underscore_Ttunderscore_Idv)))))

(assert
  (forall ((smt__CONSTANTunderscore_aunderscore_ Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_aunderscore_
        smt__CONSTANTunderscore_Acceptorsunderscore_)
      (=>
        (=
          (smt__ACTIONunderscore_Phase2bunderscore_
            smt__CONSTANTunderscore_aunderscore_)
          smt__TLAunderscore_underscore_Ttunderscore_Idv)
        (=
          smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h6d380
          smt__TLAunderscore_underscore_Ttunderscore_Idv)))))

;; Goal
(assert
  (!
    (not
      (= smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h6d380
        smt__TLAunderscore_underscore_Ttunderscore_Idv)) :named |Goal|))

(check-sat)
(exit)
