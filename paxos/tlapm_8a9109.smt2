;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_Quorums_,
;;	       NEW VARIABLE VARIABLE_msgs_,
;;	       NEW VARIABLE VARIABLE_maxBal_,
;;	       NEW VARIABLE VARIABLE_maxVBal_,
;;	       NEW VARIABLE VARIABLE_maxVal_,
;;	       ASSUME STATE_Inv_ ,
;;	              ACTION_Next_ ,
;;	              ?h15bf9 ,
;;	              NEW CONSTANT CONSTANT_v_ \in CONSTANT_Values_,
;;	              NEW CONSTANT CONSTANT_b_ \in CONSTANT_Ballots_,
;;	              STATE_SafeAt_(CONSTANT_v_, CONSTANT_b_) 
;;	       PROVE  ?h39afa(CONSTANT_v_, CONSTANT_b_) 
;;	PROVE  STATE_Inv_ /\ ACTION_Next_ /\ ?h15bf9
;;	       => (\A CONSTANT_v_ \in CONSTANT_Values_,
;;	              CONSTANT_b_ \in CONSTANT_Ballots_ :
;;	              STATE_SafeAt_(CONSTANT_v_, CONSTANT_b_)
;;	              => ?h39afa(CONSTANT_v_, CONSTANT_b_))
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #12
;; Generated from file "./Paxos.tla", line 236, characters 3-9

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9 () Idv)

(declare-fun smt__TLAunderscore_underscore_Anonunderscore_h39afa (Idv
  Idv) Idv)

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

(assert
  (=>
    (= smt__STATEunderscore_Invunderscore_
      smt__TLAunderscore_underscore_Ttunderscore_Idv)
    (=>
      (= smt__ACTIONunderscore_Nextunderscore_
        smt__TLAunderscore_underscore_Ttunderscore_Idv)
      (=>
        (=
          smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9
          smt__TLAunderscore_underscore_Ttunderscore_Idv)
        (forall ((smt__CONSTANTunderscore_vunderscore_ Idv))
          (=>
            (smt__TLAunderscore_underscore_Mem
              smt__CONSTANTunderscore_vunderscore_
              smt__CONSTANTunderscore_Valuesunderscore_)
            (forall ((smt__CONSTANTunderscore_bunderscore_ Idv))
              (=>
                (smt__TLAunderscore_underscore_Mem
                  smt__CONSTANTunderscore_bunderscore_
                  smt__CONSTANTunderscore_Ballotsunderscore_)
                (=>
                  (=
                    (smt__STATEunderscore_SafeAtunderscore_
                      smt__CONSTANTunderscore_vunderscore_
                      smt__CONSTANTunderscore_bunderscore_)
                    smt__TLAunderscore_underscore_Ttunderscore_Idv)
                  (=
                    (smt__TLAunderscore_underscore_Anonunderscore_h39afa
                      smt__CONSTANTunderscore_vunderscore_
                      smt__CONSTANTunderscore_bunderscore_)
                    smt__TLAunderscore_underscore_Ttunderscore_Idv))))))))))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and
            (= smt__STATEunderscore_Invunderscore_
              smt__TLAunderscore_underscore_Ttunderscore_Idv)
            (= smt__ACTIONunderscore_Nextunderscore_
              smt__TLAunderscore_underscore_Ttunderscore_Idv))
          (=
            smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9
            smt__TLAunderscore_underscore_Ttunderscore_Idv))
        (forall
          ((smt__CONSTANTunderscore_vunderscore_ Idv)
            (smt__CONSTANTunderscore_bunderscore_ Idv))
          (=>
            (and
              (smt__TLAunderscore_underscore_Mem
                smt__CONSTANTunderscore_vunderscore_
                smt__CONSTANTunderscore_Valuesunderscore_)
              (smt__TLAunderscore_underscore_Mem
                smt__CONSTANTunderscore_bunderscore_
                smt__CONSTANTunderscore_Ballotsunderscore_))
            (=>
              (=
                (smt__STATEunderscore_SafeAtunderscore_
                  smt__CONSTANTunderscore_vunderscore_
                  smt__CONSTANTunderscore_bunderscore_)
                smt__TLAunderscore_underscore_Ttunderscore_Idv)
              (=
                (smt__TLAunderscore_underscore_Anonunderscore_h39afa
                  smt__CONSTANTunderscore_vunderscore_
                  smt__CONSTANTunderscore_bunderscore_)
                smt__TLAunderscore_underscore_Ttunderscore_Idv))))))
    :named |Goal|))

(check-sat)
(exit)
