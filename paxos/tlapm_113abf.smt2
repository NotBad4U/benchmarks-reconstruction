;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_Quorums_,
;;	       NEW VARIABLE VARIABLE_msgs_,
;;	       NEW VARIABLE VARIABLE_maxBal_,
;;	       NEW VARIABLE VARIABLE_maxVBal_,
;;	       NEW VARIABLE VARIABLE_maxVal_,
;;	       STATE_TypeOK_ /\ STATE_MsgInv_
;;	       /\ (\A CONSTANT_a_ \in CONSTANT_Acceptors_ :
;;	              /\ VARIABLE_maxVal_[CONSTANT_a_] = CONSTANT_None_
;;	                 <=> VARIABLE_maxVBal_[CONSTANT_a_] = -1
;;	              /\ VARIABLE_maxVBal_[CONSTANT_a_]
;;	                 =< VARIABLE_maxBal_[CONSTANT_a_]
;;	              /\ VARIABLE_maxVBal_[CONSTANT_a_] >= 0
;;	                 => CONSTANT_VotedForIn_(CONSTANT_a_,
;;	                                         VARIABLE_maxVal_[CONSTANT_a_],
;;	                                         VARIABLE_maxVBal_[CONSTANT_a_])
;;	              /\ \A CONSTANT_c_ \in Nat :
;;	                    CONSTANT_c_ > VARIABLE_maxVBal_[CONSTANT_a_]
;;	                    => ~(\E CONSTANT_v_ \in CONSTANT_Values_ :
;;	                            CONSTANT_VotedForIn_(CONSTANT_a_, CONSTANT_v_,
;;	                                                 CONSTANT_c_))) ,
;;	       ACTION_Next_ ,
;;	       NEW CONSTANT CONSTANT_a_ \in CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_m_ \in VARIABLE_msgs_,
;;	       \A CONSTANT_acc_ \in CONSTANT_Acceptors_ :
;;	          /\ ?VARIABLE_maxVal_#prime[CONSTANT_acc_] = CONSTANT_None_
;;	             <=> ?VARIABLE_maxVBal_#prime[CONSTANT_acc_] = -1
;;	          /\ ?VARIABLE_maxVBal_#prime[CONSTANT_acc_]
;;	             =< ?VARIABLE_maxBal_#prime[CONSTANT_acc_] ,
;;	       ASSUME NEW CONSTANT CONSTANT_acc_ \in CONSTANT_Acceptors_,
;;	              ?VARIABLE_maxVBal_#prime[CONSTANT_acc_] >= 0 
;;	       PROVE  CONSTANT_VotedForIn_(CONSTANT_acc_,
;;	                                   ?VARIABLE_maxVal_#prime[CONSTANT_acc_],
;;	                                   ?VARIABLE_maxVBal_#prime[CONSTANT_acc_]) ,
;;	       ASSUME NEW CONSTANT CONSTANT_acc_ \in CONSTANT_Acceptors_,
;;	              NEW CONSTANT CONSTANT_c_ \in Nat,
;;	              CONSTANT_c_ > ?VARIABLE_maxVBal_#prime[CONSTANT_acc_] ,
;;	              NEW CONSTANT CONSTANT_v_ \in CONSTANT_Values_,
;;	              CONSTANT_VotedForIn_(CONSTANT_acc_, CONSTANT_v_, CONSTANT_c_) 
;;	       PROVE  FALSE 
;;	PROVE  \A CONSTANT_a__1 \in CONSTANT_Acceptors_ :
;;	          /\ ?VARIABLE_maxVal_#prime[CONSTANT_a__1] = CONSTANT_None_
;;	             <=> ?VARIABLE_maxVBal_#prime[CONSTANT_a__1] = -1
;;	          /\ ?VARIABLE_maxVBal_#prime[CONSTANT_a__1]
;;	             =< ?VARIABLE_maxBal_#prime[CONSTANT_a__1]
;;	          /\ ?VARIABLE_maxVBal_#prime[CONSTANT_a__1] >= 0
;;	             => CONSTANT_VotedForIn_(CONSTANT_a__1,
;;	                                     ?VARIABLE_maxVal_#prime[CONSTANT_a__1],
;;	                                     ?VARIABLE_maxVBal_#prime[CONSTANT_a__1])
;;	          /\ \A CONSTANT_c_ \in Nat :
;;	                CONSTANT_c_ > ?VARIABLE_maxVBal_#prime[CONSTANT_a__1]
;;	                => ~(\E CONSTANT_v_ \in CONSTANT_Values_ :
;;	                        CONSTANT_VotedForIn_(CONSTANT_a__1, CONSTANT_v_,
;;	                                             CONSTANT_c_))
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #97
;; Generated from file "./Paxos.tla", line 335, characters 17-18

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

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_IntUminus (Idv) Idv)

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

;; Axiom: Typing TIntUminus
(assert
  (!
    (forall ((smt__x1 Int))
      (!
        (=
          (smt__TLAunderscore_underscore_IntUminus
            (smt__TLAunderscore_underscore_Castunderscore_Int smt__x1))
          (smt__TLAunderscore_underscore_Castunderscore_Int (- smt__x1)))
        :pattern ((smt__TLAunderscore_underscore_IntUminus
                    (smt__TLAunderscore_underscore_Castunderscore_Int smt__x1)))))
    :named |Typing TIntUminus|))

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
    (forall ((smt__CONSTANTunderscore_aunderscore_ Idv))
      (=>
        (smt__TLAunderscore_underscore_Mem
          smt__CONSTANTunderscore_aunderscore_
          smt__CONSTANTunderscore_Acceptorsunderscore_)
        (and
          (=
            (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
              (smt__TLAunderscore_underscore_FunApp
                smt__VARIABLEunderscore_maxValunderscore_
                smt__CONSTANTunderscore_aunderscore_)
              smt__CONSTANTunderscore_Noneunderscore_)
            (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
              (smt__TLAunderscore_underscore_FunApp
                smt__VARIABLEunderscore_maxVBalunderscore_
                smt__CONSTANTunderscore_aunderscore_)
              (smt__TLAunderscore_underscore_IntUminus
                (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
          (smt__TLAunderscore_underscore_IntLteq
            (smt__TLAunderscore_underscore_FunApp
              smt__VARIABLEunderscore_maxVBalunderscore_
              smt__CONSTANTunderscore_aunderscore_)
            (smt__TLAunderscore_underscore_FunApp
              smt__VARIABLEunderscore_maxBalunderscore_
              smt__CONSTANTunderscore_aunderscore_))
          (=>
            (smt__TLAunderscore_underscore_IntLteq
              (smt__TLAunderscore_underscore_Castunderscore_Int 0)
              (smt__TLAunderscore_underscore_FunApp
                smt__VARIABLEunderscore_maxVBalunderscore_
                smt__CONSTANTunderscore_aunderscore_))
            (=
              (smt__CONSTANTunderscore_VotedForInunderscore_
                smt__CONSTANTunderscore_aunderscore_
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxValunderscore_
                  smt__CONSTANTunderscore_aunderscore_)
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxVBalunderscore_
                  smt__CONSTANTunderscore_aunderscore_))
              smt__TLAunderscore_underscore_Ttunderscore_Idv))
          (forall ((smt__CONSTANTunderscore_cunderscore_ Idv))
            (=>
              (smt__TLAunderscore_underscore_Mem
                smt__CONSTANTunderscore_cunderscore_
                smt__TLAunderscore_underscore_NatSet)
              (=>
                (and
                  (smt__TLAunderscore_underscore_IntLteq
                    (smt__TLAunderscore_underscore_FunApp
                      smt__VARIABLEunderscore_maxVBalunderscore_
                      smt__CONSTANTunderscore_aunderscore_)
                    smt__CONSTANTunderscore_cunderscore_)
                  (not
                    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_maxVBalunderscore_
                        smt__CONSTANTunderscore_aunderscore_)
                      smt__CONSTANTunderscore_cunderscore_)))
                (not
                  (exists ((smt__CONSTANTunderscore_vunderscore_ Idv))
                    (and
                      (smt__TLAunderscore_underscore_Mem
                        smt__CONSTANTunderscore_vunderscore_
                        smt__CONSTANTunderscore_Valuesunderscore_)
                      (=
                        (smt__CONSTANTunderscore_VotedForInunderscore_
                          smt__CONSTANTunderscore_aunderscore_
                          smt__CONSTANTunderscore_vunderscore_
                          smt__CONSTANTunderscore_cunderscore_)
                        smt__TLAunderscore_underscore_Ttunderscore_Idv))))))))))))

(assert
  (= smt__ACTIONunderscore_Nextunderscore_
    smt__TLAunderscore_underscore_Ttunderscore_Idv))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANTunderscore_aunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_aunderscore_
    smt__CONSTANTunderscore_Acceptorsunderscore_))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANTunderscore_munderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_munderscore_
    smt__VARIABLEunderscore_msgsunderscore_))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (forall ((smt__CONSTANTunderscore_accunderscore_ Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem
        smt__CONSTANTunderscore_accunderscore_
        smt__CONSTANTunderscore_Acceptorsunderscore_)
      (and
        (=
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            (smt__TLAunderscore_underscore_FunApp
              smt__VARIABLEunderscore_maxValunderscore_underscore_prime
              smt__CONSTANTunderscore_accunderscore_)
            smt__CONSTANTunderscore_Noneunderscore_)
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            (smt__TLAunderscore_underscore_FunApp
              smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
              smt__CONSTANTunderscore_accunderscore_)
            (smt__TLAunderscore_underscore_IntUminus
              (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
        (smt__TLAunderscore_underscore_IntLteq
          (smt__TLAunderscore_underscore_FunApp
            smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
            smt__CONSTANTunderscore_accunderscore_)
          (smt__TLAunderscore_underscore_FunApp
            smt__VARIABLEunderscore_maxBalunderscore_underscore_prime
            smt__CONSTANTunderscore_accunderscore_))))))

(assert
  (forall ((smt__CONSTANTunderscore_accunderscore_ Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem
        smt__CONSTANTunderscore_accunderscore_
        smt__CONSTANTunderscore_Acceptorsunderscore_)
      (=>
        (smt__TLAunderscore_underscore_IntLteq
          (smt__TLAunderscore_underscore_Castunderscore_Int 0)
          (smt__TLAunderscore_underscore_FunApp
            smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
            smt__CONSTANTunderscore_accunderscore_))
        (=
          (smt__CONSTANTunderscore_VotedForInunderscore_
            smt__CONSTANTunderscore_accunderscore_
            (smt__TLAunderscore_underscore_FunApp
              smt__VARIABLEunderscore_maxValunderscore_underscore_prime
              smt__CONSTANTunderscore_accunderscore_)
            (smt__TLAunderscore_underscore_FunApp
              smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
              smt__CONSTANTunderscore_accunderscore_))
          smt__TLAunderscore_underscore_Ttunderscore_Idv)))))

(assert
  (forall ((smt__CONSTANTunderscore_accunderscore_ Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem
        smt__CONSTANTunderscore_accunderscore_
        smt__CONSTANTunderscore_Acceptorsunderscore_)
      (forall ((smt__CONSTANTunderscore_cunderscore_ Idv))
        (=>
          (smt__TLAunderscore_underscore_Mem
            smt__CONSTANTunderscore_cunderscore_
            smt__TLAunderscore_underscore_NatSet)
          (=>
            (and
              (smt__TLAunderscore_underscore_IntLteq
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
                  smt__CONSTANTunderscore_accunderscore_)
                smt__CONSTANTunderscore_cunderscore_)
              (not
                (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                  (smt__TLAunderscore_underscore_FunApp
                    smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
                    smt__CONSTANTunderscore_accunderscore_)
                  smt__CONSTANTunderscore_cunderscore_)))
            (forall ((smt__CONSTANTunderscore_vunderscore_ Idv))
              (=>
                (smt__TLAunderscore_underscore_Mem
                  smt__CONSTANTunderscore_vunderscore_
                  smt__CONSTANTunderscore_Valuesunderscore_)
                (=>
                  (=
                    (smt__CONSTANTunderscore_VotedForInunderscore_
                      smt__CONSTANTunderscore_accunderscore_
                      smt__CONSTANTunderscore_vunderscore_
                      smt__CONSTANTunderscore_cunderscore_)
                    smt__TLAunderscore_underscore_Ttunderscore_Idv) false)))))))))

;; Goal
(assert
  (!
    (not
      (forall ((smt__CONSTANTunderscore_aunderscore__1 Idv))
        (=>
          (smt__TLAunderscore_underscore_Mem
            smt__CONSTANTunderscore_aunderscore__1
            smt__CONSTANTunderscore_Acceptorsunderscore_)
          (and
            (=
              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxValunderscore_underscore_prime
                  smt__CONSTANTunderscore_aunderscore__1)
                smt__CONSTANTunderscore_Noneunderscore_)
              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
                  smt__CONSTANTunderscore_aunderscore__1)
                (smt__TLAunderscore_underscore_IntUminus
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
            (smt__TLAunderscore_underscore_IntLteq
              (smt__TLAunderscore_underscore_FunApp
                smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
                smt__CONSTANTunderscore_aunderscore__1)
              (smt__TLAunderscore_underscore_FunApp
                smt__VARIABLEunderscore_maxBalunderscore_underscore_prime
                smt__CONSTANTunderscore_aunderscore__1))
            (=>
              (smt__TLAunderscore_underscore_IntLteq
                (smt__TLAunderscore_underscore_Castunderscore_Int 0)
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
                  smt__CONSTANTunderscore_aunderscore__1))
              (=
                (smt__CONSTANTunderscore_VotedForInunderscore_
                  smt__CONSTANTunderscore_aunderscore__1
                  (smt__TLAunderscore_underscore_FunApp
                    smt__VARIABLEunderscore_maxValunderscore_underscore_prime
                    smt__CONSTANTunderscore_aunderscore__1)
                  (smt__TLAunderscore_underscore_FunApp
                    smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
                    smt__CONSTANTunderscore_aunderscore__1))
                smt__TLAunderscore_underscore_Ttunderscore_Idv))
            (forall ((smt__CONSTANTunderscore_cunderscore_ Idv))
              (=>
                (smt__TLAunderscore_underscore_Mem
                  smt__CONSTANTunderscore_cunderscore_
                  smt__TLAunderscore_underscore_NatSet)
                (=>
                  (and
                    (smt__TLAunderscore_underscore_IntLteq
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
                        smt__CONSTANTunderscore_aunderscore__1)
                      smt__CONSTANTunderscore_cunderscore_)
                    (not
                      (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                        (smt__TLAunderscore_underscore_FunApp
                          smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
                          smt__CONSTANTunderscore_aunderscore__1)
                        smt__CONSTANTunderscore_cunderscore_)))
                  (not
                    (exists ((smt__CONSTANTunderscore_vunderscore_ Idv))
                      (and
                        (smt__TLAunderscore_underscore_Mem
                          smt__CONSTANTunderscore_vunderscore_
                          smt__CONSTANTunderscore_Valuesunderscore_)
                        (=
                          (smt__CONSTANTunderscore_VotedForInunderscore_
                            smt__CONSTANTunderscore_aunderscore__1
                            smt__CONSTANTunderscore_vunderscore_
                            smt__CONSTANTunderscore_cunderscore_)
                          smt__TLAunderscore_underscore_Ttunderscore_Idv)))))))))))
    :named |Goal|))

(check-sat)
(exit)
