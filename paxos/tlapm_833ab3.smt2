;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_Quorums_,
;;	       NEW VARIABLE VARIABLE_msgs_,
;;	       NEW VARIABLE VARIABLE_maxBal_,
;;	       NEW VARIABLE VARIABLE_maxVBal_,
;;	       NEW VARIABLE VARIABLE_maxVal_,
;;	       ASSUME ?h15bf9 ,
;;	              CONSTANT_Consistency_ ,
;;	              ACTION_Next_ ,
;;	              {CONSTANT_v_ \in CONSTANT_Values_ :
;;	                 \E CONSTANT_b_ \in CONSTANT_Ballots_ :
;;	                    \E CONSTANT_Q_ \in CONSTANT_Quorums_ :
;;	                       \A CONSTANT_a_ \in CONSTANT_Q_ :
;;	                          \E CONSTANT_m_ \in ?VARIABLE_msgs_#prime :
;;	                             /\ CONSTANT_m_.type = "2b"
;;	                             /\ CONSTANT_m_.val = CONSTANT_v_
;;	                             /\ CONSTANT_m_.bal = CONSTANT_b_
;;	                             /\ CONSTANT_m_.acc = CONSTANT_a_}
;;	              # {CONSTANT_v_ \in CONSTANT_Values_ :
;;	                   \E CONSTANT_b_ \in CONSTANT_Ballots_ :
;;	                      \E CONSTANT_Q_ \in CONSTANT_Quorums_ :
;;	                         \A CONSTANT_a_ \in CONSTANT_Q_ :
;;	                            \E CONSTANT_m_ \in VARIABLE_msgs_ :
;;	                               /\ CONSTANT_m_.type = "2b"
;;	                               /\ CONSTANT_m_.val = CONSTANT_v_
;;	                               /\ CONSTANT_m_.bal = CONSTANT_b_
;;	                               /\ CONSTANT_m_.acc = CONSTANT_a_} 
;;	       PROVE  ACTION_C!Next_ 
;;	PROVE  ?h15bf9 /\ CONSTANT_Consistency_
;;	       /\ (ACTION_Next_
;;	           \/ (/\ ?VARIABLE_msgs_#prime = VARIABLE_msgs_
;;	               /\ ?VARIABLE_maxBal_#prime = VARIABLE_maxBal_
;;	               /\ ?VARIABLE_maxVBal_#prime = VARIABLE_maxVBal_
;;	               /\ ?VARIABLE_maxVal_#prime = VARIABLE_maxVal_))
;;	       => ACTION_C!Next_
;;	          \/ {CONSTANT_v_ \in CONSTANT_Values_ :
;;	                \E CONSTANT_b_ \in CONSTANT_Ballots_ :
;;	                   \E CONSTANT_Q_ \in CONSTANT_Quorums_ :
;;	                      \A CONSTANT_a_ \in CONSTANT_Q_ :
;;	                         \E CONSTANT_m_ \in ?VARIABLE_msgs_#prime :
;;	                            /\ CONSTANT_m_.type = "2b"
;;	                            /\ CONSTANT_m_.val = CONSTANT_v_
;;	                            /\ CONSTANT_m_.bal = CONSTANT_b_
;;	                            /\ CONSTANT_m_.acc = CONSTANT_a_}
;;	             = {CONSTANT_v_ \in CONSTANT_Values_ :
;;	                  \E CONSTANT_b_ \in CONSTANT_Ballots_ :
;;	                     \E CONSTANT_Q_ \in CONSTANT_Quorums_ :
;;	                        \A CONSTANT_a_ \in CONSTANT_Q_ :
;;	                           \E CONSTANT_m_ \in VARIABLE_msgs_ :
;;	                              /\ CONSTANT_m_.type = "2b"
;;	                              /\ CONSTANT_m_.val = CONSTANT_v_
;;	                              /\ CONSTANT_m_.bal = CONSTANT_b_
;;	                              /\ CONSTANT_m_.acc = CONSTANT_a_}
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #257
;; Generated from file "./Paxos.tla", line 505, characters 5-6

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9 () Idv)

(declare-fun smt__TLAunderscore_underscore_FunApp (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLAunderscore_underscore_FunIsafcn (Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_0 () Idv)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

; omitted declaration of 'TLA__SetSt' (second-order)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_2b () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_acc () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_bal () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_type () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_val () Idv)

(declare-fun smt__TLAunderscore_underscore_StrSet () Idv)

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

; omitted fact (second-order)

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

; omitted fact (second-order)

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

;; Axiom: StrLitIsstr 2b
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr 2b|))

;; Axiom: StrLitIsstr acc
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_acc
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr acc|))

;; Axiom: StrLitIsstr bal
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_bal
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr bal|))

;; Axiom: StrLitIsstr type
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_type
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr type|))

;; Axiom: StrLitIsstr val
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr val|))

;; Axiom: StrLitDistinct 2b type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct 2b type|))

;; Axiom: StrLitDistinct acc 2b
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_acc
      smt__TLAunderscore_underscore_StrLitunderscore_2b)
    :named |StrLitDistinct acc 2b|))

;; Axiom: StrLitDistinct acc bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_acc
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct acc bal|))

;; Axiom: StrLitDistinct acc type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_acc
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct acc type|))

;; Axiom: StrLitDistinct acc val
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_acc
      smt__TLAunderscore_underscore_StrLitunderscore_val)
    :named |StrLitDistinct acc val|))

;; Axiom: StrLitDistinct bal 2b
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_bal
      smt__TLAunderscore_underscore_StrLitunderscore_2b)
    :named |StrLitDistinct bal 2b|))

;; Axiom: StrLitDistinct bal type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_bal
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct bal type|))

;; Axiom: StrLitDistinct bal val
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_bal
      smt__TLAunderscore_underscore_StrLitunderscore_val)
    :named |StrLitDistinct bal val|))

;; Axiom: StrLitDistinct val 2b
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrLitunderscore_2b)
    :named |StrLitDistinct val 2b|))

;; Axiom: StrLitDistinct val type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct val type|))

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

(declare-fun smt__ACTIONunderscore_Cexclamationmarkunderscore_Nextunderscore_ () Idv)

(declare-fun smt__TEMPORALunderscore_Cexclamationmarkunderscore_Specunderscore_ () Idv)

; hidden fact

; hidden fact

; hidden fact

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
            (exists ((smt__CONSTANTunderscore_bunderscore_ Idv))
              (and
                (smt__TLAunderscore_underscore_Mem
                  smt__CONSTANTunderscore_bunderscore_
                  smt__CONSTANTunderscore_Ballotsunderscore_)
                (exists ((smt__CONSTANTunderscore_Qunderscore_ Idv))
                  (and
                    (smt__TLAunderscore_underscore_Mem
                      smt__CONSTANTunderscore_Qunderscore_
                      smt__CONSTANTunderscore_Quorumsunderscore_)
                    (forall ((smt__CONSTANTunderscore_aunderscore_ Idv))
                      (=>
                        (smt__TLAunderscore_underscore_Mem
                          smt__CONSTANTunderscore_aunderscore_
                          smt__CONSTANTunderscore_Qunderscore_)
                        (exists ((smt__CONSTANTunderscore_munderscore_ Idv))
                          (and
                            (smt__TLAunderscore_underscore_Mem
                              smt__CONSTANTunderscore_munderscore_
                              smt__VARIABLEunderscore_msgsunderscore_underscore_prime)
                            (and
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_type)
                                smt__TLAunderscore_underscore_StrLitunderscore_2b)
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_val)
                                smt__x)
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                                smt__CONSTANTunderscore_bunderscore_)
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_acc)
                                smt__CONSTANTunderscore_aunderscore_))))))))))))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
                      smt__a)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__a)
                   (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
                     smt__a)))) :named |SetStDef TLA__SetSt_flatnd_1|))

(declare-fun smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_2 (Idv) Idv)

;; Axiom: SetStDef TLA__SetSt_flatnd_2
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_2
              smt__a))
          (and (smt__TLAunderscore_underscore_Mem smt__x smt__a)
            (exists ((smt__CONSTANTunderscore_bunderscore_ Idv))
              (and
                (smt__TLAunderscore_underscore_Mem
                  smt__CONSTANTunderscore_bunderscore_
                  smt__CONSTANTunderscore_Ballotsunderscore_)
                (exists ((smt__CONSTANTunderscore_Qunderscore_ Idv))
                  (and
                    (smt__TLAunderscore_underscore_Mem
                      smt__CONSTANTunderscore_Qunderscore_
                      smt__CONSTANTunderscore_Quorumsunderscore_)
                    (forall ((smt__CONSTANTunderscore_aunderscore_ Idv))
                      (=>
                        (smt__TLAunderscore_underscore_Mem
                          smt__CONSTANTunderscore_aunderscore_
                          smt__CONSTANTunderscore_Qunderscore_)
                        (exists ((smt__CONSTANTunderscore_munderscore_ Idv))
                          (and
                            (smt__TLAunderscore_underscore_Mem
                              smt__CONSTANTunderscore_munderscore_
                              smt__VARIABLEunderscore_msgsunderscore_)
                            (and
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_type)
                                smt__TLAunderscore_underscore_StrLitunderscore_2b)
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_val)
                                smt__x)
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                                smt__CONSTANTunderscore_bunderscore_)
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_acc)
                                smt__CONSTANTunderscore_aunderscore_))))))))))))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_2
                      smt__a)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__a)
                   (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_2
                     smt__a)))) :named |SetStDef TLA__SetSt_flatnd_2|))

(assert
  (=>
    (= smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9
      smt__TLAunderscore_underscore_Ttunderscore_Idv)
    (=>
      (= smt__CONSTANTunderscore_Consistencyunderscore_
        smt__TLAunderscore_underscore_Ttunderscore_Idv)
      (=>
        (= smt__ACTIONunderscore_Nextunderscore_
          smt__TLAunderscore_underscore_Ttunderscore_Idv)
        (=>
          (not
            (smt__TLAunderscore_underscore_TrigEqunderscore_Setdollarsignunderscore_Idvdollarsignunderscore_
              (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
                smt__CONSTANTunderscore_Valuesunderscore_)
              (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_2
                smt__CONSTANTunderscore_Valuesunderscore_)))
          (= smt__ACTIONunderscore_Cexclamationmarkunderscore_Nextunderscore_
            smt__TLAunderscore_underscore_Ttunderscore_Idv))))))

(declare-fun smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_3 (Idv) Idv)

;; Axiom: SetStDef TLA__SetSt_flatnd_3
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_3
              smt__a))
          (and (smt__TLAunderscore_underscore_Mem smt__x smt__a)
            (exists ((smt__CONSTANTunderscore_bunderscore_ Idv))
              (and
                (smt__TLAunderscore_underscore_Mem
                  smt__CONSTANTunderscore_bunderscore_
                  smt__CONSTANTunderscore_Ballotsunderscore_)
                (exists ((smt__CONSTANTunderscore_Qunderscore_ Idv))
                  (and
                    (smt__TLAunderscore_underscore_Mem
                      smt__CONSTANTunderscore_Qunderscore_
                      smt__CONSTANTunderscore_Quorumsunderscore_)
                    (forall ((smt__CONSTANTunderscore_aunderscore_ Idv))
                      (=>
                        (smt__TLAunderscore_underscore_Mem
                          smt__CONSTANTunderscore_aunderscore_
                          smt__CONSTANTunderscore_Qunderscore_)
                        (exists ((smt__CONSTANTunderscore_munderscore_ Idv))
                          (and
                            (smt__TLAunderscore_underscore_Mem
                              smt__CONSTANTunderscore_munderscore_
                              smt__VARIABLEunderscore_msgsunderscore_underscore_prime)
                            (and
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_type)
                                smt__TLAunderscore_underscore_StrLitunderscore_2b)
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_val)
                                smt__x)
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                                smt__CONSTANTunderscore_bunderscore_)
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_acc)
                                smt__CONSTANTunderscore_aunderscore_))))))))))))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_3
                      smt__a)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__a)
                   (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_3
                     smt__a)))) :named |SetStDef TLA__SetSt_flatnd_3|))

(declare-fun smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_4 (Idv) Idv)

;; Axiom: SetStDef TLA__SetSt_flatnd_4
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_4
              smt__a))
          (and (smt__TLAunderscore_underscore_Mem smt__x smt__a)
            (exists ((smt__CONSTANTunderscore_bunderscore_ Idv))
              (and
                (smt__TLAunderscore_underscore_Mem
                  smt__CONSTANTunderscore_bunderscore_
                  smt__CONSTANTunderscore_Ballotsunderscore_)
                (exists ((smt__CONSTANTunderscore_Qunderscore_ Idv))
                  (and
                    (smt__TLAunderscore_underscore_Mem
                      smt__CONSTANTunderscore_Qunderscore_
                      smt__CONSTANTunderscore_Quorumsunderscore_)
                    (forall ((smt__CONSTANTunderscore_aunderscore_ Idv))
                      (=>
                        (smt__TLAunderscore_underscore_Mem
                          smt__CONSTANTunderscore_aunderscore_
                          smt__CONSTANTunderscore_Qunderscore_)
                        (exists ((smt__CONSTANTunderscore_munderscore_ Idv))
                          (and
                            (smt__TLAunderscore_underscore_Mem
                              smt__CONSTANTunderscore_munderscore_
                              smt__VARIABLEunderscore_msgsunderscore_)
                            (and
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_type)
                                smt__TLAunderscore_underscore_StrLitunderscore_2b)
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_val)
                                smt__x)
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                                smt__CONSTANTunderscore_bunderscore_)
                              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                (smt__TLAunderscore_underscore_FunApp
                                  smt__CONSTANTunderscore_munderscore_
                                  smt__TLAunderscore_underscore_StrLitunderscore_acc)
                                smt__CONSTANTunderscore_aunderscore_))))))))))))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_4
                      smt__a)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__a)
                   (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_4
                     smt__a)))) :named |SetStDef TLA__SetSt_flatnd_4|))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and
            (=
              smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9
              smt__TLAunderscore_underscore_Ttunderscore_Idv)
            (= smt__CONSTANTunderscore_Consistencyunderscore_
              smt__TLAunderscore_underscore_Ttunderscore_Idv))
          (or
            (= smt__ACTIONunderscore_Nextunderscore_
              smt__TLAunderscore_underscore_Ttunderscore_Idv)
            (and
              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                smt__VARIABLEunderscore_msgsunderscore_underscore_prime
                smt__VARIABLEunderscore_msgsunderscore_)
              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                smt__VARIABLEunderscore_maxBalunderscore_underscore_prime
                smt__VARIABLEunderscore_maxBalunderscore_)
              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
                smt__VARIABLEunderscore_maxVBalunderscore_)
              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                smt__VARIABLEunderscore_maxValunderscore_underscore_prime
                smt__VARIABLEunderscore_maxValunderscore_))))
        (or
          (= smt__ACTIONunderscore_Cexclamationmarkunderscore_Nextunderscore_
            smt__TLAunderscore_underscore_Ttunderscore_Idv)
          (smt__TLAunderscore_underscore_TrigEqunderscore_Setdollarsignunderscore_Idvdollarsignunderscore_
            (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_3
              smt__CONSTANTunderscore_Valuesunderscore_)
            (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_4
              smt__CONSTANTunderscore_Valuesunderscore_))))) :named |Goal|))

(check-sat)
(exit)
