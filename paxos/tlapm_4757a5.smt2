;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_Quorums_,
;;	       NEW VARIABLE VARIABLE_msgs_,
;;	       NEW VARIABLE VARIABLE_maxBal_,
;;	       NEW VARIABLE VARIABLE_maxVBal_,
;;	       NEW VARIABLE VARIABLE_maxVal_,
;;	       STATE_TypeOK_ /\ STATE_MsgInv_ /\ STATE_AccInv_ ,
;;	       ACTION_Next_ ,
;;	       NEW CONSTANT CONSTANT_b_ \in Nat,
;;	       NEW CONSTANT CONSTANT_v_ \in CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_Q_ \in CONSTANT_Quorums_,
;;	       NEW CONSTANT CONSTANT_S_ \in SUBSET {CONSTANT_m_ \in VARIABLE_msgs_ :
;;	                                              CONSTANT_m_.type = "1b"
;;	                                              /\ CONSTANT_m_.bal
;;	                                                 = CONSTANT_b_},
;;	       NEW CONSTANT CONSTANT_c_ \in 0..CONSTANT_b_ - 1,
;;	       NEW CONSTANT CONSTANT_ma_ \in CONSTANT_S_,
;;	       NEW CONSTANT CONSTANT_d_ \in 0..CONSTANT_b_ - 1,
;;	       CONSTANT_d_ = CONSTANT_c_ ,
;;	       \A CONSTANT_q_ \in CONSTANT_Q_, CONSTANT_w_ \in CONSTANT_Values_ :
;;	          CONSTANT_VotedForIn_(CONSTANT_q_, CONSTANT_w_, CONSTANT_c_)
;;	          => CONSTANT_w_ = CONSTANT_v_ ,
;;	       \A CONSTANT_q_ \in CONSTANT_Q_ :
;;	          VARIABLE_maxBal_[CONSTANT_q_] > CONSTANT_c_ 
;;	PROVE  \E CONSTANT_QQ_ \in CONSTANT_Quorums_ :
;;	          \A CONSTANT_q_ \in CONSTANT_QQ_ :
;;	             CONSTANT_VotedForIn_(CONSTANT_q_, CONSTANT_v_, CONSTANT_d_)
;;	             \/ (/\ \A CONSTANT_v__1 \in CONSTANT_Values_ :
;;	                       ~CONSTANT_VotedForIn_(CONSTANT_q_, CONSTANT_v__1,
;;	                                             CONSTANT_d_)
;;	                 /\ VARIABLE_maxBal_[CONSTANT_q_] > CONSTANT_d_)
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #189
;; Generated from file "./Paxos.tla", line 425, characters 15-16

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

(declare-fun smt__TLAunderscore_underscore_IntMinus (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntRange (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_NatSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Projunderscore_Int (Idv) Int)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_0 () Idv)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

; omitted declaration of 'TLA__SetSt' (second-order)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_1b () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_bal () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_type () Idv)

(declare-fun smt__TLAunderscore_underscore_StrSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Subset (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SubsetEq (Idv Idv) Bool)

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

;; Axiom: SubsetDefAlt
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_Subset smt__a))
          (smt__TLAunderscore_underscore_SubsetEq smt__x smt__a))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_Subset smt__a)))
        :pattern ((smt__TLAunderscore_underscore_SubsetEq smt__x smt__a)
                   (smt__TLAunderscore_underscore_Subset smt__a))))
    :named |SubsetDefAlt|))

; omitted fact (second-order)

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

;; Axiom: StrLitIsstr 1b
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_1b
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr 1b|))

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

;; Axiom: StrLitDistinct 1b type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1b
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct 1b type|))

;; Axiom: StrLitDistinct bal 1b
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_bal
      smt__TLAunderscore_underscore_StrLitunderscore_1b)
    :named |StrLitDistinct bal 1b|))

;; Axiom: StrLitDistinct bal type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_bal
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct bal type|))

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

(declare-fun smt__CONSTANTunderscore_bunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_bunderscore_
    smt__TLAunderscore_underscore_NatSet))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANTunderscore_vunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_vunderscore_
    smt__CONSTANTunderscore_Valuesunderscore_))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANTunderscore_Qunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_Qunderscore_
    smt__CONSTANTunderscore_Quorumsunderscore_))

(declare-fun smt__CONSTANTunderscore_Sunderscore_ () Idv)

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
            (and
              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                (smt__TLAunderscore_underscore_FunApp smt__x
                  smt__TLAunderscore_underscore_StrLitunderscore_type)
                smt__TLAunderscore_underscore_StrLitunderscore_1b)
              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                (smt__TLAunderscore_underscore_FunApp smt__x
                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                smt__CONSTANTunderscore_bunderscore_))))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
                      smt__a)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x smt__a)
                   (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
                     smt__a)))) :named |SetStDef TLA__SetSt_flatnd_1|))

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_Sunderscore_
    (smt__TLAunderscore_underscore_Subset
      (smt__TLAunderscore_underscore_SetStunderscore_flatndunderscore_1
        smt__VARIABLEunderscore_msgsunderscore_))))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANTunderscore_cunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_cunderscore_
    (smt__TLAunderscore_underscore_IntRange
      (smt__TLAunderscore_underscore_Castunderscore_Int 0)
      (smt__TLAunderscore_underscore_IntMinus
        smt__CONSTANTunderscore_bunderscore_
        (smt__TLAunderscore_underscore_Castunderscore_Int 1)))))

; hidden fact

(declare-fun smt__CONSTANTunderscore_maunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_maunderscore_
    smt__CONSTANTunderscore_Sunderscore_))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANTunderscore_dunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_dunderscore_
    (smt__TLAunderscore_underscore_IntRange
      (smt__TLAunderscore_underscore_Castunderscore_Int 0)
      (smt__TLAunderscore_underscore_IntMinus
        smt__CONSTANTunderscore_bunderscore_
        (smt__TLAunderscore_underscore_Castunderscore_Int 1)))))

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
  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
    smt__CONSTANTunderscore_dunderscore_ smt__CONSTANTunderscore_cunderscore_))

(assert
  (forall
    ((smt__CONSTANTunderscore_qunderscore_ Idv)
      (smt__CONSTANTunderscore_wunderscore_ Idv))
    (=>
      (and
        (smt__TLAunderscore_underscore_Mem
          smt__CONSTANTunderscore_qunderscore_
          smt__CONSTANTunderscore_Qunderscore_)
        (smt__TLAunderscore_underscore_Mem
          smt__CONSTANTunderscore_wunderscore_
          smt__CONSTANTunderscore_Valuesunderscore_))
      (=>
        (=
          (smt__CONSTANTunderscore_VotedForInunderscore_
            smt__CONSTANTunderscore_qunderscore_
            smt__CONSTANTunderscore_wunderscore_
            smt__CONSTANTunderscore_cunderscore_)
          smt__TLAunderscore_underscore_Ttunderscore_Idv)
        (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
          smt__CONSTANTunderscore_wunderscore_
          smt__CONSTANTunderscore_vunderscore_)))))

(assert
  (forall ((smt__CONSTANTunderscore_qunderscore_ Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_qunderscore_
        smt__CONSTANTunderscore_Qunderscore_)
      (and
        (smt__TLAunderscore_underscore_IntLteq
          smt__CONSTANTunderscore_cunderscore_
          (smt__TLAunderscore_underscore_FunApp
            smt__VARIABLEunderscore_maxBalunderscore_
            smt__CONSTANTunderscore_qunderscore_))
        (not
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            smt__CONSTANTunderscore_cunderscore_
            (smt__TLAunderscore_underscore_FunApp
              smt__VARIABLEunderscore_maxBalunderscore_
              smt__CONSTANTunderscore_qunderscore_)))))))

;; Goal
(assert
  (!
    (not
      (exists ((smt__CONSTANTunderscore_QQunderscore_ Idv))
        (and
          (smt__TLAunderscore_underscore_Mem
            smt__CONSTANTunderscore_QQunderscore_
            smt__CONSTANTunderscore_Quorumsunderscore_)
          (forall ((smt__CONSTANTunderscore_qunderscore_ Idv))
            (=>
              (smt__TLAunderscore_underscore_Mem
                smt__CONSTANTunderscore_qunderscore_
                smt__CONSTANTunderscore_QQunderscore_)
              (or
                (=
                  (smt__CONSTANTunderscore_VotedForInunderscore_
                    smt__CONSTANTunderscore_qunderscore_
                    smt__CONSTANTunderscore_vunderscore_
                    smt__CONSTANTunderscore_dunderscore_)
                  smt__TLAunderscore_underscore_Ttunderscore_Idv)
                (and
                  (forall ((smt__CONSTANTunderscore_vunderscore__1 Idv))
                    (=>
                      (smt__TLAunderscore_underscore_Mem
                        smt__CONSTANTunderscore_vunderscore__1
                        smt__CONSTANTunderscore_Valuesunderscore_)
                      (not
                        (=
                          (smt__CONSTANTunderscore_VotedForInunderscore_
                            smt__CONSTANTunderscore_qunderscore_
                            smt__CONSTANTunderscore_vunderscore__1
                            smt__CONSTANTunderscore_dunderscore_)
                          smt__TLAunderscore_underscore_Ttunderscore_Idv))))
                  (and
                    (smt__TLAunderscore_underscore_IntLteq
                      smt__CONSTANTunderscore_dunderscore_
                      (smt__TLAunderscore_underscore_FunApp
                        smt__VARIABLEunderscore_maxBalunderscore_
                        smt__CONSTANTunderscore_qunderscore_))
                    (not
                      (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                        smt__CONSTANTunderscore_dunderscore_
                        (smt__TLAunderscore_underscore_FunApp
                          smt__VARIABLEunderscore_maxBalunderscore_
                          smt__CONSTANTunderscore_qunderscore_)))))))))))
    :named |Goal|))

(check-sat)
(exit)
