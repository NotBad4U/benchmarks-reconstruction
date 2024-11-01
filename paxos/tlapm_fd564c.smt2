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
;;	       ?h15bf9 ,
;;	       NEW CONSTANT CONSTANT_v_ \in CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_b_ \in Nat,
;;	       STATE_SafeAt_(CONSTANT_v_, CONSTANT_b_) ,
;;	       NEW CONSTANT CONSTANT_a_ \in CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_m_ \in VARIABLE_msgs_,
;;	       NEW CONSTANT CONSTANT_aa_ \in CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_bb_ \in Nat,
;;	       NEW CONSTANT CONSTANT_vv_ \in CONSTANT_Values_,
;;	       /\ /\ \A CONSTANT_v__1 \in CONSTANT_Values_ :
;;	                ~(\E CONSTANT_m__1 \in VARIABLE_msgs_ :
;;	                     /\ CONSTANT_m__1.type = "2b"
;;	                     /\ CONSTANT_m__1.val = CONSTANT_v__1
;;	                     /\ CONSTANT_m__1.bal = CONSTANT_bb_
;;	                     /\ CONSTANT_m__1.acc = CONSTANT_aa_)
;;	          /\ VARIABLE_maxBal_[CONSTANT_aa_] > CONSTANT_bb_
;;	       /\ \E CONSTANT_m__1 \in ?VARIABLE_msgs_#prime :
;;	             /\ CONSTANT_m__1.type = "2b"
;;	             /\ CONSTANT_m__1.val = CONSTANT_vv_
;;	             /\ CONSTANT_m__1.bal = CONSTANT_bb_
;;	             /\ CONSTANT_m__1.acc = CONSTANT_aa_ 
;;	PROVE  [type |-> "2b", val |-> CONSTANT_vv_, bal |-> CONSTANT_bb_,
;;	        acc |-> CONSTANT_aa_]
;;	       \notin VARIABLE_msgs_
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #36
;; Generated from file "./Paxos.tla", line 262, characters 7-8

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9 () Idv)

(declare-fun smt__TLAunderscore_underscore_Castunderscore_Int (Int) Idv)

(declare-fun smt__TLAunderscore_underscore_FunApp (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLAunderscore_underscore_FunIsafcn (Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntLteq (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_NatSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Projunderscore_Int (Idv) Int)

(declare-fun smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val (Idv
  Idv Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_4 (Idv Idv Idv
  Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_2b () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_acc () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_bal () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_type () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_val () Idv)

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

;; Axiom: EnumDefIntro 4
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv))
      (!
        (and
          (smt__TLAunderscore_underscore_Mem smt__a1
            (smt__TLAunderscore_underscore_SetEnumunderscore_4 smt__a1
              smt__a2 smt__a3 smt__a4))
          (smt__TLAunderscore_underscore_Mem smt__a2
            (smt__TLAunderscore_underscore_SetEnumunderscore_4 smt__a1
              smt__a2 smt__a3 smt__a4))
          (smt__TLAunderscore_underscore_Mem smt__a3
            (smt__TLAunderscore_underscore_SetEnumunderscore_4 smt__a1
              smt__a2 smt__a3 smt__a4))
          (smt__TLAunderscore_underscore_Mem smt__a4
            (smt__TLAunderscore_underscore_SetEnumunderscore_4 smt__a1
              smt__a2 smt__a3 smt__a4)))
        :pattern ((smt__TLAunderscore_underscore_SetEnumunderscore_4 
                    smt__a1 smt__a2 smt__a3 smt__a4))))
    :named |EnumDefIntro 4|))

;; Axiom: EnumDefElim 4
(assert
  (!
    (forall
      ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetEnumunderscore_4 smt__a1
              smt__a2 smt__a3 smt__a4))
          (or (= smt__x smt__a1) (= smt__x smt__a2) (= smt__x smt__a3)
            (= smt__x smt__a4)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetEnumunderscore_4
                      smt__a1 smt__a2 smt__a3 smt__a4)))))
    :named |EnumDefElim 4|))

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

;; Axiom: RecIsafcn acc bal type val
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv))
      (!
        (smt__TLAunderscore_underscore_FunIsafcn
          (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
            smt__x1 smt__x2 smt__x3 smt__x4))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                    smt__x1 smt__x2 smt__x3 smt__x4))))
    :named |RecIsafcn acc bal type val|))

;; Axiom: RecDomDef acc bal type val
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunDom
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
              smt__x1 smt__x2 smt__x3 smt__x4))
          (smt__TLAunderscore_underscore_SetEnumunderscore_4
            smt__TLAunderscore_underscore_StrLitunderscore_acc
            smt__TLAunderscore_underscore_StrLitunderscore_bal
            smt__TLAunderscore_underscore_StrLitunderscore_type
            smt__TLAunderscore_underscore_StrLitunderscore_val))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                    smt__x1 smt__x2 smt__x3 smt__x4))))
    :named |RecDomDef acc bal type val|))

;; Axiom: RecAppDef acc bal type val
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv))
      (!
        (and
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                smt__x1 smt__x2 smt__x3 smt__x4)
              smt__TLAunderscore_underscore_StrLitunderscore_acc) smt__x1)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                smt__x1 smt__x2 smt__x3 smt__x4)
              smt__TLAunderscore_underscore_StrLitunderscore_bal) smt__x2)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                smt__x1 smt__x2 smt__x3 smt__x4)
              smt__TLAunderscore_underscore_StrLitunderscore_type) smt__x3)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                smt__x1 smt__x2 smt__x3 smt__x4)
              smt__TLAunderscore_underscore_StrLitunderscore_val) smt__x4))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                    smt__x1 smt__x2 smt__x3 smt__x4))))
    :named |RecAppDef acc bal type val|))

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

(declare-fun smt__CONSTANTunderscore_Noneunderscore_ () Idv)

; hidden fact

(declare-fun smt__STATEunderscore_Initunderscore_ () Idv)

(declare-fun smt__ACTIONunderscore_Phase1aunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Phase1bunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Phase2aunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Phase2bunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Nextunderscore_ () Idv)

(declare-fun smt__TEMPORALunderscore_Specunderscore_ () Idv)

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

(assert
  (= smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9
    smt__TLAunderscore_underscore_Ttunderscore_Idv))

(declare-fun smt__CONSTANTunderscore_vunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_vunderscore_
    smt__CONSTANTunderscore_Valuesunderscore_))

(declare-fun smt__CONSTANTunderscore_bunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_bunderscore_
    smt__TLAunderscore_underscore_NatSet))

(assert
  (=
    (smt__STATEunderscore_SafeAtunderscore_
      smt__CONSTANTunderscore_vunderscore_
      smt__CONSTANTunderscore_bunderscore_)
    smt__TLAunderscore_underscore_Ttunderscore_Idv))

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

(declare-fun smt__CONSTANTunderscore_aaunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_aaunderscore_
    smt__CONSTANTunderscore_Acceptorsunderscore_))

(declare-fun smt__CONSTANTunderscore_bbunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_bbunderscore_
    smt__TLAunderscore_underscore_NatSet))

; hidden fact

(declare-fun smt__CONSTANTunderscore_vvunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_vvunderscore_
    smt__CONSTANTunderscore_Valuesunderscore_))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (and
    (and
      (forall ((smt__CONSTANTunderscore_vunderscore__1 Idv))
        (=>
          (smt__TLAunderscore_underscore_Mem
            smt__CONSTANTunderscore_vunderscore__1
            smt__CONSTANTunderscore_Valuesunderscore_)
          (not
            (exists ((smt__CONSTANTunderscore_munderscore__1 Idv))
              (and
                (smt__TLAunderscore_underscore_Mem
                  smt__CONSTANTunderscore_munderscore__1
                  smt__VARIABLEunderscore_msgsunderscore_)
                (and
                  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                    (smt__TLAunderscore_underscore_FunApp
                      smt__CONSTANTunderscore_munderscore__1
                      smt__TLAunderscore_underscore_StrLitunderscore_type)
                    smt__TLAunderscore_underscore_StrLitunderscore_2b)
                  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                    (smt__TLAunderscore_underscore_FunApp
                      smt__CONSTANTunderscore_munderscore__1
                      smt__TLAunderscore_underscore_StrLitunderscore_val)
                    smt__CONSTANTunderscore_vunderscore__1)
                  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                    (smt__TLAunderscore_underscore_FunApp
                      smt__CONSTANTunderscore_munderscore__1
                      smt__TLAunderscore_underscore_StrLitunderscore_bal)
                    smt__CONSTANTunderscore_bbunderscore_)
                  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                    (smt__TLAunderscore_underscore_FunApp
                      smt__CONSTANTunderscore_munderscore__1
                      smt__TLAunderscore_underscore_StrLitunderscore_acc)
                    smt__CONSTANTunderscore_aaunderscore_)))))))
      (and
        (smt__TLAunderscore_underscore_IntLteq
          smt__CONSTANTunderscore_bbunderscore_
          (smt__TLAunderscore_underscore_FunApp
            smt__VARIABLEunderscore_maxBalunderscore_
            smt__CONSTANTunderscore_aaunderscore_))
        (not
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            smt__CONSTANTunderscore_bbunderscore_
            (smt__TLAunderscore_underscore_FunApp
              smt__VARIABLEunderscore_maxBalunderscore_
              smt__CONSTANTunderscore_aaunderscore_)))))
    (exists ((smt__CONSTANTunderscore_munderscore__1 Idv))
      (and
        (smt__TLAunderscore_underscore_Mem
          smt__CONSTANTunderscore_munderscore__1
          smt__VARIABLEunderscore_msgsunderscore_underscore_prime)
        (and
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            (smt__TLAunderscore_underscore_FunApp
              smt__CONSTANTunderscore_munderscore__1
              smt__TLAunderscore_underscore_StrLitunderscore_type)
            smt__TLAunderscore_underscore_StrLitunderscore_2b)
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            (smt__TLAunderscore_underscore_FunApp
              smt__CONSTANTunderscore_munderscore__1
              smt__TLAunderscore_underscore_StrLitunderscore_val)
            smt__CONSTANTunderscore_vvunderscore_)
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            (smt__TLAunderscore_underscore_FunApp
              smt__CONSTANTunderscore_munderscore__1
              smt__TLAunderscore_underscore_StrLitunderscore_bal)
            smt__CONSTANTunderscore_bbunderscore_)
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            (smt__TLAunderscore_underscore_FunApp
              smt__CONSTANTunderscore_munderscore__1
              smt__TLAunderscore_underscore_StrLitunderscore_acc)
            smt__CONSTANTunderscore_aaunderscore_))))))

;; Goal
(assert
  (!
    (not
      (not
        (smt__TLAunderscore_underscore_Mem
          (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
            smt__CONSTANTunderscore_aaunderscore_
            smt__CONSTANTunderscore_bbunderscore_
            smt__TLAunderscore_underscore_StrLitunderscore_2b
            smt__CONSTANTunderscore_vvunderscore_)
          smt__VARIABLEunderscore_msgsunderscore_))) :named |Goal|))

(check-sat)
(exit)
