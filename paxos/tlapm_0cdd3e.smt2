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
;;	       ?VARIABLE_msgs_#prime
;;	       = VARIABLE_msgs_
;;	         \cup {[type |-> "2a", bal |-> CONSTANT_b_, val |-> CONSTANT_v_]} 
;;	PROVE  \A CONSTANT_aa_, CONSTANT_vv_, CONSTANT_bb_ :
;;	          (\E CONSTANT_m_ \in ?VARIABLE_msgs_#prime :
;;	              /\ CONSTANT_m_.type = "2b"
;;	              /\ CONSTANT_m_.val = CONSTANT_vv_
;;	              /\ CONSTANT_m_.bal = CONSTANT_bb_
;;	              /\ CONSTANT_m_.acc = CONSTANT_aa_)
;;	          <=> (\E CONSTANT_m_ \in VARIABLE_msgs_ :
;;	                  /\ CONSTANT_m_.type = "2b"
;;	                  /\ CONSTANT_m_.val = CONSTANT_vv_
;;	                  /\ CONSTANT_m_.bal = CONSTANT_bb_
;;	                  /\ CONSTANT_m_.acc = CONSTANT_aa_)
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #163
;; Generated from file "./Paxos.tla", line 386, characters 9-10

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_Castunderscore_Int (Int) Idv)

(declare-fun smt__TLAunderscore_underscore_Cup (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_FunApp (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_FunDom (Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLAunderscore_underscore_FunIsafcn (Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntLteq (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_NatSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Projunderscore_Int (Idv) Int)

(declare-fun smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val (Idv
  Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_1 (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_3 (Idv Idv
  Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_2a () Idv)

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

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (!
        (smt__TLAunderscore_underscore_Mem smt__a1
          (smt__TLAunderscore_underscore_SetEnumunderscore_1 smt__a1))
        :pattern ((smt__TLAunderscore_underscore_SetEnumunderscore_1 smt__a1))))
    :named |EnumDefIntro 1|))

;; Axiom: EnumDefIntro 3
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv))
      (!
        (and
          (smt__TLAunderscore_underscore_Mem smt__a1
            (smt__TLAunderscore_underscore_SetEnumunderscore_3 smt__a1
              smt__a2 smt__a3))
          (smt__TLAunderscore_underscore_Mem smt__a2
            (smt__TLAunderscore_underscore_SetEnumunderscore_3 smt__a1
              smt__a2 smt__a3))
          (smt__TLAunderscore_underscore_Mem smt__a3
            (smt__TLAunderscore_underscore_SetEnumunderscore_3 smt__a1
              smt__a2 smt__a3)))
        :pattern ((smt__TLAunderscore_underscore_SetEnumunderscore_3 
                    smt__a1 smt__a2 smt__a3)))) :named |EnumDefIntro 3|))

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

;; Axiom: EnumDefElim 3
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetEnumunderscore_3 smt__a1
              smt__a2 smt__a3))
          (or (= smt__x smt__a1) (= smt__x smt__a2) (= smt__x smt__a3)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetEnumunderscore_3
                      smt__a1 smt__a2 smt__a3))))) :named |EnumDefElim 3|))

;; Axiom: StrLitIsstr 2a
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_2a
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr 2a|))

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

;; Axiom: StrLitDistinct 2a bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2a
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct 2a bal|))

;; Axiom: StrLitDistinct 2a type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2a
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct 2a type|))

;; Axiom: StrLitDistinct 2a val
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2a
      smt__TLAunderscore_underscore_StrLitunderscore_val)
    :named |StrLitDistinct 2a val|))

;; Axiom: StrLitDistinct 2b 2a
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrLitunderscore_2a)
    :named |StrLitDistinct 2b 2a|))

;; Axiom: StrLitDistinct 2b bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct 2b bal|))

;; Axiom: StrLitDistinct 2b type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct 2b type|))

;; Axiom: StrLitDistinct 2b val
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrLitunderscore_val)
    :named |StrLitDistinct 2b val|))

;; Axiom: StrLitDistinct acc 2a
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_acc
      smt__TLAunderscore_underscore_StrLitunderscore_2a)
    :named |StrLitDistinct acc 2a|))

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

;; Axiom: StrLitDistinct type bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_type
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct type bal|))

;; Axiom: StrLitDistinct val bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct val bal|))

;; Axiom: StrLitDistinct val type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct val type|))

;; Axiom: RecIsafcn bal type val
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv))
      (!
        (smt__TLAunderscore_underscore_FunIsafcn
          (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
            smt__x1 smt__x2 smt__x3))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
                    smt__x1 smt__x2 smt__x3))))
    :named |RecIsafcn bal type val|))

;; Axiom: RecDomDef bal type val
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunDom
            (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
              smt__x1 smt__x2 smt__x3))
          (smt__TLAunderscore_underscore_SetEnumunderscore_3
            smt__TLAunderscore_underscore_StrLitunderscore_bal
            smt__TLAunderscore_underscore_StrLitunderscore_type
            smt__TLAunderscore_underscore_StrLitunderscore_val))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
                    smt__x1 smt__x2 smt__x3))))
    :named |RecDomDef bal type val|))

;; Axiom: RecAppDef bal type val
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv))
      (!
        (and
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
                smt__x1 smt__x2 smt__x3)
              smt__TLAunderscore_underscore_StrLitunderscore_bal) smt__x1)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
                smt__x1 smt__x2 smt__x3)
              smt__TLAunderscore_underscore_StrLitunderscore_type) smt__x2)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
                smt__x1 smt__x2 smt__x3)
              smt__TLAunderscore_underscore_StrLitunderscore_val) smt__x3))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
                    smt__x1 smt__x2 smt__x3))))
    :named |RecAppDef bal type val|))

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

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Setdollarsignunderscore_Idvdollarsignunderscore_
    smt__VARIABLEunderscore_msgsunderscore_underscore_prime
    (smt__TLAunderscore_underscore_Cup
      smt__VARIABLEunderscore_msgsunderscore_
      (smt__TLAunderscore_underscore_SetEnumunderscore_1
        (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
          smt__CONSTANTunderscore_bunderscore_
          smt__TLAunderscore_underscore_StrLitunderscore_2a
          smt__CONSTANTunderscore_vunderscore_)))))

;; Goal
(assert
  (!
    (not
      (forall
        ((smt__CONSTANTunderscore_aaunderscore_ Idv)
          (smt__CONSTANTunderscore_vvunderscore_ Idv)
          (smt__CONSTANTunderscore_bbunderscore_ Idv))
        (=
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
                  smt__CONSTANTunderscore_vvunderscore_)
                (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                  (smt__TLAunderscore_underscore_FunApp
                    smt__CONSTANTunderscore_munderscore_
                    smt__TLAunderscore_underscore_StrLitunderscore_bal)
                  smt__CONSTANTunderscore_bbunderscore_)
                (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                  (smt__TLAunderscore_underscore_FunApp
                    smt__CONSTANTunderscore_munderscore_
                    smt__TLAunderscore_underscore_StrLitunderscore_acc)
                  smt__CONSTANTunderscore_aaunderscore_))))
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
                  smt__CONSTANTunderscore_vvunderscore_)
                (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                  (smt__TLAunderscore_underscore_FunApp
                    smt__CONSTANTunderscore_munderscore_
                    smt__TLAunderscore_underscore_StrLitunderscore_bal)
                  smt__CONSTANTunderscore_bbunderscore_)
                (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                  (smt__TLAunderscore_underscore_FunApp
                    smt__CONSTANTunderscore_munderscore_
                    smt__TLAunderscore_underscore_StrLitunderscore_acc)
                  smt__CONSTANTunderscore_aaunderscore_))))))) :named |Goal|))

(check-sat)
(exit)