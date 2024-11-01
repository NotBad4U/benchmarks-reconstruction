;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_Quorums_,
;;	       NEW VARIABLE VARIABLE_msgs_,
;;	       NEW VARIABLE VARIABLE_maxBal_,
;;	       NEW VARIABLE VARIABLE_maxVBal_,
;;	       NEW VARIABLE VARIABLE_maxVal_,
;;	       (/\ VARIABLE_msgs_ \in SUBSET CONSTANT_Messages_
;;	        /\ VARIABLE_maxVBal_ \in [CONSTANT_Acceptors_ -> Nat \cup {-1}]
;;	        /\ VARIABLE_maxBal_ \in [CONSTANT_Acceptors_ -> Nat \cup {-1}]
;;	        /\ VARIABLE_maxVal_
;;	           \in [CONSTANT_Acceptors_ ->
;;	                  CONSTANT_Values_ \cup {CONSTANT_None_}]
;;	        /\ \A CONSTANT_a_ \in CONSTANT_Acceptors_ :
;;	              VARIABLE_maxBal_[CONSTANT_a_] >= VARIABLE_maxVBal_[CONSTANT_a_])
;;	       /\ STATE_MsgInv_
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
;;	       /\ CONSTANT_m_.bal > VARIABLE_maxBal_[CONSTANT_a_]
;;	       /\ ACTION_Send_([type |-> "1b", bal |-> CONSTANT_m_.bal,
;;	                        maxVBal |-> VARIABLE_maxVBal_[CONSTANT_a_],
;;	                        maxVal |-> VARIABLE_maxVal_[CONSTANT_a_],
;;	                        acc |-> CONSTANT_a_]) ,
;;	       CONSTANT_m_.type = "1a" ,
;;	       ?VARIABLE_maxBal_#prime
;;	       = [VARIABLE_maxBal_ EXCEPT ![CONSTANT_a_] = CONSTANT_m_.bal] ,
;;	       ?VARIABLE_maxVBal_#prime = VARIABLE_maxVBal_ ,
;;	       ?VARIABLE_maxVal_#prime = VARIABLE_maxVal_ 
;;	PROVE  \/ /\ [type |-> "1b", bal |-> CONSTANT_m_.bal,
;;	              maxVBal |-> VARIABLE_maxVBal_[CONSTANT_a_],
;;	              maxVal |-> VARIABLE_maxVal_[CONSTANT_a_], acc |-> CONSTANT_a_].maxVal
;;	             \in CONSTANT_Values_
;;	          /\ [type |-> "1b", bal |-> CONSTANT_m_.bal,
;;	              maxVBal |-> VARIABLE_maxVBal_[CONSTANT_a_],
;;	              maxVal |-> VARIABLE_maxVal_[CONSTANT_a_], acc |-> CONSTANT_a_].maxVBal
;;	             \in Nat
;;	          /\ CONSTANT_VotedForIn_([type |-> "1b", bal |-> CONSTANT_m_.bal,
;;	                                   maxVBal |-> VARIABLE_maxVBal_[CONSTANT_a_],
;;	                                   maxVal |-> VARIABLE_maxVal_[CONSTANT_a_],
;;	                                   acc |-> CONSTANT_a_].acc,
;;	                                  [type |-> "1b", bal |-> CONSTANT_m_.bal,
;;	                                   maxVBal |-> VARIABLE_maxVBal_[CONSTANT_a_],
;;	                                   maxVal |-> VARIABLE_maxVal_[CONSTANT_a_],
;;	                                   acc |-> CONSTANT_a_].maxVal,
;;	                                  [type |-> "1b", bal |-> CONSTANT_m_.bal,
;;	                                   maxVBal |-> VARIABLE_maxVBal_[CONSTANT_a_],
;;	                                   maxVal |-> VARIABLE_maxVal_[CONSTANT_a_],
;;	                                   acc |-> CONSTANT_a_].maxVBal)
;;	       \/ /\ [type |-> "1b", bal |-> CONSTANT_m_.bal,
;;	              maxVBal |-> VARIABLE_maxVBal_[CONSTANT_a_],
;;	              maxVal |-> VARIABLE_maxVal_[CONSTANT_a_], acc |-> CONSTANT_a_].maxVal
;;	             = CONSTANT_None_
;;	          /\ [type |-> "1b", bal |-> CONSTANT_m_.bal,
;;	              maxVBal |-> VARIABLE_maxVBal_[CONSTANT_a_],
;;	              maxVal |-> VARIABLE_maxVal_[CONSTANT_a_], acc |-> CONSTANT_a_].maxVBal
;;	             = -1
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #143
;; Generated from file "./Paxos.tla", line 359, characters 9-10

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_Castunderscore_Int (Int) Idv)

(declare-fun smt__TLAunderscore_underscore_Cup (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_FunApp (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_FunDom (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_FunExcept (Idv Idv Idv) Idv)

; omitted declaration of 'TLA__FunFcn' (second-order)

(declare-fun smt__TLAunderscore_underscore_FunIsafcn (Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_FunSet (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntLteq (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_IntUminus (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_NatSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Projunderscore_Int (Idv) Int)

(declare-fun smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type (Idv
  Idv Idv Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_1 (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_5 (Idv Idv Idv
  Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_1a () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_1b () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_acc () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_bal () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_maxVBal () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_maxVal () Idv)

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

;; Axiom: FunSetIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (and (smt__TLAunderscore_underscore_FunIsafcn smt__f)
            (= (smt__TLAunderscore_underscore_FunDom smt__f) smt__a)
            (forall ((smt__x Idv))
              (=> (smt__TLAunderscore_underscore_Mem smt__x smt__a)
                (smt__TLAunderscore_underscore_Mem
                  (smt__TLAunderscore_underscore_FunApp smt__f smt__x) 
                  smt__b))))
          (smt__TLAunderscore_underscore_Mem smt__f
            (smt__TLAunderscore_underscore_FunSet smt__a smt__b)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__f
                    (smt__TLAunderscore_underscore_FunSet smt__a smt__b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__f
            (smt__TLAunderscore_underscore_FunSet smt__a smt__b))
          (and (smt__TLAunderscore_underscore_FunIsafcn smt__f)
            (= (smt__TLAunderscore_underscore_FunDom smt__f) smt__a)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__f
                    (smt__TLAunderscore_underscore_FunSet smt__a smt__b)))))
    :named |FunSetElim1|))

;; Axiom: FunSetElim2
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv) (smt__x Idv))
      (!
        (=>
          (and
            (smt__TLAunderscore_underscore_Mem smt__f
              (smt__TLAunderscore_underscore_FunSet smt__a smt__b))
            (smt__TLAunderscore_underscore_Mem smt__x smt__a))
          (smt__TLAunderscore_underscore_Mem
            (smt__TLAunderscore_underscore_FunApp smt__f smt__x) smt__b))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__f
                    (smt__TLAunderscore_underscore_FunSet smt__a smt__b))
                   (smt__TLAunderscore_underscore_Mem smt__x smt__a))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__f
                    (smt__TLAunderscore_underscore_FunSet smt__a smt__b))
                   (smt__TLAunderscore_underscore_FunApp smt__f smt__x))))
    :named |FunSetElim2|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: FunExceptIsafcn
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (smt__TLAunderscore_underscore_FunIsafcn
          (smt__TLAunderscore_underscore_FunExcept smt__f smt__x smt__y))
        :pattern ((smt__TLAunderscore_underscore_FunExcept smt__f smt__x
                    smt__y)))) :named |FunExceptIsafcn|))

;; Axiom: FunExceptDomDef
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunDom
            (smt__TLAunderscore_underscore_FunExcept smt__f smt__x smt__y))
          (smt__TLAunderscore_underscore_FunDom smt__f))
        :pattern ((smt__TLAunderscore_underscore_FunExcept smt__f smt__x
                    smt__y)))) :named |FunExceptDomDef|))

;; Axiom: FunExceptAppDef1
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_FunDom smt__f))
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_FunExcept smt__f smt__x smt__y)
              smt__x) smt__y))
        :pattern ((smt__TLAunderscore_underscore_FunExcept smt__f smt__x
                    smt__y)))) :named |FunExceptAppDef1|))

;; Axiom: FunExceptAppDef2
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv) (smt__z Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__z
            (smt__TLAunderscore_underscore_FunDom smt__f))
          (and
            (=> (= smt__z smt__x)
              (=
                (smt__TLAunderscore_underscore_FunApp
                  (smt__TLAunderscore_underscore_FunExcept smt__f smt__x
                    smt__y) smt__z) smt__y))
            (=> (distinct smt__z smt__x)
              (=
                (smt__TLAunderscore_underscore_FunApp
                  (smt__TLAunderscore_underscore_FunExcept smt__f smt__x
                    smt__y) smt__z)
                (smt__TLAunderscore_underscore_FunApp smt__f smt__z)))))
        :pattern ((smt__TLAunderscore_underscore_FunApp
                    (smt__TLAunderscore_underscore_FunExcept smt__f smt__x
                      smt__y) smt__z))
        :pattern ((smt__TLAunderscore_underscore_FunExcept smt__f smt__x
                    smt__y)
                   (smt__TLAunderscore_underscore_FunApp smt__f smt__z))))
    :named |FunExceptAppDef2|))

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (!
        (smt__TLAunderscore_underscore_Mem smt__a1
          (smt__TLAunderscore_underscore_SetEnumunderscore_1 smt__a1))
        :pattern ((smt__TLAunderscore_underscore_SetEnumunderscore_1 smt__a1))))
    :named |EnumDefIntro 1|))

;; Axiom: EnumDefIntro 5
(assert
  (!
    (forall
      ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv) (smt__a5 Idv))
      (!
        (and
          (smt__TLAunderscore_underscore_Mem smt__a1
            (smt__TLAunderscore_underscore_SetEnumunderscore_5 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5))
          (smt__TLAunderscore_underscore_Mem smt__a2
            (smt__TLAunderscore_underscore_SetEnumunderscore_5 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5))
          (smt__TLAunderscore_underscore_Mem smt__a3
            (smt__TLAunderscore_underscore_SetEnumunderscore_5 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5))
          (smt__TLAunderscore_underscore_Mem smt__a4
            (smt__TLAunderscore_underscore_SetEnumunderscore_5 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5))
          (smt__TLAunderscore_underscore_Mem smt__a5
            (smt__TLAunderscore_underscore_SetEnumunderscore_5 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5)))
        :pattern ((smt__TLAunderscore_underscore_SetEnumunderscore_5 
                    smt__a1 smt__a2 smt__a3 smt__a4 smt__a5))))
    :named |EnumDefIntro 5|))

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

;; Axiom: EnumDefElim 5
(assert
  (!
    (forall
      ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv) (smt__a5 Idv)
        (smt__x Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetEnumunderscore_5 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5))
          (or (= smt__x smt__a1) (= smt__x smt__a2) (= smt__x smt__a3)
            (= smt__x smt__a4) (= smt__x smt__a5)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetEnumunderscore_5
                      smt__a1 smt__a2 smt__a3 smt__a4 smt__a5)))))
    :named |EnumDefElim 5|))

;; Axiom: StrLitIsstr 1a
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_1a
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr 1a|))

;; Axiom: StrLitIsstr 1b
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_1b
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr 1b|))

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

;; Axiom: StrLitIsstr maxVBal
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_maxVBal
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr maxVBal|))

;; Axiom: StrLitIsstr maxVal
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_maxVal
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr maxVal|))

;; Axiom: StrLitIsstr type
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_type
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr type|))

;; Axiom: StrLitDistinct 1a 1b
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1a
      smt__TLAunderscore_underscore_StrLitunderscore_1b)
    :named |StrLitDistinct 1a 1b|))

;; Axiom: StrLitDistinct 1a acc
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1a
      smt__TLAunderscore_underscore_StrLitunderscore_acc)
    :named |StrLitDistinct 1a acc|))

;; Axiom: StrLitDistinct 1a bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1a
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct 1a bal|))

;; Axiom: StrLitDistinct 1a maxVBal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1a
      smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
    :named |StrLitDistinct 1a maxVBal|))

;; Axiom: StrLitDistinct 1a maxVal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1a
      smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
    :named |StrLitDistinct 1a maxVal|))

;; Axiom: StrLitDistinct 1a type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1a
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct 1a type|))

;; Axiom: StrLitDistinct 1b acc
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1b
      smt__TLAunderscore_underscore_StrLitunderscore_acc)
    :named |StrLitDistinct 1b acc|))

;; Axiom: StrLitDistinct 1b bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1b
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct 1b bal|))

;; Axiom: StrLitDistinct 1b maxVBal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1b
      smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
    :named |StrLitDistinct 1b maxVBal|))

;; Axiom: StrLitDistinct 1b maxVal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1b
      smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
    :named |StrLitDistinct 1b maxVal|))

;; Axiom: StrLitDistinct 1b type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1b
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct 1b type|))

;; Axiom: StrLitDistinct acc bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_acc
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct acc bal|))

;; Axiom: StrLitDistinct maxVBal acc
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_maxVBal
      smt__TLAunderscore_underscore_StrLitunderscore_acc)
    :named |StrLitDistinct maxVBal acc|))

;; Axiom: StrLitDistinct maxVBal bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_maxVBal
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct maxVBal bal|))

;; Axiom: StrLitDistinct maxVal acc
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_maxVal
      smt__TLAunderscore_underscore_StrLitunderscore_acc)
    :named |StrLitDistinct maxVal acc|))

;; Axiom: StrLitDistinct maxVal bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_maxVal
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct maxVal bal|))

;; Axiom: StrLitDistinct maxVal maxVBal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_maxVal
      smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
    :named |StrLitDistinct maxVal maxVBal|))

;; Axiom: StrLitDistinct type acc
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_type
      smt__TLAunderscore_underscore_StrLitunderscore_acc)
    :named |StrLitDistinct type acc|))

;; Axiom: StrLitDistinct type bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_type
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct type bal|))

;; Axiom: StrLitDistinct type maxVBal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_type
      smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
    :named |StrLitDistinct type maxVBal|))

;; Axiom: StrLitDistinct type maxVal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_type
      smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
    :named |StrLitDistinct type maxVal|))

;; Axiom: RecIsafcn acc bal maxVBal maxVal type
(assert
  (!
    (forall
      ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x5 Idv))
      (!
        (smt__TLAunderscore_underscore_FunIsafcn
          (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
            smt__x1 smt__x2 smt__x3 smt__x4 smt__x5))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                    smt__x1 smt__x2 smt__x3 smt__x4 smt__x5))))
    :named |RecIsafcn acc bal maxVBal maxVal type|))

;; Axiom: RecDomDef acc bal maxVBal maxVal type
(assert
  (!
    (forall
      ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x5 Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunDom
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
              smt__x1 smt__x2 smt__x3 smt__x4 smt__x5))
          (smt__TLAunderscore_underscore_SetEnumunderscore_5
            smt__TLAunderscore_underscore_StrLitunderscore_acc
            smt__TLAunderscore_underscore_StrLitunderscore_bal
            smt__TLAunderscore_underscore_StrLitunderscore_maxVBal
            smt__TLAunderscore_underscore_StrLitunderscore_maxVal
            smt__TLAunderscore_underscore_StrLitunderscore_type))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                    smt__x1 smt__x2 smt__x3 smt__x4 smt__x5))))
    :named |RecDomDef acc bal maxVBal maxVal type|))

;; Axiom: RecAppDef acc bal maxVBal maxVal type
(assert
  (!
    (forall
      ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x5 Idv))
      (!
        (and
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
              smt__TLAunderscore_underscore_StrLitunderscore_acc) smt__x1)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
              smt__TLAunderscore_underscore_StrLitunderscore_bal) smt__x2)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
              smt__TLAunderscore_underscore_StrLitunderscore_maxVBal) 
            smt__x3)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
              smt__TLAunderscore_underscore_StrLitunderscore_maxVal) 
            smt__x4)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
              smt__TLAunderscore_underscore_StrLitunderscore_type) smt__x5))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                    smt__x1 smt__x2 smt__x3 smt__x4 smt__x5))))
    :named |RecAppDef acc bal maxVBal maxVal type|))

;; Axiom: RecExcept acc bal maxVBal maxVal type 1
(assert
  (!
    (forall
      ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x5 Idv)
        (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
              smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
            smt__TLAunderscore_underscore_StrLitunderscore_acc smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
            smt__x smt__x2 smt__x3 smt__x4 smt__x5))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                      smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
                    smt__TLAunderscore_underscore_StrLitunderscore_acc 
                    smt__x))))
    :named |RecExcept acc bal maxVBal maxVal type 1|))

;; Axiom: RecExcept acc bal maxVBal maxVal type 2
(assert
  (!
    (forall
      ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x5 Idv)
        (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
              smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
            smt__TLAunderscore_underscore_StrLitunderscore_bal smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
            smt__x1 smt__x smt__x3 smt__x4 smt__x5))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                      smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
                    smt__TLAunderscore_underscore_StrLitunderscore_bal 
                    smt__x))))
    :named |RecExcept acc bal maxVBal maxVal type 2|))

;; Axiom: RecExcept acc bal maxVBal maxVal type 3
(assert
  (!
    (forall
      ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x5 Idv)
        (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
              smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
            smt__TLAunderscore_underscore_StrLitunderscore_maxVBal smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
            smt__x1 smt__x2 smt__x smt__x4 smt__x5))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                      smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
                    smt__TLAunderscore_underscore_StrLitunderscore_maxVBal
                    smt__x))))
    :named |RecExcept acc bal maxVBal maxVal type 3|))

;; Axiom: RecExcept acc bal maxVBal maxVal type 4
(assert
  (!
    (forall
      ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x5 Idv)
        (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
              smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
            smt__TLAunderscore_underscore_StrLitunderscore_maxVal smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
            smt__x1 smt__x2 smt__x3 smt__x smt__x5))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                      smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
                    smt__TLAunderscore_underscore_StrLitunderscore_maxVal
                    smt__x))))
    :named |RecExcept acc bal maxVBal maxVal type 4|))

;; Axiom: RecExcept acc bal maxVBal maxVal type 5
(assert
  (!
    (forall
      ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x5 Idv)
        (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
              smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
            smt__TLAunderscore_underscore_StrLitunderscore_type smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
            smt__x1 smt__x2 smt__x3 smt__x4 smt__x))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                      smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
                    smt__TLAunderscore_underscore_StrLitunderscore_type
                    smt__x))))
    :named |RecExcept acc bal maxVBal maxVal type 5|))

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
      (and
        (smt__TLAunderscore_underscore_Mem
          smt__VARIABLEunderscore_msgsunderscore_
          (smt__TLAunderscore_underscore_Subset
            smt__CONSTANTunderscore_Messagesunderscore_))
        (smt__TLAunderscore_underscore_Mem
          smt__VARIABLEunderscore_maxVBalunderscore_
          (smt__TLAunderscore_underscore_FunSet
            smt__CONSTANTunderscore_Acceptorsunderscore_
            (smt__TLAunderscore_underscore_Cup
              smt__TLAunderscore_underscore_NatSet
              (smt__TLAunderscore_underscore_SetEnumunderscore_1
                (smt__TLAunderscore_underscore_IntUminus
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1))))))
        (smt__TLAunderscore_underscore_Mem
          smt__VARIABLEunderscore_maxBalunderscore_
          (smt__TLAunderscore_underscore_FunSet
            smt__CONSTANTunderscore_Acceptorsunderscore_
            (smt__TLAunderscore_underscore_Cup
              smt__TLAunderscore_underscore_NatSet
              (smt__TLAunderscore_underscore_SetEnumunderscore_1
                (smt__TLAunderscore_underscore_IntUminus
                  (smt__TLAunderscore_underscore_Castunderscore_Int 1))))))
        (smt__TLAunderscore_underscore_Mem
          smt__VARIABLEunderscore_maxValunderscore_
          (smt__TLAunderscore_underscore_FunSet
            smt__CONSTANTunderscore_Acceptorsunderscore_
            (smt__TLAunderscore_underscore_Cup
              smt__CONSTANTunderscore_Valuesunderscore_
              (smt__TLAunderscore_underscore_SetEnumunderscore_1
                smt__CONSTANTunderscore_Noneunderscore_))))
        (forall ((smt__CONSTANTunderscore_aunderscore_ Idv))
          (=>
            (smt__TLAunderscore_underscore_Mem
              smt__CONSTANTunderscore_aunderscore_
              smt__CONSTANTunderscore_Acceptorsunderscore_)
            (smt__TLAunderscore_underscore_IntLteq
              (smt__TLAunderscore_underscore_FunApp
                smt__VARIABLEunderscore_maxVBalunderscore_
                smt__CONSTANTunderscore_aunderscore_)
              (smt__TLAunderscore_underscore_FunApp
                smt__VARIABLEunderscore_maxBalunderscore_
                smt__CONSTANTunderscore_aunderscore_)))))
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

(assert
  (and
    (and
      (smt__TLAunderscore_underscore_IntLteq
        (smt__TLAunderscore_underscore_FunApp
          smt__VARIABLEunderscore_maxBalunderscore_
          smt__CONSTANTunderscore_aunderscore_)
        (smt__TLAunderscore_underscore_FunApp
          smt__CONSTANTunderscore_munderscore_
          smt__TLAunderscore_underscore_StrLitunderscore_bal))
      (not
        (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
          (smt__TLAunderscore_underscore_FunApp
            smt__VARIABLEunderscore_maxBalunderscore_
            smt__CONSTANTunderscore_aunderscore_)
          (smt__TLAunderscore_underscore_FunApp
            smt__CONSTANTunderscore_munderscore_
            smt__TLAunderscore_underscore_StrLitunderscore_bal))))
    (=
      (smt__ACTIONunderscore_Sendunderscore_
        (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
          smt__CONSTANTunderscore_aunderscore_
          (smt__TLAunderscore_underscore_FunApp
            smt__CONSTANTunderscore_munderscore_
            smt__TLAunderscore_underscore_StrLitunderscore_bal)
          (smt__TLAunderscore_underscore_FunApp
            smt__VARIABLEunderscore_maxVBalunderscore_
            smt__CONSTANTunderscore_aunderscore_)
          (smt__TLAunderscore_underscore_FunApp
            smt__VARIABLEunderscore_maxValunderscore_
            smt__CONSTANTunderscore_aunderscore_)
          smt__TLAunderscore_underscore_StrLitunderscore_1b))
      smt__TLAunderscore_underscore_Ttunderscore_Idv)))

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
    (smt__TLAunderscore_underscore_FunApp
      smt__CONSTANTunderscore_munderscore_
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    smt__TLAunderscore_underscore_StrLitunderscore_1a))

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
    smt__VARIABLEunderscore_maxBalunderscore_underscore_prime
    (smt__TLAunderscore_underscore_FunExcept
      smt__VARIABLEunderscore_maxBalunderscore_
      smt__CONSTANTunderscore_aunderscore_
      (smt__TLAunderscore_underscore_FunApp
        smt__CONSTANTunderscore_munderscore_
        smt__TLAunderscore_underscore_StrLitunderscore_bal))))

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
    smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
    smt__VARIABLEunderscore_maxVBalunderscore_))

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
    smt__VARIABLEunderscore_maxValunderscore_underscore_prime
    smt__VARIABLEunderscore_maxValunderscore_))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

;; Goal
(assert
  (!
    (not
      (or
        (and
          (smt__TLAunderscore_underscore_Mem
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                smt__CONSTANTunderscore_aunderscore_
                (smt__TLAunderscore_underscore_FunApp
                  smt__CONSTANTunderscore_munderscore_
                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxVBalunderscore_
                  smt__CONSTANTunderscore_aunderscore_)
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxValunderscore_
                  smt__CONSTANTunderscore_aunderscore_)
                smt__TLAunderscore_underscore_StrLitunderscore_1b)
              smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
            smt__CONSTANTunderscore_Valuesunderscore_)
          (smt__TLAunderscore_underscore_Mem
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                smt__CONSTANTunderscore_aunderscore_
                (smt__TLAunderscore_underscore_FunApp
                  smt__CONSTANTunderscore_munderscore_
                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxVBalunderscore_
                  smt__CONSTANTunderscore_aunderscore_)
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxValunderscore_
                  smt__CONSTANTunderscore_aunderscore_)
                smt__TLAunderscore_underscore_StrLitunderscore_1b)
              smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
            smt__TLAunderscore_underscore_NatSet)
          (=
            (smt__CONSTANTunderscore_VotedForInunderscore_
              (smt__TLAunderscore_underscore_FunApp
                (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                  smt__CONSTANTunderscore_aunderscore_
                  (smt__TLAunderscore_underscore_FunApp
                    smt__CONSTANTunderscore_munderscore_
                    smt__TLAunderscore_underscore_StrLitunderscore_bal)
                  (smt__TLAunderscore_underscore_FunApp
                    smt__VARIABLEunderscore_maxVBalunderscore_
                    smt__CONSTANTunderscore_aunderscore_)
                  (smt__TLAunderscore_underscore_FunApp
                    smt__VARIABLEunderscore_maxValunderscore_
                    smt__CONSTANTunderscore_aunderscore_)
                  smt__TLAunderscore_underscore_StrLitunderscore_1b)
                smt__TLAunderscore_underscore_StrLitunderscore_acc)
              (smt__TLAunderscore_underscore_FunApp
                (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                  smt__CONSTANTunderscore_aunderscore_
                  (smt__TLAunderscore_underscore_FunApp
                    smt__CONSTANTunderscore_munderscore_
                    smt__TLAunderscore_underscore_StrLitunderscore_bal)
                  (smt__TLAunderscore_underscore_FunApp
                    smt__VARIABLEunderscore_maxVBalunderscore_
                    smt__CONSTANTunderscore_aunderscore_)
                  (smt__TLAunderscore_underscore_FunApp
                    smt__VARIABLEunderscore_maxValunderscore_
                    smt__CONSTANTunderscore_aunderscore_)
                  smt__TLAunderscore_underscore_StrLitunderscore_1b)
                smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
              (smt__TLAunderscore_underscore_FunApp
                (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                  smt__CONSTANTunderscore_aunderscore_
                  (smt__TLAunderscore_underscore_FunApp
                    smt__CONSTANTunderscore_munderscore_
                    smt__TLAunderscore_underscore_StrLitunderscore_bal)
                  (smt__TLAunderscore_underscore_FunApp
                    smt__VARIABLEunderscore_maxVBalunderscore_
                    smt__CONSTANTunderscore_aunderscore_)
                  (smt__TLAunderscore_underscore_FunApp
                    smt__VARIABLEunderscore_maxValunderscore_
                    smt__CONSTANTunderscore_aunderscore_)
                  smt__TLAunderscore_underscore_StrLitunderscore_1b)
                smt__TLAunderscore_underscore_StrLitunderscore_maxVBal))
            smt__TLAunderscore_underscore_Ttunderscore_Idv))
        (and
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                smt__CONSTANTunderscore_aunderscore_
                (smt__TLAunderscore_underscore_FunApp
                  smt__CONSTANTunderscore_munderscore_
                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxVBalunderscore_
                  smt__CONSTANTunderscore_aunderscore_)
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxValunderscore_
                  smt__CONSTANTunderscore_aunderscore_)
                smt__TLAunderscore_underscore_StrLitunderscore_1b)
              smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
            smt__CONSTANTunderscore_Noneunderscore_)
          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                smt__CONSTANTunderscore_aunderscore_
                (smt__TLAunderscore_underscore_FunApp
                  smt__CONSTANTunderscore_munderscore_
                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxVBalunderscore_
                  smt__CONSTANTunderscore_aunderscore_)
                (smt__TLAunderscore_underscore_FunApp
                  smt__VARIABLEunderscore_maxValunderscore_
                  smt__CONSTANTunderscore_aunderscore_)
                smt__TLAunderscore_underscore_StrLitunderscore_1b)
              smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
            (smt__TLAunderscore_underscore_IntUminus
              (smt__TLAunderscore_underscore_Castunderscore_Int 1))))))
    :named |Goal|))

(check-sat)
(exit)
