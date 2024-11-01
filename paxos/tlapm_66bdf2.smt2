;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_Values_,
;;	       NEW CONSTANT CONSTANT_Quorums_,
;;	       NEW VARIABLE VARIABLE_msgs_,
;;	       NEW VARIABLE VARIABLE_maxBal_,
;;	       NEW VARIABLE VARIABLE_maxVBal_,
;;	       NEW VARIABLE VARIABLE_maxVal_,
;;	       (/\ VARIABLE_msgs_
;;	           \in SUBSET ([type : {"1a"}, bal : Nat]
;;	                       \cup [type : {"1b"}, bal : Nat,
;;	                             maxVBal : Nat \cup {-1},
;;	                             maxVal : CONSTANT_Values_ \cup {CONSTANT_None_},
;;	                             acc : CONSTANT_Acceptors_]
;;	                       \cup [type : {"2a"}, bal : Nat,
;;	                             val : CONSTANT_Values_]
;;	                       \cup [type : {"2b"}, bal : Nat,
;;	                             val : CONSTANT_Values_,
;;	                             acc : CONSTANT_Acceptors_])
;;	        /\ VARIABLE_maxVBal_ \in [CONSTANT_Acceptors_ -> Nat \cup {-1}]
;;	        /\ VARIABLE_maxBal_ \in [CONSTANT_Acceptors_ -> Nat \cup {-1}]
;;	        /\ VARIABLE_maxVal_
;;	           \in [CONSTANT_Acceptors_ ->
;;	                  CONSTANT_Values_ \cup {CONSTANT_None_}]
;;	        /\ \A CONSTANT_a_ \in CONSTANT_Acceptors_ :
;;	              VARIABLE_maxBal_[CONSTANT_a_] >= VARIABLE_maxVBal_[CONSTANT_a_])
;;	       /\ (\A CONSTANT_m_ \in VARIABLE_msgs_ :
;;	              /\ CONSTANT_m_.type = "1b"
;;	                 => (/\ CONSTANT_m_.bal =< VARIABLE_maxBal_[CONSTANT_m_.acc]
;;	                     /\ \/ /\ CONSTANT_m_.maxVal \in CONSTANT_Values_
;;	                           /\ CONSTANT_m_.maxVBal \in Nat
;;	                           /\ \E CONSTANT_m__1 \in VARIABLE_msgs_ :
;;	                                 /\ CONSTANT_m__1.type = "2b"
;;	                                 /\ CONSTANT_m__1.val = CONSTANT_m_.maxVal
;;	                                 /\ CONSTANT_m__1.bal = CONSTANT_m_.maxVBal
;;	                                 /\ CONSTANT_m__1.acc = CONSTANT_m_.acc
;;	                        \/ /\ CONSTANT_m_.maxVal = CONSTANT_None_
;;	                           /\ CONSTANT_m_.maxVBal = -1
;;	                     /\ \A CONSTANT_c_
;;	                           \in CONSTANT_m_.maxVBal + 1..CONSTANT_m_.bal - 1 :
;;	                           ~(\E CONSTANT_v_ \in CONSTANT_Values_ :
;;	                                \E CONSTANT_m__1 \in VARIABLE_msgs_ :
;;	                                   /\ CONSTANT_m__1.type = "2b"
;;	                                   /\ CONSTANT_m__1.val = CONSTANT_v_
;;	                                   /\ CONSTANT_m__1.bal = CONSTANT_c_
;;	                                   /\ CONSTANT_m__1.acc = CONSTANT_m_.acc))
;;	              /\ CONSTANT_m_.type = "2a"
;;	                 => (/\ STATE_SafeAt_(CONSTANT_m_.val, CONSTANT_m_.bal)
;;	                     /\ \A CONSTANT_ma_ \in VARIABLE_msgs_ :
;;	                           CONSTANT_ma_.type = "2a"
;;	                           /\ CONSTANT_ma_.bal = CONSTANT_m_.bal
;;	                           => CONSTANT_ma_ = CONSTANT_m_)
;;	              /\ CONSTANT_m_.type = "2b"
;;	                 => (/\ \E CONSTANT_ma_ \in VARIABLE_msgs_ :
;;	                           /\ CONSTANT_ma_.type = "2a"
;;	                           /\ CONSTANT_ma_.bal = CONSTANT_m_.bal
;;	                           /\ CONSTANT_ma_.val = CONSTANT_m_.val
;;	                     /\ CONSTANT_m_.bal =< VARIABLE_maxVBal_[CONSTANT_m_.acc]))
;;	       /\ STATE_AccInv_ ,
;;	       ACTION_Next_ ,
;;	       NEW CONSTANT CONSTANT_a_ \in CONSTANT_Acceptors_,
;;	       NEW CONSTANT CONSTANT_m_ \in VARIABLE_msgs_,
;;	       CONSTANT_m_.bal >= VARIABLE_maxBal_[CONSTANT_a_] ,
;;	       CONSTANT_m_.type = "2a" ,
;;	       ?VARIABLE_msgs_#prime
;;	       = VARIABLE_msgs_
;;	         \cup {[type |-> "2b", bal |-> CONSTANT_m_.bal,
;;	                val |-> CONSTANT_m_.val, acc |-> CONSTANT_a_]} ,
;;	       ?VARIABLE_maxVBal_#prime
;;	       = [VARIABLE_maxVBal_ EXCEPT ![CONSTANT_a_] = CONSTANT_m_.bal] ,
;;	       ?VARIABLE_maxBal_#prime
;;	       = [VARIABLE_maxBal_ EXCEPT ![CONSTANT_a_] = CONSTANT_m_.bal] ,
;;	       ?VARIABLE_maxVal_#prime
;;	       = [VARIABLE_maxVal_ EXCEPT ![CONSTANT_a_] = CONSTANT_m_.val] 
;;	PROVE  \A CONSTANT_mm_ \in VARIABLE_msgs_ :
;;	          CONSTANT_mm_.type = "1b"
;;	          => (\A CONSTANT_v_ \in CONSTANT_Values_,
;;	                 CONSTANT_c_
;;	                 \in CONSTANT_mm_.maxVBal + 1..CONSTANT_mm_.bal - 1 :
;;	                 ~(\E CONSTANT_m__1 \in VARIABLE_msgs_ :
;;	                      /\ CONSTANT_m__1.type = "2b"
;;	                      /\ CONSTANT_m__1.val = CONSTANT_v_
;;	                      /\ CONSTANT_m__1.bal = CONSTANT_c_
;;	                      /\ CONSTANT_m__1.acc = CONSTANT_mm_.acc)
;;	                 => ~(\E CONSTANT_m__1 \in ?VARIABLE_msgs_#prime :
;;	                         /\ CONSTANT_m__1.type = "2b"
;;	                         /\ CONSTANT_m__1.val = CONSTANT_v_
;;	                         /\ CONSTANT_m__1.bal = CONSTANT_c_
;;	                         /\ CONSTANT_m__1.acc = CONSTANT_mm_.acc))
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #218
;; Generated from file "./Paxos.tla", line 446, characters 9-10

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

(declare-fun smt__TLAunderscore_underscore_IntMinus (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntPlus (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntRange (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_IntUminus (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_NatSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Projunderscore_Int (Idv) Int)

(declare-fun smt__TLAunderscore_underscore_RecordSetunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type (Idv
  Idv Idv Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_RecordSetunderscore_accunderscore_balunderscore_typeunderscore_val (Idv
  Idv Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_RecordSetunderscore_balunderscore_type (Idv
  Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_RecordSetunderscore_balunderscore_typeunderscore_val (Idv
  Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type (Idv
  Idv Idv Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val (Idv
  Idv Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type (Idv
  Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val (Idv
  Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_1 (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_2 (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_3 (Idv Idv
  Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_4 (Idv Idv Idv
  Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetEnumunderscore_5 (Idv Idv Idv
  Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_1a () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_1b () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_2a () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_2b () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_acc () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_bal () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_maxVBal () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_maxVal () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_type () Idv)

(declare-fun smt__TLAunderscore_underscore_StrLitunderscore_val () Idv)

(declare-fun smt__TLAunderscore_underscore_StrSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Subset (Idv) Idv)

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

;; Axiom: EnumDefIntro 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv))
      (!
        (and
          (smt__TLAunderscore_underscore_Mem smt__a1
            (smt__TLAunderscore_underscore_SetEnumunderscore_2 smt__a1
              smt__a2))
          (smt__TLAunderscore_underscore_Mem smt__a2
            (smt__TLAunderscore_underscore_SetEnumunderscore_2 smt__a1
              smt__a2)))
        :pattern ((smt__TLAunderscore_underscore_SetEnumunderscore_2 
                    smt__a1 smt__a2)))) :named |EnumDefIntro 2|))

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

;; Axiom: EnumDefElim 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__x
            (smt__TLAunderscore_underscore_SetEnumunderscore_2 smt__a1
              smt__a2)) (or (= smt__x smt__a1) (= smt__x smt__a2)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__x
                    (smt__TLAunderscore_underscore_SetEnumunderscore_2
                      smt__a1 smt__a2))))) :named |EnumDefElim 2|))

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

;; Axiom: StrLitIsstr val
(assert
  (!
    (smt__TLAunderscore_underscore_Mem
      smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrSet) :named |StrLitIsstr val|))

;; Axiom: StrLitDistinct 1a bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1a
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct 1a bal|))

;; Axiom: StrLitDistinct 1a type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1a
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct 1a type|))

;; Axiom: StrLitDistinct 1b 1a
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_1b
      smt__TLAunderscore_underscore_StrLitunderscore_1a)
    :named |StrLitDistinct 1b 1a|))

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

;; Axiom: StrLitDistinct 2a 1a
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2a
      smt__TLAunderscore_underscore_StrLitunderscore_1a)
    :named |StrLitDistinct 2a 1a|))

;; Axiom: StrLitDistinct 2a 1b
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2a
      smt__TLAunderscore_underscore_StrLitunderscore_1b)
    :named |StrLitDistinct 2a 1b|))

;; Axiom: StrLitDistinct 2a acc
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2a
      smt__TLAunderscore_underscore_StrLitunderscore_acc)
    :named |StrLitDistinct 2a acc|))

;; Axiom: StrLitDistinct 2a bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2a
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct 2a bal|))

;; Axiom: StrLitDistinct 2a maxVBal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2a
      smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
    :named |StrLitDistinct 2a maxVBal|))

;; Axiom: StrLitDistinct 2a maxVal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2a
      smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
    :named |StrLitDistinct 2a maxVal|))

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

;; Axiom: StrLitDistinct 2b 1a
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrLitunderscore_1a)
    :named |StrLitDistinct 2b 1a|))

;; Axiom: StrLitDistinct 2b 1b
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrLitunderscore_1b)
    :named |StrLitDistinct 2b 1b|))

;; Axiom: StrLitDistinct 2b 2a
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrLitunderscore_2a)
    :named |StrLitDistinct 2b 2a|))

;; Axiom: StrLitDistinct 2b acc
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrLitunderscore_acc)
    :named |StrLitDistinct 2b acc|))

;; Axiom: StrLitDistinct 2b bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct 2b bal|))

;; Axiom: StrLitDistinct 2b maxVBal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
    :named |StrLitDistinct 2b maxVBal|))

;; Axiom: StrLitDistinct 2b maxVal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_2b
      smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
    :named |StrLitDistinct 2b maxVal|))

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

;; Axiom: StrLitDistinct acc 1a
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_acc
      smt__TLAunderscore_underscore_StrLitunderscore_1a)
    :named |StrLitDistinct acc 1a|))

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

;; Axiom: StrLitDistinct maxVBal 1a
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_maxVBal
      smt__TLAunderscore_underscore_StrLitunderscore_1a)
    :named |StrLitDistinct maxVBal 1a|))

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

;; Axiom: StrLitDistinct maxVBal type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_maxVBal
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct maxVBal type|))

;; Axiom: StrLitDistinct maxVal 1a
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_maxVal
      smt__TLAunderscore_underscore_StrLitunderscore_1a)
    :named |StrLitDistinct maxVal 1a|))

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

;; Axiom: StrLitDistinct maxVal type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_maxVal
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct maxVal type|))

;; Axiom: StrLitDistinct type bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_type
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct type bal|))

;; Axiom: StrLitDistinct val 1a
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrLitunderscore_1a)
    :named |StrLitDistinct val 1a|))

;; Axiom: StrLitDistinct val 1b
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrLitunderscore_1b)
    :named |StrLitDistinct val 1b|))

;; Axiom: StrLitDistinct val acc
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrLitunderscore_acc)
    :named |StrLitDistinct val acc|))

;; Axiom: StrLitDistinct val bal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrLitunderscore_bal)
    :named |StrLitDistinct val bal|))

;; Axiom: StrLitDistinct val maxVBal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
    :named |StrLitDistinct val maxVBal|))

;; Axiom: StrLitDistinct val maxVal
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
    :named |StrLitDistinct val maxVal|))

;; Axiom: StrLitDistinct val type
(assert
  (!
    (distinct smt__TLAunderscore_underscore_StrLitunderscore_val
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    :named |StrLitDistinct val type|))

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

;; Axiom: RecIsafcn bal type
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv))
      (!
        (smt__TLAunderscore_underscore_FunIsafcn
          (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
            smt__x1 smt__x2))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
                    smt__x1 smt__x2)))) :named |RecIsafcn bal type|))

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

;; Axiom: RecDomDef bal type
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunDom
            (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
              smt__x1 smt__x2))
          (smt__TLAunderscore_underscore_SetEnumunderscore_2
            smt__TLAunderscore_underscore_StrLitunderscore_bal
            smt__TLAunderscore_underscore_StrLitunderscore_type))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
                    smt__x1 smt__x2)))) :named |RecDomDef bal type|))

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

;; Axiom: RecAppDef bal type
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv))
      (!
        (and
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
                smt__x1 smt__x2)
              smt__TLAunderscore_underscore_StrLitunderscore_bal) smt__x1)
          (=
            (smt__TLAunderscore_underscore_FunApp
              (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
                smt__x1 smt__x2)
              smt__TLAunderscore_underscore_StrLitunderscore_type) smt__x2))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
                    smt__x1 smt__x2)))) :named |RecAppDef bal type|))

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

;; Axiom: RecExcept acc bal type val 1
(assert
  (!
    (forall
      ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
              smt__x1 smt__x2 smt__x3 smt__x4)
            smt__TLAunderscore_underscore_StrLitunderscore_acc smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
            smt__x smt__x2 smt__x3 smt__x4))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                      smt__x1 smt__x2 smt__x3 smt__x4)
                    smt__TLAunderscore_underscore_StrLitunderscore_acc 
                    smt__x)))) :named |RecExcept acc bal type val 1|))

;; Axiom: RecExcept acc bal type val 2
(assert
  (!
    (forall
      ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
              smt__x1 smt__x2 smt__x3 smt__x4)
            smt__TLAunderscore_underscore_StrLitunderscore_bal smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
            smt__x1 smt__x smt__x3 smt__x4))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                      smt__x1 smt__x2 smt__x3 smt__x4)
                    smt__TLAunderscore_underscore_StrLitunderscore_bal 
                    smt__x)))) :named |RecExcept acc bal type val 2|))

;; Axiom: RecExcept acc bal type val 3
(assert
  (!
    (forall
      ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
              smt__x1 smt__x2 smt__x3 smt__x4)
            smt__TLAunderscore_underscore_StrLitunderscore_type smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
            smt__x1 smt__x2 smt__x smt__x4))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                      smt__x1 smt__x2 smt__x3 smt__x4)
                    smt__TLAunderscore_underscore_StrLitunderscore_type
                    smt__x)))) :named |RecExcept acc bal type val 3|))

;; Axiom: RecExcept acc bal type val 4
(assert
  (!
    (forall
      ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
              smt__x1 smt__x2 smt__x3 smt__x4)
            smt__TLAunderscore_underscore_StrLitunderscore_val smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
            smt__x1 smt__x2 smt__x3 smt__x))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                      smt__x1 smt__x2 smt__x3 smt__x4)
                    smt__TLAunderscore_underscore_StrLitunderscore_val 
                    smt__x)))) :named |RecExcept acc bal type val 4|))

;; Axiom: RecExcept bal type 1
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
              smt__x1 smt__x2)
            smt__TLAunderscore_underscore_StrLitunderscore_bal smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
            smt__x smt__x2))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
                      smt__x1 smt__x2)
                    smt__TLAunderscore_underscore_StrLitunderscore_bal 
                    smt__x)))) :named |RecExcept bal type 1|))

;; Axiom: RecExcept bal type 2
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
              smt__x1 smt__x2)
            smt__TLAunderscore_underscore_StrLitunderscore_type smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
            smt__x1 smt__x))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
                      smt__x1 smt__x2)
                    smt__TLAunderscore_underscore_StrLitunderscore_type
                    smt__x)))) :named |RecExcept bal type 2|))

;; Axiom: RecExcept bal type val 1
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
              smt__x1 smt__x2 smt__x3)
            smt__TLAunderscore_underscore_StrLitunderscore_bal smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
            smt__x smt__x2 smt__x3))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
                      smt__x1 smt__x2 smt__x3)
                    smt__TLAunderscore_underscore_StrLitunderscore_bal 
                    smt__x)))) :named |RecExcept bal type val 1|))

;; Axiom: RecExcept bal type val 2
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
              smt__x1 smt__x2 smt__x3)
            smt__TLAunderscore_underscore_StrLitunderscore_type smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
            smt__x1 smt__x smt__x3))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
                      smt__x1 smt__x2 smt__x3)
                    smt__TLAunderscore_underscore_StrLitunderscore_type
                    smt__x)))) :named |RecExcept bal type val 2|))

;; Axiom: RecExcept bal type val 3
(assert
  (!
    (forall ((smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x Idv))
      (!
        (=
          (smt__TLAunderscore_underscore_FunExcept
            (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
              smt__x1 smt__x2 smt__x3)
            smt__TLAunderscore_underscore_StrLitunderscore_val smt__x)
          (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
            smt__x1 smt__x2 smt__x))
        :pattern ((smt__TLAunderscore_underscore_FunExcept
                    (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
                      smt__x1 smt__x2 smt__x3)
                    smt__TLAunderscore_underscore_StrLitunderscore_val 
                    smt__x)))) :named |RecExcept bal type val 3|))

;; Axiom: RecSetIntro acc bal maxVBal maxVal type
(assert
  (!
    (forall
      ((smt__s1 Idv) (smt__s2 Idv) (smt__s3 Idv) (smt__s4 Idv) (smt__s5 Idv)
        (smt__x1 Idv) (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv) (smt__x5 Idv))
      (!
        (=>
          (and (smt__TLAunderscore_underscore_Mem smt__x1 smt__s1)
            (smt__TLAunderscore_underscore_Mem smt__x2 smt__s2)
            (smt__TLAunderscore_underscore_Mem smt__x3 smt__s3)
            (smt__TLAunderscore_underscore_Mem smt__x4 smt__s4)
            (smt__TLAunderscore_underscore_Mem smt__x5 smt__s5))
          (smt__TLAunderscore_underscore_Mem
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
              smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
            (smt__TLAunderscore_underscore_RecordSetunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
              smt__s1 smt__s2 smt__s3 smt__s4 smt__s5)))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                    smt__x1 smt__x2 smt__x3 smt__x4 smt__x5)
                   (smt__TLAunderscore_underscore_RecordSetunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                     smt__s1 smt__s2 smt__s3 smt__s4 smt__s5))))
    :named |RecSetIntro acc bal maxVBal maxVal type|))

;; Axiom: RecSetIntro acc bal type val
(assert
  (!
    (forall
      ((smt__s1 Idv) (smt__s2 Idv) (smt__s3 Idv) (smt__s4 Idv) (smt__x1 Idv)
        (smt__x2 Idv) (smt__x3 Idv) (smt__x4 Idv))
      (!
        (=>
          (and (smt__TLAunderscore_underscore_Mem smt__x1 smt__s1)
            (smt__TLAunderscore_underscore_Mem smt__x2 smt__s2)
            (smt__TLAunderscore_underscore_Mem smt__x3 smt__s3)
            (smt__TLAunderscore_underscore_Mem smt__x4 smt__s4))
          (smt__TLAunderscore_underscore_Mem
            (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
              smt__x1 smt__x2 smt__x3 smt__x4)
            (smt__TLAunderscore_underscore_RecordSetunderscore_accunderscore_balunderscore_typeunderscore_val
              smt__s1 smt__s2 smt__s3 smt__s4)))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                    smt__x1 smt__x2 smt__x3 smt__x4)
                   (smt__TLAunderscore_underscore_RecordSetunderscore_accunderscore_balunderscore_typeunderscore_val
                     smt__s1 smt__s2 smt__s3 smt__s4))))
    :named |RecSetIntro acc bal type val|))

;; Axiom: RecSetIntro bal type
(assert
  (!
    (forall ((smt__s1 Idv) (smt__s2 Idv) (smt__x1 Idv) (smt__x2 Idv))
      (!
        (=>
          (and (smt__TLAunderscore_underscore_Mem smt__x1 smt__s1)
            (smt__TLAunderscore_underscore_Mem smt__x2 smt__s2))
          (smt__TLAunderscore_underscore_Mem
            (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
              smt__x1 smt__x2)
            (smt__TLAunderscore_underscore_RecordSetunderscore_balunderscore_type
              smt__s1 smt__s2)))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
                    smt__x1 smt__x2)
                   (smt__TLAunderscore_underscore_RecordSetunderscore_balunderscore_type
                     smt__s1 smt__s2)))) :named |RecSetIntro bal type|))

;; Axiom: RecSetIntro bal type val
(assert
  (!
    (forall
      ((smt__s1 Idv) (smt__s2 Idv) (smt__s3 Idv) (smt__x1 Idv) (smt__x2 Idv)
        (smt__x3 Idv))
      (!
        (=>
          (and (smt__TLAunderscore_underscore_Mem smt__x1 smt__s1)
            (smt__TLAunderscore_underscore_Mem smt__x2 smt__s2)
            (smt__TLAunderscore_underscore_Mem smt__x3 smt__s3))
          (smt__TLAunderscore_underscore_Mem
            (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
              smt__x1 smt__x2 smt__x3)
            (smt__TLAunderscore_underscore_RecordSetunderscore_balunderscore_typeunderscore_val
              smt__s1 smt__s2 smt__s3)))
        :pattern ((smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
                    smt__x1 smt__x2 smt__x3)
                   (smt__TLAunderscore_underscore_RecordSetunderscore_balunderscore_typeunderscore_val
                     smt__s1 smt__s2 smt__s3))))
    :named |RecSetIntro bal type val|))

;; Axiom: RecSetElim acc bal maxVBal maxVal type
(assert
  (!
    (forall
      ((smt__s1 Idv) (smt__s2 Idv) (smt__s3 Idv) (smt__s4 Idv) (smt__s5 Idv)
        (smt__r Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__r
            (smt__TLAunderscore_underscore_RecordSetunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
              smt__s1 smt__s2 smt__s3 smt__s4 smt__s5))
          (and
            (= smt__r
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_acc)
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_type)))
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_acc) smt__s1)
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_bal) smt__s2)
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
              smt__s3)
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
              smt__s4)
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_type) 
              smt__s5)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__r
                    (smt__TLAunderscore_underscore_RecordSetunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                      smt__s1 smt__s2 smt__s3 smt__s4 smt__s5)))))
    :named |RecSetElim acc bal maxVBal maxVal type|))

;; Axiom: RecSetElim acc bal type val
(assert
  (!
    (forall
      ((smt__s1 Idv) (smt__s2 Idv) (smt__s3 Idv) (smt__s4 Idv) (smt__r Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__r
            (smt__TLAunderscore_underscore_RecordSetunderscore_accunderscore_balunderscore_typeunderscore_val
              smt__s1 smt__s2 smt__s3 smt__s4))
          (and
            (= smt__r
              (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_acc)
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_type)
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_val)))
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_acc) smt__s1)
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_bal) smt__s2)
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_type) 
              smt__s3)
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_val) smt__s4)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__r
                    (smt__TLAunderscore_underscore_RecordSetunderscore_accunderscore_balunderscore_typeunderscore_val
                      smt__s1 smt__s2 smt__s3 smt__s4)))))
    :named |RecSetElim acc bal type val|))

;; Axiom: RecSetElim bal type
(assert
  (!
    (forall ((smt__s1 Idv) (smt__s2 Idv) (smt__r Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__r
            (smt__TLAunderscore_underscore_RecordSetunderscore_balunderscore_type
              smt__s1 smt__s2))
          (and
            (= smt__r
              (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_type
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_type)))
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_bal) smt__s1)
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_type) 
              smt__s2)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__r
                    (smt__TLAunderscore_underscore_RecordSetunderscore_balunderscore_type
                      smt__s1 smt__s2))))) :named |RecSetElim bal type|))

;; Axiom: RecSetElim bal type val
(assert
  (!
    (forall ((smt__s1 Idv) (smt__s2 Idv) (smt__s3 Idv) (smt__r Idv))
      (!
        (=>
          (smt__TLAunderscore_underscore_Mem smt__r
            (smt__TLAunderscore_underscore_RecordSetunderscore_balunderscore_typeunderscore_val
              smt__s1 smt__s2 smt__s3))
          (and
            (= smt__r
              (smt__TLAunderscore_underscore_Recordunderscore_balunderscore_typeunderscore_val
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_bal)
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_type)
                (smt__TLAunderscore_underscore_FunApp smt__r
                  smt__TLAunderscore_underscore_StrLitunderscore_val)))
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_bal) smt__s1)
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_type) 
              smt__s2)
            (smt__TLAunderscore_underscore_Mem
              (smt__TLAunderscore_underscore_FunApp smt__r
                smt__TLAunderscore_underscore_StrLitunderscore_val) smt__s3)))
        :pattern ((smt__TLAunderscore_underscore_Mem smt__r
                    (smt__TLAunderscore_underscore_RecordSetunderscore_balunderscore_typeunderscore_val
                      smt__s1 smt__s2 smt__s3)))))
    :named |RecSetElim bal type val|))

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

;; Axiom: Typing TIntPlus
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (smt__TLAunderscore_underscore_IntPlus
            (smt__TLAunderscore_underscore_Castunderscore_Int smt__x1)
            (smt__TLAunderscore_underscore_Castunderscore_Int smt__x2))
          (smt__TLAunderscore_underscore_Castunderscore_Int
            (+ smt__x1 smt__x2)))
        :pattern ((smt__TLAunderscore_underscore_IntPlus
                    (smt__TLAunderscore_underscore_Castunderscore_Int smt__x1)
                    (smt__TLAunderscore_underscore_Castunderscore_Int smt__x2)))))
    :named |Typing TIntPlus|))

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

(declare-fun smt__STATEunderscore_WontVoteInunderscore_ (Idv Idv) Idv)

(declare-fun smt__STATEunderscore_SafeAtunderscore_ (Idv Idv) Idv)

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
      (and
        (smt__TLAunderscore_underscore_Mem
          smt__VARIABLEunderscore_msgsunderscore_
          (smt__TLAunderscore_underscore_Subset
            (smt__TLAunderscore_underscore_Cup
              (smt__TLAunderscore_underscore_Cup
                (smt__TLAunderscore_underscore_Cup
                  (smt__TLAunderscore_underscore_RecordSetunderscore_balunderscore_type
                    smt__TLAunderscore_underscore_NatSet
                    (smt__TLAunderscore_underscore_SetEnumunderscore_1
                      smt__TLAunderscore_underscore_StrLitunderscore_1a))
                  (smt__TLAunderscore_underscore_RecordSetunderscore_accunderscore_balunderscore_maxVBalunderscore_maxValunderscore_type
                    smt__CONSTANTunderscore_Acceptorsunderscore_
                    smt__TLAunderscore_underscore_NatSet
                    (smt__TLAunderscore_underscore_Cup
                      smt__TLAunderscore_underscore_NatSet
                      (smt__TLAunderscore_underscore_SetEnumunderscore_1
                        (smt__TLAunderscore_underscore_IntUminus
                          (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
                    (smt__TLAunderscore_underscore_Cup
                      smt__CONSTANTunderscore_Valuesunderscore_
                      (smt__TLAunderscore_underscore_SetEnumunderscore_1
                        smt__CONSTANTunderscore_Noneunderscore_))
                    (smt__TLAunderscore_underscore_SetEnumunderscore_1
                      smt__TLAunderscore_underscore_StrLitunderscore_1b)))
                (smt__TLAunderscore_underscore_RecordSetunderscore_balunderscore_typeunderscore_val
                  smt__TLAunderscore_underscore_NatSet
                  (smt__TLAunderscore_underscore_SetEnumunderscore_1
                    smt__TLAunderscore_underscore_StrLitunderscore_2a)
                  smt__CONSTANTunderscore_Valuesunderscore_))
              (smt__TLAunderscore_underscore_RecordSetunderscore_accunderscore_balunderscore_typeunderscore_val
                smt__CONSTANTunderscore_Acceptorsunderscore_
                smt__TLAunderscore_underscore_NatSet
                (smt__TLAunderscore_underscore_SetEnumunderscore_1
                  smt__TLAunderscore_underscore_StrLitunderscore_2b)
                smt__CONSTANTunderscore_Valuesunderscore_))))
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
      (forall ((smt__CONSTANTunderscore_munderscore_ Idv))
        (=>
          (smt__TLAunderscore_underscore_Mem
            smt__CONSTANTunderscore_munderscore_
            smt__VARIABLEunderscore_msgsunderscore_)
          (and
            (=>
              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                (smt__TLAunderscore_underscore_FunApp
                  smt__CONSTANTunderscore_munderscore_
                  smt__TLAunderscore_underscore_StrLitunderscore_type)
                smt__TLAunderscore_underscore_StrLitunderscore_1b)
              (and
                (smt__TLAunderscore_underscore_IntLteq
                  (smt__TLAunderscore_underscore_FunApp
                    smt__CONSTANTunderscore_munderscore_
                    smt__TLAunderscore_underscore_StrLitunderscore_bal)
                  (smt__TLAunderscore_underscore_FunApp
                    smt__VARIABLEunderscore_maxBalunderscore_
                    (smt__TLAunderscore_underscore_FunApp
                      smt__CONSTANTunderscore_munderscore_
                      smt__TLAunderscore_underscore_StrLitunderscore_acc)))
                (or
                  (and
                    (smt__TLAunderscore_underscore_Mem
                      (smt__TLAunderscore_underscore_FunApp
                        smt__CONSTANTunderscore_munderscore_
                        smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
                      smt__CONSTANTunderscore_Valuesunderscore_)
                    (smt__TLAunderscore_underscore_Mem
                      (smt__TLAunderscore_underscore_FunApp
                        smt__CONSTANTunderscore_munderscore_
                        smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
                      smt__TLAunderscore_underscore_NatSet)
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
                            (smt__TLAunderscore_underscore_FunApp
                              smt__CONSTANTunderscore_munderscore_
                              smt__TLAunderscore_underscore_StrLitunderscore_maxVal))
                          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                            (smt__TLAunderscore_underscore_FunApp
                              smt__CONSTANTunderscore_munderscore__1
                              smt__TLAunderscore_underscore_StrLitunderscore_bal)
                            (smt__TLAunderscore_underscore_FunApp
                              smt__CONSTANTunderscore_munderscore_
                              smt__TLAunderscore_underscore_StrLitunderscore_maxVBal))
                          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                            (smt__TLAunderscore_underscore_FunApp
                              smt__CONSTANTunderscore_munderscore__1
                              smt__TLAunderscore_underscore_StrLitunderscore_acc)
                            (smt__TLAunderscore_underscore_FunApp
                              smt__CONSTANTunderscore_munderscore_
                              smt__TLAunderscore_underscore_StrLitunderscore_acc))))))
                  (and
                    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                      (smt__TLAunderscore_underscore_FunApp
                        smt__CONSTANTunderscore_munderscore_
                        smt__TLAunderscore_underscore_StrLitunderscore_maxVal)
                      smt__CONSTANTunderscore_Noneunderscore_)
                    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                      (smt__TLAunderscore_underscore_FunApp
                        smt__CONSTANTunderscore_munderscore_
                        smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
                      (smt__TLAunderscore_underscore_IntUminus
                        (smt__TLAunderscore_underscore_Castunderscore_Int 1)))))
                (forall ((smt__CONSTANTunderscore_cunderscore_ Idv))
                  (=>
                    (smt__TLAunderscore_underscore_Mem
                      smt__CONSTANTunderscore_cunderscore_
                      (smt__TLAunderscore_underscore_IntRange
                        (smt__TLAunderscore_underscore_IntPlus
                          (smt__TLAunderscore_underscore_FunApp
                            smt__CONSTANTunderscore_munderscore_
                            smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
                          (smt__TLAunderscore_underscore_Castunderscore_Int 1))
                        (smt__TLAunderscore_underscore_IntMinus
                          (smt__TLAunderscore_underscore_FunApp
                            smt__CONSTANTunderscore_munderscore_
                            smt__TLAunderscore_underscore_StrLitunderscore_bal)
                          (smt__TLAunderscore_underscore_Castunderscore_Int 1))))
                    (not
                      (exists ((smt__CONSTANTunderscore_vunderscore_ Idv))
                        (and
                          (smt__TLAunderscore_underscore_Mem
                            smt__CONSTANTunderscore_vunderscore_
                            smt__CONSTANTunderscore_Valuesunderscore_)
                          (exists
                            ((smt__CONSTANTunderscore_munderscore__1 Idv))
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
                                  smt__CONSTANTunderscore_vunderscore_)
                                (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                  (smt__TLAunderscore_underscore_FunApp
                                    smt__CONSTANTunderscore_munderscore__1
                                    smt__TLAunderscore_underscore_StrLitunderscore_bal)
                                  smt__CONSTANTunderscore_cunderscore_)
                                (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                                  (smt__TLAunderscore_underscore_FunApp
                                    smt__CONSTANTunderscore_munderscore__1
                                    smt__TLAunderscore_underscore_StrLitunderscore_acc)
                                  (smt__TLAunderscore_underscore_FunApp
                                    smt__CONSTANTunderscore_munderscore_
                                    smt__TLAunderscore_underscore_StrLitunderscore_acc))))))))))))
            (=>
              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                (smt__TLAunderscore_underscore_FunApp
                  smt__CONSTANTunderscore_munderscore_
                  smt__TLAunderscore_underscore_StrLitunderscore_type)
                smt__TLAunderscore_underscore_StrLitunderscore_2a)
              (and
                (=
                  (smt__STATEunderscore_SafeAtunderscore_
                    (smt__TLAunderscore_underscore_FunApp
                      smt__CONSTANTunderscore_munderscore_
                      smt__TLAunderscore_underscore_StrLitunderscore_val)
                    (smt__TLAunderscore_underscore_FunApp
                      smt__CONSTANTunderscore_munderscore_
                      smt__TLAunderscore_underscore_StrLitunderscore_bal))
                  smt__TLAunderscore_underscore_Ttunderscore_Idv)
                (forall ((smt__CONSTANTunderscore_maunderscore_ Idv))
                  (=>
                    (smt__TLAunderscore_underscore_Mem
                      smt__CONSTANTunderscore_maunderscore_
                      smt__VARIABLEunderscore_msgsunderscore_)
                    (=>
                      (and
                        (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                          (smt__TLAunderscore_underscore_FunApp
                            smt__CONSTANTunderscore_maunderscore_
                            smt__TLAunderscore_underscore_StrLitunderscore_type)
                          smt__TLAunderscore_underscore_StrLitunderscore_2a)
                        (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                          (smt__TLAunderscore_underscore_FunApp
                            smt__CONSTANTunderscore_maunderscore_
                            smt__TLAunderscore_underscore_StrLitunderscore_bal)
                          (smt__TLAunderscore_underscore_FunApp
                            smt__CONSTANTunderscore_munderscore_
                            smt__TLAunderscore_underscore_StrLitunderscore_bal)))
                      (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                        smt__CONSTANTunderscore_maunderscore_
                        smt__CONSTANTunderscore_munderscore_))))))
            (=>
              (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                (smt__TLAunderscore_underscore_FunApp
                  smt__CONSTANTunderscore_munderscore_
                  smt__TLAunderscore_underscore_StrLitunderscore_type)
                smt__TLAunderscore_underscore_StrLitunderscore_2b)
              (and
                (exists ((smt__CONSTANTunderscore_maunderscore_ Idv))
                  (and
                    (smt__TLAunderscore_underscore_Mem
                      smt__CONSTANTunderscore_maunderscore_
                      smt__VARIABLEunderscore_msgsunderscore_)
                    (and
                      (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                        (smt__TLAunderscore_underscore_FunApp
                          smt__CONSTANTunderscore_maunderscore_
                          smt__TLAunderscore_underscore_StrLitunderscore_type)
                        smt__TLAunderscore_underscore_StrLitunderscore_2a)
                      (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                        (smt__TLAunderscore_underscore_FunApp
                          smt__CONSTANTunderscore_maunderscore_
                          smt__TLAunderscore_underscore_StrLitunderscore_bal)
                        (smt__TLAunderscore_underscore_FunApp
                          smt__CONSTANTunderscore_munderscore_
                          smt__TLAunderscore_underscore_StrLitunderscore_bal))
                      (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                        (smt__TLAunderscore_underscore_FunApp
                          smt__CONSTANTunderscore_maunderscore_
                          smt__TLAunderscore_underscore_StrLitunderscore_val)
                        (smt__TLAunderscore_underscore_FunApp
                          smt__CONSTANTunderscore_munderscore_
                          smt__TLAunderscore_underscore_StrLitunderscore_val)))))
                (smt__TLAunderscore_underscore_IntLteq
                  (smt__TLAunderscore_underscore_FunApp
                    smt__CONSTANTunderscore_munderscore_
                    smt__TLAunderscore_underscore_StrLitunderscore_bal)
                  (smt__TLAunderscore_underscore_FunApp
                    smt__VARIABLEunderscore_maxVBalunderscore_
                    (smt__TLAunderscore_underscore_FunApp
                      smt__CONSTANTunderscore_munderscore_
                      smt__TLAunderscore_underscore_StrLitunderscore_acc)))))))))
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
  (smt__TLAunderscore_underscore_IntLteq
    (smt__TLAunderscore_underscore_FunApp
      smt__VARIABLEunderscore_maxBalunderscore_
      smt__CONSTANTunderscore_aunderscore_)
    (smt__TLAunderscore_underscore_FunApp
      smt__CONSTANTunderscore_munderscore_
      smt__TLAunderscore_underscore_StrLitunderscore_bal)))

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
    (smt__TLAunderscore_underscore_FunApp
      smt__CONSTANTunderscore_munderscore_
      smt__TLAunderscore_underscore_StrLitunderscore_type)
    smt__TLAunderscore_underscore_StrLitunderscore_2a))

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Setdollarsignunderscore_Idvdollarsignunderscore_
    smt__VARIABLEunderscore_msgsunderscore_underscore_prime
    (smt__TLAunderscore_underscore_Cup
      smt__VARIABLEunderscore_msgsunderscore_
      (smt__TLAunderscore_underscore_SetEnumunderscore_1
        (smt__TLAunderscore_underscore_Recordunderscore_accunderscore_balunderscore_typeunderscore_val
          smt__CONSTANTunderscore_aunderscore_
          (smt__TLAunderscore_underscore_FunApp
            smt__CONSTANTunderscore_munderscore_
            smt__TLAunderscore_underscore_StrLitunderscore_bal)
          smt__TLAunderscore_underscore_StrLitunderscore_2b
          (smt__TLAunderscore_underscore_FunApp
            smt__CONSTANTunderscore_munderscore_
            smt__TLAunderscore_underscore_StrLitunderscore_val))))))

(assert
  (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
    smt__VARIABLEunderscore_maxVBalunderscore_underscore_prime
    (smt__TLAunderscore_underscore_FunExcept
      smt__VARIABLEunderscore_maxVBalunderscore_
      smt__CONSTANTunderscore_aunderscore_
      (smt__TLAunderscore_underscore_FunApp
        smt__CONSTANTunderscore_munderscore_
        smt__TLAunderscore_underscore_StrLitunderscore_bal))))

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
    smt__VARIABLEunderscore_maxValunderscore_underscore_prime
    (smt__TLAunderscore_underscore_FunExcept
      smt__VARIABLEunderscore_maxValunderscore_
      smt__CONSTANTunderscore_aunderscore_
      (smt__TLAunderscore_underscore_FunApp
        smt__CONSTANTunderscore_munderscore_
        smt__TLAunderscore_underscore_StrLitunderscore_val))))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

;; Goal
(assert
  (!
    (not
      (forall ((smt__CONSTANTunderscore_mmunderscore_ Idv))
        (=>
          (smt__TLAunderscore_underscore_Mem
            smt__CONSTANTunderscore_mmunderscore_
            smt__VARIABLEunderscore_msgsunderscore_)
          (=>
            (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
              (smt__TLAunderscore_underscore_FunApp
                smt__CONSTANTunderscore_mmunderscore_
                smt__TLAunderscore_underscore_StrLitunderscore_type)
              smt__TLAunderscore_underscore_StrLitunderscore_1b)
            (forall
              ((smt__CONSTANTunderscore_vunderscore_ Idv)
                (smt__CONSTANTunderscore_cunderscore_ Idv))
              (=>
                (and
                  (smt__TLAunderscore_underscore_Mem
                    smt__CONSTANTunderscore_vunderscore_
                    smt__CONSTANTunderscore_Valuesunderscore_)
                  (smt__TLAunderscore_underscore_Mem
                    smt__CONSTANTunderscore_cunderscore_
                    (smt__TLAunderscore_underscore_IntRange
                      (smt__TLAunderscore_underscore_IntPlus
                        (smt__TLAunderscore_underscore_FunApp
                          smt__CONSTANTunderscore_mmunderscore_
                          smt__TLAunderscore_underscore_StrLitunderscore_maxVBal)
                        (smt__TLAunderscore_underscore_Castunderscore_Int 1))
                      (smt__TLAunderscore_underscore_IntMinus
                        (smt__TLAunderscore_underscore_FunApp
                          smt__CONSTANTunderscore_mmunderscore_
                          smt__TLAunderscore_underscore_StrLitunderscore_bal)
                        (smt__TLAunderscore_underscore_Castunderscore_Int 1)))))
                (=>
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
                            smt__CONSTANTunderscore_vunderscore_)
                          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                            (smt__TLAunderscore_underscore_FunApp
                              smt__CONSTANTunderscore_munderscore__1
                              smt__TLAunderscore_underscore_StrLitunderscore_bal)
                            smt__CONSTANTunderscore_cunderscore_)
                          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                            (smt__TLAunderscore_underscore_FunApp
                              smt__CONSTANTunderscore_munderscore__1
                              smt__TLAunderscore_underscore_StrLitunderscore_acc)
                            (smt__TLAunderscore_underscore_FunApp
                              smt__CONSTANTunderscore_mmunderscore_
                              smt__TLAunderscore_underscore_StrLitunderscore_acc))))))
                  (not
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
                            smt__CONSTANTunderscore_vunderscore_)
                          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                            (smt__TLAunderscore_underscore_FunApp
                              smt__CONSTANTunderscore_munderscore__1
                              smt__TLAunderscore_underscore_StrLitunderscore_bal)
                            smt__CONSTANTunderscore_cunderscore_)
                          (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
                            (smt__TLAunderscore_underscore_FunApp
                              smt__CONSTANTunderscore_munderscore__1
                              smt__TLAunderscore_underscore_StrLitunderscore_acc)
                            (smt__TLAunderscore_underscore_FunApp
                              smt__CONSTANTunderscore_mmunderscore_
                              smt__TLAunderscore_underscore_StrLitunderscore_acc)))))))))))))
    :named |Goal|))

(check-sat)
(exit)
