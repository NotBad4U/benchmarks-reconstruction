;; Proof obligation:
;;	ASSUME NEW CONSTANT CST_Client_,
;;	       NEW CONSTANT CST_Resource_,
;;	       NEW VARIABLE VAR_unsat_,
;;	       NEW VARIABLE VAR_alloc_,
;;	       NEW CONSTANT CST_clt_ \in CST_Client_,
;;	       NEW CONSTANT CST_S_ \in SUBSET CST_Resource_,
;;	       NEW CONSTANT CST_c1_ \in CST_Client_,
;;	       NEW CONSTANT CST_c2_ \in CST_Client_,
;;	       NEW CONSTANT CST_r_ \in CST_Resource_,
;;	       /\ /\ VAR_unsat_
;;	             \in [CST_Client_ -> SUBSET CST_Resource_]
;;	          /\ VAR_alloc_
;;	             \in [CST_Client_ -> SUBSET CST_Resource_]
;;	       /\ STATE_Mutex_
;;	       /\ ACTION_Allocate_(CST_clt_, CST_S_) ,
;;	       CST_r_
;;	       \in ?VAR_alloc_#prime[CST_c1_]
;;	           \cap ?VAR_alloc_#prime[CST_c2_] ,
;;	       ?VAR_alloc_#prime[CST_c2_] = VAR_alloc_[CST_c2_] ,
;;	       CST_c1_ # CST_c2_ 
;;	PROVE  CST_r_
;;	       \notin CST_Resource_
;;	              \ (UNION {VAR_alloc_[CST_c_] :
;;	                          CST_c_ \in CST_Client_})
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #64
;; Generated from file "/home/rosalied/Documents/work/thesis-eval/tla_specs/tlaps_examples/Allocator.tla", line 241, characters 5-6

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun Cap (Idv Idv) Idv)

(declare-fun FunApp (Idv Idv) Idv)

(declare-fun FunDom (Idv) Idv)

; omitted declaration of '_FunFcn' (second-order)

(declare-fun FunIsafcn (Idv) Bool)

(declare-fun FunSet (Idv Idv) Idv)

(declare-fun IsSetOf (Idv) Bool)

(declare-fun Mem (Idv Idv) Bool)

(declare-fun SetEnum___0 () Idv)

(declare-fun SetExtTrigger (Idv Idv) Bool)

(declare-fun SetMinus (Idv Idv) Idv)

; omitted declaration of '_SetOf_1' (second-order)

(declare-fun Subset (Idv) Idv)

(declare-fun SubsetEq (Idv Idv) Bool)

(declare-fun TrigEq___Idv (Idv Idv) Bool)

(declare-fun Tt___Idv () Idv)

(declare-fun Union (Idv) Idv)

;; Axiom: SetExt
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (= (Mem smt__z smt__x)
              (Mem smt__z smt__y))) (= smt__x smt__y))
        :pattern ((SetExtTrigger smt__x smt__y))))
    :named |SetExt|))

;; Axiom: SubsetEqIntro
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (=> (Mem smt__z smt__x)
              (Mem smt__z smt__y)))
          (SubsetEq smt__x smt__y))
        :pattern ((SubsetEq smt__x smt__y))))
    :named |SubsetEqIntro|))

;; Axiom: SubsetEqElim
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv) (smt__z Idv))
      (!
        (=>
          (and (SubsetEq smt__x smt__y)
            (Mem smt__z smt__x))
          (Mem smt__z smt__y))
        :pattern ((SubsetEq smt__x smt__y)
                   (Mem smt__z smt__x)))) :named |SubsetEqElim|))

;; Axiom: UnionIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv) (smt__y Idv))
      (!
        (=>
          (and (Mem smt__y smt__a)
            (Mem smt__x smt__y))
          (Mem smt__x (Union smt__a)))
        :pattern ((Mem smt__y smt__a)
                   (Mem smt__x (Union smt__a)))
        :pattern ((Mem smt__x smt__y)
                   (Mem smt__x (Union smt__a)))
        :pattern ((Mem smt__y smt__a)
                   (Mem smt__x smt__y)
                   (Union smt__a)))) :named |UnionIntro|))

;; Axiom: UnionElim
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=> (Mem smt__x (Union smt__a))
          (exists ((smt__y Idv))
            (and (Mem smt__y smt__a)
              (Mem smt__x smt__y))))
        :pattern ((Mem smt__x (Union smt__a)))))
    :named |UnionElim|))

;; Axiom: SubsetDefAlt
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (= (Mem smt__x (Subset smt__a))
          (SubsetEq smt__x smt__a))
        :pattern ((Mem smt__x (Subset smt__a)))
        :pattern ((SubsetEq smt__x smt__a)
                   (Subset smt__a)))) :named |SubsetDefAlt|))

;; Axiom: CapDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (= (Mem smt__x (Cap smt__a smt__b))
          (and (Mem smt__x smt__a)
            (Mem smt__x smt__b)))
        :pattern ((Mem smt__x (Cap smt__a smt__b)))
        :pattern ((Mem smt__x smt__a)
                   (Cap smt__a smt__b))
        :pattern ((Mem smt__x smt__b)
                   (Cap smt__a smt__b)))) :named |CapDef|))

;; Axiom: SetMinusDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (= (Mem smt__x (SetMinus smt__a smt__b))
          (and (Mem smt__x smt__a)
            (not (Mem smt__x smt__b))))
        :pattern ((Mem smt__x
                    (SetMinus smt__a smt__b)))
        :pattern ((Mem smt__x smt__a)
                   (SetMinus smt__a smt__b))
        :pattern ((Mem smt__x smt__b)
                   (SetMinus smt__a smt__b))))
    :named |SetMinusDef|))

;; Axiom: FunExt
(assert
  (!
    (forall ((smt__f Idv) (smt__g Idv))
      (!
        (=>
          (and (FunIsafcn smt__f)
            (FunIsafcn smt__g)
            (= (FunDom smt__f) (FunDom smt__g))
            (forall ((smt__x Idv))
              (=> (Mem smt__x (FunDom smt__f))
                (= (FunApp smt__f smt__x)
                  (FunApp smt__g smt__x))))) (= smt__f smt__g))
        :pattern ((FunIsafcn smt__f)
                   (FunIsafcn smt__g)))) :named |FunExt|))

; omitted fact (second-order)

;; Axiom: FunSetIntro
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (and (FunIsafcn smt__f)
            (= (FunDom smt__f) smt__a)
            (forall ((smt__x Idv))
              (=> (Mem smt__x smt__a)
                (Mem (FunApp smt__f smt__x)
                  smt__b))))
          (Mem smt__f (FunSet smt__a smt__b)))
        :pattern ((Mem smt__f
                    (FunSet smt__a smt__b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=> (Mem smt__f (FunSet smt__a smt__b))
          (and (FunIsafcn smt__f)
            (= (FunDom smt__f) smt__a)))
        :pattern ((Mem smt__f
                    (FunSet smt__a smt__b)))))
    :named |FunSetElim1|))

;; Axiom: FunSetElim2
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv) (smt__x Idv))
      (!
        (=>
          (and
            (Mem smt__f (FunSet smt__a smt__b))
            (Mem smt__x smt__a))
          (Mem (FunApp smt__f smt__x) smt__b))
        :pattern ((Mem smt__f
                    (FunSet smt__a smt__b))
                   (Mem smt__x smt__a))
        :pattern ((Mem smt__f
                    (FunSet smt__a smt__b))
                   (FunApp smt__f smt__x))))
    :named |FunSetElim2|))

; omitted fact (second-order)

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: DisjointTrigger
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (SetExtTrigger (Cap smt__x smt__y)
          SetEnum___0)
        :pattern ((Cap smt__x smt__y))))
    :named |DisjointTrigger|))

;; Axiom: CompareSetOfTrigger
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv))
      (! (SetExtTrigger smt__a smt__b)
        :pattern ((IsSetOf smt__a)
                   (IsSetOf smt__b))))
    :named |CompareSetOfTrigger|))

;; Axiom: EnumDefElim 0
(assert
  (!
    (forall ((smt__x Idv))
      (! (not (Mem smt__x SetEnum___0))
        :pattern ((Mem smt__x SetEnum___0))))
    :named |EnumDefElim 0|))

; omitted fact (second-order)

; omitted fact (second-order)

;; Axiom: ExtTrigEqDef Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (! (= (TrigEq___Idv smt__x smt__y) (= smt__x smt__y))
        :pattern ((TrigEq___Idv smt__x smt__y))))
    :named |ExtTrigEqDef Idv|))

; omitted fact (second-order)

; hidden fact

; hidden fact

; omitted declaration of 'CST_EnabledWrapper_' (second-order)

; omitted declaration of 'CST_CdotWrapper_' (second-order)

(declare-fun CST___Client___ () Idv)

(declare-fun CST___Resource___ () Idv)

(declare-fun VAR___unsat___ () Idv)

(declare-fun VAR___unsat______prime () Idv)

(declare-fun VAR___alloc___ () Idv)

(declare-fun VAR___alloc______prime () Idv)

(declare-fun STATE___Init___ () Idv)

(declare-fun ACTION___Request___ (Idv Idv) Idv)

(declare-fun ACTION___Allocate___ (Idv Idv) Idv)

(declare-fun ACTION___Return___ (Idv Idv) Idv)

(declare-fun ACTION___Next___ () Idv)

(declare-fun STATE___vars___ () Idv)

(declare-fun TEMPORAL___SimpleAllocator___ () Idv)

(declare-fun STATE___Mutex___ () Idv)

(declare-fun TEMPORAL___ClientsWillReturn___ () Idv)

(declare-fun TEMPORAL___ClientsWillObtain___ () Idv)

(declare-fun TEMPORAL___InfOftenSatisfied___ () Idv)

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun CST___clt___ () Idv)

(assert (Mem CST___clt___ CST___Client___))

(declare-fun CST___S___ () Idv)

(assert
  (Mem CST___S___
    (Subset CST___Resource___)))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun CST___c1___ () Idv)

(assert (Mem CST___c1___ CST___Client___))

(declare-fun CST___c2___ () Idv)

(assert (Mem CST___c2___ CST___Client___))

(declare-fun CST___r___ () Idv)

(assert (Mem CST___r___ CST___Resource___))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

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
  (and
    (and
      (Mem VAR___unsat___
        (FunSet CST___Client___
          (Subset CST___Resource___)))
      (Mem VAR___alloc___
        (FunSet CST___Client___
          (Subset CST___Resource___))))
    (= STATE___Mutex___ Tt___Idv)
    (=
      (ACTION___Allocate___ CST___clt___ CST___S___)
      Tt___Idv)))

(assert
  (Mem CST___r___
    (Cap
      (FunApp VAR___alloc______prime
        CST___c1___)
      (FunApp VAR___alloc______prime
        CST___c2___))))

(assert
  (TrigEq___Idv
    (FunApp VAR___alloc______prime
      CST___c2___)
    (FunApp VAR___alloc___ CST___c2___)))

(assert
  (not
    (TrigEq___Idv CST___c1___ CST___c2___)))

(declare-fun SetOf___1___flatnd___1 (Idv) Idv)

;; Axiom: SetOfIntro 1 _SetOf_1_flatnd_1
(assert
  (!
    (forall ((smt__a1 Idv) (smt__y1 Idv))
      (!
        (=> (and (Mem smt__y1 smt__a1))
          (Mem
            (FunApp VAR___alloc___ smt__y1)
            (SetOf___1___flatnd___1 smt__a1)))
        :pattern ((FunApp VAR___alloc___ smt__y1)
                   (SetOf___1___flatnd___1 smt__a1))
        :pattern ((SetOf___1___flatnd___1 smt__a1)
                   (Mem smt__y1 smt__a1))))
    :named |SetOfIntro 1 _SetOf_1_flatnd_1|))

;; Axiom: SetOfElim 1 _SetOf_1_flatnd_1
(assert
  (!
    (forall ((smt__a1 Idv) (smt__x Idv))
      (!
        (=>
          (Mem smt__x
            (SetOf___1___flatnd___1 smt__a1))
          (exists ((smt__y1 Idv))
            (and (Mem smt__y1 smt__a1)
              (= smt__x
                (FunApp VAR___alloc___ smt__y1)))))
        :pattern ((Mem smt__x
                    (SetOf___1___flatnd___1 smt__a1)))))
    :named |SetOfElim 1 _SetOf_1_flatnd_1|))

;; Axiom: AssertIsSetOf 1 _SetOf_1_flatnd_1
(assert
  (!
    (forall ((smt__a Idv))
      (!
        (IsSetOf (SetOf___1___flatnd___1 smt__a))
        :pattern ((SetOf___1___flatnd___1 smt__a))))
    :named |AssertIsSetOf 1 _SetOf_1_flatnd_1|))

;; Goal
(assert
  (!
    (not
      (not
        (Mem CST___r___
          (SetMinus CST___Resource___
            (Union
              (SetOf___1___flatnd___1 CST___Client___))))))
    :named |Goal|))

(check-sat)
(get-proof)
