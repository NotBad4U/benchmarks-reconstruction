;; Proof obligation:
;;	ASSUME NEW CONSTANT CST_Client_,
;;	       NEW CONSTANT CST_Resource_,
;;	       NEW VARIABLE VAR_unsat_,
;;	       NEW VARIABLE VAR_alloc_,
;;	       NEW CONSTANT CST_c_ \in CST_Client_,
;;	       NEW CONSTANT CST_S_ \in SUBSET CST_Resource_
;;	PROVE  (/\ VAR_unsat_
;;	           \in [CST_Client_ -> SUBSET CST_Resource_]
;;	        /\ VAR_alloc_
;;	           \in [CST_Client_ -> SUBSET CST_Resource_])
;;	       /\ (/\ CST_S_ # {}
;;	              /\ CST_S_ \subseteq VAR_alloc_[CST_c_]
;;	           /\ ?VAR_alloc_#prime
;;	              = [VAR_alloc_ EXCEPT
;;	                   ![CST_c_] = VAR_alloc_[CST_c_]
;;	                                    \ CST_S_]
;;	           /\ ?VAR_unsat_#prime = VAR_unsat_)
;;	       => (/\ ?VAR_unsat_#prime
;;	              \in [CST_Client_ -> SUBSET CST_Resource_]
;;	           /\ ?VAR_alloc_#prime
;;	              \in [CST_Client_ -> SUBSET CST_Resource_])
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #4
;; Generated from file "/home/rosalied/Documents/work/thesis-eval/tla_specs/tlaps_examples/Allocator.tla", line 146, characters 1-2

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun FunApp (Idv Idv) Idv)

(declare-fun FunDom (Idv) Idv)

(declare-fun FunExcept (Idv Idv Idv) Idv)

; omitted declaration of '_FunFcn' (second-order)

(declare-fun FunIsafcn (Idv) Bool)

(declare-fun FunSet (Idv Idv) Idv)

(declare-fun Mem (Idv Idv) Bool)

(declare-fun SetEnum___0 () Idv)

(declare-fun SetExtTrigger (Idv Idv) Bool)

(declare-fun SetMinus (Idv Idv) Idv)

(declare-fun Subset (Idv) Idv)

(declare-fun SubsetEq (Idv Idv) Bool)

(declare-fun TrigEq___Idv (Idv Idv) Bool)

(declare-fun TrigEq___Setdollarsign___Idvdollarsign___ (Idv
  Idv) Bool)

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

;; Axiom: FunExceptIsafcn
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (FunIsafcn
          (FunExcept smt__f smt__x smt__y))
        :pattern ((FunExcept smt__f smt__x smt__y))))
    :named |FunExceptIsafcn|))

;; Axiom: FunExceptDomDef
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (=
          (FunDom
            (FunExcept smt__f smt__x smt__y))
          (FunDom smt__f))
        :pattern ((FunExcept smt__f smt__x smt__y))))
    :named |FunExceptDomDef|))

;; Axiom: FunExceptAppDef1
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv))
      (!
        (=> (Mem smt__x (FunDom smt__f))
          (=
            (FunApp
              (FunExcept smt__f smt__x smt__y) smt__x) 
            smt__y))
        :pattern ((FunExcept smt__f smt__x smt__y))))
    :named |FunExceptAppDef1|))

;; Axiom: FunExceptAppDef2
(assert
  (!
    (forall ((smt__f Idv) (smt__x Idv) (smt__y Idv) (smt__z Idv))
      (!
        (=> (Mem smt__z (FunDom smt__f))
          (and
            (=> (= smt__z smt__x)
              (=
                (FunApp
                  (FunExcept smt__f smt__x smt__y) smt__z)
                smt__y))
            (=> (distinct smt__z smt__x)
              (=
                (FunApp
                  (FunExcept smt__f smt__x smt__y) smt__z)
                (FunApp smt__f smt__z)))))
        :pattern ((FunApp
                    (FunExcept smt__f smt__x smt__y) smt__z))
        :pattern ((FunExcept smt__f smt__x smt__y)
                   (FunApp smt__f smt__z))))
    :named |FunExceptAppDef2|))

;; Axiom: EnumDefElim 0
(assert
  (!
    (forall ((smt__x Idv))
      (! (not (Mem smt__x SetEnum___0))
        :pattern ((Mem smt__x SetEnum___0))))
    :named |EnumDefElim 0|))

;; Axiom: ExtTrigEqDef Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (! (= (TrigEq___Idv smt__x smt__y) (= smt__x smt__y))
        :pattern ((TrigEq___Idv smt__x smt__y))))
    :named |ExtTrigEqDef Idv|))

;; Axiom: ExtTrigEqDef Set$Idv$
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=
          (TrigEq___Setdollarsign___Idvdollarsign___ smt__x
            smt__y) (= smt__x smt__y))
        :pattern ((TrigEq___Setdollarsign___Idvdollarsign___
                    smt__x smt__y)))) :named |ExtTrigEqDef Set$Idv$|))

;; Axiom: ExtTrigEqTrigger Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (! (SetExtTrigger smt__x smt__y)
        :pattern ((TrigEq___Setdollarsign___Idvdollarsign___
                    smt__x smt__y)))) :named |ExtTrigEqTrigger Idv|))

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

(declare-fun STATE___available___ () Idv)

(declare-fun STATE___Init___ () Idv)

(declare-fun ACTION___Request___ (Idv Idv) Idv)

(declare-fun ACTION___Allocate___ (Idv Idv) Idv)

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

(declare-fun CST___c___ () Idv)

(assert (Mem CST___c___ CST___Client___))

(declare-fun CST___S___ () Idv)

(assert
  (Mem CST___S___
    (Subset CST___Resource___)))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and
            (Mem VAR___unsat___
              (FunSet CST___Client___
                (Subset CST___Resource___)))
            (Mem VAR___alloc___
              (FunSet CST___Client___
                (Subset CST___Resource___))))
          (and
            (and
              (not
                (TrigEq___Setdollarsign___Idvdollarsign___
                  CST___S___ SetEnum___0))
              (SubsetEq CST___S___
                (FunApp VAR___alloc___
                  CST___c___)))
            (TrigEq___Idv VAR___alloc______prime
              (FunExcept VAR___alloc___
                CST___c___
                (SetMinus
                  (FunApp VAR___alloc___
                    CST___c___) CST___S___)))
            (TrigEq___Idv VAR___unsat______prime
              VAR___unsat___)))
        (and
          (Mem VAR___unsat______prime
            (FunSet CST___Client___
              (Subset CST___Resource___)))
          (Mem VAR___alloc______prime
            (FunSet CST___Client___
              (Subset CST___Resource___))))))
    :named |Goal|))

(check-sat)
(get-proof)
