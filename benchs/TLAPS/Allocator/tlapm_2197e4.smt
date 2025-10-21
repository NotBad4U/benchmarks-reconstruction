;; Proof obligation:
;;	ASSUME NEW CONSTANT CST_Client_,
;;	       NEW CONSTANT CST_Resource_,
;;	       NEW VARIABLE VAR_unsat_,
;;	       NEW VARIABLE VAR_alloc_,
;;	       NEW CONSTANT CST_clt_ \in CST_Client_,
;;	       NEW CONSTANT CST_S_ \in SUBSET CST_Resource_,
;;	       ASSUME STATE_TypeInvariant_ ,
;;	              STATE_Mutex_ ,
;;	              ACTION_Allocate_(CST_clt_, CST_S_) 
;;	       PROVE  ?h93432 
;;	PROVE  STATE_TypeInvariant_ /\ STATE_Mutex_
;;	       /\ ACTION_Allocate_(CST_clt_, CST_S_) => ?h93432
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #35
;; Generated from file "/home/rosalied/Documents/work/thesis-eval/tla_specs/tlaps_examples/Allocator.tla", line 214, characters 3-9

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun Anon___OPAQUE___h93432 () Idv)

(declare-fun Mem (Idv Idv) Bool)

(declare-fun SetExtTrigger (Idv Idv) Bool)

(declare-fun Subset (Idv) Idv)

(declare-fun SubsetEq (Idv Idv) Bool)

(declare-fun Tt___Idv () Idv)

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

(declare-fun STATE___TypeInvariant___ () Idv)

(declare-fun STATE___available___ () Idv)

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

(assert
  (=> (= STATE___TypeInvariant___ Tt___Idv)
    (=> (= STATE___Mutex___ Tt___Idv)
      (=>
        (=
          (ACTION___Allocate___ CST___clt___
            CST___S___) Tt___Idv)
        (= Anon___OPAQUE___h93432 Tt___Idv)))))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and (= STATE___TypeInvariant___ Tt___Idv)
            (= STATE___Mutex___ Tt___Idv))
          (=
            (ACTION___Allocate___ CST___clt___
              CST___S___) Tt___Idv))
        (= Anon___OPAQUE___h93432 Tt___Idv)))
    :named |Goal|))

(check-sat)
(get-proof)
