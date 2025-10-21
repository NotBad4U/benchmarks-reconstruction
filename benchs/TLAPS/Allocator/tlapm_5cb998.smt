;; Proof obligation:
;;	ASSUME NEW CONSTANT CST_Client_,
;;	       NEW CONSTANT CST_Resource_,
;;	       NEW VARIABLE VAR_unsat_,
;;	       NEW VARIABLE VAR_alloc_,
;;	       NEW CONSTANT CST_c_ \in CST_Client_,
;;	       NEW CONSTANT CST_S_ \in SUBSET CST_Resource_,
;;	       \/ ACTION_Request_(CST_c_, CST_S_)
;;	       \/ ACTION_Allocate_(CST_c_, CST_S_)
;;	       \/ ACTION_Return_(CST_c_, CST_S_) ,
;;	       /\ STATE_TypeInvariant_
;;	       /\ ACTION_Next_ ,
;;	       ASSUME NEW CONSTANT CST_c__1 \in CST_Client_,
;;	              NEW CONSTANT CST_S__1 \in SUBSET CST_Resource_
;;	       PROVE  STATE_TypeInvariant_
;;	              /\ ACTION_Request_(CST_c__1, CST_S__1) => ?h12c0a ,
;;	       ASSUME NEW CONSTANT CST_c__1 \in CST_Client_,
;;	              NEW CONSTANT CST_S__1 \in SUBSET CST_Resource_
;;	       PROVE  STATE_TypeInvariant_
;;	              /\ ACTION_Allocate_(CST_c__1, CST_S__1) => ?h12c0a ,
;;	       ASSUME NEW CONSTANT CST_c__1 \in CST_Client_,
;;	              NEW CONSTANT CST_S__1 \in SUBSET CST_Resource_
;;	       PROVE  STATE_TypeInvariant_
;;	              /\ ACTION_Return_(CST_c__1, CST_S__1) => ?h12c0a 
;;	PROVE  ?h12c0a
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #8
;; Generated from file "/home/rosalied/Documents/work/thesis-eval/tla_specs/tlaps_examples/Allocator.tla", line 158, characters 5-6

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun Anon___OPAQUE___h12c0a () Idv)

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

(declare-fun CST___c___ () Idv)

(assert (Mem CST___c___ CST___Client___))

(declare-fun CST___S___ () Idv)

(assert
  (Mem CST___S___
    (Subset CST___Resource___)))

(assert
  (or
    (= (ACTION___Request___ CST___c___ CST___S___)
      Tt___Idv)
    (= (ACTION___Allocate___ CST___c___ CST___S___)
      Tt___Idv)
    (= (ACTION___Return___ CST___c___ CST___S___)
      Tt___Idv)))

; hidden fact

; hidden fact

(assert
  (and (= STATE___TypeInvariant___ Tt___Idv)
    (= ACTION___Next___ Tt___Idv)))

(assert
  (forall ((CST___c____1 Idv))
    (=> (Mem CST___c____1 CST___Client___)
      (forall ((CST___S____1 Idv))
        (=>
          (Mem CST___S____1
            (Subset CST___Resource___))
          (=>
            (and (= STATE___TypeInvariant___ Tt___Idv)
              (=
                (ACTION___Request___ CST___c____1
                  CST___S____1) Tt___Idv))
            (= Anon___OPAQUE___h12c0a Tt___Idv)))))))

(assert
  (forall ((CST___c____1 Idv))
    (=> (Mem CST___c____1 CST___Client___)
      (forall ((CST___S____1 Idv))
        (=>
          (Mem CST___S____1
            (Subset CST___Resource___))
          (=>
            (and (= STATE___TypeInvariant___ Tt___Idv)
              (=
                (ACTION___Allocate___ CST___c____1
                  CST___S____1) Tt___Idv))
            (= Anon___OPAQUE___h12c0a Tt___Idv)))))))

(assert
  (forall ((CST___c____1 Idv))
    (=> (Mem CST___c____1 CST___Client___)
      (forall ((CST___S____1 Idv))
        (=>
          (Mem CST___S____1
            (Subset CST___Resource___))
          (=>
            (and (= STATE___TypeInvariant___ Tt___Idv)
              (=
                (ACTION___Return___ CST___c____1
                  CST___S____1) Tt___Idv))
            (= Anon___OPAQUE___h12c0a Tt___Idv)))))))

;; Goal
(assert
  (! (not (= Anon___OPAQUE___h12c0a Tt___Idv))
    :named |Goal|))

(check-sat)
(get-proof)
