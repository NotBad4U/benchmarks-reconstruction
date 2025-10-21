;; Proof obligation:
;;	ASSUME NEW CONSTANT CST_Client_,
;;	       NEW CONSTANT CST_Resource_,
;;	       NEW VARIABLE VAR_unsat_,
;;	       NEW VARIABLE VAR_alloc_,
;;	       ASSUME ACTION_Next_ 
;;	       PROVE  STATE_TypeInvariant_ /\ STATE_Mutex_
;;	              /\ (ACTION_Next_ \/ ?h6fbaa = STATE_vars_) => ?h93432 ,
;;	       ASSUME ?h6fbaa = STATE_vars_ 
;;	       PROVE  STATE_TypeInvariant_ /\ STATE_Mutex_
;;	              /\ (ACTION_Next_ \/ ?h6fbaa = STATE_vars_) => ?h93432 
;;	PROVE  STATE_TypeInvariant_ /\ STATE_Mutex_
;;	       /\ (ACTION_Next_ \/ ?h6fbaa = STATE_vars_) => ?h93432
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #109
;; Generated from file "/home/rosalied/Documents/work/thesis-eval/tla_specs/tlaps_examples/Allocator.tla", line 284, characters 11-12

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun Anon___OPAQUE___h6fbaa () Idv)

(declare-fun Anon___OPAQUE___h93432 () Idv)

(declare-fun TrigEq___Idv (Idv Idv) Bool)

(declare-fun Tt___Idv () Idv)

;; Axiom: ExtTrigEqDef Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (! (= (TrigEq___Idv smt__x smt__y) (= smt__x smt__y))
        :pattern ((TrigEq___Idv smt__x smt__y))))
    :named |ExtTrigEqDef Idv|))

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

; hidden fact

; hidden fact

; hidden fact

(assert
  (=> (= ACTION___Next___ Tt___Idv)
    (=>
      (and
        (and (= STATE___TypeInvariant___ Tt___Idv)
          (= STATE___Mutex___ Tt___Idv))
        (or (= ACTION___Next___ Tt___Idv)
          (TrigEq___Idv Anon___OPAQUE___h6fbaa
            STATE___vars___)))
      (= Anon___OPAQUE___h93432 Tt___Idv))))

(assert
  (=>
    (TrigEq___Idv Anon___OPAQUE___h6fbaa
      STATE___vars___)
    (=>
      (and
        (and (= STATE___TypeInvariant___ Tt___Idv)
          (= STATE___Mutex___ Tt___Idv))
        (or (= ACTION___Next___ Tt___Idv)
          (TrigEq___Idv Anon___OPAQUE___h6fbaa
            STATE___vars___)))
      (= Anon___OPAQUE___h93432 Tt___Idv))))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and (= STATE___TypeInvariant___ Tt___Idv)
            (= STATE___Mutex___ Tt___Idv))
          (or (= ACTION___Next___ Tt___Idv)
            (TrigEq___Idv Anon___OPAQUE___h6fbaa
              STATE___vars___)))
        (= Anon___OPAQUE___h93432 Tt___Idv)))
    :named |Goal|))

(check-sat)
(get-proof)
