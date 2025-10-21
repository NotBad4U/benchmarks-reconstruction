;; Proof obligation:
;;	ASSUME NEW CONSTANT CST_Client_,
;;	       NEW CONSTANT CST_Resource_,
;;	       NEW VARIABLE VAR_unsat_,
;;	       NEW VARIABLE VAR_alloc_
;;	PROVE  (/\ VAR_unsat_ = [CST_c_ \in CST_Client_ |-> {}]
;;	        /\ VAR_alloc_ = [CST_c_ \in CST_Client_ |-> {}])
;;	       => (\A CST_c1_, CST_c2_ \in CST_Client_ :
;;	              \A CST_r_ \in CST_Resource_ :
;;	                 CST_r_
;;	                 \in VAR_alloc_[CST_c1_]
;;	                     \cap VAR_alloc_[CST_c2_]
;;	                 => CST_c1_ = CST_c2_)
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #20
;; Generated from file "/home/rosalied/Documents/work/thesis-eval/tla_specs/tlaps_examples/Allocator.tla", line 173, characters 1-2

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun Cap (Idv Idv) Idv)

(declare-fun FunApp (Idv Idv) Idv)

(declare-fun FunDom (Idv) Idv)

; omitted declaration of '_FunFcn' (second-order)

(declare-fun FunIsafcn (Idv) Bool)

(declare-fun Mem (Idv Idv) Bool)

(declare-fun SetEnum___0 () Idv)

(declare-fun SetExtTrigger (Idv Idv) Bool)

(declare-fun TrigEq___Idv (Idv Idv) Bool)

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

(declare-fun ACTION___Request___ (Idv Idv) Idv)

(declare-fun ACTION___Allocate___ (Idv Idv) Idv)

(declare-fun ACTION___Return___ (Idv Idv) Idv)

(declare-fun ACTION___Next___ () Idv)

(declare-fun STATE___vars___ () Idv)

(declare-fun TEMPORAL___SimpleAllocator___ () Idv)

(declare-fun TEMPORAL___ClientsWillReturn___ () Idv)

(declare-fun TEMPORAL___ClientsWillObtain___ () Idv)

(declare-fun TEMPORAL___InfOftenSatisfied___ () Idv)

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun FunFcn___flatnd___1 (Idv) Idv)

;; Axiom: FunConstrIsafcn _FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv))
      (! (FunIsafcn (FunFcn___flatnd___1 smt__a))
        :pattern ((FunFcn___flatnd___1 smt__a))))
    :named |FunConstrIsafcn _FunFcn_flatnd_1|))

;; Axiom: FunDomDef _FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv))
      (!
        (= (FunDom (FunFcn___flatnd___1 smt__a))
          smt__a) :pattern ((FunFcn___flatnd___1 smt__a))))
    :named |FunDomDef _FunFcn_flatnd_1|))

;; Axiom: FunAppDef _FunFcn_flatnd_1
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=> (Mem smt__x smt__a)
          (=
            (FunApp (FunFcn___flatnd___1 smt__a)
              smt__x) SetEnum___0))
        :pattern ((FunApp
                    (FunFcn___flatnd___1 smt__a) smt__x))
        :pattern ((Mem smt__x smt__a)
                   (FunFcn___flatnd___1 smt__a))))
    :named |FunAppDef _FunFcn_flatnd_1|))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (TrigEq___Idv VAR___unsat___
            (FunFcn___flatnd___1 CST___Client___))
          (TrigEq___Idv VAR___alloc___
            (FunFcn___flatnd___1 CST___Client___)))
        (forall ((CST___c1___ Idv) (CST___c2___ Idv))
          (=>
            (and
              (Mem CST___c1___
                CST___Client___)
              (Mem CST___c2___
                CST___Client___))
            (forall ((CST___r___ Idv))
              (=>
                (Mem CST___r___
                  CST___Resource___)
                (=>
                  (Mem CST___r___
                    (Cap
                      (FunApp VAR___alloc___
                        CST___c1___)
                      (FunApp VAR___alloc___
                        CST___c2___)))
                  (TrigEq___Idv CST___c1___
                    CST___c2___)))))))) :named |Goal|))

(check-sat)
(get-proof)
