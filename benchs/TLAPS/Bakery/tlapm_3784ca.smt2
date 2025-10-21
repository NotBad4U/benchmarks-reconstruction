;; Proof obligation:
;;	ASSUME NEW CONSTANT CST_N_,
;;	       NEW VARIABLE VAR_num_,
;;	       NEW VARIABLE VAR_flag_,
;;	       NEW VARIABLE VAR_pc_,
;;	       NEW VARIABLE VAR_unread_,
;;	       NEW VARIABLE VAR_max_,
;;	       NEW VARIABLE VAR_nxt_,
;;	       CST_N_ \in Nat ,
;;	       ASSUME STATE_TypeOK_
;;	              /\ (\A CST_i_ \in 1..CST_N_ :
;;	                     STATE_IInv_(CST_i_)) ,
;;	              ACTION_Next_ \/ ?h6fbaa = STATE_vars_ 
;;	       PROVE  ?h15bf9
;;	              /\ (\A CST_i_ \in 1..CST_N_ : ?h222f4(CST_i_)) 
;;	PROVE  STATE_TypeOK_
;;	       /\ (\A CST_i_ \in 1..CST_N_ : STATE_IInv_(CST_i_))
;;	       /\ (ACTION_Next_ \/ ?h6fbaa = STATE_vars_)
;;	       => ?h15bf9
;;	          /\ (\A CST_i_ \in 1..CST_N_ : ?h222f4(CST_i_))
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #18
;; Generated from file "./examples/Bakery.tla", line 316, characters 5-11

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun Anon_OPAQUE_h15bf9 () Idv)

(declare-fun Anon_OPAQUE_h6fbaa () Idv)

(declare-fun Anon_h222f4 (Idv) Idv)

(declare-fun Cast_Int (Int) Idv)

(declare-fun IntLteq (Idv Idv) Bool)

(declare-fun IntRange (Idv Idv) Idv)

(declare-fun IntSet () Idv)

(declare-fun Mem (Idv Idv) Bool)

(declare-fun NatSet () Idv)

(declare-fun Proj_Int (Idv) Int)

(declare-fun SetExtTrigger (Idv Idv) Bool)

(declare-fun TrigEq_Idv (Idv
  Idv) Bool)

(declare-fun Tt_Idv () Idv)

;; Axiom: SetExt
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (=>
          (forall ((smt__z Idv))
            (= (Mem smt__z smt__x)
              (Mem smt__z smt__y)))
          (= smt__x smt__y))
        :pattern ((SetExtTrigger smt__x smt__y))))
    :named |SetExt|))

;; Axiom: NatSetDef
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=
          (Mem smt__x
            NatSet)
          (and
            (Mem smt__x
              IntSet)
            (IntLteq
              (Cast_Int 0) smt__x)))
        :pattern ((Mem smt__x
                    NatSet))))
    :named |NatSetDef|))

;; Axiom: IntRangeDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (=
          (Mem smt__x
            (IntRange smt__a smt__b))
          (and
            (Mem smt__x
              IntSet)
            (IntLteq smt__a smt__x)
            (IntLteq smt__x smt__b)))
        :pattern ((Mem smt__x
                    (IntRange smt__a smt__b)))))
    :named |IntRangeDef|))

;; Axiom: CastInjAlt Int
(assert
  (!
    (forall ((smt__x Int))
      (!
        (= smt__x
          (Proj_Int
            (Cast_Int smt__x)))
        :pattern ((Cast_Int smt__x))))
    :named |CastInjAlt Int|))

;; Axiom: TypeGuardIntro Int
(assert
  (!
    (forall ((smt__z Int))
      (!
        (Mem
          (Cast_Int smt__z)
          IntSet)
        :pattern ((Cast_Int smt__z))))
    :named |TypeGuardIntro Int|))

;; Axiom: TypeGuardElim Int
(assert
  (!
    (forall ((smt__x Idv))
      (!
        (=>
          (Mem smt__x
            IntSet)
          (= smt__x
            (Cast_Int
              (Proj_Int smt__x))))
        :pattern ((Mem smt__x
                    IntSet))))
    :named |TypeGuardElim Int|))

;; Axiom: Typing TIntLteq
(assert
  (!
    (forall ((smt__x1 Int) (smt__x2 Int))
      (!
        (=
          (IntLteq
            (Cast_Int smt__x1)
            (Cast_Int smt__x2))
          (<= smt__x1 smt__x2))
        :pattern ((IntLteq
                    (Cast_Int smt__x1)
                    (Cast_Int smt__x2)))))
    :named |Typing TIntLteq|))

;; Axiom: ExtTrigEqDef Idv
(assert
  (!
    (forall ((smt__x Idv) (smt__y Idv))
      (!
        (= (TrigEq_Idv smt__x smt__y)
          (= smt__x smt__y))
        :pattern ((TrigEq_Idv 
                    smt__x smt__y)))) :named |ExtTrigEqDef Idv|))

; hidden fact

; hidden fact

; omitted declaration of 'CST_EnabledWrapper_' (second-order)

; omitted declaration of 'CST_CdotWrapper_' (second-order)

(declare-fun CST_N_ () Idv)

; hidden fact

(declare-fun VAR_num_ () Idv)

(declare-fun VAR_num_prime () Idv)

(declare-fun VAR_flag_ () Idv)

(declare-fun VAR_flag_prime () Idv)

(declare-fun VAR_pc_ () Idv)

(declare-fun VAR_pc_prime () Idv)

(declare-fun STATE_LL_ (Idv Idv) Idv)

(declare-fun VAR_unread_ () Idv)

(declare-fun VAR_unread_prime () Idv)

(declare-fun VAR_max_ () Idv)

(declare-fun VAR_max_prime () Idv)

(declare-fun VAR_nxt_ () Idv)

(declare-fun VAR_nxt_prime () Idv)

(declare-fun STATE_vars_ () Idv)

(declare-fun STATE_Init_ () Idv)

(declare-fun ACTION_p1_ (Idv) Idv)

(declare-fun ACTION_p2_ (Idv) Idv)

(declare-fun ACTION_p3_ (Idv) Idv)

(declare-fun ACTION_p4_ (Idv) Idv)

(declare-fun ACTION_p5_ (Idv) Idv)

(declare-fun ACTION_p6_ (Idv) Idv)

(declare-fun ACTION_cs_ (Idv) Idv)

(declare-fun ACTION_p7_ (Idv) Idv)

(declare-fun ACTION_p_ (Idv) Idv)

(declare-fun ACTION_Next_ () Idv)

(declare-fun TEMPORAL_Spec_ () Idv)

(declare-fun STATE_MutualExclusion_ () Idv)

(declare-fun STATE_TypeOK_ () Idv)

(declare-fun STATE_After_ (Idv Idv) Idv)

(declare-fun STATE_IInv_ (Idv) Idv)

(assert
  (Mem CST_N_
    NatSet))

; hidden fact

; hidden fact

; hidden fact

(assert
  (=>
    (and
      (= STATE_TypeOK_
        Tt_Idv)
      (forall ((CST_i_ Idv))
        (=>
          (Mem
            CST_i_
            (IntRange
              (Cast_Int 1)
              CST_N_))
          (=
            (STATE_IInv_
              CST_i_)
            Tt_Idv))))
    (=>
      (or
        (= ACTION_Next_
          Tt_Idv)
        (TrigEq_Idv
          Anon_OPAQUE_h6fbaa
          STATE_vars_))
      (and
        (=
          Anon_OPAQUE_h15bf9
          Tt_Idv)
        (forall ((CST_i_ Idv))
          (=>
            (Mem
              CST_i_
              (IntRange
                (Cast_Int 1)
                CST_N_))
            (=
              (Anon_h222f4
                CST_i_)
              Tt_Idv)))))))

;; Goal
(assert
  (!
    (not
      (=>
        (and
          (and
            (= STATE_TypeOK_
              Tt_Idv)
            (forall ((CST_i_ Idv))
              (=>
                (Mem
                  CST_i_
                  (IntRange
                    (Cast_Int 1)
                    CST_N_))
                (=
                  (STATE_IInv_
                    CST_i_)
                  Tt_Idv))))
          (or
            (= ACTION_Next_
              Tt_Idv)
            (TrigEq_Idv
              Anon_OPAQUE_h6fbaa
              STATE_vars_)))
        (and
          (=
            Anon_OPAQUE_h15bf9
            Tt_Idv)
          (forall ((CST_i_ Idv))
            (=>
              (Mem
                CST_i_
                (IntRange
                  (Cast_Int 1)
                  CST_N_))
              (=
                (Anon_h222f4
                  CST_i_)
                Tt_Idv))))))
    :named |Goal|))

(check-sat)
(exit)
