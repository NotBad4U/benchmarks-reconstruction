;; Proof obligation:
;;	ASSUME NEW CONSTANT CONSTANT_N_,
;;	       NEW VARIABLE VARIABLE_num_,
;;	       NEW VARIABLE VARIABLE_flag_,
;;	       NEW VARIABLE VARIABLE_pc_,
;;	       NEW VARIABLE VARIABLE_unread_,
;;	       NEW VARIABLE VARIABLE_max_,
;;	       NEW VARIABLE VARIABLE_nxt_,
;;	       CONSTANT_N_ \in Nat ,
;;	       STATE_TypeOK_
;;	       /\ (\A CONSTANT_i_ \in 1..CONSTANT_N_ : STATE_IInv_(CONSTANT_i_)) ,
;;	       ACTION_Next_ \/ ?h6fbaa = STATE_vars_ ,
;;	       NEW CONSTANT CONSTANT_self_ \in 1..CONSTANT_N_,
;;	       ?h15bf9 ,
;;	       ASSUME NEW CONSTANT CONSTANT_i_ \in 1..CONSTANT_N_
;;	       PROVE  ?h222f4(CONSTANT_i_) 
;;	PROVE  ?h15bf9 /\ (\A CONSTANT_i_ \in 1..CONSTANT_N_ : ?h222f4(CONSTANT_i_))
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #33
;; Generated from file "./examples/Bakery.tla", line 340, characters 15-16

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9 () Idv)

(declare-fun smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h6fbaa () Idv)

(declare-fun smt__TLAunderscore_underscore_Anonunderscore_h222f4 (Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_Castunderscore_Int (Int) Idv)

(declare-fun smt__TLAunderscore_underscore_IntLteq (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_IntRange (Idv Idv) Idv)

(declare-fun smt__TLAunderscore_underscore_IntSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Mem (Idv Idv) Bool)

(declare-fun smt__TLAunderscore_underscore_NatSet () Idv)

(declare-fun smt__TLAunderscore_underscore_Projunderscore_Int (Idv) Int)

(declare-fun smt__TLAunderscore_underscore_SetExtTrigger (Idv Idv) Bool)

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

; hidden fact

; hidden fact

; omitted declaration of 'CONSTANT_EnabledWrapper_' (second-order)

; omitted declaration of 'CONSTANT_CdotWrapper_' (second-order)

(declare-fun smt__CONSTANTunderscore_Nunderscore_ () Idv)

; hidden fact

(declare-fun smt__VARIABLEunderscore_numunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_numunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_flagunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_flagunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_pcunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_pcunderscore_underscore_prime () Idv)

(declare-fun smt__STATEunderscore_LLunderscore_ (Idv Idv) Idv)

(declare-fun smt__VARIABLEunderscore_unreadunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_unreadunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_maxunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_maxunderscore_underscore_prime () Idv)

(declare-fun smt__VARIABLEunderscore_nxtunderscore_ () Idv)

(declare-fun smt__VARIABLEunderscore_nxtunderscore_underscore_prime () Idv)

(declare-fun smt__STATEunderscore_varsunderscore_ () Idv)

(declare-fun smt__STATEunderscore_Initunderscore_ () Idv)

(declare-fun smt__ACTIONunderscore_p1underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_p2underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_p3underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_p4underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_p5underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_p6underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_csunderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_p7underscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_punderscore_ (Idv) Idv)

(declare-fun smt__ACTIONunderscore_Nextunderscore_ () Idv)

(declare-fun smt__TEMPORALunderscore_Specunderscore_ () Idv)

(declare-fun smt__STATEunderscore_MutualExclusionunderscore_ () Idv)

(declare-fun smt__STATEunderscore_TypeOKunderscore_ () Idv)

(declare-fun smt__STATEunderscore_Afterunderscore_ (Idv Idv) Idv)

(declare-fun smt__STATEunderscore_IInvunderscore_ (Idv) Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_Nunderscore_
    smt__TLAunderscore_underscore_NatSet))

; hidden fact

; hidden fact

; hidden fact

(assert
  (and
    (= smt__STATEunderscore_TypeOKunderscore_
      smt__TLAunderscore_underscore_Ttunderscore_Idv)
    (forall ((smt__CONSTANTunderscore_iunderscore_ Idv))
      (=>
        (smt__TLAunderscore_underscore_Mem
          smt__CONSTANTunderscore_iunderscore_
          (smt__TLAunderscore_underscore_IntRange
            (smt__TLAunderscore_underscore_Castunderscore_Int 1)
            smt__CONSTANTunderscore_Nunderscore_))
        (=
          (smt__STATEunderscore_IInvunderscore_
            smt__CONSTANTunderscore_iunderscore_)
          smt__TLAunderscore_underscore_Ttunderscore_Idv)))))

(assert
  (or
    (= smt__ACTIONunderscore_Nextunderscore_
      smt__TLAunderscore_underscore_Ttunderscore_Idv)
    (smt__TLAunderscore_underscore_TrigEqunderscore_Idv
      smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h6fbaa
      smt__STATEunderscore_varsunderscore_)))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(declare-fun smt__CONSTANTunderscore_selfunderscore_ () Idv)

(assert
  (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_selfunderscore_
    (smt__TLAunderscore_underscore_IntRange
      (smt__TLAunderscore_underscore_Castunderscore_Int 1)
      smt__CONSTANTunderscore_Nunderscore_)))

; hidden fact

; hidden fact

; hidden fact

; hidden fact

; hidden fact

(assert
  (= smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9
    smt__TLAunderscore_underscore_Ttunderscore_Idv))

(assert
  (forall ((smt__CONSTANTunderscore_iunderscore_ Idv))
    (=>
      (smt__TLAunderscore_underscore_Mem smt__CONSTANTunderscore_iunderscore_
        (smt__TLAunderscore_underscore_IntRange
          (smt__TLAunderscore_underscore_Castunderscore_Int 1)
          smt__CONSTANTunderscore_Nunderscore_))
      (=
        (smt__TLAunderscore_underscore_Anonunderscore_h222f4
          smt__CONSTANTunderscore_iunderscore_)
        smt__TLAunderscore_underscore_Ttunderscore_Idv))))

;; Goal
(assert
  (!
    (not
      (and
        (=
          smt__TLAunderscore_underscore_Anonunderscore_OPAQUEunderscore_h15bf9
          smt__TLAunderscore_underscore_Ttunderscore_Idv)
        (forall ((smt__CONSTANTunderscore_iunderscore_ Idv))
          (=>
            (smt__TLAunderscore_underscore_Mem
              smt__CONSTANTunderscore_iunderscore_
              (smt__TLAunderscore_underscore_IntRange
                (smt__TLAunderscore_underscore_Castunderscore_Int 1)
                smt__CONSTANTunderscore_Nunderscore_))
            (=
              (smt__TLAunderscore_underscore_Anonunderscore_h222f4
                smt__CONSTANTunderscore_iunderscore_)
              smt__TLAunderscore_underscore_Ttunderscore_Idv)))))
    :named |Goal|))

(check-sat)
(exit)
