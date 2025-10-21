;; Proof obligation:
;;	ASSUME NEW CONSTANT CST_N_,
;;	       NEW VARIABLE VAR_num_,
;;	       NEW VARIABLE VAR_flag_,
;;	       NEW VARIABLE VAR_pc_,
;;	       NEW VARIABLE VAR_unread_,
;;	       NEW VARIABLE VAR_max_,
;;	       NEW VARIABLE VAR_nxt_,
;;	       CST_N_ \in Nat ,
;;	       (/\ VAR_num_ \in [1..CST_N_ -> Nat]
;;	        /\ VAR_flag_ \in [1..CST_N_ -> BOOLEAN]
;;	        /\ VAR_unread_ \in [1..CST_N_ -> SUBSET 1..CST_N_]
;;	        /\ \A CST_i_ \in 1..CST_N_ :
;;	              VAR_pc_[CST_i_] \in {"p2", "p5", "p6"}
;;	              => CST_i_ \notin VAR_unread_[CST_i_]
;;	        /\ VAR_max_ \in [1..CST_N_ -> Nat]
;;	        /\ VAR_nxt_ \in [1..CST_N_ -> 1..CST_N_]
;;	        /\ \A CST_i_ \in 1..CST_N_ :
;;	              VAR_pc_[CST_i_] = "p6"
;;	              => VAR_nxt_[CST_i_] # CST_i_
;;	        /\ VAR_pc_
;;	           \in [1..CST_N_ ->
;;	                  {"p1", "p2", "p3", "p4", "p5", "p6", "cs", "p7"}])
;;	       /\ (\A CST_i_ \in 1..CST_N_ :
;;	              /\ /\ VAR_pc_[CST_i_] \in {"p1", "p2"}
;;	                    => VAR_num_[CST_i_] = 0
;;	                 /\ VAR_num_[CST_i_] = 0
;;	                    => VAR_pc_[CST_i_] \in {"p1", "p2", "p3", "p7"}
;;	              /\ /\ VAR_flag_[CST_i_]
;;	                    => VAR_pc_[CST_i_] \in {"p1", "p2", "p3", "p4"}
;;	                 /\ VAR_pc_[CST_i_] \in {"p2", "p3"}
;;	                    => VAR_flag_[CST_i_]
;;	              /\ VAR_pc_[CST_i_] \in {"p5", "p6"}
;;	                 => (\A CST_j_
;;	                        \in (1..CST_N_ \ VAR_unread_[CST_i_])
;;	                            \ {CST_i_} :
;;	                        /\ VAR_num_[CST_i_] > 0
;;	                        /\ \/ VAR_pc_[CST_j_] = "p1"
;;	                           \/ /\ VAR_pc_[CST_j_] = "p2"
;;	                              /\ \/ CST_i_
;;	                                    \in VAR_unread_[CST_j_]
;;	                                 \/ VAR_max_[CST_j_]
;;	                                    >= VAR_num_[CST_i_]
;;	                           \/ /\ VAR_pc_[CST_j_] = "p3"
;;	                              /\ VAR_max_[CST_j_]
;;	                                 >= VAR_num_[CST_i_]
;;	                           \/ /\ VAR_pc_[CST_j_]
;;	                                 \in {"p4", "p5", "p6"}
;;	                              /\ \/ VAR_num_[CST_i_]
;;	                                    < VAR_num_[CST_j_]
;;	                                 \/ /\ VAR_num_[CST_j_]
;;	                                       = VAR_num_[CST_i_]
;;	                                    /\ CST_i_ =< CST_j_
;;	                              /\ VAR_pc_[CST_j_] \in {"p5", "p6"}
;;	                                 => CST_i_
;;	                                    \in VAR_unread_[CST_j_]
;;	                           \/ VAR_pc_[CST_j_] = "p7")
;;	              /\ (/\ VAR_pc_[CST_i_] = "p6"
;;	                  /\ \/ VAR_pc_[VAR_nxt_[CST_i_]] = "p2"
;;	                        /\ CST_i_
;;	                           \notin VAR_unread_[VAR_nxt_[CST_i_]]
;;	                     \/ VAR_pc_[VAR_nxt_[CST_i_]] = "p3")
;;	                 => VAR_max_[VAR_nxt_[CST_i_]]
;;	                    >= VAR_num_[CST_i_]
;;	              /\ VAR_pc_[CST_i_] = "cs"
;;	                 => (\A CST_j_ \in 1..CST_N_ \ {CST_i_} :
;;	                        /\ VAR_num_[CST_i_] > 0
;;	                        /\ \/ VAR_pc_[CST_j_] = "p1"
;;	                           \/ /\ VAR_pc_[CST_j_] = "p2"
;;	                              /\ \/ CST_i_
;;	                                    \in VAR_unread_[CST_j_]
;;	                                 \/ VAR_max_[CST_j_]
;;	                                    >= VAR_num_[CST_i_]
;;	                           \/ /\ VAR_pc_[CST_j_] = "p3"
;;	                              /\ VAR_max_[CST_j_]
;;	                                 >= VAR_num_[CST_i_]
;;	                           \/ /\ VAR_pc_[CST_j_]
;;	                                 \in {"p4", "p5", "p6"}
;;	                              /\ \/ VAR_num_[CST_i_]
;;	                                    < VAR_num_[CST_j_]
;;	                                 \/ /\ VAR_num_[CST_j_]
;;	                                       = VAR_num_[CST_i_]
;;	                                    /\ CST_i_ =< CST_j_
;;	                              /\ VAR_pc_[CST_j_] \in {"p5", "p6"}
;;	                                 => CST_i_
;;	                                    \in VAR_unread_[CST_j_]
;;	                           \/ VAR_pc_[CST_j_] = "p7")) ,
;;	       ACTION_Next_
;;	       \/ (/\ ?VAR_num_#prime = VAR_num_
;;	           /\ ?VAR_flag_#prime = VAR_flag_
;;	           /\ ?VAR_pc_#prime = VAR_pc_
;;	           /\ ?VAR_unread_#prime = VAR_unread_
;;	           /\ ?VAR_max_#prime = VAR_max_
;;	           /\ ?VAR_nxt_#prime = VAR_nxt_) ,
;;	       ?VAR_num_#prime = VAR_num_ ,
;;	       ?VAR_flag_#prime = VAR_flag_ ,
;;	       ?VAR_pc_#prime = VAR_pc_ ,
;;	       ?VAR_unread_#prime = VAR_unread_ ,
;;	       ?VAR_max_#prime = VAR_max_ ,
;;	       ?VAR_nxt_#prime = VAR_nxt_ 
;;	PROVE  (/\ ?VAR_num_#prime \in [1..CST_N_ -> Nat]
;;	        /\ ?VAR_flag_#prime \in [1..CST_N_ -> BOOLEAN]
;;	        /\ ?VAR_unread_#prime
;;	           \in [1..CST_N_ -> SUBSET 1..CST_N_]
;;	        /\ \A CST_i_ \in 1..CST_N_ :
;;	              ?VAR_pc_#prime[CST_i_] \in {"p2", "p5", "p6"}
;;	              => CST_i_ \notin ?VAR_unread_#prime[CST_i_]
;;	        /\ ?VAR_max_#prime \in [1..CST_N_ -> Nat]
;;	        /\ ?VAR_nxt_#prime \in [1..CST_N_ -> 1..CST_N_]
;;	        /\ \A CST_i_ \in 1..CST_N_ :
;;	              ?VAR_pc_#prime[CST_i_] = "p6"
;;	              => ?VAR_nxt_#prime[CST_i_] # CST_i_
;;	        /\ ?VAR_pc_#prime
;;	           \in [1..CST_N_ ->
;;	                  {"p1", "p2", "p3", "p4", "p5", "p6", "cs", "p7"}])
;;	       /\ (\A CST_i_ \in 1..CST_N_ :
;;	              /\ /\ ?VAR_pc_#prime[CST_i_] \in {"p1", "p2"}
;;	                    => ?VAR_num_#prime[CST_i_] = 0
;;	                 /\ ?VAR_num_#prime[CST_i_] = 0
;;	                    => ?VAR_pc_#prime[CST_i_]
;;	                       \in {"p1", "p2", "p3", "p7"}
;;	              /\ /\ ?VAR_flag_#prime[CST_i_]
;;	                    => ?VAR_pc_#prime[CST_i_]
;;	                       \in {"p1", "p2", "p3", "p4"}
;;	                 /\ ?VAR_pc_#prime[CST_i_] \in {"p2", "p3"}
;;	                    => ?VAR_flag_#prime[CST_i_]
;;	              /\ ?VAR_pc_#prime[CST_i_] \in {"p5", "p6"}
;;	                 => (\A CST_j_
;;	                        \in (1..CST_N_
;;	                             \ ?VAR_unread_#prime[CST_i_])
;;	                            \ {CST_i_} :
;;	                        /\ ?VAR_num_#prime[CST_i_] > 0
;;	                        /\ \/ ?VAR_pc_#prime[CST_j_] = "p1"
;;	                           \/ /\ ?VAR_pc_#prime[CST_j_] = "p2"
;;	                              /\ \/ CST_i_
;;	                                    \in ?VAR_unread_#prime[CST_j_]
;;	                                 \/ ?VAR_max_#prime[CST_j_]
;;	                                    >= ?VAR_num_#prime[CST_i_]
;;	                           \/ /\ ?VAR_pc_#prime[CST_j_] = "p3"
;;	                              /\ ?VAR_max_#prime[CST_j_]
;;	                                 >= ?VAR_num_#prime[CST_i_]
;;	                           \/ /\ ?VAR_pc_#prime[CST_j_]
;;	                                 \in {"p4", "p5", "p6"}
;;	                              /\ \/ ?VAR_num_#prime[CST_i_]
;;	                                    < ?VAR_num_#prime[CST_j_]
;;	                                 \/ /\ ?VAR_num_#prime[CST_j_]
;;	                                       = ?VAR_num_#prime[CST_i_]
;;	                                    /\ CST_i_ =< CST_j_
;;	                              /\ ?VAR_pc_#prime[CST_j_]
;;	                                 \in {"p5", "p6"}
;;	                                 => CST_i_
;;	                                    \in ?VAR_unread_#prime[CST_j_]
;;	                           \/ ?VAR_pc_#prime[CST_j_] = "p7")
;;	              /\ (/\ ?VAR_pc_#prime[CST_i_] = "p6"
;;	                  /\ \/ ?VAR_pc_#prime[?VAR_nxt_#prime[CST_i_]]
;;	                        = "p2"
;;	                        /\ CST_i_
;;	                           \notin ?VAR_unread_#prime[?VAR_nxt_#prime[CST_i_]]
;;	                     \/ ?VAR_pc_#prime[?VAR_nxt_#prime[CST_i_]]
;;	                        = "p3")
;;	                 => ?VAR_max_#prime[?VAR_nxt_#prime[CST_i_]]
;;	                    >= ?VAR_num_#prime[CST_i_]
;;	              /\ ?VAR_pc_#prime[CST_i_] = "cs"
;;	                 => (\A CST_j_ \in 1..CST_N_ \ {CST_i_} :
;;	                        /\ ?VAR_num_#prime[CST_i_] > 0
;;	                        /\ \/ ?VAR_pc_#prime[CST_j_] = "p1"
;;	                           \/ /\ ?VAR_pc_#prime[CST_j_] = "p2"
;;	                              /\ \/ CST_i_
;;	                                    \in ?VAR_unread_#prime[CST_j_]
;;	                                 \/ ?VAR_max_#prime[CST_j_]
;;	                                    >= ?VAR_num_#prime[CST_i_]
;;	                           \/ /\ ?VAR_pc_#prime[CST_j_] = "p3"
;;	                              /\ ?VAR_max_#prime[CST_j_]
;;	                                 >= ?VAR_num_#prime[CST_i_]
;;	                           \/ /\ ?VAR_pc_#prime[CST_j_]
;;	                                 \in {"p4", "p5", "p6"}
;;	                              /\ \/ ?VAR_num_#prime[CST_i_]
;;	                                    < ?VAR_num_#prime[CST_j_]
;;	                                 \/ /\ ?VAR_num_#prime[CST_j_]
;;	                                       = ?VAR_num_#prime[CST_i_]
;;	                                    /\ CST_i_ =< CST_j_
;;	                              /\ ?VAR_pc_#prime[CST_j_]
;;	                                 \in {"p5", "p6"}
;;	                                 => CST_i_
;;	                                    \in ?VAR_unread_#prime[CST_j_]
;;	                           \/ ?VAR_pc_#prime[CST_j_] = "p7"))
;; TLA+ Proof Manager 1.5.0
;; Proof obligation #53
;; Generated from file "./examples/Bakery.tla", line 358, characters 5-6

(set-logic UFNIA)

;; Sorts

(declare-sort Idv 0)

;; Hypotheses

(declare-fun BoolSet () Idv)

(declare-fun Cast_Int (Int) Idv)

(declare-fun FunApp (Idv Idv) Idv)

(declare-fun FunDom (Idv) Idv)

; omitted declaration of '_FunFcn' (second-order)

(declare-fun FunIsafcn (Idv) Bool)

(declare-fun FunSet (Idv Idv) Idv)

(declare-fun IntLteq (Idv Idv) Bool)

(declare-fun IntRange (Idv Idv) Idv)

(declare-fun IntSet () Idv)

(declare-fun Mem (Idv Idv) Bool)

(declare-fun NatSet () Idv)

(declare-fun Proj_Int (Idv) Int)

(declare-fun SetEnum_1 (Idv) Idv)

(declare-fun SetEnum_2 (Idv Idv) Idv)

(declare-fun SetEnum_3 (Idv Idv
  Idv) Idv)

(declare-fun SetEnum_4 (Idv Idv Idv
  Idv) Idv)

(declare-fun SetEnum_8 (Idv Idv Idv
  Idv Idv Idv Idv Idv) Idv)

(declare-fun SetExtTrigger (Idv Idv) Bool)

(declare-fun SetMinus (Idv Idv) Idv)

(declare-fun StrLit_cs () Idv)

(declare-fun StrLit_p1 () Idv)

(declare-fun StrLit_p2 () Idv)

(declare-fun StrLit_p3 () Idv)

(declare-fun StrLit_p4 () Idv)

(declare-fun StrLit_p5 () Idv)

(declare-fun StrLit_p6 () Idv)

(declare-fun StrLit_p7 () Idv)

(declare-fun StrSet () Idv)

(declare-fun Subset (Idv) Idv)

(declare-fun SubsetEq (Idv Idv) Bool)

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
                   (Mem smt__z smt__x))))
    :named |SubsetEqElim|))

;; Axiom: SubsetDefAlt
(assert
  (!
    (forall ((smt__a Idv) (smt__x Idv))
      (!
        (=
          (Mem smt__x
            (Subset smt__a))
          (SubsetEq smt__x smt__a))
        :pattern ((Mem smt__x
                    (Subset smt__a)))
        :pattern ((SubsetEq smt__x smt__a)
                   (Subset smt__a))))
    :named |SubsetDefAlt|))

;; Axiom: SetMinusDef
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__x Idv))
      (!
        (=
          (Mem smt__x
            (SetMinus smt__a smt__b))
          (and (Mem smt__x smt__a)
            (not (Mem smt__x smt__b))))
        :pattern ((Mem smt__x
                    (SetMinus smt__a smt__b)))
        :pattern ((Mem smt__x smt__a)
                   (SetMinus smt__a smt__b))
        :pattern ((Mem smt__x smt__b)
                   (SetMinus smt__a smt__b))))
    :named |SetMinusDef|))

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

;; Axiom: FunExt
(assert
  (!
    (forall ((smt__f Idv) (smt__g Idv))
      (!
        (=>
          (and (FunIsafcn smt__f)
            (FunIsafcn smt__g)
            (= (FunDom smt__f)
              (FunDom smt__g))
            (forall ((smt__x Idv))
              (=>
                (Mem smt__x
                  (FunDom smt__f))
                (= (FunApp smt__f smt__x)
                  (FunApp smt__g smt__x)))))
          (= smt__f smt__g))
        :pattern ((FunIsafcn smt__f)
                   (FunIsafcn smt__g))))
    :named |FunExt|))

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
                (Mem
                  (FunApp smt__f smt__x) 
                  smt__b))))
          (Mem smt__f
            (FunSet smt__a smt__b)))
        :pattern ((Mem smt__f
                    (FunSet smt__a smt__b)))))
    :named |FunSetIntro|))

;; Axiom: FunSetElim1
(assert
  (!
    (forall ((smt__a Idv) (smt__b Idv) (smt__f Idv))
      (!
        (=>
          (Mem smt__f
            (FunSet smt__a smt__b))
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
            (Mem smt__f
              (FunSet smt__a smt__b))
            (Mem smt__x smt__a))
          (Mem
            (FunApp smt__f smt__x) smt__b))
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

;; Axiom: EnumDefIntro 1
(assert
  (!
    (forall ((smt__a1 Idv))
      (!
        (Mem smt__a1
          (SetEnum_1 smt__a1))
        :pattern ((SetEnum_1 smt__a1))))
    :named |EnumDefIntro 1|))

;; Axiom: EnumDefIntro 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv))
      (!
        (and
          (Mem smt__a1
            (SetEnum_2 smt__a1
              smt__a2))
          (Mem smt__a2
            (SetEnum_2 smt__a1
              smt__a2)))
        :pattern ((SetEnum_2 
                    smt__a1 smt__a2)))) :named |EnumDefIntro 2|))

;; Axiom: EnumDefIntro 3
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv))
      (!
        (and
          (Mem smt__a1
            (SetEnum_3 smt__a1
              smt__a2 smt__a3))
          (Mem smt__a2
            (SetEnum_3 smt__a1
              smt__a2 smt__a3))
          (Mem smt__a3
            (SetEnum_3 smt__a1
              smt__a2 smt__a3)))
        :pattern ((SetEnum_3 
                    smt__a1 smt__a2 smt__a3)))) :named |EnumDefIntro 3|))

;; Axiom: EnumDefIntro 4
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv))
      (!
        (and
          (Mem smt__a1
            (SetEnum_4 smt__a1
              smt__a2 smt__a3 smt__a4))
          (Mem smt__a2
            (SetEnum_4 smt__a1
              smt__a2 smt__a3 smt__a4))
          (Mem smt__a3
            (SetEnum_4 smt__a1
              smt__a2 smt__a3 smt__a4))
          (Mem smt__a4
            (SetEnum_4 smt__a1
              smt__a2 smt__a3 smt__a4)))
        :pattern ((SetEnum_4 
                    smt__a1 smt__a2 smt__a3 smt__a4))))
    :named |EnumDefIntro 4|))

;; Axiom: EnumDefIntro 8
(assert
  (!
    (forall
      ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv) (smt__a5 Idv)
        (smt__a6 Idv) (smt__a7 Idv) (smt__a8 Idv))
      (!
        (and
          (Mem smt__a1
            (SetEnum_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (Mem smt__a2
            (SetEnum_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (Mem smt__a3
            (SetEnum_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (Mem smt__a4
            (SetEnum_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (Mem smt__a5
            (SetEnum_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (Mem smt__a6
            (SetEnum_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (Mem smt__a7
            (SetEnum_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (Mem smt__a8
            (SetEnum_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8)))
        :pattern ((SetEnum_8 
                    smt__a1 smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7
                    smt__a8)))) :named |EnumDefIntro 8|))

;; Axiom: EnumDefElim 1
(assert
  (!
    (forall ((smt__a1 Idv) (smt__x Idv))
      (!
        (=>
          (Mem smt__x
            (SetEnum_1 smt__a1))
          (= smt__x smt__a1))
        :pattern ((Mem smt__x
                    (SetEnum_1
                      smt__a1))))) :named |EnumDefElim 1|))

;; Axiom: EnumDefElim 2
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__x Idv))
      (!
        (=>
          (Mem smt__x
            (SetEnum_2 smt__a1
              smt__a2)) (or (= smt__x smt__a1) (= smt__x smt__a2)))
        :pattern ((Mem smt__x
                    (SetEnum_2
                      smt__a1 smt__a2))))) :named |EnumDefElim 2|))

;; Axiom: EnumDefElim 3
(assert
  (!
    (forall ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__x Idv))
      (!
        (=>
          (Mem smt__x
            (SetEnum_3 smt__a1
              smt__a2 smt__a3))
          (or (= smt__x smt__a1) (= smt__x smt__a2) (= smt__x smt__a3)))
        :pattern ((Mem smt__x
                    (SetEnum_3
                      smt__a1 smt__a2 smt__a3))))) :named |EnumDefElim 3|))

;; Axiom: EnumDefElim 4
(assert
  (!
    (forall
      ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv) (smt__x Idv))
      (!
        (=>
          (Mem smt__x
            (SetEnum_4 smt__a1
              smt__a2 smt__a3 smt__a4))
          (or (= smt__x smt__a1) (= smt__x smt__a2) (= smt__x smt__a3)
            (= smt__x smt__a4)))
        :pattern ((Mem smt__x
                    (SetEnum_4
                      smt__a1 smt__a2 smt__a3 smt__a4)))))
    :named |EnumDefElim 4|))

;; Axiom: EnumDefElim 8
(assert
  (!
    (forall
      ((smt__a1 Idv) (smt__a2 Idv) (smt__a3 Idv) (smt__a4 Idv) (smt__a5 Idv)
        (smt__a6 Idv) (smt__a7 Idv) (smt__a8 Idv) (smt__x Idv))
      (!
        (=>
          (Mem smt__x
            (SetEnum_8 smt__a1
              smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 smt__a7 smt__a8))
          (or (= smt__x smt__a1) (= smt__x smt__a2) (= smt__x smt__a3)
            (= smt__x smt__a4) (= smt__x smt__a5) (= smt__x smt__a6)
            (= smt__x smt__a7) (= smt__x smt__a8)))
        :pattern ((Mem smt__x
                    (SetEnum_8
                      smt__a1 smt__a2 smt__a3 smt__a4 smt__a5 smt__a6 
                      smt__a7 smt__a8))))) :named |EnumDefElim 8|))

;; Axiom: StrLitIsstr cs
(assert
  (!
    (Mem
      StrLit_cs
      StrSet) :named |StrLitIsstr cs|))

;; Axiom: StrLitIsstr p1
(assert
  (!
    (Mem
      StrLit_p1
      StrSet) :named |StrLitIsstr p1|))

;; Axiom: StrLitIsstr p2
(assert
  (!
    (Mem
      StrLit_p2
      StrSet) :named |StrLitIsstr p2|))

;; Axiom: StrLitIsstr p3
(assert
  (!
    (Mem
      StrLit_p3
      StrSet) :named |StrLitIsstr p3|))

;; Axiom: StrLitIsstr p4
(assert
  (!
    (Mem
      StrLit_p4
      StrSet) :named |StrLitIsstr p4|))

;; Axiom: StrLitIsstr p5
(assert
  (!
    (Mem
      StrLit_p5
      StrSet) :named |StrLitIsstr p5|))

;; Axiom: StrLitIsstr p6
(assert
  (!
    (Mem
      StrLit_p6
      StrSet) :named |StrLitIsstr p6|))

;; Axiom: StrLitIsstr p7
(assert
  (!
    (Mem
      StrLit_p7
      StrSet) :named |StrLitIsstr p7|))

;; Axiom: StrLitDistinct cs p1
(assert
  (!
    (distinct StrLit_cs
      StrLit_p1)
    :named |StrLitDistinct cs p1|))

;; Axiom: StrLitDistinct cs p2
(assert
  (!
    (distinct StrLit_cs
      StrLit_p2)
    :named |StrLitDistinct cs p2|))

;; Axiom: StrLitDistinct cs p3
(assert
  (!
    (distinct StrLit_cs
      StrLit_p3)
    :named |StrLitDistinct cs p3|))

;; Axiom: StrLitDistinct cs p4
(assert
  (!
    (distinct StrLit_cs
      StrLit_p4)
    :named |StrLitDistinct cs p4|))

;; Axiom: StrLitDistinct cs p5
(assert
  (!
    (distinct StrLit_cs
      StrLit_p5)
    :named |StrLitDistinct cs p5|))

;; Axiom: StrLitDistinct cs p6
(assert
  (!
    (distinct StrLit_cs
      StrLit_p6)
    :named |StrLitDistinct cs p6|))

;; Axiom: StrLitDistinct p1 p2
(assert
  (!
    (distinct StrLit_p1
      StrLit_p2)
    :named |StrLitDistinct p1 p2|))

;; Axiom: StrLitDistinct p1 p5
(assert
  (!
    (distinct StrLit_p1
      StrLit_p5)
    :named |StrLitDistinct p1 p5|))

;; Axiom: StrLitDistinct p1 p6
(assert
  (!
    (distinct StrLit_p1
      StrLit_p6)
    :named |StrLitDistinct p1 p6|))

;; Axiom: StrLitDistinct p3 p1
(assert
  (!
    (distinct StrLit_p3
      StrLit_p1)
    :named |StrLitDistinct p3 p1|))

;; Axiom: StrLitDistinct p3 p2
(assert
  (!
    (distinct StrLit_p3
      StrLit_p2)
    :named |StrLitDistinct p3 p2|))

;; Axiom: StrLitDistinct p3 p5
(assert
  (!
    (distinct StrLit_p3
      StrLit_p5)
    :named |StrLitDistinct p3 p5|))

;; Axiom: StrLitDistinct p3 p6
(assert
  (!
    (distinct StrLit_p3
      StrLit_p6)
    :named |StrLitDistinct p3 p6|))

;; Axiom: StrLitDistinct p4 p1
(assert
  (!
    (distinct StrLit_p4
      StrLit_p1)
    :named |StrLitDistinct p4 p1|))

;; Axiom: StrLitDistinct p4 p2
(assert
  (!
    (distinct StrLit_p4
      StrLit_p2)
    :named |StrLitDistinct p4 p2|))

;; Axiom: StrLitDistinct p4 p3
(assert
  (!
    (distinct StrLit_p4
      StrLit_p3)
    :named |StrLitDistinct p4 p3|))

;; Axiom: StrLitDistinct p4 p5
(assert
  (!
    (distinct StrLit_p4
      StrLit_p5)
    :named |StrLitDistinct p4 p5|))

;; Axiom: StrLitDistinct p4 p6
(assert
  (!
    (distinct StrLit_p4
      StrLit_p6)
    :named |StrLitDistinct p4 p6|))

;; Axiom: StrLitDistinct p5 p2
(assert
  (!
    (distinct StrLit_p5
      StrLit_p2)
    :named |StrLitDistinct p5 p2|))

;; Axiom: StrLitDistinct p6 p2
(assert
  (!
    (distinct StrLit_p6
      StrLit_p2)
    :named |StrLitDistinct p6 p2|))

;; Axiom: StrLitDistinct p6 p5
(assert
  (!
    (distinct StrLit_p6
      StrLit_p5)
    :named |StrLitDistinct p6 p5|))

;; Axiom: StrLitDistinct p7 cs
(assert
  (!
    (distinct StrLit_p7
      StrLit_cs)
    :named |StrLitDistinct p7 cs|))

;; Axiom: StrLitDistinct p7 p1
(assert
  (!
    (distinct StrLit_p7
      StrLit_p1)
    :named |StrLitDistinct p7 p1|))

;; Axiom: StrLitDistinct p7 p2
(assert
  (!
    (distinct StrLit_p7
      StrLit_p2)
    :named |StrLitDistinct p7 p2|))

;; Axiom: StrLitDistinct p7 p3
(assert
  (!
    (distinct StrLit_p7
      StrLit_p3)
    :named |StrLitDistinct p7 p3|))

;; Axiom: StrLitDistinct p7 p4
(assert
  (!
    (distinct StrLit_p7
      StrLit_p4)
    :named |StrLitDistinct p7 p4|))

;; Axiom: StrLitDistinct p7 p5
(assert
  (!
    (distinct StrLit_p7
      StrLit_p5)
    :named |StrLitDistinct p7 p5|))

;; Axiom: StrLitDistinct p7 p6
(assert
  (!
    (distinct StrLit_p7
      StrLit_p6)
    :named |StrLitDistinct p7 p6|))

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

(declare-fun VAR_unread_ () Idv)

(declare-fun VAR_unread_prime () Idv)

(declare-fun VAR_max_ () Idv)

(declare-fun VAR_max_prime () Idv)

(declare-fun VAR_nxt_ () Idv)

(declare-fun VAR_nxt_prime () Idv)

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

(assert
  (Mem CST_N_
    NatSet))

; hidden fact

; hidden fact

; hidden fact

(assert
  (and
    (and
      (Mem
        VAR_num_
        (FunSet
          (IntRange
            (Cast_Int 1)
            CST_N_)
          NatSet))
      (Mem
        VAR_flag_
        (FunSet
          (IntRange
            (Cast_Int 1)
            CST_N_)
          BoolSet))
      (Mem
        VAR_unread_
        (FunSet
          (IntRange
            (Cast_Int 1)
            CST_N_)
          (Subset
            (IntRange
              (Cast_Int 1)
              CST_N_))))
      (forall ((CST_i_ Idv))
        (=>
          (Mem
            CST_i_
            (IntRange
              (Cast_Int 1)
              CST_N_))
          (=>
            (Mem
              (FunApp
                VAR_pc_
                CST_i_)
              (SetEnum_3
                StrLit_p2
                StrLit_p5
                StrLit_p6))
            (not
              (Mem
                CST_i_
                (FunApp
                  VAR_unread_
                  CST_i_))))))
      (Mem
        VAR_max_
        (FunSet
          (IntRange
            (Cast_Int 1)
            CST_N_)
          NatSet))
      (Mem
        VAR_nxt_
        (FunSet
          (IntRange
            (Cast_Int 1)
            CST_N_)
          (IntRange
            (Cast_Int 1)
            CST_N_)))
      (forall ((CST_i_ Idv))
        (=>
          (Mem
            CST_i_
            (IntRange
              (Cast_Int 1)
              CST_N_))
          (=>
            (TrigEq_Idv
              (FunApp
                VAR_pc_
                CST_i_)
              StrLit_p6)
            (not
              (TrigEq_Idv
                (FunApp
                  VAR_nxt_
                  CST_i_)
                CST_i_)))))
      (Mem
        VAR_pc_
        (FunSet
          (IntRange
            (Cast_Int 1)
            CST_N_)
          (SetEnum_8
            StrLit_p1
            StrLit_p2
            StrLit_p3
            StrLit_p4
            StrLit_p5
            StrLit_p6
            StrLit_cs
            StrLit_p7))))
    (forall ((CST_i_ Idv))
      (=>
        (Mem
          CST_i_
          (IntRange
            (Cast_Int 1)
            CST_N_))
        (and
          (and
            (=>
              (Mem
                (FunApp
                  VAR_pc_
                  CST_i_)
                (SetEnum_2
                  StrLit_p1
                  StrLit_p2))
              (TrigEq_Idv
                (FunApp
                  VAR_num_
                  CST_i_)
                (Cast_Int 0)))
            (=>
              (TrigEq_Idv
                (FunApp
                  VAR_num_
                  CST_i_)
                (Cast_Int 0))
              (Mem
                (FunApp
                  VAR_pc_
                  CST_i_)
                (SetEnum_4
                  StrLit_p1
                  StrLit_p2
                  StrLit_p3
                  StrLit_p7))))
          (and
            (=>
              (=
                (FunApp
                  VAR_flag_
                  CST_i_)
                Tt_Idv)
              (Mem
                (FunApp
                  VAR_pc_
                  CST_i_)
                (SetEnum_4
                  StrLit_p1
                  StrLit_p2
                  StrLit_p3
                  StrLit_p4)))
            (=>
              (Mem
                (FunApp
                  VAR_pc_
                  CST_i_)
                (SetEnum_2
                  StrLit_p2
                  StrLit_p3))
              (=
                (FunApp
                  VAR_flag_
                  CST_i_)
                Tt_Idv)))
          (=>
            (Mem
              (FunApp
                VAR_pc_
                CST_i_)
              (SetEnum_2
                StrLit_p5
                StrLit_p6))
            (forall ((CST_j_ Idv))
              (=>
                (Mem
                  CST_j_
                  (SetMinus
                    (SetMinus
                      (IntRange
                        (Cast_Int 1)
                        CST_N_)
                      (FunApp
                        VAR_unread_
                        CST_i_))
                    (SetEnum_1
                      CST_i_)))
                (and
                  (and
                    (IntLteq
                      (Cast_Int 0)
                      (FunApp
                        VAR_num_
                        CST_i_))
                    (not
                      (TrigEq_Idv
                        (Cast_Int 0)
                        (FunApp
                          VAR_num_
                          CST_i_))))
                  (or
                    (TrigEq_Idv
                      (FunApp
                        VAR_pc_
                        CST_j_)
                      StrLit_p1)
                    (and
                      (TrigEq_Idv
                        (FunApp
                          VAR_pc_
                          CST_j_)
                        StrLit_p2)
                      (or
                        (Mem
                          CST_i_
                          (FunApp
                            VAR_unread_
                            CST_j_))
                        (IntLteq
                          (FunApp
                            VAR_num_
                            CST_i_)
                          (FunApp
                            VAR_max_
                            CST_j_))))
                    (and
                      (TrigEq_Idv
                        (FunApp
                          VAR_pc_
                          CST_j_)
                        StrLit_p3)
                      (IntLteq
                        (FunApp
                          VAR_num_
                          CST_i_)
                        (FunApp
                          VAR_max_
                          CST_j_)))
                    (and
                      (Mem
                        (FunApp
                          VAR_pc_
                          CST_j_)
                        (SetEnum_3
                          StrLit_p4
                          StrLit_p5
                          StrLit_p6))
                      (or
                        (and
                          (IntLteq
                            (FunApp
                              VAR_num_
                              CST_i_)
                            (FunApp
                              VAR_num_
                              CST_j_))
                          (not
                            (TrigEq_Idv
                              (FunApp
                                VAR_num_
                                CST_i_)
                              (FunApp
                                VAR_num_
                                CST_j_))))
                        (and
                          (TrigEq_Idv
                            (FunApp
                              VAR_num_
                              CST_j_)
                            (FunApp
                              VAR_num_
                              CST_i_))
                          (IntLteq
                            CST_i_
                            CST_j_)))
                      (=>
                        (Mem
                          (FunApp
                            VAR_pc_
                            CST_j_)
                          (SetEnum_2
                            StrLit_p5
                            StrLit_p6))
                        (Mem
                          CST_i_
                          (FunApp
                            VAR_unread_
                            CST_j_))))
                    (TrigEq_Idv
                      (FunApp
                        VAR_pc_
                        CST_j_)
                      StrLit_p7))))))
          (=>
            (and
              (TrigEq_Idv
                (FunApp
                  VAR_pc_
                  CST_i_)
                StrLit_p6)
              (or
                (and
                  (TrigEq_Idv
                    (FunApp
                      VAR_pc_
                      (FunApp
                        VAR_nxt_
                        CST_i_))
                    StrLit_p2)
                  (not
                    (Mem
                      CST_i_
                      (FunApp
                        VAR_unread_
                        (FunApp
                          VAR_nxt_
                          CST_i_)))))
                (TrigEq_Idv
                  (FunApp
                    VAR_pc_
                    (FunApp
                      VAR_nxt_
                      CST_i_))
                  StrLit_p3)))
            (IntLteq
              (FunApp
                VAR_num_
                CST_i_)
              (FunApp
                VAR_max_
                (FunApp
                  VAR_nxt_
                  CST_i_))))
          (=>
            (TrigEq_Idv
              (FunApp
                VAR_pc_
                CST_i_)
              StrLit_cs)
            (forall ((CST_j_ Idv))
              (=>
                (Mem
                  CST_j_
                  (SetMinus
                    (IntRange
                      (Cast_Int 1)
                      CST_N_)
                    (SetEnum_1
                      CST_i_)))
                (and
                  (and
                    (IntLteq
                      (Cast_Int 0)
                      (FunApp
                        VAR_num_
                        CST_i_))
                    (not
                      (TrigEq_Idv
                        (Cast_Int 0)
                        (FunApp
                          VAR_num_
                          CST_i_))))
                  (or
                    (TrigEq_Idv
                      (FunApp
                        VAR_pc_
                        CST_j_)
                      StrLit_p1)
                    (and
                      (TrigEq_Idv
                        (FunApp
                          VAR_pc_
                          CST_j_)
                        StrLit_p2)
                      (or
                        (Mem
                          CST_i_
                          (FunApp
                            VAR_unread_
                            CST_j_))
                        (IntLteq
                          (FunApp
                            VAR_num_
                            CST_i_)
                          (FunApp
                            VAR_max_
                            CST_j_))))
                    (and
                      (TrigEq_Idv
                        (FunApp
                          VAR_pc_
                          CST_j_)
                        StrLit_p3)
                      (IntLteq
                        (FunApp
                          VAR_num_
                          CST_i_)
                        (FunApp
                          VAR_max_
                          CST_j_)))
                    (and
                      (Mem
                        (FunApp
                          VAR_pc_
                          CST_j_)
                        (SetEnum_3
                          StrLit_p4
                          StrLit_p5
                          StrLit_p6))
                      (or
                        (and
                          (IntLteq
                            (FunApp
                              VAR_num_
                              CST_i_)
                            (FunApp
                              VAR_num_
                              CST_j_))
                          (not
                            (TrigEq_Idv
                              (FunApp
                                VAR_num_
                                CST_i_)
                              (FunApp
                                VAR_num_
                                CST_j_))))
                        (and
                          (TrigEq_Idv
                            (FunApp
                              VAR_num_
                              CST_j_)
                            (FunApp
                              VAR_num_
                              CST_i_))
                          (IntLteq
                            CST_i_
                            CST_j_)))
                      (=>
                        (Mem
                          (FunApp
                            VAR_pc_
                            CST_j_)
                          (SetEnum_2
                            StrLit_p5
                            StrLit_p6))
                        (Mem
                          CST_i_
                          (FunApp
                            VAR_unread_
                            CST_j_))))
                    (TrigEq_Idv
                      (FunApp
                        VAR_pc_
                        CST_j_)
                      StrLit_p7)))))))))))

(assert
  (or
    (= ACTION_Next_
      Tt_Idv)
    (and
      (TrigEq_Idv
        VAR_num_prime
        VAR_num_)
      (TrigEq_Idv
        VAR_flag_prime
        VAR_flag_)
      (TrigEq_Idv
        VAR_pc_prime
        VAR_pc_)
      (TrigEq_Idv
        VAR_unread_prime
        VAR_unread_)
      (TrigEq_Idv
        VAR_max_prime
        VAR_max_)
      (TrigEq_Idv
        VAR_nxt_prime
        VAR_nxt_))))

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
  (TrigEq_Idv
    VAR_num_prime
    VAR_num_))

(assert
  (TrigEq_Idv
    VAR_flag_prime
    VAR_flag_))

(assert
  (TrigEq_Idv
    VAR_pc_prime
    VAR_pc_))

(assert
  (TrigEq_Idv
    VAR_unread_prime
    VAR_unread_))

(assert
  (TrigEq_Idv
    VAR_max_prime
    VAR_max_))

(assert
  (TrigEq_Idv
    VAR_nxt_prime
    VAR_nxt_))

;; Goal
(assert
  (!
    (not
      (and
        (and
          (Mem
            VAR_num_prime
            (FunSet
              (IntRange
                (Cast_Int 1)
                CST_N_)
              NatSet))
          (Mem
            VAR_flag_prime
            (FunSet
              (IntRange
                (Cast_Int 1)
                CST_N_)
              BoolSet))
          (Mem
            VAR_unread_prime
            (FunSet
              (IntRange
                (Cast_Int 1)
                CST_N_)
              (Subset
                (IntRange
                  (Cast_Int 1)
                  CST_N_))))
          (forall ((CST_i_ Idv))
            (=>
              (Mem
                CST_i_
                (IntRange
                  (Cast_Int 1)
                  CST_N_))
              (=>
                (Mem
                  (FunApp
                    VAR_pc_prime
                    CST_i_)
                  (SetEnum_3
                    StrLit_p2
                    StrLit_p5
                    StrLit_p6))
                (not
                  (Mem
                    CST_i_
                    (FunApp
                      VAR_unread_prime
                      CST_i_))))))
          (Mem
            VAR_max_prime
            (FunSet
              (IntRange
                (Cast_Int 1)
                CST_N_)
              NatSet))
          (Mem
            VAR_nxt_prime
            (FunSet
              (IntRange
                (Cast_Int 1)
                CST_N_)
              (IntRange
                (Cast_Int 1)
                CST_N_)))
          (forall ((CST_i_ Idv))
            (=>
              (Mem
                CST_i_
                (IntRange
                  (Cast_Int 1)
                  CST_N_))
              (=>
                (TrigEq_Idv
                  (FunApp
                    VAR_pc_prime
                    CST_i_)
                  StrLit_p6)
                (not
                  (TrigEq_Idv
                    (FunApp
                      VAR_nxt_prime
                      CST_i_)
                    CST_i_)))))
          (Mem
            VAR_pc_prime
            (FunSet
              (IntRange
                (Cast_Int 1)
                CST_N_)
              (SetEnum_8
                StrLit_p1
                StrLit_p2
                StrLit_p3
                StrLit_p4
                StrLit_p5
                StrLit_p6
                StrLit_cs
                StrLit_p7))))
        (forall ((CST_i_ Idv))
          (=>
            (Mem
              CST_i_
              (IntRange
                (Cast_Int 1)
                CST_N_))
            (and
              (and
                (=>
                  (Mem
                    (FunApp
                      VAR_pc_prime
                      CST_i_)
                    (SetEnum_2
                      StrLit_p1
                      StrLit_p2))
                  (TrigEq_Idv
                    (FunApp
                      VAR_num_prime
                      CST_i_)
                    (Cast_Int 0)))
                (=>
                  (TrigEq_Idv
                    (FunApp
                      VAR_num_prime
                      CST_i_)
                    (Cast_Int 0))
                  (Mem
                    (FunApp
                      VAR_pc_prime
                      CST_i_)
                    (SetEnum_4
                      StrLit_p1
                      StrLit_p2
                      StrLit_p3
                      StrLit_p7))))
              (and
                (=>
                  (=
                    (FunApp
                      VAR_flag_prime
                      CST_i_)
                    Tt_Idv)
                  (Mem
                    (FunApp
                      VAR_pc_prime
                      CST_i_)
                    (SetEnum_4
                      StrLit_p1
                      StrLit_p2
                      StrLit_p3
                      StrLit_p4)))
                (=>
                  (Mem
                    (FunApp
                      VAR_pc_prime
                      CST_i_)
                    (SetEnum_2
                      StrLit_p2
                      StrLit_p3))
                  (=
                    (FunApp
                      VAR_flag_prime
                      CST_i_)
                    Tt_Idv)))
              (=>
                (Mem
                  (FunApp
                    VAR_pc_prime
                    CST_i_)
                  (SetEnum_2
                    StrLit_p5
                    StrLit_p6))
                (forall ((CST_j_ Idv))
                  (=>
                    (Mem
                      CST_j_
                      (SetMinus
                        (SetMinus
                          (IntRange
                            (Cast_Int
                              1) CST_N_)
                          (FunApp
                            VAR_unread_prime
                            CST_i_))
                        (SetEnum_1
                          CST_i_)))
                    (and
                      (and
                        (IntLteq
                          (Cast_Int 0)
                          (FunApp
                            VAR_num_prime
                            CST_i_))
                        (not
                          (TrigEq_Idv
                            (Cast_Int
                              0)
                            (FunApp
                              VAR_num_prime
                              CST_i_))))
                      (or
                        (TrigEq_Idv
                          (FunApp
                            VAR_pc_prime
                            CST_j_)
                          StrLit_p1)
                        (and
                          (TrigEq_Idv
                            (FunApp
                              VAR_pc_prime
                              CST_j_)
                            StrLit_p2)
                          (or
                            (Mem
                              CST_i_
                              (FunApp
                                VAR_unread_prime
                                CST_j_))
                            (IntLteq
                              (FunApp
                                VAR_num_prime
                                CST_i_)
                              (FunApp
                                VAR_max_prime
                                CST_j_))))
                        (and
                          (TrigEq_Idv
                            (FunApp
                              VAR_pc_prime
                              CST_j_)
                            StrLit_p3)
                          (IntLteq
                            (FunApp
                              VAR_num_prime
                              CST_i_)
                            (FunApp
                              VAR_max_prime
                              CST_j_)))
                        (and
                          (Mem
                            (FunApp
                              VAR_pc_prime
                              CST_j_)
                            (SetEnum_3
                              StrLit_p4
                              StrLit_p5
                              StrLit_p6))
                          (or
                            (and
                              (IntLteq
                                (FunApp
                                  VAR_num_prime
                                  CST_i_)
                                (FunApp
                                  VAR_num_prime
                                  CST_j_))
                              (not
                                (TrigEq_Idv
                                  (FunApp
                                    VAR_num_prime
                                    CST_i_)
                                  (FunApp
                                    VAR_num_prime
                                    CST_j_))))
                            (and
                              (TrigEq_Idv
                                (FunApp
                                  VAR_num_prime
                                  CST_j_)
                                (FunApp
                                  VAR_num_prime
                                  CST_i_))
                              (IntLteq
                                CST_i_
                                CST_j_)))
                          (=>
                            (Mem
                              (FunApp
                                VAR_pc_prime
                                CST_j_)
                              (SetEnum_2
                                StrLit_p5
                                StrLit_p6))
                            (Mem
                              CST_i_
                              (FunApp
                                VAR_unread_prime
                                CST_j_))))
                        (TrigEq_Idv
                          (FunApp
                            VAR_pc_prime
                            CST_j_)
                          StrLit_p7))))))
              (=>
                (and
                  (TrigEq_Idv
                    (FunApp
                      VAR_pc_prime
                      CST_i_)
                    StrLit_p6)
                  (or
                    (and
                      (TrigEq_Idv
                        (FunApp
                          VAR_pc_prime
                          (FunApp
                            VAR_nxt_prime
                            CST_i_))
                        StrLit_p2)
                      (not
                        (Mem
                          CST_i_
                          (FunApp
                            VAR_unread_prime
                            (FunApp
                              VAR_nxt_prime
                              CST_i_)))))
                    (TrigEq_Idv
                      (FunApp
                        VAR_pc_prime
                        (FunApp
                          VAR_nxt_prime
                          CST_i_))
                      StrLit_p3)))
                (IntLteq
                  (FunApp
                    VAR_num_prime
                    CST_i_)
                  (FunApp
                    VAR_max_prime
                    (FunApp
                      VAR_nxt_prime
                      CST_i_))))
              (=>
                (TrigEq_Idv
                  (FunApp
                    VAR_pc_prime
                    CST_i_)
                  StrLit_cs)
                (forall ((CST_j_ Idv))
                  (=>
                    (Mem
                      CST_j_
                      (SetMinus
                        (IntRange
                          (Cast_Int 1)
                          CST_N_)
                        (SetEnum_1
                          CST_i_)))
                    (and
                      (and
                        (IntLteq
                          (Cast_Int 0)
                          (FunApp
                            VAR_num_prime
                            CST_i_))
                        (not
                          (TrigEq_Idv
                            (Cast_Int
                              0)
                            (FunApp
                              VAR_num_prime
                              CST_i_))))
                      (or
                        (TrigEq_Idv
                          (FunApp
                            VAR_pc_prime
                            CST_j_)
                          StrLit_p1)
                        (and
                          (TrigEq_Idv
                            (FunApp
                              VAR_pc_prime
                              CST_j_)
                            StrLit_p2)
                          (or
                            (Mem
                              CST_i_
                              (FunApp
                                VAR_unread_prime
                                CST_j_))
                            (IntLteq
                              (FunApp
                                VAR_num_prime
                                CST_i_)
                              (FunApp
                                VAR_max_prime
                                CST_j_))))
                        (and
                          (TrigEq_Idv
                            (FunApp
                              VAR_pc_prime
                              CST_j_)
                            StrLit_p3)
                          (IntLteq
                            (FunApp
                              VAR_num_prime
                              CST_i_)
                            (FunApp
                              VAR_max_prime
                              CST_j_)))
                        (and
                          (Mem
                            (FunApp
                              VAR_pc_prime
                              CST_j_)
                            (SetEnum_3
                              StrLit_p4
                              StrLit_p5
                              StrLit_p6))
                          (or
                            (and
                              (IntLteq
                                (FunApp
                                  VAR_num_prime
                                  CST_i_)
                                (FunApp
                                  VAR_num_prime
                                  CST_j_))
                              (not
                                (TrigEq_Idv
                                  (FunApp
                                    VAR_num_prime
                                    CST_i_)
                                  (FunApp
                                    VAR_num_prime
                                    CST_j_))))
                            (and
                              (TrigEq_Idv
                                (FunApp
                                  VAR_num_prime
                                  CST_j_)
                                (FunApp
                                  VAR_num_prime
                                  CST_i_))
                              (IntLteq
                                CST_i_
                                CST_j_)))
                          (=>
                            (Mem
                              (FunApp
                                VAR_pc_prime
                                CST_j_)
                              (SetEnum_2
                                StrLit_p5
                                StrLit_p6))
                            (Mem
                              CST_i_
                              (FunApp
                                VAR_unread_prime
                                CST_j_))))
                        (TrigEq_Idv
                          (FunApp
                            VAR_pc_prime
                            CST_j_)
                          StrLit_p7)))))))))))
    :named |Goal|))

(check-sat)
(exit)
