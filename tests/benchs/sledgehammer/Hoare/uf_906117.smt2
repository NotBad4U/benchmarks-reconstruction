(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status sat)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-sort S3 0)
(declare-sort S4 0)
(declare-sort S5 0)
(declare-sort S6 0)
(declare-sort S7 0)
(declare-sort S8 0)
(declare-sort S9 0)
(declare-sort S10 0)
(declare-sort S11 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S2) S3)
(declare-fun f7 () S5)
(declare-fun f8 () S4)
(declare-fun f9 (S6 S6) S1)
(declare-fun f10 () S6)
(declare-fun f11 (S7 S6) S6)
(declare-fun f12 (S8) S7)
(declare-fun f13 (S9 S4) S8)
(declare-fun f14 (S10 S5) S9)
(declare-fun f15 (S11 S4) S10)
(declare-fun f16 () S11)
(declare-fun f17 (S8 S6) S1)
(declare-fun f18 (S6 S8) S1)
(declare-fun f19 () S1)
(declare-fun f20 (S6) S6)
(assert (not (= f1 f2)))
(assert (not (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (forall ((?v2 S2)) (=> (forall ((?v3 S2)) (=> (= ?v3 ?v1) (= (f3 (f6 f7 ?v3) ?v2) f1))) (= (f3 (f4 f8 ?v0) ?v2) f1)))))))
(assert (= (f9 f10 (f11 (f12 (f13 (f14 (f15 f16 f5) f7) f8)) f10)) f1))
(assert (forall ((?v0 S4) (?v1 S5) (?v2 S4) (?v3 S4) (?v4 S5) (?v5 S4)) (= (= (f13 (f14 (f15 f16 ?v0) ?v1) ?v2) (f13 (f14 (f15 f16 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S6)) (=> (= (f17 ?v0 (f11 (f12 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f17 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S8) (?v1 S6) (?v2 S8)) (=> (=> (not (= (f17 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f17 ?v0 (f11 (f12 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S8)) (=> (= (f17 ?v0 f10) f1) false)))
(assert (forall ((?v0 S8) (?v1 S6)) (not (= f10 (f11 (f12 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S6)) (not (= (f11 (f12 ?v0) ?v1) f10))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f17 ?v0 (f11 (f12 ?v1) f10)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (= (= (f11 (f12 ?v0) (f11 (f12 ?v1) f10)) (f11 (f12 ?v2) (f11 (f12 ?v3) f10))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f17 ?v0 (f11 (f12 ?v1) f10)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f11 (f12 ?v0) f10) (f11 (f12 ?v1) f10)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8)) (= (= (f18 f10 ?v0) f1) (= f19 f1))))
(assert (forall ((?v0 S6) (?v1 S8)) (=> (= ?v0 f10) (not (= (f17 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S6)) (= (= (f20 ?v0) f10) (forall ((?v1 S8)) (not (= (f18 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S8)) (= (= (f17 ?v0 f10) f1) false)))
(check-sat)
(exit)