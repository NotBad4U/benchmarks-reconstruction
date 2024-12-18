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
(declare-sort S12 0)
(declare-sort S13 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S6) S4)
(declare-fun f6 (S7 S8) S5)
(declare-fun f7 (S9 S6) S7)
(declare-fun f8 () S9)
(declare-fun f9 (S2) S6)
(declare-fun f10 (S10) S8)
(declare-fun f11 (S2) S10)
(declare-fun f12 (S2) S6)
(declare-fun f13 () S3)
(declare-fun f14 (S2) S8)
(declare-fun f15 (S4 S11) S1)
(declare-fun f16 () S11)
(declare-fun f17 (S12 S4) S1)
(declare-fun f18 () S12)
(declare-fun f19 (S3 S13) S11)
(declare-fun f20 () S13)
(declare-fun f21 (S11 S11) S11)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 (f6 (f7 f8 (f9 ?v0)) (f10 (f11 ?v0))) (f12 ?v0)))))
(assert (forall ((?v0 S2)) (= (f3 f13 ?v0) (f5 (f6 (f7 f8 (f9 ?v0)) (f14 ?v0)) (f12 ?v0)))))
(assert (not (=> (forall ((?v0 S4)) (=> (= (f15 ?v0 f16) f1) (= (f17 f18 ?v0) f1))) (forall ((?v0 S4)) (=> (= (f15 ?v0 (f19 f13 f20)) f1) (= (f17 f18 ?v0) f1))))))
(assert (forall ((?v0 S12)) (=> (forall ((?v1 S4)) (=> (= (f15 ?v1 (f21 f16 (f19 f13 f20))) f1) (= (f17 ?v0 ?v1) f1))) (forall ((?v1 S4)) (=> (= (f15 ?v1 (f19 f4 f20)) f1) (= (f17 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6)) (= (f17 f18 (f5 (f6 (f7 f8 ?v0) (f14 ?v1)) ?v2)) f1)))
(check-sat)
(exit)
