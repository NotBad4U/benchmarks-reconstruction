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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S3) S1)
(declare-fun f4 (S5 S2) S4)
(declare-fun f5 () S5)
(declare-fun f6 () S5)
(declare-fun f7 () S5)
(declare-fun f8 () S5)
(declare-fun f9 () S5)
(declare-fun f10 () S5)
(declare-fun f11 (S6 S6) S1)
(declare-fun f12 () S6)
(declare-fun f13 (S7 S6) S6)
(declare-fun f14 (S8) S7)
(declare-fun f15 (S5 S9 S5) S8)
(declare-fun f16 () S9)
(declare-fun f17 () S6)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (or (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f7 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f3 (f4 f8 ?v0) ?v1) f1) (or (= (f3 (f4 f9 ?v0) ?v1) f1) (= (f3 (f4 f10 ?v0) ?v1) f1)))))
(assert (not (= (f11 f12 (f13 (f14 (f15 f8 f16 f5)) f17)) f1)))
(assert (= (f11 f12 (f13 (f14 (f15 f9 f16 f6)) f17)) f1))
(assert (= (f11 f12 (f13 (f14 (f15 f10 f16 f7)) f17)) f1))
(assert (forall ((?v0 S6) (?v1 S5) (?v2 S9) (?v3 S5) (?v4 S5) (?v5 S5)) (=> (= (f11 ?v0 (f13 (f14 (f15 ?v1 ?v2 ?v3)) f17)) f1) (=> (forall ((?v6 S2) (?v7 S3)) (=> (= (f3 (f4 ?v4 ?v6) ?v7) f1) (forall ((?v8 S3)) (=> (forall ((?v9 S2)) (=> (= (f3 (f4 ?v1 ?v9) ?v7) f1) (= (f3 (f4 ?v3 ?v9) ?v8) f1))) (= (f3 (f4 ?v5 ?v6) ?v8) f1))))) (= (f11 ?v0 (f13 (f14 (f15 ?v4 ?v2 ?v5)) f17)) f1)))))
(check-sat)
(exit)