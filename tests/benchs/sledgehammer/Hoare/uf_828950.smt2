(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unsat)
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
(declare-sort S14 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S4) S3)
(declare-fun f6 (S7 S5) S2)
(declare-fun f7 (S8 S6) S7)
(declare-fun f8 (S9 S5) S8)
(declare-fun f9 () S9)
(declare-fun f10 (S12 S11) S1)
(declare-fun f11 (S5 S10) S12)
(declare-fun f12 (S6 S11 S4 S11) S1)
(declare-fun f13 (S2 S3) S1)
(declare-fun f14 (S13 S3) S3)
(declare-fun f15 (S2) S13)
(declare-fun f16 (S14 S3) S2)
(declare-fun f17 () S14)
(declare-fun f18 () S3)
(declare-fun f19 (S3) S3)
(declare-fun f20 (S3 S3) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) false)))
(assert (forall ((?v0 S4) (?v1 S5) (?v2 S6) (?v3 S5)) (= (= (f3 (f5 ?v0) (f6 (f7 (f8 f9 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S10) (?v5 S11)) (=> (= (f10 (f11 ?v1 ?v4) ?v5) f1) (forall ((?v6 S11)) (=> (= (f12 ?v2 ?v5 ?v0 ?v6) f1) (= (f10 (f11 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f13 ?v0 (f14 (f15 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2)) (= (f16 f17 (f14 (f15 ?v0) f18)) ?v0)))
(assert (= f18 (f19 f4)))
(assert (not (forall ((?v0 S5) (?v1 S3) (?v2 S6) (?v3 S5) (?v4 S4)) (=> (forall ((?v5 S10) (?v6 S11)) (=> (= (f10 (f11 ?v0 ?v5) ?v6) f1) (exists ((?v7 S5) (?v8 S5)) (and (and (= (f20 ?v1 (f14 (f15 (f6 (f7 (f8 f9 ?v7) ?v2) ?v8)) f18)) f1) (forall ((?v9 S4)) (=> (forall ((?v10 S2)) (=> (= (f13 ?v10 ?v1) f1) (= (f3 (f5 ?v9) ?v10) f1))) (forall ((?v10 S2)) (=> (= (f13 ?v10 (f14 (f15 (f6 (f7 (f8 f9 ?v7) ?v2) ?v8)) f18)) f1) (= (f3 (f5 ?v9) ?v10) f1)))))) (forall ((?v9 S11)) (=> (forall ((?v10 S10)) (=> (= (f10 (f11 ?v7 ?v10) ?v6) f1) (= (f10 (f11 ?v8 ?v10) ?v9) f1))) (= (f10 (f11 ?v3 ?v5) ?v9) f1))))))) (=> (forall ((?v5 S2)) (=> (= (f13 ?v5 ?v1) f1) (= (f3 (f5 ?v4) ?v5) f1))) (= (f3 (f5 ?v4) (f6 (f7 (f8 f9 ?v0) ?v2) ?v3)) f1))))))
(check-sat)
(exit)