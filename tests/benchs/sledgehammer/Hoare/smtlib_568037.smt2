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
(declare-sort S15 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S2) S1)
(declare-fun f4 (S5 S3) S4)
(declare-fun f5 (S6 S2) S5)
(declare-fun f6 () S6)
(declare-fun f7 (S9 S8) S1)
(declare-fun f8 (S2 S7) S9)
(declare-fun f9 (S3 S8 S10 S8) S1)
(declare-fun f10 () S10)
(declare-fun f11 (S11 S12) S13)
(declare-fun f12 (S2 S3 S2) S12)
(declare-fun f13 (S14 S2) S13)
(declare-fun f14 (S15 S3) S14)
(declare-fun f15 (S11 S2) S15)
(declare-fun f16 (S6 S12) S1)
(declare-fun f17 () S2)
(declare-fun f18 () S3)
(declare-fun f19 () S2)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 f6 ?v0) ?v1) ?v2) f1) (forall ((?v3 S7) (?v4 S8)) (=> (= (f7 (f8 ?v0 ?v3) ?v4) f1) (forall ((?v5 S8)) (=> (= (f9 ?v1 ?v4 f10 ?v5) f1) (= (f7 (f8 ?v2 ?v3) ?v5) f1))))))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S3) (?v3 S2)) (= (f11 ?v0 (f12 ?v1 ?v2 ?v3)) (f13 (f14 (f15 ?v0 ?v1) ?v2) ?v3))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S3) (?v3 S2)) (= (= (f16 ?v0 (f12 ?v1 ?v2 ?v3)) f1) (= (f3 (f4 (f5 ?v0 ?v1) ?v2) ?v3) f1))))
(assert (not (= (= (f16 f6 (f12 f17 f18 f19)) f1) (forall ((?v0 S7) (?v1 S8)) (=> (= (f7 (f8 f17 ?v0) ?v1) f1) (forall ((?v2 S8)) (=> (= (f9 f18 ?v1 f10 ?v2) f1) (= (f7 (f8 f19 ?v0) ?v2) f1))))))))
(check-sat)
(exit)
