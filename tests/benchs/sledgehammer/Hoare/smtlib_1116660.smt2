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
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S6 S5) S4)
(declare-fun f6 () S5)
(declare-fun f7 (S7 S8) S6)
(declare-fun f8 () S7)
(declare-fun f9 (S2) S8)
(declare-fun f10 (S6) S5)
(declare-fun f11 () S3)
(declare-fun f12 (S9 S2) S6)
(declare-fun f13 () S9)
(declare-fun f14 (S11 S10) S1)
(declare-fun f15 (S5 S10) S11)
(declare-fun f16 (S12 S12) S1)
(declare-fun f17 (S13 S12) S12)
(declare-fun f18 (S4) S13)
(declare-fun f19 () S12)
(declare-fun f20 (S12) S13)
(declare-fun f21 () S12)
(declare-fun f22 (S14 S15) S12)
(declare-fun f23 (S3) S14)
(declare-fun f24 () S15)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f7 f8 (f9 ?v0)))) (= (f3 f4 ?v0) (f5 f6 ?v_0 (f10 ?v_0))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (f3 f11 ?v0) (f5 f6 ?v_0 (f10 ?v_0))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f14 (f15 f6 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S5) (?v2 S6) (?v3 S5) (?v4 S5)) (=> (= (f16 ?v0 (f17 (f18 (f5 ?v1 ?v2 ?v3)) f19)) f1) (=> (forall ((?v5 S10) (?v6 S10)) (=> (= (f14 (f15 ?v3 ?v5) ?v6) f1) (= (f14 (f15 ?v4 ?v5) ?v6) f1))) (= (f16 ?v0 (f17 (f18 (f5 ?v1 ?v2 ?v4)) f19)) f1)))))
(assert (forall ((?v0 S2) (?v1 S10) (?v2 S10)) (=> (= (f14 (f15 (f10 (f7 f8 (f9 ?v0))) ?v1) ?v2) f1) (= (f14 (f15 (f10 (f12 f13 ?v0)) ?v1) ?v2) f1))))
(assert (not (forall ((?v0 S2)) (let ((?v_0 (f17 (f20 f21) (f22 (f23 f11) f24))) (?v_1 (f7 f8 (f9 ?v0)))) (=> (= (f16 ?v_0 (f22 (f23 f4) f24)) f1) (=> (= (f16 ?v_0 (f17 (f18 (f5 f6 ?v_1 (f10 ?v_1))) f19)) f1) (= (f16 ?v_0 (f17 (f18 (f5 f6 ?v_1 (f10 (f12 f13 ?v0)))) f19)) f1)))))))
(check-sat)
(exit)