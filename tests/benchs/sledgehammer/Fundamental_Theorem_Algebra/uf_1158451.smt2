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
(declare-fun f3 () S1)
(declare-fun f4 () S2)
(declare-fun f5 () S3)
(declare-fun f6 (S5 S3) S3)
(declare-fun f7 (S6 S3) S5)
(declare-fun f8 () S6)
(declare-fun f9 (S7 S4) S3)
(declare-fun f10 () S7)
(declare-fun f11 () S3)
(declare-fun f12 (S8 S4) S4)
(declare-fun f13 (S9 S2) S8)
(declare-fun f14 () S9)
(declare-fun f15 (S10 S2) S2)
(declare-fun f16 () S10)
(declare-fun f17 (S11 S4) S10)
(declare-fun f18 () S11)
(declare-fun f19 () S4)
(declare-fun f20 (S12 S2) S10)
(declare-fun f21 () S12)
(declare-fun f22 () S12)
(declare-fun f23 (S13 S3) S2)
(declare-fun f24 (S14 S2) S13)
(declare-fun f25 () S14)
(declare-fun f26 () S9)
(assert (not (= f1 f2)))
(assert (not (= f3 f1)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S4)) (=> (not (= ?v0 f4)) (=> (not (= ?v1 f5)) (=> (= (f6 (f7 f8 (f6 (f7 f8 (f9 f10 ?v2)) ?v1)) f11) (f9 f10 (f12 (f13 f14 (f15 f16 (f15 (f17 f18 f19) f4))) f19))) (=> (forall ((?v3 S2)) (let ((?v_0 (f17 f18 (f12 (f13 f14 (f15 f16 (f15 (f17 f18 f19) f4))) f19)))) (= (f15 ?v_0 ?v3) (f15 (f20 f21 (f15 ?v_0 f4)) (f15 (f20 f22 (f23 (f24 f25 ?v3) ?v1)) (f15 (f17 f18 (f12 (f13 f26 ?v0) ?v2)) ?v3)))))) (= f3 f1)))))))
(assert (exists ((?v0 S3) (?v1 S2) (?v2 S4)) (and (not (= ?v1 f4)) (and (not (= ?v0 f5)) (and (= (f6 (f7 f8 (f6 (f7 f8 (f9 f10 ?v2)) ?v0)) f11) (f9 f10 (f12 (f13 f14 (f15 f16 (f15 (f17 f18 f19) f4))) f19))) (forall ((?v3 S2)) (let ((?v_0 (f17 f18 (f12 (f13 f14 (f15 f16 (f15 (f17 f18 f19) f4))) f19)))) (= (f15 ?v_0 ?v3) (f15 (f20 f21 (f15 ?v_0 f4)) (f15 (f20 f22 (f23 (f24 f25 ?v3) ?v0)) (f15 (f17 f18 (f12 (f13 f26 ?v1) ?v2)) ?v3)))))))))))
(check-sat)
(exit)
