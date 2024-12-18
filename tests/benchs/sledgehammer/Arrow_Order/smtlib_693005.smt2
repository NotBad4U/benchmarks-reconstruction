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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2) S1)
(declare-fun f4 () S2)
(declare-fun f5 (S3 S4) S1)
(declare-fun f6 () S4)
(declare-fun f7 (S7 S8) S1)
(declare-fun f8 (S5 S5) S7)
(declare-fun f9 (S3 S6) S8)
(declare-fun f10 (S2 S3) S8)
(declare-fun f11 () S5)
(declare-fun f12 () S5)
(declare-fun f13 () S3)
(declare-fun f14 () S3)
(assert (not (= f1 f2)))
(assert (= (f3 f4) f1))
(assert (forall ((?v0 S2)) (= (= (f3 ?v0) f1) (forall ((?v1 S3)) (=> (= (f5 ?v1 f6) f1) (forall ((?v2 S3)) (=> (= (f5 ?v2 f6) f1) (forall ((?v3 S5) (?v4 S5)) (let ((?v_0 (f8 ?v3 ?v4))) (=> (forall ((?v5 S6)) (= (= (f7 ?v_0 (f9 ?v1 ?v5)) f1) (= (f7 ?v_0 (f9 ?v2 ?v5)) f1))) (= (= (f7 ?v_0 (f10 ?v0 ?v1)) f1) (= (f7 ?v_0 (f10 ?v0 ?v2)) f1))))))))))))
(assert (let ((?v_0 (f8 f11 f12))) (not (=> (= (f7 ?v_0 (f10 f4 f13)) f1) (=> (forall ((?v0 S6)) (= (= (f7 ?v_0 (f9 f13 ?v0)) f1) (= (f7 ?v_0 (f9 f14 ?v0)) f1))) (=> (forall ((?v0 S3)) (=> (= (f5 ?v0 f6) f1) (forall ((?v1 S3)) (=> (= (f5 ?v1 f6) f1) (forall ((?v2 S5) (?v3 S5)) (let ((?v_1 (f8 ?v2 ?v3))) (=> (forall ((?v4 S6)) (= (= (f7 ?v_1 (f9 ?v0 ?v4)) f1) (= (f7 ?v_1 (f9 ?v1 ?v4)) f1))) (= (= (f7 ?v_1 (f10 f4 ?v0)) f1) (= (f7 ?v_1 (f10 f4 ?v1)) f1))))))))) (=> (= (f5 f14 f6) f1) (=> (= (f5 f13 f6) f1) (= (f7 ?v_0 (f10 f4 f14)) f1)))))))))
(check-sat)
(exit)
