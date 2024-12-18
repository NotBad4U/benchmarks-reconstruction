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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S6) S3)
(declare-fun f7 () S5)
(declare-fun f8 (S3 S3) S6)
(declare-fun f9 () S3)
(declare-fun f10 () S3)
(declare-fun f11 () S3)
(declare-fun f12 () S3)
(declare-fun f13 () S4)
(declare-fun f14 () S4)
(declare-fun f15 (S3) S1)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f4 f5 f9)) (?v_1 (f4 f5 f10))) (not (= (f3 (f4 f5 (f6 f7 (f8 f9 f10))) (f6 f7 (f8 f11 f12))) (f6 f7 (f8 (f3 (f4 f13 (f3 ?v_0 f11)) (f3 ?v_1 f12)) (f3 (f4 f14 (f3 ?v_0 f12)) (f3 ?v_1 f11))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3) (?v5 S3) (?v6 S3)) (let ((?v_0 (f4 f5 ?v1))) (= (f3 (f4 f13 (f3 (f4 f5 (f3 (f4 f14 ?v0) (f3 ?v_0 ?v2))) ?v3)) (f3 (f4 f5 (f3 (f4 f14 ?v4) (f3 ?v_0 ?v5))) ?v6)) (f3 (f4 f14 (f3 (f4 f13 (f3 (f4 f5 ?v0) ?v3)) (f3 (f4 f5 ?v4) ?v6))) (f3 ?v_0 (f3 (f4 f13 (f3 (f4 f5 ?v2) ?v3)) (f3 (f4 f5 ?v5) ?v6))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f14 (f3 ?v_0 ?v1)) (f3 (f4 f5 ?v2) ?v3)) (f3 (f4 f13 (f3 ?v_0 (f3 (f4 f14 ?v1) ?v3))) (f3 (f4 f5 (f3 (f4 f14 ?v0) ?v2)) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (= (= (f3 (f4 f13 (f3 (f4 f5 ?v0) ?v1)) ?v2) (f3 (f4 f13 (f3 (f4 f5 ?v3) ?v1)) ?v4)) (= ?v2 (f3 (f4 f13 (f3 (f4 f5 (f3 (f4 f14 ?v3) ?v0)) ?v1)) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (= (= (f3 (f4 f13 (f3 (f4 f5 ?v0) ?v1)) ?v2) (f3 (f4 f13 (f3 (f4 f5 ?v3) ?v1)) ?v4)) (= (f3 (f4 f13 (f3 (f4 f5 (f3 (f4 f14 ?v0) ?v3)) ?v1)) ?v2) ?v4))))
(assert (forall ((?v0 S3)) (= (= (f15 ?v0) f1) (exists ((?v1 S3) (?v2 S3)) (= (f6 f7 (f8 ?v1 ?v2)) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f14 ?v0) ?v1) ?v2) (= ?v0 (f3 (f4 f13 ?v2) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f3 (f4 f14 ?v1) ?v2)) (f3 (f4 f14 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f5 (f3 (f4 f14 ?v0) ?v1)) ?v2) (f3 (f4 f14 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f3 (f4 f13 ?v1) ?v2)) (f3 (f4 f13 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f5 (f3 (f4 f13 ?v0) ?v1)) ?v2) (f3 (f4 f13 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f13 (f3 (f4 f14 ?v0) ?v1)) ?v1) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f13 ?v0) ?v1) (f3 (f4 f13 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f13 ?v0))) (=> (= (f3 ?v_0 ?v1) (f3 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f13 ?v0))) (=> (= (f3 ?v_0 ?v1) (f3 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f3 (f4 f13 ?v0) ?v1) (f3 (f4 f13 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f13 ?v0))) (= (= (f3 ?v_0 ?v1) (f3 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f13 ?v0))) (= (f3 (f4 f13 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f13 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f4 f14 ?v0) ?v1) (f3 (f4 f14 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f5 ?v0) ?v1) (f3 (f4 f5 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f13 ?v0))) (= (f3 (f4 f13 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f13 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f4 f13 ?v0)) (?v_0 (f4 f13 ?v1))) (= (f3 ?v_1 (f3 ?v_0 ?v2)) (f3 ?v_0 (f3 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f13 ?v0) ?v1) (f3 (f4 f13 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (f3 (f4 f13 (f3 (f4 f5 ?v0) ?v1)) (f3 (f4 f13 (f3 (f4 f5 ?v2) ?v1)) ?v3)) (f3 (f4 f13 (f3 (f4 f5 (f3 (f4 f13 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f5 (f3 (f4 f13 ?v0) ?v1)) ?v2) (f3 (f4 f13 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(check-sat)
(exit)
