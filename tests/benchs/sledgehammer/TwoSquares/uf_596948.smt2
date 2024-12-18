(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status sat)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-sort S3 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 () S2)
(declare-fun f5 () S2)
(declare-fun f6 (S3 S2) S2)
(declare-fun f7 () S3)
(declare-fun f8 () S3)
(declare-fun f9 (S2) S1)
(declare-fun f10 () S2)
(declare-fun f11 () S3)
(assert (not (= f1 f2)))
(assert (not (= (f3 f4 f5) f1)))
(assert (forall ((?v0 S2)) (= (f3 ?v0 ?v0) f1)))
(assert (forall ((?v0 S2)) (= (f3 ?v0 ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 ?v0 ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v1 ?v2) f1) (= (f3 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2)) (= (= f4 ?v0) (= ?v0 f4))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 ?v0 ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 ?v1) (and (= (f3 ?v0 ?v1) f1) (= (f3 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= ?v0 ?v1) (= (f3 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 ?v1) f1) (= (= (f3 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f3 ?v0 ?v1) f1) false) (=> (=> (= (f3 ?v1 ?v0) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v2 ?v0) f1) (= (f3 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v1 ?v2) f1) (= (f3 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f3 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f3 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f3 ?v2 ?v1) f1) (= (f3 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f3 ?v1 ?v2) f1) (= (f3 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2)) (=> (= ?v0 (f6 ?v1 ?v2)) (=> (= (f3 ?v3 ?v2) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 ?v5 ?v4) f1) (= (f3 (f6 ?v1 ?v5) (f6 ?v1 ?v4)) f1))) (= (f3 (f6 ?v1 ?v3) ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f6 ?v2 ?v0) ?v3) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 ?v5 ?v4) f1) (= (f3 (f6 ?v2 ?v5) (f6 ?v2 ?v4)) f1))) (= (f3 ?v3 (f6 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f6 f7 ?v0) (f6 f7 ?v1)) f1) (= (f3 ?v0 ?v1) f1))))
(assert (= (f6 f8 f4) f4))
(assert (not (= (f9 f4) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f6 f7 ?v0) (f6 f7 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f6 f8 ?v0) (f6 f8 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f6 f7 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f6 f7 ?v0))) (= (f6 f8 ?v_0) ?v_0))))
(assert (forall ((?v0 S2)) (= (f6 f7 ?v0) (f6 f8 ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f6 f7 ?v0) (f6 f7 ?v1)) f1) (= (f3 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f6 f8 ?v0) (f6 f8 ?v1)) f1) (= (f3 ?v0 ?v1) f1))))
(assert (= (f9 (f6 f7 f10)) f1))
(assert (forall ((?v0 S2)) (not (= (f9 (f6 f7 (f6 f11 ?v0))) f1))))
(check-sat)
(exit)
