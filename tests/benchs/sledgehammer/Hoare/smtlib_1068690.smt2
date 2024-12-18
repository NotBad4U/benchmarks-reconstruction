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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S3 S3) S1)
(declare-fun f6 () S3)
(declare-fun f7 (S4 S3) S3)
(declare-fun f8 (S2) S4)
(declare-fun f9 (S5 S6) S2)
(declare-fun f10 () S5)
(declare-fun f11 () S6)
(declare-fun f12 () S3)
(declare-fun f13 () S1)
(declare-fun f14 () S1)
(declare-fun f15 (S7) S1)
(declare-fun f16 () S7)
(declare-fun f17 (S8 S7) S2)
(declare-fun f18 () S8)
(declare-fun f19 (S9) S7)
(declare-fun f20 (S6) S9)
(declare-fun f21 (S2 S3) S1)
(declare-fun f22 (S6) S7)
(declare-fun f23 (S3) S3)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) false)))
(assert (not (= (f5 f6 (f7 (f8 (f9 f10 f11)) f12)) f1)))
(assert (= f13 f1))
(assert (= f14 f1))
(assert (= (f15 f16) f1))
(assert (= (f5 (f7 (f8 (f9 f10 f11)) f6) (f7 (f8 (f17 f18 (f19 (f20 f11)))) f12)) f1))
(assert (forall ((?v0 S3)) (= (f5 ?v0 f12) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f5 ?v0 ?v1) f1) (=> (= (f5 ?v2 ?v0) f1) (= (f5 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f8 ?v1))) (=> (= (f5 ?v0 (f7 ?v_0 f12)) f1) (=> (= (f5 ?v0 ?v2) f1) (= (f5 ?v0 (f7 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f8 ?v1))) (=> (= (f5 ?v0 (f7 ?v_0 ?v2)) f1) (and (= (f5 ?v0 (f7 ?v_0 f12)) f1) (= (f5 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f21 ?v0 (f7 (f8 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f21 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (=> (not (= (f21 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f21 ?v0 (f7 (f8 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S6) (?v1 S3)) (let ((?v_0 (f8 (f17 f18 (f22 ?v0))))) (=> (= (f5 (f7 ?v_0 ?v1) (f7 (f8 (f17 f18 (f19 (f20 ?v0)))) f12)) f1) (= (f5 ?v1 (f7 ?v_0 f12)) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f21 ?v0 f12) f1) false)))
(assert (= (= f13 f1) (exists ((?v0 S10) (?v1 S10)) (not (= ?v0 ?v1)))))
(assert (=> (= f13 f1) (forall ((?v0 S10)) (=> (forall ((?v1 S10)) (= ?v1 ?v0)) false))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f12 (f7 (f8 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f7 (f8 ?v0) ?v1) f12))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f21 ?v0 (f7 (f8 ?v1) f12)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f7 (f8 ?v0) (f7 (f8 ?v1) f12)) (f7 (f8 ?v2) (f7 (f8 ?v3) f12))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f21 ?v0 (f7 (f8 ?v1) f12)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f7 (f8 ?v0) f12) (f7 (f8 ?v1) f12)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f12) (not (= (f21 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f23 ?v0) f12) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f21 ?v0 f12) f1) false)))
(assert (forall ((?v0 S3)) (= (= f12 (f23 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f21 ?v1 f12) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f21 ?v1 f12) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f21 ?v1 ?v0) f1)) (not (= ?v0 f12)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f21 ?v1 ?v0) f1))) (= ?v0 f12))))
(assert (= f12 (f23 f4)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f21 ?v0 ?v1) f1) (= (f7 (f8 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (= (f21 ?v0 ?v1) f1) (= (f21 ?v0 (f7 (f8 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 ?v0))) (=> (not (= (f21 ?v0 ?v1) f1)) (=> (not (= (f21 ?v0 ?v2) f1)) (= (= (f7 ?v_0 ?v1) (f7 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f7 (f8 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (= (f21 ?v0 (f7 (f8 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f21 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f8 ?v0)) (?v_0 (f8 ?v1))) (= (f7 ?v_1 (f7 ?v_0 ?v2)) (f7 ?v_0 (f7 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f8 ?v0))) (let ((?v_1 (f7 ?v_0 ?v1))) (= (f7 ?v_0 ?v_1) ?v_1)))))
(check-sat)
(exit)
