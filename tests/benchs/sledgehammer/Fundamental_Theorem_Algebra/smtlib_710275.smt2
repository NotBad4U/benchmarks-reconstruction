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
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S4 S2) S3)
(declare-fun f6 () S4)
(declare-fun f7 () S2)
(declare-fun f8 (S5 S3) S3)
(declare-fun f9 (S6 S3) S5)
(declare-fun f10 () S6)
(declare-fun f11 () S3)
(declare-fun f12 () S5)
(declare-fun f13 () S2)
(declare-fun f14 (S7 S3) S1)
(declare-fun f15 (S8 S2) S7)
(declare-fun f16 () S8)
(declare-fun f17 () S4)
(declare-fun f18 () S6)
(declare-fun f19 (S9 S2) S2)
(declare-fun f20 () S9)
(declare-fun f21 (S10 S2) S9)
(declare-fun f22 () S10)
(declare-fun f23 () S2)
(declare-fun f24 (S11 S3) S7)
(declare-fun f25 () S11)
(declare-fun f26 (S12 S1) S1)
(declare-fun f27 (S13 S1) S12)
(declare-fun f28 () S13)
(declare-fun f29 () S1)
(declare-fun f30 () S10)
(assert (not (= f1 f2)))
(assert (not (forall ((?v0 S2)) (=> (= (f3 f4 ?v0) f1) (= (f3 (f5 f6 ?v0) f7) f1)))))
(assert (= (f3 (f8 (f9 f10 f11) (f8 f12 f4)) f7) f1))
(assert (exists ((?v0 S2)) (= (f3 f4 ?v0) f1)))
(assert (= (f3 f4 f13) f1))
(assert (= (f3 (f8 (f9 f10 f11) (f8 f12 f4)) f7) f1))
(assert (exists ((?v0 S2)) (= (f14 (f15 f16 ?v0) (f8 f12 f4)) f1)))
(assert (exists ((?v0 S2)) (forall ((?v1 S2)) (=> (= (f3 f4 ?v1) f1) (= (f3 (f5 f17 ?v1) ?v0) f1)))))
(assert (exists ((?v0 S2)) (= (f3 (f8 (f9 f10 f11) (f8 f12 f4)) ?v0) f1)))
(assert (=> (forall ((?v0 S2)) (=> (= (f3 (f8 (f9 f10 f11) (f8 f12 f4)) ?v0) f1) false)) false))
(assert (forall ((?v0 S2)) (= (f3 (f5 f6 ?v0) ?v0) f1)))
(assert (exists ((?v0 S2)) (= (f3 (f8 (f9 f18 f11) (f8 f12 f4)) ?v0) f1)))
(assert (forall ((?v0 S2)) (= (f3 (f5 f6 ?v0) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f5 f6 ?v0) ?v1) f1) (= (f3 (f5 f6 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f5 f6 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f5 f6 ?v0) ?v1) f1) (=> (= (f3 (f5 f6 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2)) (= (f3 (f5 f6 ?v0) (f19 f20 ?v0)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f3 (f5 f6 ?v0) (f19 (f21 f22 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f3 (f5 f6 ?v0) (f19 (f21 f22 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S2)) (=> (= (f3 f4 ?v0) f1) (= (f3 (f5 f17 ?v0) f23) f1))))
(assert (= (f3 (f5 f17 f13) f23) f1))
(assert (=> (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f4 ?v0) f1) (=> (forall ((?v2 S2)) (=> (= (f3 f4 ?v2) f1) (= (f3 (f5 f17 ?v2) ?v1) f1))) false))) false))
(assert (forall ((?v0 S3)) (not (= (f14 (f24 f25 f11) ?v0) f1))))
(assert (forall ((?v0 S1)) (not (= (f26 (f27 f28 f29) ?v0) f1))))
(assert (forall ((?v0 S2)) (not (= (f3 (f5 f17 ?v0) ?v0) f1))))
(assert (forall ((?v0 S1)) (not (= (f26 (f27 f28 ?v0) ?v0) f1))))
(assert (forall ((?v0 S3)) (not (= (f14 (f24 f25 ?v0) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f11 ?v0) f1) (= f29 f1))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f11)) (= (f14 (f24 f25 ?v0) f11) f1))))
(assert (forall ((?v0 S1)) (= (not (= (= ?v0 f1) (= f29 f1))) (= (f26 (f27 f28 ?v0) f29) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= ?v0 ?v1)) (or (= (f3 (f5 f17 ?v0) ?v1) f1) (= (f3 (f5 f17 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f5 f17 ?v0) ?v1) f1)) (or (= (f3 (f5 f17 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f5 f17 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f5 f17 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f17 ?v0))) (= (= (f3 ?v_0 (f19 (f21 f22 ?v1) ?v2)) f1) (or (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f17 ?v0))) (= (= (f3 ?v_0 (f19 (f21 f30 ?v1) ?v2)) f1) (and (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f3 (f5 f17 (f19 (f21 f22 ?v0) ?v1)) ?v2) f1) (and (= (f3 (f5 f17 ?v0) ?v2) f1) (= (f3 (f5 f17 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f3 (f5 f17 (f19 (f21 f30 ?v0) ?v1)) ?v2) f1) (or (= (f3 (f5 f17 ?v0) ?v2) f1) (= (f3 (f5 f17 ?v1) ?v2) f1)))))
(check-sat)
(exit)
