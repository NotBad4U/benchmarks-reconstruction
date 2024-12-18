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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S2) S3)
(declare-fun f5 (S5 S4) S1)
(declare-fun f6 (S4) S5)
(declare-fun f7 (S2) S3)
(declare-fun f8 (S4) S5)
(declare-fun f9 (S6 S3) S3)
(declare-fun f10 (S2) S6)
(declare-fun f11 (S7 S5) S5)
(declare-fun f12 (S4) S7)
(declare-fun f13 (S2) S6)
(declare-fun f14 (S4) S7)
(declare-fun f15 () S3)
(declare-fun f16 () S5)
(declare-fun f17 (S8) S1)
(declare-fun f18 () S8)
(declare-fun f19 (S3 S3) S1)
(declare-fun f20 () S3)
(declare-fun f21 (S2) S6)
(declare-fun f22 (S9 S8) S2)
(declare-fun f23 () S9)
(declare-fun f24 () S3)
(declare-fun f25 () S1)
(declare-fun f26 (S4 S5) S1)
(declare-fun f27 (S10) S5)
(declare-fun f28 () S10)
(declare-fun f29 (S4) S8)
(declare-fun f30 (S2 S3) S1)
(declare-fun f31 (S4) S7)
(declare-fun f32 () S5)
(declare-fun f33 (S3) S3)
(declare-fun f34 (S5) S5)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f5 (f6 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f7 ?v0) ?v1) f1) (= ?v1 ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f5 (f8 ?v0) ?v1) f1) (= ?v1 ?v0))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f9 (f10 ?v0) ?v1) ?v2) f1) (and (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S5) (?v2 S4)) (= (= (f5 (f11 (f12 ?v0) ?v1) ?v2) f1) (and (= ?v0 ?v2) (= (f5 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f9 (f13 ?v0) ?v1) ?v2) f1) (and (= ?v2 ?v0) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S5) (?v2 S4)) (= (= (f5 (f11 (f14 ?v0) ?v1) ?v2) f1) (and (= ?v2 ?v0) (= (f5 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f15 ?v0) f1) false)))
(assert (forall ((?v0 S4)) (= (= (f5 f16 ?v0) f1) false)))
(assert (not (=> (= (f17 f18) f1) (= (f19 f20 (f9 (f21 (f22 f23 f18)) f24)) f1))))
(assert (= f25 f1))
(assert (forall ((?v0 S4)) (=> (= (f26 ?v0 (f27 f28)) f1) (= (f19 f20 (f9 (f21 (f22 f23 (f29 ?v0))) f24)) f1))))
(assert (forall ((?v0 S3)) (= (f19 ?v0 f24) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f19 ?v0 ?v1) f1) (=> (= (f19 ?v2 ?v0) f1) (= (f19 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f21 ?v1))) (=> (= (f19 ?v0 (f9 ?v_0 f24)) f1) (=> (= (f19 ?v0 ?v2) f1) (= (f19 ?v0 (f9 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f21 ?v1))) (=> (= (f19 ?v0 (f9 ?v_0 ?v2)) f1) (and (= (f19 ?v0 (f9 ?v_0 f24)) f1) (= (f19 ?v0 ?v2) f1))))))
(assert (=> (= (f17 f18) f1) (=> false false)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f30 ?v0 (f9 (f21 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f30 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S5)) (=> (= (f26 ?v0 (f11 (f31 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f26 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (=> (not (= (f30 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f30 ?v0 (f9 (f21 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S5) (?v2 S4)) (=> (=> (not (= (f26 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f26 ?v0 (f11 (f31 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4)) (=> (= (f26 ?v0 f32) f1) false)))
(assert (forall ((?v0 S2)) (=> (= (f30 ?v0 f24) f1) false)))
(assert (= (f17 f18) f1))
(assert (forall ((?v0 S2)) (= (f33 (f4 ?v0)) (f9 (f21 ?v0) f24))))
(assert (forall ((?v0 S4)) (= (f34 (f6 ?v0)) (f11 (f31 ?v0) f32))))
(assert (forall ((?v0 S2)) (= (f33 (f7 ?v0)) (f9 (f21 ?v0) f24))))
(assert (forall ((?v0 S4)) (= (f34 (f8 ?v0)) (f11 (f31 ?v0) f32))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f33 (f9 (f10 ?v0) ?v1)) (ite (= (f3 ?v1 ?v0) f1) (f9 (f21 ?v0) f24) f24))))
(assert (forall ((?v0 S4) (?v1 S5)) (= (f34 (f11 (f12 ?v0) ?v1)) (ite (= (f5 ?v1 ?v0) f1) (f11 (f31 ?v0) f32) f32))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f33 (f9 (f13 ?v0) ?v1)) (ite (= (f3 ?v1 ?v0) f1) (f9 (f21 ?v0) f24) f24))))
(assert (forall ((?v0 S4) (?v1 S5)) (= (f34 (f11 (f14 ?v0) ?v1)) (ite (= (f5 ?v1 ?v0) f1) (f11 (f31 ?v0) f32) f32))))
(assert (forall ((?v0 S4)) (not (= f18 (f29 ?v0)))))
(assert (forall ((?v0 S4)) (not (= (f29 ?v0) f18))))
(assert (= (= f25 f1) (exists ((?v0 S11) (?v1 S11)) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S4)) (=> (= ?v0 f32) (not (= (f26 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f24) (not (= (f30 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f33 ?v0) f24) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S5)) (= (= (f34 ?v0) f32) (forall ((?v1 S4)) (not (= (f5 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S4)) (= (= (f26 ?v0 f32) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f30 ?v0 f24) f1) false)))
(assert (forall ((?v0 S3)) (= (= f24 (f33 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S5)) (= (= f32 (f34 ?v0)) (forall ((?v1 S4)) (not (= (f5 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S5)) (= (forall ((?v1 S4)) (=> (= (f26 ?v1 f32) f1) (= (f5 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f30 ?v1 f24) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S5)) (= (exists ((?v1 S4)) (and (= (f26 ?v1 f32) f1) (= (f5 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f30 ?v1 f24) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S5)) (= (exists ((?v1 S4)) (= (f26 ?v1 ?v0) f1)) (not (= ?v0 f32)))))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f30 ?v1 ?v0) f1)) (not (= ?v0 f24)))))
(assert (forall ((?v0 S5)) (= (forall ((?v1 S4)) (not (= (f26 ?v1 ?v0) f1))) (= ?v0 f32))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f30 ?v1 ?v0) f1))) (= ?v0 f24))))
(assert (= f24 (f33 f15)))
(assert (= f32 (f34 f16)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f30 ?v0 ?v1) f1) (= (f9 (f21 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S4) (?v1 S5)) (=> (= (f26 ?v0 ?v1) f1) (= (f11 (f31 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (= (f30 ?v0 ?v1) f1) (= (f30 ?v0 (f9 (f21 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S5) (?v2 S4)) (=> (= (f26 ?v0 ?v1) f1) (= (f26 ?v0 (f11 (f31 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f21 ?v0))) (=> (not (= (f30 ?v0 ?v1) f1)) (=> (not (= (f30 ?v0 ?v2) f1)) (= (= (f9 ?v_0 ?v1) (f9 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S4) (?v1 S5) (?v2 S5)) (let ((?v_0 (f31 ?v0))) (=> (not (= (f26 ?v0 ?v1) f1)) (=> (not (= (f26 ?v0 ?v2) f1)) (= (= (f11 ?v_0 ?v1) (f11 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f9 (f21 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S5) (?v2 S4)) (= (= (f5 (f11 (f31 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f5 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (= (f30 ?v0 (f9 (f21 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f30 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S5)) (= (= (f26 ?v0 (f11 (f31 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f26 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f21 ?v0)) (?v_0 (f21 ?v1))) (= (f9 ?v_1 (f9 ?v_0 ?v2)) (f9 ?v_0 (f9 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S5)) (let ((?v_1 (f31 ?v0)) (?v_0 (f31 ?v1))) (= (f11 ?v_1 (f11 ?v_0 ?v2)) (f11 ?v_0 (f11 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f21 ?v0))) (let ((?v_1 (f9 ?v_0 ?v1))) (= (f9 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S4) (?v1 S5)) (let ((?v_0 (f31 ?v0))) (let ((?v_1 (f11 ?v_0 ?v1))) (= (f11 ?v_0 ?v_1) ?v_1)))))
(check-sat)
(exit)
