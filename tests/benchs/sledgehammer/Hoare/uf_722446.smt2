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
(declare-sort S14 0)
(declare-sort S15 0)
(declare-sort S16 0)
(declare-sort S17 0)
(declare-sort S18 0)
(declare-sort S19 0)
(declare-sort S20 0)
(declare-sort S21 0)
(declare-sort S22 0)
(declare-sort S23 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S1) S1)
(declare-fun f4 () S2)
(declare-fun f5 (S4 S3) S1)
(declare-fun f6 () S4)
(declare-fun f7 (S6 S4) S1)
(declare-fun f8 (S7 S3) S6)
(declare-fun f9 () S7)
(declare-fun f10 () S4)
(declare-fun f11 (S8 S5) S4)
(declare-fun f12 () S8)
(declare-fun f13 (S9 S4) S4)
(declare-fun f14 (S10 S3) S9)
(declare-fun f15 () S10)
(declare-fun f16 (S11 S12) S3)
(declare-fun f17 (S13 S14) S11)
(declare-fun f18 (S15 S12) S13)
(declare-fun f19 () S15)
(declare-fun f20 () S12)
(declare-fun f21 (S16 S14) S14)
(declare-fun f22 (S17 S18) S16)
(declare-fun f23 () S17)
(declare-fun f24 () S18)
(declare-fun f25 () S14)
(declare-fun f26 (S19 S18) S12)
(declare-fun f27 (S20 S12) S19)
(declare-fun f28 () S20)
(declare-fun f29 (S21 S18) S18)
(declare-fun f30 (S22 S2) S21)
(declare-fun f31 () S22)
(declare-fun f32 () S4)
(declare-fun f33 (S23 S4) S6)
(declare-fun f34 () S23)
(declare-fun f35 () S23)
(declare-fun f36 () S9)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S1)) (= (= (f3 f4 ?v0) f1) (not (= ?v0 f1)))))
(assert (forall ((?v0 S3)) (= (= (f5 f6 ?v0) f1) false)))
(assert (not (forall ((?v0 S5)) (=> (forall ((?v1 S3)) (=> (= (f7 (f8 f9 ?v1) f10) f1) (= (f5 (f11 f12 ?v0) ?v1) f1))) (forall ((?v1 S3)) (=> (= (f7 (f8 f9 ?v1) (f13 (f14 f15 (f16 (f17 (f18 f19 f20) (f21 (f22 f23 f24) f25)) (f26 (f27 f28 f20) (f29 (f30 f31 f4) f24)))) f32)) f1) (= (f5 (f11 f12 ?v0) ?v1) f1)))))))
(assert (forall ((?v0 S5)) (=> (forall ((?v1 S3)) (=> (= (f7 (f8 f9 ?v1) f10) f1) (= (f5 (f11 f12 ?v0) ?v1) f1))) (forall ((?v1 S3)) (=> (= (f7 (f8 f9 ?v1) (f13 (f14 f15 (f16 (f17 (f18 f19 (f26 (f27 f28 f20) f24)) f25) f20)) f32)) f1) (= (f5 (f11 f12 ?v0) ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S14) (?v2 S12) (?v3 S12) (?v4 S14) (?v5 S12)) (= (= (f16 (f17 (f18 f19 ?v0) ?v1) ?v2) (f16 (f17 (f18 f19 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f7 (f33 f34 ?v0) ?v1) f1) (forall ((?v2 S5)) (=> (forall ((?v3 S3)) (=> (= (f7 (f8 f9 ?v3) ?v0) f1) (= (f5 (f11 f12 ?v2) ?v3) f1))) (forall ((?v3 S3)) (=> (= (f7 (f8 f9 ?v3) ?v1) f1) (= (f5 (f11 f12 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S4) (?v1 S12) (?v2 S18) (?v3 S14)) (let ((?v_0 (f33 f35 ?v0)) (?v_1 (f27 f28 ?v1))) (=> (= (f7 ?v_0 (f13 (f14 f15 (f16 (f17 (f18 f19 (f26 ?v_1 ?v2)) ?v3) ?v1)) f32)) f1) (= (f7 ?v_0 (f13 (f14 f15 (f16 (f17 (f18 f19 ?v1) (f21 (f22 f23 ?v2) ?v3)) (f26 ?v_1 (f29 (f30 f31 f4) ?v2)))) f32)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S4)) (let ((?v_0 (f8 f9 ?v0))) (=> (= (f7 ?v_0 (f13 (f14 f15 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f7 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (=> (=> (not (= (f7 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f7 ?v_0 (f13 (f14 f15 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3)) (=> (= (f7 (f8 f9 ?v0) f32) f1) false)))
(assert (forall ((?v0 S3) (?v1 S4)) (not (= f32 (f13 (f14 f15 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S4)) (not (= (f13 (f14 f15 ?v0) ?v1) f32))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f7 (f8 f9 ?v0) (f13 (f14 f15 ?v1) f32)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (= (f13 (f14 f15 ?v0) (f13 (f14 f15 ?v1) f32)) (f13 (f14 f15 ?v2) (f13 (f14 f15 ?v3) f32))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f8 f9 ?v0) (f13 (f14 f15 ?v1) f32)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f33 f35 ?v2))) (=> (= (f7 (f33 f35 ?v0) ?v1) f1) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S4)) (= (f7 (f33 f35 ?v0) f32) f1)))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S4)) (let ((?v_0 (f33 f35 ?v0)) (?v_1 (f14 f15 ?v1))) (=> (= (f7 ?v_0 (f13 ?v_1 ?v2)) f1) (and (= (f7 ?v_0 (f13 ?v_1 f32)) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S4)) (let ((?v_0 (f33 f35 ?v0)) (?v_1 (f14 f15 ?v1))) (=> (= (f7 ?v_0 (f13 ?v_1 f32)) f1) (=> (= (f7 ?v_0 ?v2) f1) (= (f7 ?v_0 (f13 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S4) (?v1 S3)) (=> (= ?v0 f32) (not (= (f7 (f8 f9 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S4)) (= (= (f13 f36 ?v0) f32) (forall ((?v1 S3)) (not (= (f5 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (= (f7 (f8 f9 ?v0) f32) f1) false)))
(assert (forall ((?v0 S4)) (= (= f32 (f13 f36 ?v0)) (forall ((?v1 S3)) (not (= (f5 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S4)) (= (forall ((?v1 S3)) (=> (= (f7 (f8 f9 ?v1) f32) f1) (= (f5 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S4)) (= (exists ((?v1 S3)) (and (= (f7 (f8 f9 ?v1) f32) f1) (= (f5 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S4)) (= (exists ((?v1 S3)) (= (f7 (f8 f9 ?v1) ?v0) f1)) (not (= ?v0 f32)))))
(assert (forall ((?v0 S4)) (= (forall ((?v1 S3)) (not (= (f7 (f8 f9 ?v1) ?v0) f1))) (= ?v0 f32))))
(assert (= f32 (f13 f36 f6)))
(assert (forall ((?v0 S3) (?v1 S4)) (=> (= (f7 (f8 f9 ?v0) ?v1) f1) (= (f13 (f14 f15 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (= (f7 ?v_0 (f13 (f14 f15 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S4)) (let ((?v_0 (f8 f9 ?v0)) (?v_1 (f14 f15 ?v0))) (=> (not (= (f7 ?v_0 ?v1) f1)) (=> (not (= (f7 ?v_0 ?v2) f1)) (= (= (f13 ?v_1 ?v1) (f13 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S3)) (= (= (f5 (f13 (f14 f15 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f5 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S4)) (let ((?v_0 (f8 f9 ?v0))) (= (= (f7 ?v_0 (f13 (f14 f15 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S4)) (let ((?v_1 (f14 f15 ?v0)) (?v_0 (f14 f15 ?v1))) (= (f13 ?v_1 (f13 ?v_0 ?v2)) (f13 ?v_0 (f13 ?v_1 ?v2))))))
(check-sat)
(exit)
