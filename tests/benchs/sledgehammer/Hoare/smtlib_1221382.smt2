(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unknown)
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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S2) S1)
(declare-fun f4 (S5 S3) S4)
(declare-fun f5 (S6 S2) S5)
(declare-fun f6 () S6)
(declare-fun f7 () S5)
(declare-fun f8 () S6)
(declare-fun f9 (S7 S3) S5)
(declare-fun f10 (S8 S5) S7)
(declare-fun f11 () S8)
(declare-fun f12 (S9 S5) S5)
(declare-fun f13 (S10 S5) S9)
(declare-fun f14 () S10)
(declare-fun f15 (S11 S1) S9)
(declare-fun f16 () S11)
(declare-fun f17 () S5)
(declare-fun f18 () S5)
(declare-fun f19 (S12 S13) S1)
(declare-fun f20 (S14 S13) S12)
(declare-fun f21 () S14)
(declare-fun f22 () S13)
(declare-fun f23 (S15 S13) S13)
(declare-fun f24 (S16 S17) S15)
(declare-fun f25 () S16)
(declare-fun f26 (S18 S5) S17)
(declare-fun f27 (S19 S20) S18)
(declare-fun f28 (S21 S5) S19)
(declare-fun f29 () S21)
(declare-fun f30 () S20)
(declare-fun f31 () S5)
(declare-fun f32 () S13)
(declare-fun f33 (S22 S17) S12)
(declare-fun f34 () S22)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 f6 ?v0) ?v1) ?v2) f1) (and (= ?v0 ?v2) (= (f3 (f4 f7 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 f8 ?v0) ?v1) ?v2) f1) (= ?v2 ?v0))))
(assert (forall ((?v0 S5) (?v1 S3) (?v2 S3)) (= (f4 (f9 (f10 f11 ?v0) ?v1) ?v2) (f4 ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3) (?v3 S2)) (= (= (f3 (f4 (f12 (f13 f14 ?v0) ?v1) ?v2) ?v3) f1) (or (= (f3 (f4 ?v0 ?v2) ?v3) f1) (= (f3 (f4 ?v1 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S1) (?v1 S5) (?v2 S3) (?v3 S2)) (= (= (f3 (f4 (f12 (f15 f16 ?v0) ?v1) ?v2) ?v3) f1) (and (= (f3 (f4 ?v1 ?v2) ?v3) f1) (= ?v0 f1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (= (f3 (f4 f17 ?v0) ?v1) f1) false)))
(assert (forall ((?v0 S3) (?v1 S2)) (= (= (f3 (f4 f18 ?v0) ?v1) f1) true)))
(assert (not (= (f19 (f20 f21 f22) (f23 (f24 f25 (f26 (f27 (f28 f29 f7) f30) f31)) f32)) f1)))
(assert (forall ((?v0 S2)) (= (f19 (f20 f21 f22) (f23 (f24 f25 (f26 (f27 (f28 f29 (f5 f6 ?v0)) f30) f31)) f32)) f1)))
(assert (forall ((?v0 S13)) (= (f19 (f20 f21 ?v0) f32) f1)))
(assert (forall ((?v0 S13) (?v1 S5) (?v2 S20)) (= (f19 (f20 f21 ?v0) (f23 (f24 f25 (f26 (f27 (f28 f29 ?v1) ?v2) f18)) f32)) f1)))
(assert (forall ((?v0 S13) (?v1 S20) (?v2 S5)) (= (f19 (f20 f21 ?v0) (f23 (f24 f25 (f26 (f27 (f28 f29 f17) ?v1) ?v2)) f32)) f1)))
(assert (forall ((?v0 S17)) (let ((?v_0 (f23 (f24 f25 ?v0) f32))) (= (f19 (f20 f21 ?v_0) ?v_0) f1))))
(assert (forall ((?v0 S5) (?v1 S20) (?v2 S5) (?v3 S5) (?v4 S20) (?v5 S5)) (= (= (f26 (f27 (f28 f29 ?v0) ?v1) ?v2) (f26 (f27 (f28 f29 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f20 f21 ?v2))) (=> (= (f19 (f20 f21 ?v0) ?v1) f1) (=> (= (f19 ?v_0 ?v0) f1) (= (f19 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S17) (?v2 S13)) (let ((?v_0 (f20 f21 ?v0)) (?v_1 (f24 f25 ?v1))) (=> (= (f19 ?v_0 (f23 ?v_1 f32)) f1) (=> (= (f19 ?v_0 ?v2) f1) (= (f19 ?v_0 (f23 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S13) (?v1 S17) (?v2 S13)) (let ((?v_0 (f20 f21 ?v0)) (?v_1 (f24 f25 ?v1))) (=> (= (f19 ?v_0 (f23 ?v_1 ?v2)) f1) (and (= (f19 ?v_0 (f23 ?v_1 f32)) f1) (= (f19 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S5) (?v2 S20) (?v3 S5) (?v4 S5) (?v5 S5)) (let ((?v_0 (f20 f21 ?v0))) (=> (= (f19 ?v_0 (f23 (f24 f25 (f26 (f27 (f28 f29 ?v1) ?v2) ?v3)) f32)) f1) (=> (= (f19 ?v_0 (f23 (f24 f25 (f26 (f27 (f28 f29 ?v4) ?v2) ?v5)) f32)) f1) (= (f19 ?v_0 (f23 (f24 f25 (f26 (f27 (f28 f29 (f12 (f13 f14 ?v1) ?v4)) ?v2) (f12 (f13 f14 ?v3) ?v5))) f32)) f1))))))
(assert (forall ((?v0 S1) (?v1 S13) (?v2 S5) (?v3 S20) (?v4 S5)) (let ((?v_0 (f20 f21 ?v1))) (=> (=> (= ?v0 f1) (= (f19 ?v_0 (f23 (f24 f25 (f26 (f27 (f28 f29 ?v2) ?v3) ?v4)) f32)) f1)) (= (f19 ?v_0 (f23 (f24 f25 (f26 (f27 (f28 f29 (f12 (f15 f16 ?v0) ?v2)) ?v3) ?v4)) f32)) f1)))))
(assert (forall ((?v0 S5) (?v1 S13) (?v2 S20) (?v3 S5)) (=> (forall ((?v4 S3) (?v5 S2)) (=> (= (f3 (f4 ?v0 ?v4) ?v5) f1) (= (f19 (f20 f21 ?v1) (f23 (f24 f25 (f26 (f27 (f28 f29 (f5 f8 ?v5)) ?v2) (f9 (f10 f11 ?v3) ?v4))) f32)) f1))) (= (f19 (f20 f21 ?v1) (f23 (f24 f25 (f26 (f27 (f28 f29 ?v0) ?v2) ?v3)) f32)) f1))))
(assert (forall ((?v0 S13) (?v1 S5) (?v2 S20) (?v3 S5) (?v4 S5)) (let ((?v_0 (f20 f21 ?v0)) (?v_1 (f27 (f28 f29 ?v1) ?v2))) (=> (= (f19 ?v_0 (f23 (f24 f25 (f26 ?v_1 ?v3)) f32)) f1) (=> (forall ((?v5 S3) (?v6 S2)) (=> (= (f3 (f4 ?v3 ?v5) ?v6) f1) (= (f3 (f4 ?v4 ?v5) ?v6) f1))) (= (f19 ?v_0 (f23 (f24 f25 (f26 ?v_1 ?v4)) f32)) f1))))))
(assert (forall ((?v0 S13) (?v1 S5) (?v2 S20) (?v3 S5) (?v4 S5)) (let ((?v_0 (f20 f21 ?v0))) (=> (= (f19 ?v_0 (f23 (f24 f25 (f26 (f27 (f28 f29 ?v1) ?v2) ?v3)) f32)) f1) (=> (forall ((?v5 S3) (?v6 S2)) (=> (= (f3 (f4 ?v4 ?v5) ?v6) f1) (= (f3 (f4 ?v1 ?v5) ?v6) f1))) (= (f19 ?v_0 (f23 (f24 f25 (f26 (f27 (f28 f29 ?v4) ?v2) ?v3)) f32)) f1))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S13)) (let ((?v_0 (f33 f34 ?v0))) (=> (= (f19 ?v_0 (f23 (f24 f25 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f19 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S17) (?v1 S13) (?v2 S17)) (let ((?v_0 (f33 f34 ?v0))) (=> (=> (not (= (f19 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f19 ?v_0 (f23 (f24 f25 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S17)) (=> (= (f19 (f33 f34 ?v0) f32) f1) false)))
(check-sat)
(exit)