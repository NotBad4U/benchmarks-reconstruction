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
(declare-sort S23 0)
(declare-sort S24 0)
(declare-sort S25 0)
(declare-sort S26 0)
(declare-sort S27 0)
(declare-sort S28 0)
(declare-sort S29 0)
(declare-sort S30 0)
(declare-sort S31 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S4 S5) S2)
(declare-fun f5 (S6 S7) S4)
(declare-fun f6 (S8 S7) S6)
(declare-fun f7 () S8)
(declare-fun f8 () S7)
(declare-fun f9 () S7)
(declare-fun f10 (S9 S5) S5)
(declare-fun f11 (S10 S11) S9)
(declare-fun f12 () S10)
(declare-fun f13 () S11)
(declare-fun f14 (S12 S11) S5)
(declare-fun f15 () S12)
(declare-fun f16 () S11)
(declare-fun f17 () S3)
(declare-fun f18 (S13 S14) S1)
(declare-fun f19 (S15 S16) S13)
(declare-fun f20 () S15)
(declare-fun f21 (S7 S7 S5) S16)
(declare-fun f22 (S17 S3) S14)
(declare-fun f23 () S17)
(declare-fun f24 (S18 S19) S1)
(declare-fun f25 (S20 S5) S18)
(declare-fun f26 () S20)
(declare-fun f27 () S12)
(declare-fun f28 (S21 S19) S19)
(declare-fun f29 () S21)
(declare-fun f30 (S22 S3) S19)
(declare-fun f31 (S23 S7) S22)
(declare-fun f32 () S23)
(declare-fun f33 () S7)
(declare-fun f34 (S24 S25) S1)
(declare-fun f35 (S26 S7) S24)
(declare-fun f36 () S26)
(declare-fun f37 () S25)
(declare-fun f38 (S27 S2) S1)
(declare-fun f39 (S28 S3) S27)
(declare-fun f40 () S28)
(declare-fun f41 () S2)
(declare-fun f42 (S29 S7) S11)
(declare-fun f43 () S29)
(declare-fun f44 (S7 S5) S16)
(declare-fun f45 (S7 S5) S16)
(declare-fun f46 (S19 S5) S1)
(declare-fun f47 () S21)
(declare-fun f48 (S30 S3) S3)
(declare-fun f49 (S31 S16) S30)
(declare-fun f50 () S31)
(declare-fun f51 () S21)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 (f5 (f6 f7 f8) f9) (f10 (f11 f12 f13) (f14 f15 f16))) f17) f1)))
(assert (= (f18 (f19 f20 (f21 f8 f9 (f10 (f11 f12 f13) (f14 f15 f16)))) (f22 f23 f17)) f1))
(assert (not (= (f24 (f25 f26 (f14 f27 f13)) (f28 f29 (f30 (f31 f32 f33) f17))) f1)))
(assert (not (= (f34 (f35 f36 f9) f37) f1)))
(assert (not (= (f34 (f35 f36 f8) f37) f1)))
(assert (= (f38 (f39 f40 f17) f41) f1))
(assert (= (f34 (f35 f36 f33) f37) f1))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S5) (?v3 S3)) (=> (= (f18 (f19 f20 (f21 ?v0 ?v1 ?v2)) (f22 f23 ?v3)) f1) (= (f24 (f25 f26 ?v2) (f28 f29 (f30 (f31 f32 f33) ?v3))) f1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S5) (?v3 S3)) (=> (= (f18 (f19 f20 (f21 ?v0 ?v1 ?v2)) (f22 f23 ?v3)) f1) (= (f24 (f25 f26 ?v2) (f30 (f31 f32 f33) ?v3)) f1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S5) (?v3 S3)) (=> (= (f18 (f19 f20 (f21 ?v0 ?v1 ?v2)) (f22 f23 ?v3)) f1) (= (f24 (f25 f26 ?v2) (f30 (f31 f32 ?v0) ?v3)) f1))))
(assert (forall ((?v0 S5) (?v1 S3) (?v2 S1)) (let ((?v_0 (=> (not (= (f24 (f25 f26 ?v0) (f28 f29 (f30 (f31 f32 f33) ?v1))) f1)) (= ?v2 f1)))) (=> ?v_0 ?v_0))))
(assert (forall ((?v0 S5) (?v1 S19)) (let ((?v_0 (f25 f26 ?v0))) (=> (= (f24 ?v_0 ?v1) f1) (= (f24 ?v_0 (f28 f29 ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S5)) (not (= (f14 f15 ?v0) (f10 (f11 f12 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S11)) (not (= (f10 (f11 f12 ?v0) ?v1) (f14 f15 ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11)) (not (= (f14 f27 ?v0) (f14 f15 ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (not (= (f14 f15 ?v0) (f14 f27 ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S5)) (not (= (f14 f27 ?v0) (f10 (f11 f12 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S11)) (not (= (f10 (f11 f12 ?v0) ?v1) (f14 f27 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S19)) (let ((?v_0 (f25 f26 ?v0)) (?v_1 (f28 f29 ?v1))) (=> (= (f24 ?v_0 (f28 f29 ?v_1)) f1) (= (f24 ?v_0 ?v_1) f1)))))
(assert (forall ((?v0 S19)) (let ((?v_0 (f28 f29 ?v0))) (= (f28 f29 ?v_0) ?v_0))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f14 f27 ?v0) (f14 f27 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S11) (?v3 S5)) (= (= (f10 (f11 f12 ?v0) ?v1) (f10 (f11 f12 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f14 f15 ?v0) (f14 f15 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S5) (?v3 S7) (?v4 S7) (?v5 S5)) (= (= (f21 ?v0 ?v1 ?v2) (f21 ?v3 ?v4 ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S7)) (=> (= (f38 (f39 f40 ?v0) f41) f1) (= (= (f24 (f25 f26 (f14 f27 (f42 f43 ?v1))) (f28 f29 (f30 (f31 f32 f33) ?v0))) f1) (= (f34 (f35 f36 ?v1) f37) f1)))))
(assert (forall ((?v0 S7) (?v1 S5) (?v2 S3)) (=> (= (f18 (f19 f20 (f44 ?v0 ?v1)) (f22 f23 ?v2)) f1) (=> (= (f34 (f35 f36 ?v0) f37) f1) (= (f24 (f25 f26 ?v1) (f30 (f31 f32 f33) ?v2)) f1)))))
(assert (forall ((?v0 S7) (?v1 S5) (?v2 S3)) (=> (not (= ?v0 f33)) (=> (= (f18 (f19 f20 (f45 ?v0 ?v1)) (f22 f23 ?v2)) f1) (= (f24 (f25 f26 ?v1) (f30 (f31 f32 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S19) (?v1 S5) (?v2 S11)) (let ((?v_0 (f28 f47 ?v0))) (=> (= (f46 ?v_0 ?v1) f1) (=> (= (f46 ?v0 (f14 f27 ?v2)) f1) (= (f46 ?v_0 (f10 (f11 f12 ?v2) ?v1)) f1))))))
(assert (forall ((?v0 S5) (?v1 S7) (?v2 S7) (?v3 S5) (?v4 S3)) (let ((?v_1 (f31 f32 f33)) (?v_0 (f25 f26 ?v0))) (=> (not (= (f24 ?v_0 (f28 f29 (f30 ?v_1 (f48 (f49 f50 (f21 ?v1 ?v2 ?v3)) ?v4)))) f1)) (not (= (f24 ?v_0 (f28 f29 (f30 ?v_1 ?v4))) f1))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S5) (?v3 S3)) (=> (= (f18 (f19 f20 (f21 ?v0 ?v1 ?v2)) (f22 f23 ?v3)) f1) (=> (=> (= (f24 (f25 f26 ?v2) (f28 f51 (f30 (f31 f32 f33) ?v3))) f1) false) false))))
(assert (forall ((?v0 S7) (?v1 S5) (?v2 S3)) (let ((?v_0 (f28 f29 (f30 (f31 f32 f33) ?v2)))) (=> (= (f24 (f25 f26 (f10 (f11 f12 (f42 f43 ?v0)) ?v1)) ?v_0) f1) (=> (= (f34 (f35 f36 ?v0) f37) f1) (= (f24 (f25 f26 ?v1) ?v_0) f1))))))
(assert (forall ((?v0 S5) (?v1 S19)) (let ((?v_0 (f25 f26 ?v0))) (=> (= (f24 ?v_0 ?v1) f1) (= (f24 ?v_0 (f28 f51 ?v1)) f1)))))
(assert (forall ((?v0 S19) (?v1 S5)) (=> (= (f46 ?v0 ?v1) f1) (= (f46 (f28 f47 ?v0) ?v1) f1))))
(assert (forall ((?v0 S7) (?v1 S3)) (= (f24 (f25 f26 (f14 f27 (f42 f43 ?v0))) (f30 (f31 f32 ?v0) ?v1)) f1)))
(check-sat)
(exit)