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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S6) S3)
(declare-fun f7 (S7 S8) S5)
(declare-fun f8 () S7)
(declare-fun f9 (S9 S3) S8)
(declare-fun f10 () S9)
(declare-fun f11 (S8 S10) S3)
(declare-fun f12 () S8)
(declare-fun f13 () S10)
(declare-fun f14 (S11 S10) S10)
(declare-fun f15 (S12 S10) S11)
(declare-fun f16 () S12)
(declare-fun f17 () S10)
(declare-fun f18 (S13 S10) S6)
(declare-fun f19 (S10) S13)
(declare-fun f20 () S10)
(declare-fun f21 () S8)
(declare-fun f22 () S8)
(declare-fun f23 (S6 S10) S1)
(declare-fun f24 (S10) S6)
(declare-fun f25 () S11)
(declare-fun f26 (S14 S10) S15)
(declare-fun f27 () S14)
(declare-fun f28 () S15)
(declare-fun f29 () S3)
(declare-fun f30 () S12)
(declare-fun f31 (S16 S15) S14)
(declare-fun f32 () S16)
(declare-fun f33 () S12)
(declare-fun f34 (S17 S15) S15)
(declare-fun f35 (S18 S15) S17)
(declare-fun f36 () S18)
(declare-fun f37 () S4)
(declare-fun f38 (S15 S15) S1)
(declare-fun f39 (S10 S6) S1)
(declare-fun f40 () S18)
(declare-fun f41 (S15 S15) S19)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f11 f21 f17))) (not (= (f3 (f4 f5 (f6 (f7 f8 (f9 f10 (f11 (f9 f10 (f11 f12 f13)) (f14 (f15 f16 f17) f17)))) (f18 (f19 f20) f13))) ?v_0) (f3 (f4 f5 (f11 f22 f13)) ?v_0)))))
(assert (= (f23 (f24 f17) f13) f1))
(assert (= (f23 (f24 f17) f13) f1))
(assert (forall ((?v0 S10)) (= (f23 (f24 (f14 (f15 f16 f17) ?v0)) f13) f1)))
(assert (forall ((?v0 S10)) (=> (= (f23 (f24 ?v0) f13) f1) (= (f23 (f24 (f14 (f15 f16 ?v0) f17)) f13) f1))))
(assert (= (f14 f25 f20) f20))
(assert (= (f26 f27 f20) f28))
(assert (= (f11 f22 f20) f29))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f14 (f15 f30 ?v0) ?v1) f20) (and (= ?v0 f20) (not (= ?v1 f20))))))
(assert (forall ((?v0 S15) (?v1 S10)) (= (= (f26 (f31 f32 ?v0) ?v1) f28) (and (= ?v0 f28) (not (= ?v1 f20))))))
(assert (forall ((?v0 S3) (?v1 S10)) (= (= (f11 (f9 f10 ?v0) ?v1) f29) (and (= ?v0 f29) (not (= ?v1 f20))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f26 f27 (f14 (f15 f30 ?v0) ?v1)) (f26 (f31 f32 (f26 f27 ?v0)) ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f11 f22 (f14 (f15 f30 ?v0) ?v1)) (f11 (f9 f10 (f11 f22 ?v0)) ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f14 f25 (f14 (f15 f30 ?v0) ?v1)) (f14 (f15 f30 (f14 f25 ?v0)) ?v1))))
(assert (forall ((?v0 S10)) (= (f14 (f15 f16 f20) ?v0) f20)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f16 ?v0) f20) ?v0)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f16 ?v0) ?v0) f20)))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f14 (f15 f16 ?v0) ?v1) f20) (=> (= (f14 (f15 f16 ?v1) ?v0) f20) (= ?v0 ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f11 f22 (f14 (f15 f33 ?v0) ?v1)) (f3 (f4 f5 (f11 f22 ?v0)) (f11 f22 ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f14 f25 (f14 (f15 f33 ?v0) ?v1)) (f14 (f15 f33 (f14 f25 ?v0)) (f14 f25 ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f26 f27 (f14 (f15 f33 ?v0) ?v1)) (f34 (f35 f36 (f26 f27 ?v0)) (f26 f27 ?v1)))))
(assert (forall ((?v0 S15) (?v1 S10)) (let ((?v_0 (f26 (f31 f32 ?v0) ?v1))) (= (f34 (f35 f36 ?v_0) ?v0) (f34 (f35 f36 ?v0) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S10)) (let ((?v_0 (f11 (f9 f10 ?v0) ?v1))) (= (f3 (f4 f5 ?v_0) ?v0) (f3 (f4 f5 ?v0) ?v_0)))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f14 (f15 f30 ?v0) ?v1))) (= (f14 (f15 f33 ?v_0) ?v0) (f14 (f15 f33 ?v0) ?v_0)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S10)) (= (f26 (f31 f32 (f34 (f35 f36 ?v0) ?v1)) ?v2) (f34 (f35 f36 (f26 (f31 f32 ?v0) ?v2)) (f26 (f31 f32 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (= (f11 (f9 f10 (f3 (f4 f5 ?v0) ?v1)) ?v2) (f3 (f4 f5 (f11 (f9 f10 ?v0) ?v2)) (f11 (f9 f10 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (f14 (f15 f30 (f14 (f15 f33 ?v0) ?v1)) ?v2) (f14 (f15 f33 (f14 (f15 f30 ?v0) ?v2)) (f14 (f15 f30 ?v1) ?v2)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S10)) (= (f26 (f31 f32 (f34 (f35 f36 ?v0) ?v1)) ?v2) (f34 (f35 f36 (f26 (f31 f32 ?v0) ?v2)) (f26 (f31 f32 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (= (f11 (f9 f10 (f3 (f4 f5 ?v0) ?v1)) ?v2) (f3 (f4 f5 (f11 (f9 f10 ?v0) ?v2)) (f11 (f9 f10 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (f14 (f15 f30 (f14 (f15 f33 ?v0) ?v1)) ?v2) (f14 (f15 f33 (f14 (f15 f30 ?v0) ?v2)) (f14 (f15 f30 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f3 (f4 f37 ?v1) ?v2)) (f3 (f4 f37 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S10)) (=> (= (f23 (f24 ?v0) f20) f1) false)))
(assert (forall ((?v0 S10)) (not (= (f23 (f24 ?v0) ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (not (= ?v0 ?v1)) (or (= (f23 (f24 ?v0) ?v1) f1) (= (f23 (f24 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f14 (f15 f33 ?v0) ?v1) (f14 (f15 f33 ?v1) ?v0))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v0))) (= (f14 (f15 f33 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f23 (f24 ?v0) ?v1) f1) false) (=> (=> (= (f23 (f24 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S10)) (=> (= (f23 (f24 ?v0) ?v0) f1) false)))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f23 (f24 ?v0) ?v1) f1) (not (= ?v1 ?v0)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f23 (f24 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S13)) (let ((?v_0 (= (f23 (f18 ?v2 ?v1) ?v0) f1))) (=> (=> (= (f23 (f24 ?v0) ?v1) f1) ?v_0) (=> (=> (= ?v0 ?v1) ?v_0) (=> (=> (= (f23 (f24 ?v1) ?v0) f1) ?v_0) ?v_0))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f30 ?v0))) (=> (= (f23 (f24 f20) ?v0) f1) (=> (= (f23 (f24 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2)) f1) (= (f23 (f24 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f24 f20))) (= (= (f23 ?v_0 (f14 (f15 f30 ?v0) ?v1)) f1) (or (= (f23 ?v_0 ?v0) f1) (= ?v1 f20))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v2))) (=> (= (f23 (f24 ?v0) ?v1) f1) (=> (= (f23 (f24 f20) ?v2) f1) (= (f23 (f24 (f14 ?v_0 ?v0)) (f14 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f23 (f24 ?v0) ?v1) f1) (=> (= (f23 (f24 f20) ?v2) f1) (= (f23 (f24 (f14 (f15 f33 ?v0) ?v2)) (f14 (f15 f33 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (= (f23 (f24 (f14 (f15 f33 ?v0) ?v1)) (f14 (f15 f33 ?v2) ?v1)) f1) (and (= (f23 (f24 f20) ?v1) f1) (= (f23 (f24 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v0))) (= (= (f23 (f24 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2)) f1) (and (= (f23 (f24 f20) ?v0) f1) (= (f23 (f24 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f24 f20))) (= (= (f23 ?v_0 (f14 (f15 f33 ?v0) ?v1)) f1) (and (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (= (f14 (f15 f33 ?v0) ?v1) (f14 (f15 f33 ?v2) ?v1)) (or (= ?v0 ?v2) (= ?v1 f20)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v0))) (= (= (f14 ?v_0 ?v1) (f14 ?v_0 ?v2)) (or (= ?v1 ?v2) (= ?v0 f20))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f14 (f15 f33 ?v0) ?v1) f20) (or (= ?v0 f20) (= ?v1 f20)))))
(assert (forall ((?v0 S10)) (= (f14 (f15 f33 ?v0) f20) f20)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f33 f20) ?v0) f20)))
(assert (forall ((?v0 S15) (?v1 S10) (?v2 S10)) (let ((?v_0 (f31 f32 ?v0))) (= (f26 (f31 f32 (f26 ?v_0 ?v1)) ?v2) (f26 ?v_0 (f14 (f15 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S10) (?v2 S10)) (let ((?v_0 (f9 f10 ?v0))) (= (f11 (f9 f10 (f11 ?v_0 ?v1)) ?v2) (f11 ?v_0 (f14 (f15 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f30 ?v0))) (= (f14 (f15 f30 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S15) (?v1 S10) (?v2 S10)) (let ((?v_0 (f31 f32 ?v0))) (= (f26 ?v_0 (f14 (f15 f33 ?v1) ?v2)) (f26 (f31 f32 (f26 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S10) (?v2 S10)) (let ((?v_0 (f9 f10 ?v0))) (= (f11 ?v_0 (f14 (f15 f33 ?v1) ?v2)) (f11 (f9 f10 (f11 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f30 ?v0))) (= (f14 ?v_0 (f14 (f15 f33 ?v1) ?v2)) (f14 (f15 f30 (f14 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (f14 (f15 f33 (f14 (f15 f16 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f14 (f15 f33 ?v0) ?v2)) (f14 (f15 f33 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v0))) (= (f14 ?v_0 (f14 (f15 f16 ?v1) ?v2)) (f14 (f15 f16 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f23 (f24 (f14 f25 ?v0)) (f14 f25 ?v1)) f1) (= (f23 (f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f38 (f26 f27 ?v0) (f26 f27 ?v1)) f1) (= (f23 (f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f23 (f24 ?v0) ?v1) f1) (= (f23 (f24 (f14 f25 ?v0)) (f14 f25 ?v1)) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f23 (f24 ?v0) ?v1) f1) (= (f38 (f26 f27 ?v0) (f26 f27 ?v1)) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f23 (f24 (f14 f25 ?v0)) (f14 f25 ?v1)) f1) (= (f23 (f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f38 (f26 f27 ?v0) (f26 f27 ?v1)) f1) (= (f23 (f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S10)) (not (= (f11 f12 ?v0) f29))))
(assert (forall ((?v0 S10)) (=> (=> (= ?v0 f20) false) (= (f23 (f24 f20) ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f23 (f24 ?v0) ?v1) f1) (not (= ?v1 f20)))))
(assert (forall ((?v0 S10)) (= (= (f23 (f24 ?v0) f20) f1) false)))
(assert (forall ((?v0 S10)) (= (not (= ?v0 f20)) (= (f23 (f24 f20) ?v0) f1))))
(assert (forall ((?v0 S10)) (not (= (f23 (f24 ?v0) f20) f1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f24 ?v0)) (?v_1 (f15 f16 ?v2))) (=> (= (f23 ?v_0 ?v1) f1) (=> (= (f23 ?v_0 ?v2) f1) (= (f23 (f24 (f14 ?v_1 ?v1)) (f14 ?v_1 ?v0)) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f23 (f24 ?v0) ?v1) f1) (= (f23 (f24 (f14 (f15 f16 ?v0) ?v2)) ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v0))) (=> (= (f23 (f24 f20) ?v0) f1) (= (f11 (f9 f10 (f11 f12 (f14 ?v_0 ?v1))) (f14 ?v_0 ?v2)) (f11 (f9 f10 (f11 f12 ?v1)) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) (f3 (f4 f5 ?v2) ?v3)) (f3 (f4 f5 (f3 ?v_0 ?v2)) (f3 (f4 f5 ?v1) ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f15 f33 ?v0))) (= (f14 (f15 f33 (f14 ?v_0 ?v1)) (f14 (f15 f33 ?v2) ?v3)) (f14 (f15 f33 (f14 ?v_0 ?v2)) (f14 (f15 f33 ?v1) ?v3))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (let ((?v_0 (f35 f36 ?v0))) (= (f34 (f35 f36 (f34 ?v_0 ?v1)) (f34 (f35 f36 ?v2) ?v3)) (f34 (f35 f36 (f34 ?v_0 ?v2)) (f34 (f35 f36 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f4 f5 (f3 (f4 f5 ?v0) ?v1))) (?v_0 (f4 f5 ?v2))) (= (f3 ?v_1 (f3 ?v_0 ?v3)) (f3 ?v_0 (f3 ?v_1 ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_1 (f15 f33 (f14 (f15 f33 ?v0) ?v1))) (?v_0 (f15 f33 ?v2))) (= (f14 ?v_1 (f14 ?v_0 ?v3)) (f14 ?v_0 (f14 ?v_1 ?v3))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (let ((?v_1 (f35 f36 (f34 (f35 f36 ?v0) ?v1))) (?v_0 (f35 f36 ?v2))) (= (f34 ?v_1 (f34 ?v_0 ?v3)) (f34 ?v_0 (f34 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f5 ?v0)) (?v_1 (f3 (f4 f5 ?v2) ?v3))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v_1) (f3 ?v_0 (f3 (f4 f5 ?v1) ?v_1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f15 f33 ?v0)) (?v_1 (f14 (f15 f33 ?v2) ?v3))) (= (f14 (f15 f33 (f14 ?v_0 ?v1)) ?v_1) (f14 ?v_0 (f14 (f15 f33 ?v1) ?v_1))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (let ((?v_0 (f35 f36 ?v0)) (?v_1 (f34 (f35 f36 ?v2) ?v3))) (= (f34 (f35 f36 (f34 ?v_0 ?v1)) ?v_1) (f34 ?v_0 (f34 (f35 f36 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 (f4 f5 (f3 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v0))) (= (f14 (f15 f33 (f14 ?v_0 ?v1)) ?v2) (f14 (f15 f33 (f14 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f35 f36 ?v0))) (= (f34 (f35 f36 (f34 ?v_0 ?v1)) ?v2) (f34 (f35 f36 (f34 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v0))) (= (f14 (f15 f33 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f35 f36 ?v0))) (= (f34 (f35 f36 (f34 ?v_0 ?v1)) ?v2) (f34 ?v_0 (f34 (f35 f36 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2)) (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v0))) (= (f14 ?v_0 (f14 (f15 f33 ?v1) ?v2)) (f14 (f15 f33 (f14 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f35 f36 ?v0))) (= (f34 ?v_0 (f34 (f35 f36 ?v1) ?v2)) (f34 (f35 f36 (f34 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f4 f5 ?v0)) (?v_0 (f4 f5 ?v1))) (= (f3 ?v_1 (f3 ?v_0 ?v2)) (f3 ?v_0 (f3 ?v_1 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_1 (f15 f33 ?v0)) (?v_0 (f15 f33 ?v1))) (= (f14 ?v_1 (f14 ?v_0 ?v2)) (f14 ?v_0 (f14 ?v_1 ?v2))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_1 (f35 f36 ?v0)) (?v_0 (f35 f36 ?v1))) (= (f34 ?v_1 (f34 ?v_0 ?v2)) (f34 ?v_0 (f34 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f5 ?v0) ?v1) (f3 (f4 f5 ?v1) ?v0))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f14 (f15 f33 ?v0) ?v1) (f14 (f15 f33 ?v1) ?v0))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (f34 (f35 f36 ?v0) ?v1) (f34 (f35 f36 ?v1) ?v0))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f24 f20))) (=> (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 (f14 (f15 f30 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S15) (?v1 S10)) (=> (= (f38 f28 ?v0) f1) (= (f38 f28 (f26 (f31 f32 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f14 f25 ?v0) (f14 f25 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f11 f22 ?v0) (f11 f22 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f26 f27 ?v0) (f26 f27 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f16 ?v0))) (= (f14 (f15 f16 (f14 ?v_0 ?v1)) ?v2) (f14 (f15 f16 (f14 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S10)) (not (= (f23 (f24 (f14 f25 ?v0)) f20) f1))))
(assert (forall ((?v0 S10)) (not (= (f38 (f26 f27 ?v0) f28) f1))))
(assert (forall ((?v0 S10)) (let ((?v_0 (f24 f20))) (= (= (f23 ?v_0 (f14 f25 ?v0)) f1) (= (f23 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S10)) (= (= (f38 f28 (f26 f27 ?v0)) f1) (= (f23 (f24 f20) ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f24 f20))) (=> (= (f23 ?v_0 ?v0) f1) (=> (= (f23 ?v_0 ?v1) f1) (= (f23 (f24 (f14 (f15 f16 ?v1) ?v0)) ?v1) f1))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f23 (f24 f20) (f14 (f15 f16 ?v0) ?v1)) f1) (= (f23 (f24 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) f29) f29)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) f29) f29)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f33 ?v0) f20) f20)))
(assert (forall ((?v0 S15)) (= (f34 (f35 f36 ?v0) f28) f28)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) f29) f29)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f29) ?v0) f29)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f29) ?v0) f29)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f33 f20) ?v0) f20)))
(assert (forall ((?v0 S15)) (= (f34 (f35 f36 f28) ?v0) f28)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f29) ?v0) f29)))
(assert (forall ((?v0 S15) (?v1 S10)) (=> (not (= ?v0 f28)) (not (= (f26 (f31 f32 ?v0) ?v1) f28)))))
(assert (forall ((?v0 S3) (?v1 S10)) (=> (not (= ?v0 f29)) (not (= (f11 (f9 f10 ?v0) ?v1) f29)))))
(assert (forall ((?v0 S10) (?v1 S6)) (= (= (f39 ?v0 ?v1) f1) (= (f23 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f5 (f3 (f4 f37 ?v0) ?v1)) ?v2) (f3 (f4 f37 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f5 (f3 (f4 f37 ?v0) ?v1)) ?v2) (f3 (f4 f37 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f3 (f4 f37 ?v1) ?v2)) (f3 (f4 f37 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f24 f20))) (= (= (f23 ?v_0 (f14 (f15 f30 ?v0) ?v1)) f1) (or (= ?v1 f20) (= (f23 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S10) (?v1 S6)) (= (forall ((?v2 S10)) (=> (= (f23 (f24 ?v2) ?v0) f1) (= (f23 ?v1 ?v2) f1))) (forall ((?v2 S10)) (=> (= (f39 ?v2 (f18 (f19 f20) ?v0)) f1) (= (f23 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S6)) (= (exists ((?v2 S10)) (and (= (f23 (f24 ?v2) ?v0) f1) (= (f23 ?v1 ?v2) f1))) (exists ((?v2 S10)) (and (= (f39 ?v2 (f18 (f19 f20) ?v0)) f1) (= (f23 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v0))) (=> (= (f23 (f24 f20) ?v0) f1) (= (= (f23 (f24 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2)) f1) (= (f23 (f24 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v0))) (=> (= (f23 (f24 f20) ?v0) f1) (= (= (f14 ?v_0 ?v1) (f14 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (= (f38 ?v0 ?v1) f1) (= (f38 (f34 (f35 f40 ?v0) ?v1) f28) f1))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f35 f36 ?v2))) (=> (= (f38 ?v0 ?v1) f1) (=> (= (f38 ?v2 f28) f1) (= (f38 (f34 ?v_0 ?v1) (f34 ?v_0 ?v0)) f1))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (=> (= (f38 ?v0 ?v1) f1) (=> (= (f38 ?v2 f28) f1) (= (f38 (f34 (f35 f36 ?v1) ?v2) (f34 (f35 f36 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v2))) (=> (= (f23 (f24 ?v0) ?v1) f1) (=> (= (f23 (f24 f20) ?v2) f1) (= (f23 (f24 (f14 ?v_0 ?v0)) (f14 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f35 f36 ?v2))) (=> (= (f38 ?v0 ?v1) f1) (=> (= (f38 f28 ?v2) f1) (= (f38 (f34 ?v_0 ?v0) (f34 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v2))) (=> (= (f23 (f24 ?v0) ?v1) f1) (=> (= (f23 (f24 f20) ?v2) f1) (= (f23 (f24 (f14 ?v_0 ?v0)) (f14 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f35 f36 ?v2))) (=> (= (f38 ?v0 ?v1) f1) (=> (= (f38 f28 ?v2) f1) (= (f38 (f34 ?v_0 ?v0) (f34 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S10)) (= (= f20 ?v0) (= ?v0 f20))))
(assert (forall ((?v0 S15)) (= (= f28 ?v0) (= ?v0 f28))))
(assert (forall ((?v0 S3)) (= (= f29 ?v0) (= ?v0 f29))))
(assert (forall ((?v0 S15) (?v1 S15)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f38 ?v0 ?v1) f1) false) (=> (=> (= (f38 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v0))) (= (f14 (f15 f33 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f35 f36 ?v0))) (= (f34 (f35 f36 (f34 ?v_0 ?v1)) ?v2) (f34 ?v_0 (f34 (f35 f36 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f4 f37 ?v0) ?v1) (f3 (f4 f37 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (=> (= (f34 (f35 f40 ?v0) ?v1) (f34 (f35 f40 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S10)) (= (f14 (f15 f33 f20) ?v0) f20)))
(assert (forall ((?v0 S15)) (= (f34 (f35 f36 f28) ?v0) f28)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f29) ?v0) f29)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f33 ?v0) f20) f20)))
(assert (forall ((?v0 S15)) (= (f34 (f35 f36 ?v0) f28) f28)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) f29) f29)))
(assert (forall ((?v0 S15) (?v1 S15)) (= (= (f34 (f35 f36 ?v0) ?v1) f28) (or (= ?v0 f28) (= ?v1 f28)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f29) (or (= ?v0 f29) (= ?v1 f29)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (not (= ?v0 f20)) (=> (not (= ?v1 f20)) (not (= (f14 (f15 f33 ?v0) ?v1) f20))))))
(assert (forall ((?v0 S15) (?v1 S15)) (=> (not (= ?v0 f28)) (=> (not (= ?v1 f28)) (not (= (f34 (f35 f36 ?v0) ?v1) f28))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 f29)) (=> (not (= ?v1 f29)) (not (= (f3 (f4 f5 ?v0) ?v1) f29))))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f14 (f15 f33 ?v0) ?v1) f20) (or (= ?v0 f20) (= ?v1 f20)))))
(assert (forall ((?v0 S15) (?v1 S15)) (=> (= (f34 (f35 f36 ?v0) ?v1) f28) (or (= ?v0 f28) (= ?v1 f28)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f29) (or (= ?v0 f29) (= ?v1 f29)))))
(assert (forall ((?v0 S15)) (= (f34 (f35 f40 ?v0) f28) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f37 ?v0) f29) ?v0)))
(assert (forall ((?v0 S15)) (= (f34 (f35 f40 ?v0) ?v0) f28)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f37 ?v0) ?v0) f29)))
(assert (forall ((?v0 S15) (?v1 S15)) (= (= ?v0 ?v1) (= (f34 (f35 f40 ?v0) ?v1) f28))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (= (f3 (f4 f37 ?v0) ?v1) f29))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (= (f34 (f35 f40 ?v0) ?v1) f28) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f37 ?v0) ?v1) f29) (= ?v0 ?v1))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (=> (= (f34 (f35 f40 ?v0) ?v1) (f34 (f35 f40 ?v2) ?v3)) (= (= (f38 ?v0 ?v1) f1) (= (f38 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f33 ?v0))) (= (= (f14 ?v_0 ?v1) (f14 ?v_0 ?v2)) (or (= ?v0 f20) (= ?v1 ?v2))))))
(assert (forall ((?v0 S15)) (not (= (f38 (f34 (f35 f36 ?v0) ?v0) f28) f1))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (= (= (f38 (f34 (f35 f36 ?v0) ?v1) (f34 (f35 f36 ?v2) ?v1)) f1) (or (and (= (f38 f28 ?v1) f1) (= (f38 ?v0 ?v2) f1)) (and (= (f38 ?v1 f28) f1) (= (f38 ?v2 ?v0) f1))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f35 f36 ?v0))) (= (= (f38 (f34 ?v_0 ?v1) (f34 ?v_0 ?v2)) f1) (or (and (= (f38 f28 ?v0) f1) (= (f38 ?v1 ?v2) f1)) (and (= (f38 ?v0 f28) f1) (= (f38 ?v2 ?v1) f1)))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f35 f36 ?v0))) (=> (= (f38 f28 ?v0) f1) (= (= (f38 (f34 ?v_0 ?v1) (f34 ?v_0 ?v2)) f1) (= (f38 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f24 f20))) (=> (= (f23 ?v_0 ?v0) f1) (=> (= (f23 ?v_0 ?v1) f1) (= (f23 ?v_0 (f14 (f15 f33 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S15) (?v1 S15)) (=> (= (f38 f28 ?v0) f1) (=> (= (f38 f28 ?v1) f1) (= (f38 f28 (f34 (f35 f36 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f23 (f24 f20) ?v0) f1) (=> (= (f23 (f24 ?v1) f20) f1) (= (f23 (f24 (f14 (f15 f33 ?v0) ?v1)) f20) f1)))))
(assert (forall ((?v0 S15) (?v1 S15)) (=> (= (f38 f28 ?v0) f1) (=> (= (f38 ?v1 f28) f1) (= (f38 (f34 (f35 f36 ?v0) ?v1) f28) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f23 (f24 f20) ?v0) f1) (=> (= (f23 (f24 ?v1) f20) f1) (= (f23 (f24 (f14 (f15 f33 ?v1) ?v0)) f20) f1)))))
(assert (forall ((?v0 S15) (?v1 S15)) (=> (= (f38 f28 ?v0) f1) (=> (= (f38 ?v1 f28) f1) (= (f38 (f34 (f35 f36 ?v1) ?v0) f28) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f24 f20))) (=> (= (f23 ?v_0 (f14 (f15 f33 ?v0) ?v1)) f1) (=> (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S15) (?v1 S15)) (=> (= (f38 f28 (f34 (f35 f36 ?v0) ?v1)) f1) (=> (= (f38 f28 ?v0) f1) (= (f38 f28 ?v1) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f24 f20))) (=> (= (f23 ?v_0 (f14 (f15 f33 ?v0) ?v1)) f1) (=> (= (f23 ?v_0 ?v1) f1) (= (f23 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S15) (?v1 S15)) (=> (= (f38 f28 (f34 (f35 f36 ?v0) ?v1)) f1) (=> (= (f38 f28 ?v1) f1) (= (f38 f28 ?v0) f1)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f35 f36 ?v0))) (=> (= (f38 ?v0 f28) f1) (= (= (f38 (f34 ?v_0 ?v1) (f34 ?v_0 ?v2)) f1) (= (f38 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f23 (f24 ?v0) f20) f1) (=> (= (f23 (f24 f20) ?v1) f1) (= (f23 (f24 (f14 (f15 f33 ?v0) ?v1)) f20) f1)))))
(assert (forall ((?v0 S15) (?v1 S15)) (=> (= (f38 ?v0 f28) f1) (=> (= (f38 f28 ?v1) f1) (= (f38 (f34 (f35 f36 ?v0) ?v1) f28) f1)))))
(assert (forall ((?v0 S15) (?v1 S15)) (=> (= (f38 ?v0 f28) f1) (=> (= (f38 ?v1 f28) f1) (= (f38 f28 (f34 (f35 f36 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f23 (f24 ?v0) ?v1) f1) (=> (= (f23 (f24 f20) ?v2) f1) (= (f23 (f24 (f14 (f15 f33 ?v0) ?v2)) (f14 (f15 f33 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (=> (= (f38 ?v0 ?v1) f1) (=> (= (f38 f28 ?v2) f1) (= (f38 (f34 (f35 f36 ?v0) ?v2) (f34 (f35 f36 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f23 (f24 ?v0) ?v1) f1) (=> (= (f23 (f24 ?v2) ?v3) f1) (= (= (f18 (f19 ?v0) ?v1) (f18 (f19 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (=> (= (f38 ?v0 ?v1) f1) (=> (= (f38 ?v2 ?v3) f1) (= (= (f41 ?v0 ?v1) (f41 ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f18 (f19 ?v0) ?v1) (f18 (f19 ?v2) ?v3)) (=> (= (f23 (f24 ?v0) ?v1) f1) (=> (= (f23 (f24 ?v2) ?v3) f1) (= ?v0 ?v2))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (=> (= (f41 ?v0 ?v1) (f41 ?v2 ?v3)) (=> (= (f38 ?v0 ?v1) f1) (=> (= (f38 ?v2 ?v3) f1) (= ?v0 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f18 (f19 ?v0) ?v1) (f18 (f19 ?v2) ?v3)) (=> (= (f23 (f24 ?v0) ?v1) f1) (=> (= (f23 (f24 ?v2) ?v3) f1) (= ?v1 ?v3))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (=> (= (f41 ?v0 ?v1) (f41 ?v2 ?v3)) (=> (= (f38 ?v0 ?v1) f1) (=> (= (f38 ?v2 ?v3) f1) (= ?v1 ?v3))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S10)) (let ((?v_0 (f35 f36 (f26 f27 ?v2)))) (=> (= (f38 ?v0 ?v1) f1) (=> (= (f23 (f24 f20) ?v2) f1) (= (f38 (f34 ?v_0 ?v0) (f34 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S10)) (= (= (f38 f28 (f26 f27 ?v0)) f1) (= (f23 (f24 f20) ?v0) f1))))
(assert (forall ((?v0 S10)) (not (= (f38 (f26 f27 ?v0) f28) f1))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (= (f38 ?v0 ?v1) f1) (= (f38 (f34 (f35 f40 ?v0) ?v1) f28) f1))))
(assert (forall ((?v0 S15) (?v1 S15)) (or (= (f38 ?v0 ?v1) f1) (or (= ?v0 ?v1) (= (f38 ?v1 ?v0) f1)))))
(check-sat)
(exit)