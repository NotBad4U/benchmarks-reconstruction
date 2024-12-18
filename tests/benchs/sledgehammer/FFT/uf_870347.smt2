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
(declare-fun f18 (S10 S10) S6)
(declare-fun f19 () S10)
(declare-fun f20 () S8)
(declare-fun f21 () S8)
(declare-fun f22 (S6 S10) S1)
(declare-fun f23 (S10) S6)
(declare-fun f24 () S3)
(declare-fun f25 (S13 S10) S14)
(declare-fun f26 () S13)
(declare-fun f27 () S14)
(declare-fun f28 () S11)
(declare-fun f29 (S15 S14) S13)
(declare-fun f30 () S15)
(declare-fun f31 () S12)
(declare-fun f32 () S12)
(declare-fun f33 (S16 S14) S14)
(declare-fun f34 (S17 S14) S16)
(declare-fun f35 () S17)
(declare-fun f36 () S4)
(declare-fun f37 (S18 S10) S6)
(declare-fun f38 (S14 S14) S1)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f11 f20 f17))) (not (= (f3 (f4 f5 (f6 (f7 f8 (f9 f10 (f11 (f9 f10 (f11 f12 f13)) (f14 (f15 f16 f17) f17)))) (f18 f19 f13))) ?v_0) (f3 (f4 f5 (f11 f21 f13)) ?v_0)))))
(assert (= (f22 (f23 f17) f13) f1))
(assert (= (f22 (f23 f17) f13) f1))
(assert (forall ((?v0 S10)) (= (f22 (f23 (f14 (f15 f16 f17) ?v0)) f13) f1)))
(assert (forall ((?v0 S10)) (=> (= (f22 (f23 ?v0) f13) f1) (= (f22 (f23 (f14 (f15 f16 ?v0) f17)) f13) f1))))
(assert (= (f11 f21 f19) f24))
(assert (= (f25 f26 f19) f27))
(assert (= (f14 f28 f19) f19))
(assert (forall ((?v0 S3) (?v1 S10)) (= (= (f11 (f9 f10 ?v0) ?v1) f24) (and (= ?v0 f24) (not (= ?v1 f19))))))
(assert (forall ((?v0 S14) (?v1 S10)) (= (= (f25 (f29 f30 ?v0) ?v1) f27) (and (= ?v0 f27) (not (= ?v1 f19))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f14 (f15 f31 ?v0) ?v1) f19) (and (= ?v0 f19) (not (= ?v1 f19))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f14 f28 (f14 (f15 f31 ?v0) ?v1)) (f14 (f15 f31 (f14 f28 ?v0)) ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f11 f21 (f14 (f15 f31 ?v0) ?v1)) (f11 (f9 f10 (f11 f21 ?v0)) ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f25 f26 (f14 (f15 f31 ?v0) ?v1)) (f25 (f29 f30 (f25 f26 ?v0)) ?v1))))
(assert (forall ((?v0 S10)) (= (f14 (f15 f16 f19) ?v0) f19)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f16 ?v0) f19) ?v0)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f16 ?v0) ?v0) f19)))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f14 (f15 f16 ?v0) ?v1) f19) (=> (= (f14 (f15 f16 ?v1) ?v0) f19) (= ?v0 ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f14 f28 (f14 (f15 f32 ?v0) ?v1)) (f14 (f15 f32 (f14 f28 ?v0)) (f14 f28 ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f11 f21 (f14 (f15 f32 ?v0) ?v1)) (f3 (f4 f5 (f11 f21 ?v0)) (f11 f21 ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f25 f26 (f14 (f15 f32 ?v0) ?v1)) (f33 (f34 f35 (f25 f26 ?v0)) (f25 f26 ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f14 (f15 f31 ?v0) ?v1))) (= (f14 (f15 f32 ?v_0) ?v0) (f14 (f15 f32 ?v0) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S10)) (let ((?v_0 (f11 (f9 f10 ?v0) ?v1))) (= (f3 (f4 f5 ?v_0) ?v0) (f3 (f4 f5 ?v0) ?v_0)))))
(assert (forall ((?v0 S14) (?v1 S10)) (let ((?v_0 (f25 (f29 f30 ?v0) ?v1))) (= (f33 (f34 f35 ?v_0) ?v0) (f33 (f34 f35 ?v0) ?v_0)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (f14 (f15 f31 (f14 (f15 f32 ?v0) ?v1)) ?v2) (f14 (f15 f32 (f14 (f15 f31 ?v0) ?v2)) (f14 (f15 f31 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (= (f11 (f9 f10 (f3 (f4 f5 ?v0) ?v1)) ?v2) (f3 (f4 f5 (f11 (f9 f10 ?v0) ?v2)) (f11 (f9 f10 ?v1) ?v2)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S10)) (= (f25 (f29 f30 (f33 (f34 f35 ?v0) ?v1)) ?v2) (f33 (f34 f35 (f25 (f29 f30 ?v0) ?v2)) (f25 (f29 f30 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (f14 (f15 f31 (f14 (f15 f32 ?v0) ?v1)) ?v2) (f14 (f15 f32 (f14 (f15 f31 ?v0) ?v2)) (f14 (f15 f31 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (= (f11 (f9 f10 (f3 (f4 f5 ?v0) ?v1)) ?v2) (f3 (f4 f5 (f11 (f9 f10 ?v0) ?v2)) (f11 (f9 f10 ?v1) ?v2)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S10)) (= (f25 (f29 f30 (f33 (f34 f35 ?v0) ?v1)) ?v2) (f33 (f34 f35 (f25 (f29 f30 ?v0) ?v2)) (f25 (f29 f30 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f3 (f4 f36 ?v1) ?v2)) (f3 (f4 f36 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S10)) (=> (= (f22 (f23 ?v0) f19) f1) false)))
(assert (forall ((?v0 S10)) (not (= (f22 (f23 ?v0) ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (not (= ?v0 ?v1)) (or (= (f22 (f23 ?v0) ?v1) f1) (= (f22 (f23 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f14 (f15 f32 ?v0) ?v1) (f14 (f15 f32 ?v1) ?v0))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f32 ?v0))) (= (f14 (f15 f32 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f32 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f22 (f23 ?v0) ?v1) f1) false) (=> (=> (= (f22 (f23 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S10)) (=> (= (f22 (f23 ?v0) ?v0) f1) false)))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f22 (f23 ?v0) ?v1) f1) (not (= ?v1 ?v0)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f22 (f23 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S18)) (let ((?v_0 (= (f22 (f37 ?v2 ?v1) ?v0) f1))) (=> (=> (= (f22 (f23 ?v0) ?v1) f1) ?v_0) (=> (=> (= ?v0 ?v1) ?v_0) (=> (=> (= (f22 (f23 ?v1) ?v0) f1) ?v_0) ?v_0))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f31 ?v0))) (=> (= (f22 (f23 f19) ?v0) f1) (=> (= (f22 (f23 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2)) f1) (= (f22 (f23 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f23 f19))) (= (= (f22 ?v_0 (f14 (f15 f31 ?v0) ?v1)) f1) (or (= (f22 ?v_0 ?v0) f1) (= ?v1 f19))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f32 ?v2))) (=> (= (f22 (f23 ?v0) ?v1) f1) (=> (= (f22 (f23 f19) ?v2) f1) (= (f22 (f23 (f14 ?v_0 ?v0)) (f14 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f22 (f23 ?v0) ?v1) f1) (=> (= (f22 (f23 f19) ?v2) f1) (= (f22 (f23 (f14 (f15 f32 ?v0) ?v2)) (f14 (f15 f32 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (= (f22 (f23 (f14 (f15 f32 ?v0) ?v1)) (f14 (f15 f32 ?v2) ?v1)) f1) (and (= (f22 (f23 f19) ?v1) f1) (= (f22 (f23 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f32 ?v0))) (= (= (f22 (f23 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2)) f1) (and (= (f22 (f23 f19) ?v0) f1) (= (f22 (f23 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f23 f19))) (= (= (f22 ?v_0 (f14 (f15 f32 ?v0) ?v1)) f1) (and (= (f22 ?v_0 ?v0) f1) (= (f22 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (= (f14 (f15 f32 ?v0) ?v1) (f14 (f15 f32 ?v2) ?v1)) (or (= ?v0 ?v2) (= ?v1 f19)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f32 ?v0))) (= (= (f14 ?v_0 ?v1) (f14 ?v_0 ?v2)) (or (= ?v1 ?v2) (= ?v0 f19))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f14 (f15 f32 ?v0) ?v1) f19) (or (= ?v0 f19) (= ?v1 f19)))))
(assert (forall ((?v0 S10)) (= (f14 (f15 f32 ?v0) f19) f19)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f32 f19) ?v0) f19)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f31 ?v0))) (= (f14 (f15 f31 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f32 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S10) (?v2 S10)) (let ((?v_0 (f9 f10 ?v0))) (= (f11 (f9 f10 (f11 ?v_0 ?v1)) ?v2) (f11 ?v_0 (f14 (f15 f32 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S10) (?v2 S10)) (let ((?v_0 (f29 f30 ?v0))) (= (f25 (f29 f30 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f14 (f15 f32 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f31 ?v0))) (= (f14 ?v_0 (f14 (f15 f32 ?v1) ?v2)) (f14 (f15 f31 (f14 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S10) (?v2 S10)) (let ((?v_0 (f9 f10 ?v0))) (= (f11 ?v_0 (f14 (f15 f32 ?v1) ?v2)) (f11 (f9 f10 (f11 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S14) (?v1 S10) (?v2 S10)) (let ((?v_0 (f29 f30 ?v0))) (= (f25 ?v_0 (f14 (f15 f32 ?v1) ?v2)) (f25 (f29 f30 (f25 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (f14 (f15 f32 (f14 (f15 f16 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f14 (f15 f32 ?v0) ?v2)) (f14 (f15 f32 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f32 ?v0))) (= (f14 ?v_0 (f14 (f15 f16 ?v1) ?v2)) (f14 (f15 f16 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f22 (f23 (f14 f28 ?v0)) (f14 f28 ?v1)) f1) (= (f22 (f23 ?v0) ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f38 (f25 f26 ?v0) (f25 f26 ?v1)) f1) (= (f22 (f23 ?v0) ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f22 (f23 ?v0) ?v1) f1) (= (f22 (f23 (f14 f28 ?v0)) (f14 f28 ?v1)) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f22 (f23 ?v0) ?v1) f1) (= (f38 (f25 f26 ?v0) (f25 f26 ?v1)) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f22 (f23 (f14 f28 ?v0)) (f14 f28 ?v1)) f1) (= (f22 (f23 ?v0) ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f38 (f25 f26 ?v0) (f25 f26 ?v1)) f1) (= (f22 (f23 ?v0) ?v1) f1))))
(assert (forall ((?v0 S10)) (not (= (f11 f12 ?v0) f24))))
(assert (forall ((?v0 S10)) (=> (=> (= ?v0 f19) false) (= (f22 (f23 f19) ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f22 (f23 ?v0) ?v1) f1) (not (= ?v1 f19)))))
(assert (forall ((?v0 S10)) (= (= (f22 (f23 ?v0) f19) f1) false)))
(assert (forall ((?v0 S10)) (= (not (= ?v0 f19)) (= (f22 (f23 f19) ?v0) f1))))
(assert (forall ((?v0 S10)) (not (= (f22 (f23 ?v0) f19) f1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f23 ?v0)) (?v_1 (f15 f16 ?v2))) (=> (= (f22 ?v_0 ?v1) f1) (=> (= (f22 ?v_0 ?v2) f1) (= (f22 (f23 (f14 ?v_1 ?v1)) (f14 ?v_1 ?v0)) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f22 (f23 ?v0) ?v1) f1) (= (f22 (f23 (f14 (f15 f16 ?v0) ?v2)) ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f32 ?v0))) (=> (= (f22 (f23 f19) ?v0) f1) (= (f11 (f9 f10 (f11 f12 (f14 ?v_0 ?v1))) (f14 ?v_0 ?v2)) (f11 (f9 f10 (f11 f12 ?v1)) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f15 f32 ?v0))) (= (f14 (f15 f32 (f14 ?v_0 ?v1)) (f14 (f15 f32 ?v2) ?v3)) (f14 (f15 f32 (f14 ?v_0 ?v2)) (f14 (f15 f32 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) (f3 (f4 f5 ?v2) ?v3)) (f3 (f4 f5 (f3 ?v_0 ?v2)) (f3 (f4 f5 ?v1) ?v3))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (let ((?v_0 (f34 f35 ?v0))) (= (f33 (f34 f35 (f33 ?v_0 ?v1)) (f33 (f34 f35 ?v2) ?v3)) (f33 (f34 f35 (f33 ?v_0 ?v2)) (f33 (f34 f35 ?v1) ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_1 (f15 f32 (f14 (f15 f32 ?v0) ?v1))) (?v_0 (f15 f32 ?v2))) (= (f14 ?v_1 (f14 ?v_0 ?v3)) (f14 ?v_0 (f14 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f4 f5 (f3 (f4 f5 ?v0) ?v1))) (?v_0 (f4 f5 ?v2))) (= (f3 ?v_1 (f3 ?v_0 ?v3)) (f3 ?v_0 (f3 ?v_1 ?v3))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (let ((?v_1 (f34 f35 (f33 (f34 f35 ?v0) ?v1))) (?v_0 (f34 f35 ?v2))) (= (f33 ?v_1 (f33 ?v_0 ?v3)) (f33 ?v_0 (f33 ?v_1 ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f15 f32 ?v0)) (?v_1 (f14 (f15 f32 ?v2) ?v3))) (= (f14 (f15 f32 (f14 ?v_0 ?v1)) ?v_1) (f14 ?v_0 (f14 (f15 f32 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f5 ?v0)) (?v_1 (f3 (f4 f5 ?v2) ?v3))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v_1) (f3 ?v_0 (f3 (f4 f5 ?v1) ?v_1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (let ((?v_0 (f34 f35 ?v0)) (?v_1 (f33 (f34 f35 ?v2) ?v3))) (= (f33 (f34 f35 (f33 ?v_0 ?v1)) ?v_1) (f33 ?v_0 (f33 (f34 f35 ?v1) ?v_1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f32 ?v0))) (= (f14 (f15 f32 (f14 ?v_0 ?v1)) ?v2) (f14 (f15 f32 (f14 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 (f4 f5 (f3 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f34 f35 ?v0))) (= (f33 (f34 f35 (f33 ?v_0 ?v1)) ?v2) (f33 (f34 f35 (f33 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f32 ?v0))) (= (f14 (f15 f32 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f32 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f34 f35 ?v0))) (= (f33 (f34 f35 (f33 ?v_0 ?v1)) ?v2) (f33 ?v_0 (f33 (f34 f35 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f32 ?v0))) (= (f14 ?v_0 (f14 (f15 f32 ?v1) ?v2)) (f14 (f15 f32 (f14 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2)) (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f34 f35 ?v0))) (= (f33 ?v_0 (f33 (f34 f35 ?v1) ?v2)) (f33 (f34 f35 (f33 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_1 (f15 f32 ?v0)) (?v_0 (f15 f32 ?v1))) (= (f14 ?v_1 (f14 ?v_0 ?v2)) (f14 ?v_0 (f14 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f4 f5 ?v0)) (?v_0 (f4 f5 ?v1))) (= (f3 ?v_1 (f3 ?v_0 ?v2)) (f3 ?v_0 (f3 ?v_1 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_1 (f34 f35 ?v0)) (?v_0 (f34 f35 ?v1))) (= (f33 ?v_1 (f33 ?v_0 ?v2)) (f33 ?v_0 (f33 ?v_1 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f14 (f15 f32 ?v0) ?v1) (f14 (f15 f32 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f5 ?v0) ?v1) (f3 (f4 f5 ?v1) ?v0))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f33 (f34 f35 ?v0) ?v1) (f33 (f34 f35 ?v1) ?v0))))
(assert (forall ((?v0 S14) (?v1 S10)) (=> (= (f38 f27 ?v0) f1) (= (f38 f27 (f25 (f29 f30 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f23 f19))) (=> (= (f22 ?v_0 ?v0) f1) (= (f22 ?v_0 (f14 (f15 f31 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f11 f21 ?v0) (f11 f21 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f25 f26 ?v0) (f25 f26 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f14 f28 ?v0) (f14 f28 ?v1)) (= ?v0 ?v1))))
(check-sat)
(exit)
