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
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 (S5 S4) S2)
(declare-fun f5 () S5)
(declare-fun f6 () S2)
(declare-fun f7 (S6 S3) S3)
(declare-fun f8 (S7 S3) S6)
(declare-fun f9 () S7)
(declare-fun f10 (S8 S9) S3)
(declare-fun f11 () S8)
(declare-fun f12 (S10 S9) S9)
(declare-fun f13 () S10)
(declare-fun f14 () S10)
(declare-fun f15 () S9)
(declare-fun f16 () S3)
(declare-fun f17 () S3)
(declare-fun f18 () S3)
(declare-fun f19 (S12 S3) S11)
(declare-fun f20 (S13 S11) S12)
(declare-fun f21 () S13)
(declare-fun f22 (S14 S11) S11)
(declare-fun f23 (S15 S11) S14)
(declare-fun f24 () S15)
(declare-fun f25 (S16 S3) S9)
(declare-fun f26 (S17 S9) S16)
(declare-fun f27 () S17)
(declare-fun f28 (S18 S9) S10)
(declare-fun f29 () S18)
(declare-fun f30 (S19 S4) S4)
(declare-fun f31 (S20 S4) S19)
(declare-fun f32 () S20)
(declare-fun f33 () S7)
(declare-fun f34 (S21 S9) S11)
(declare-fun f35 () S21)
(declare-fun f36 () S10)
(declare-fun f37 (S22 S9) S4)
(declare-fun f38 () S22)
(declare-fun f39 () S4)
(declare-fun f40 () S6)
(declare-fun f41 () S7)
(declare-fun f42 () S15)
(declare-fun f43 () S18)
(declare-fun f44 () S20)
(declare-fun f45 () S14)
(declare-fun f46 () S10)
(declare-fun f47 () S19)
(declare-fun f48 () S9)
(declare-fun f49 () S11)
(declare-fun f50 () S4)
(declare-fun f51 () S3)
(declare-fun f52 (S11) S1)
(declare-fun f53 (S9) S1)
(declare-fun f54 (S4) S1)
(declare-fun f55 () S3)
(declare-fun f56 () S9)
(declare-fun f57 () S11)
(declare-fun f58 () S4)
(declare-fun f59 (S3) S1)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15))))) (?v_1 (f7 (f8 f9 f17) f18))) (not (= (f3 (f4 f5 (f3 f6 (f7 ?v_0 f16))) (f7 ?v_0 ?v_1)) (f3 (f4 f5 (f3 f6 f16)) ?v_1)))))
(assert (let ((?v_0 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))))) (let ((?v_1 (f4 f5 (f3 f6 (f7 ?v_0 f16)))) (?v_2 (f8 f9 f17))) (= (f3 ?v_1 (f7 ?v_2 (f7 ?v_0 f18))) (f3 ?v_1 (f7 ?v_0 (f7 ?v_2 f18)))))))
(assert (forall ((?v0 S11) (?v1 S3)) (let ((?v_0 (f20 f21 ?v0))) (let ((?v_1 (f19 ?v_0 ?v1))) (= (f19 ?v_0 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1)) (f22 (f23 f24 ?v_1) ?v_1))))))
(assert (forall ((?v0 S9) (?v1 S3)) (let ((?v_0 (f26 f27 ?v0))) (let ((?v_1 (f25 ?v_0 ?v1))) (= (f25 ?v_0 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1)) (f12 (f28 f29 ?v_1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f4 f5 ?v0))) (let ((?v_1 (f3 ?v_0 ?v1))) (= (f3 ?v_0 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1)) (f30 (f31 f32 ?v_1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f8 f33 ?v0))) (let ((?v_1 (f7 ?v_0 ?v1))) (= (f7 ?v_0 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1)) (f7 (f8 f9 ?v_1) ?v_1))))))
(assert (forall ((?v0 S9)) (let ((?v_0 (f34 f35 ?v0))) (= (f19 (f20 f21 ?v_0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f22 (f23 f24 ?v_0) ?v_0)))))
(assert (forall ((?v0 S9)) (let ((?v_0 (f12 f36 ?v0))) (= (f25 (f26 f27 ?v_0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f12 (f28 f29 ?v_0) ?v_0)))))
(assert (forall ((?v0 S9)) (let ((?v_0 (f37 f38 ?v0))) (= (f3 (f4 f5 ?v_0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f30 (f31 f32 ?v_0) ?v_0)))))
(assert (forall ((?v0 S9)) (let ((?v_0 (f10 f11 ?v0))) (= (f7 (f8 f33 ?v_0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f7 (f8 f9 ?v_0) ?v_0)))))
(assert (forall ((?v0 S11) (?v1 S3)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f20 f21 ?v0))) (= (f19 ?v_0 (f7 (f8 f9 ?v_1) ?v1)) (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S9) (?v1 S3)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f26 f27 ?v0))) (= (f25 ?v_0 (f7 (f8 f9 ?v_1) ?v1)) (f25 (f26 f27 (f25 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f7 (f8 f9 ?v_1) ?v1)) (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f8 f33 ?v0))) (= (f7 ?v_0 (f7 (f8 f9 ?v_1) ?v1)) (f7 (f8 f33 (f7 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S11)) (= (f22 (f23 f24 ?v0) ?v0) (f19 (f20 f21 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))))))
(assert (forall ((?v0 S9)) (= (f12 (f28 f29 ?v0) ?v0) (f25 (f26 f27 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))))))
(assert (forall ((?v0 S4)) (= (f30 (f31 f32 ?v0) ?v0) (f3 (f4 f5 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 ?v0) ?v0) (f7 (f8 f33 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))))))
(assert (forall ((?v0 S11)) (= (f19 (f20 f21 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f22 (f23 f24 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f25 (f26 f27 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f12 (f28 f29 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f30 (f31 f32 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f33 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f7 (f8 f9 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f19 (f20 f21 ?v0) (f10 f11 (f12 f14 (f12 f14 f15)))) (f22 (f23 f24 (f22 (f23 f24 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S9)) (= (f25 (f26 f27 ?v0) (f10 f11 (f12 f14 (f12 f14 f15)))) (f12 (f28 f29 (f12 (f28 f29 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) (f10 f11 (f12 f14 (f12 f14 f15)))) (f30 (f31 f32 (f30 (f31 f32 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f33 ?v0) (f10 f11 (f12 f14 (f12 f14 f15)))) (f7 (f8 f9 (f7 (f8 f9 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S11)) (= (f22 (f23 f24 ?v0) (f34 f35 (f12 f14 f15))) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f28 f29 ?v0) (f12 f36 (f12 f14 f15))) ?v0)))
(assert (forall ((?v0 S4)) (= (f30 (f31 f32 ?v0) (f37 f38 (f12 f14 f15))) ?v0)))
(assert (forall ((?v0 S11)) (= (f22 (f23 f24 (f34 f35 (f12 f14 f15))) ?v0) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f28 f29 (f12 f36 (f12 f14 f15))) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f30 (f31 f32 (f37 f38 (f12 f14 f15))) ?v0) ?v0)))
(assert (= (f3 f6 (f10 f11 (f12 f13 (f12 f13 (f12 f14 f15))))) f39))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S3)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 ?v_0 (f7 (f8 f9 ?v1) ?v2)) (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v0))) (= (f25 ?v_0 (f7 (f8 f9 ?v1) ?v2)) (f25 (f26 f27 (f25 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f7 (f8 f9 ?v1) ?v2)) (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f33 ?v0))) (= (f7 ?v_0 (f7 (f8 f9 ?v1) ?v2)) (f7 (f8 f33 (f7 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S3)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v0))) (= (f25 (f26 f27 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f33 ?v0))) (= (f7 (f8 f33 (f7 ?v_0 ?v1)) ?v2) (f7 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (= (f12 f13 f15) f15))
(assert (forall ((?v0 S9)) (= (f12 (f28 f29 f15) ?v0) f15)))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v0))) (= (f25 (f26 f27 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 (f28 f29 (f12 f13 ?v0)) ?v1) (f12 f13 (f12 (f28 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f23 f24 ?v0))) (= (f22 (f23 f24 (f22 ?v_0 ?v1)) (f22 (f23 f24 ?v2) ?v3)) (f22 (f23 f24 (f22 ?v_0 ?v2)) (f22 (f23 f24 ?v1) ?v3))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (let ((?v_0 (f28 f29 ?v0))) (= (f12 (f28 f29 (f12 ?v_0 ?v1)) (f12 (f28 f29 ?v2) ?v3)) (f12 (f28 f29 (f12 ?v_0 ?v2)) (f12 (f28 f29 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f7 (f8 f9 (f7 ?v_0 ?v1)) (f7 (f8 f9 ?v2) ?v3)) (f7 (f8 f9 (f7 ?v_0 ?v2)) (f7 (f8 f9 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f31 f32 ?v0))) (= (f30 (f31 f32 (f30 ?v_0 ?v1)) (f30 (f31 f32 ?v2) ?v3)) (f30 (f31 f32 (f30 ?v_0 ?v2)) (f30 (f31 f32 ?v1) ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_1 (f23 f24 (f22 (f23 f24 ?v0) ?v1))) (?v_0 (f23 f24 ?v2))) (= (f22 ?v_1 (f22 ?v_0 ?v3)) (f22 ?v_0 (f22 ?v_1 ?v3))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (let ((?v_1 (f28 f29 (f12 (f28 f29 ?v0) ?v1))) (?v_0 (f28 f29 ?v2))) (= (f12 ?v_1 (f12 ?v_0 ?v3)) (f12 ?v_0 (f12 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f8 f9 (f7 (f8 f9 ?v0) ?v1))) (?v_0 (f8 f9 ?v2))) (= (f7 ?v_1 (f7 ?v_0 ?v3)) (f7 ?v_0 (f7 ?v_1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_1 (f31 f32 (f30 (f31 f32 ?v0) ?v1))) (?v_0 (f31 f32 ?v2))) (= (f30 ?v_1 (f30 ?v_0 ?v3)) (f30 ?v_0 (f30 ?v_1 ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f23 f24 ?v0)) (?v_1 (f22 (f23 f24 ?v2) ?v3))) (= (f22 (f23 f24 (f22 ?v_0 ?v1)) ?v_1) (f22 ?v_0 (f22 (f23 f24 ?v1) ?v_1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (let ((?v_0 (f28 f29 ?v0)) (?v_1 (f12 (f28 f29 ?v2) ?v3))) (= (f12 (f28 f29 (f12 ?v_0 ?v1)) ?v_1) (f12 ?v_0 (f12 (f28 f29 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f8 f9 ?v0)) (?v_1 (f7 (f8 f9 ?v2) ?v3))) (= (f7 (f8 f9 (f7 ?v_0 ?v1)) ?v_1) (f7 ?v_0 (f7 (f8 f9 ?v1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f31 f32 ?v0)) (?v_1 (f30 (f31 f32 ?v2) ?v3))) (= (f30 (f31 f32 (f30 ?v_0 ?v1)) ?v_1) (f30 ?v_0 (f30 (f31 f32 ?v1) ?v_1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f23 f24 ?v0))) (= (f22 (f23 f24 (f22 ?v_0 ?v1)) ?v2) (f22 (f23 f24 (f22 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f28 f29 ?v0))) (= (f12 (f28 f29 (f12 ?v_0 ?v1)) ?v2) (f12 (f28 f29 (f12 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f7 (f8 f9 (f7 ?v_0 ?v1)) ?v2) (f7 (f8 f9 (f7 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f31 f32 ?v0))) (= (f30 (f31 f32 (f30 ?v_0 ?v1)) ?v2) (f30 (f31 f32 (f30 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f23 f24 ?v0))) (= (f22 (f23 f24 (f22 ?v_0 ?v1)) ?v2) (f22 ?v_0 (f22 (f23 f24 ?v1) ?v2))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f28 f29 ?v0))) (= (f12 (f28 f29 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f28 f29 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f7 (f8 f9 (f7 ?v_0 ?v1)) ?v2) (f7 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f31 f32 ?v0))) (= (f30 (f31 f32 (f30 ?v_0 ?v1)) ?v2) (f30 ?v_0 (f30 (f31 f32 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f23 f24 ?v0))) (= (f22 ?v_0 (f22 (f23 f24 ?v1) ?v2)) (f22 (f23 f24 (f22 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f28 f29 ?v0))) (= (f12 ?v_0 (f12 (f28 f29 ?v1) ?v2)) (f12 (f28 f29 (f12 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f7 ?v_0 (f7 (f8 f9 ?v1) ?v2)) (f7 (f8 f9 (f7 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f31 f32 ?v0))) (= (f30 ?v_0 (f30 (f31 f32 ?v1) ?v2)) (f30 (f31 f32 (f30 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_1 (f23 f24 ?v0)) (?v_0 (f23 f24 ?v1))) (= (f22 ?v_1 (f22 ?v_0 ?v2)) (f22 ?v_0 (f22 ?v_1 ?v2))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_1 (f28 f29 ?v0)) (?v_0 (f28 f29 ?v1))) (= (f12 ?v_1 (f12 ?v_0 ?v2)) (f12 ?v_0 (f12 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f8 f9 ?v0)) (?v_0 (f8 f9 ?v1))) (= (f7 ?v_1 (f7 ?v_0 ?v2)) (f7 ?v_0 (f7 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f31 f32 ?v0)) (?v_0 (f31 f32 ?v1))) (= (f30 ?v_1 (f30 ?v_0 ?v2)) (f30 ?v_0 (f30 ?v_1 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f22 (f23 f24 ?v0) ?v1) (f22 (f23 f24 ?v1) ?v0))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 (f28 f29 ?v0) ?v1) (f12 (f28 f29 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f30 (f31 f32 ?v0) ?v1) (f30 (f31 f32 ?v1) ?v0))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f34 f35 ?v0) (f34 f35 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f12 f36 ?v0) (f12 f36 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f37 f38 ?v0) (f37 f38 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S11)) (let ((?v_0 (f34 f35 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_0 (f12 f36 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S3)) (let ((?v_0 (f10 f11 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S4)) (let ((?v_0 (f37 f38 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f12 f14 ?v0) (f12 f14 ?v1)) (= ?v0 ?v1))))
(assert (= (= f15 f15) true))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f12 f13 ?v0) (f12 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S11)) (= (f22 (f23 f24 (f34 f35 ?v0)) (f22 (f23 f24 (f34 f35 ?v1)) ?v2)) (f22 (f23 f24 (f34 f35 (f12 (f28 f29 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (= (f12 (f28 f29 (f12 f36 ?v0)) (f12 (f28 f29 (f12 f36 ?v1)) ?v2)) (f12 (f28 f29 (f12 f36 (f12 (f28 f29 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S4)) (= (f30 (f31 f32 (f37 f38 ?v0)) (f30 (f31 f32 (f37 f38 ?v1)) ?v2)) (f30 (f31 f32 (f37 f38 (f12 (f28 f29 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f22 (f23 f24 (f34 f35 ?v0)) (f34 f35 ?v1)) (f34 f35 (f12 (f28 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 (f28 f29 (f12 f36 ?v0)) (f12 f36 ?v1)) (f12 f36 (f12 (f28 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f30 (f31 f32 (f37 f38 ?v0)) (f37 f38 ?v1)) (f37 f38 (f12 (f28 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f34 f35 (f12 (f28 f29 ?v0) ?v1)) (f22 (f23 f24 (f34 f35 ?v0)) (f34 f35 ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 f36 (f12 (f28 f29 ?v0) ?v1)) (f12 (f28 f29 (f12 f36 ?v0)) (f12 f36 ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f37 f38 (f12 (f28 f29 ?v0) ?v1)) (f30 (f31 f32 (f37 f38 ?v0)) (f37 f38 ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S3)) (= (f19 (f20 f21 (f22 (f23 f24 ?v0) ?v1)) ?v2) (f22 (f23 f24 (f19 (f20 f21 ?v0) ?v2)) (f19 (f20 f21 ?v1) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S3)) (= (f25 (f26 f27 (f12 (f28 f29 ?v0) ?v1)) ?v2) (f12 (f28 f29 (f25 (f26 f27 ?v0) ?v2)) (f25 (f26 f27 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (= (f3 (f4 f5 (f30 (f31 f32 ?v0) ?v1)) ?v2) (f30 (f31 f32 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f7 (f8 f33 (f7 (f8 f9 ?v0) ?v1)) ?v2) (f7 (f8 f9 (f7 (f8 f33 ?v0) ?v2)) (f7 (f8 f33 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S3)) (= (f19 (f20 f21 (f22 (f23 f24 ?v0) ?v1)) ?v2) (f22 (f23 f24 (f19 (f20 f21 ?v0) ?v2)) (f19 (f20 f21 ?v1) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S3)) (= (f25 (f26 f27 (f12 (f28 f29 ?v0) ?v1)) ?v2) (f12 (f28 f29 (f25 (f26 f27 ?v0) ?v2)) (f25 (f26 f27 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (= (f3 (f4 f5 (f30 (f31 f32 ?v0) ?v1)) ?v2) (f30 (f31 f32 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f7 (f8 f33 (f7 (f8 f9 ?v0) ?v1)) ?v2) (f7 (f8 f9 (f7 (f8 f33 ?v0) ?v2)) (f7 (f8 f33 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S3)) (let ((?v_0 (f19 (f20 f21 ?v0) ?v1))) (= (f22 (f23 f24 ?v_0) ?v0) (f22 (f23 f24 ?v0) ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S3)) (let ((?v_0 (f25 (f26 f27 ?v0) ?v1))) (= (f12 (f28 f29 ?v_0) ?v0) (f12 (f28 f29 ?v0) ?v_0)))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f3 (f4 f5 ?v0) ?v1))) (= (f30 (f31 f32 ?v_0) ?v0) (f30 (f31 f32 ?v0) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f7 (f8 f33 ?v0) ?v1))) (= (f7 (f8 f9 ?v_0) ?v0) (f7 (f8 f9 ?v0) ?v_0)))))
(assert (forall ((?v0 S9)) (= (= (f12 f14 ?v0) f15) false)))
(assert (forall ((?v0 S9)) (= (= f15 (f12 f14 ?v0)) false)))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f12 f14 ?v0) (f12 f13 ?v1)) false)))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f12 f13 ?v0) (f12 f14 ?v1)) false)))
(assert (forall ((?v0 S9)) (= (= (f12 f13 ?v0) f15) (= ?v0 f15))))
(assert (forall ((?v0 S9)) (= (= f15 (f12 f13 ?v0)) (= f15 ?v0))))
(assert (forall ((?v0 S11)) (let ((?v_0 (f12 f13 (f12 f14 f15)))) (let ((?v_1 (f10 f11 ?v_0))) (= (f22 (f23 f24 (f34 f35 (f12 f13 ?v_0))) (f19 (f20 f21 ?v0) ?v_1)) (f19 (f20 f21 (f22 (f23 f24 (f34 f35 ?v_0)) ?v0)) ?v_1))))))
(assert (forall ((?v0 S11) (?v1 S3)) (let ((?v_0 (f20 f21 ?v0))) (let ((?v_1 (f19 ?v_0 ?v1))) (= (f19 ?v_0 (f7 f40 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1))) (f22 (f23 f24 ?v0) (f22 (f23 f24 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S9) (?v1 S3)) (let ((?v_0 (f26 f27 ?v0))) (let ((?v_1 (f25 ?v_0 ?v1))) (= (f25 ?v_0 (f7 f40 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1))) (f12 (f28 f29 ?v0) (f12 (f28 f29 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f4 f5 ?v0))) (let ((?v_1 (f3 ?v_0 ?v1))) (= (f3 ?v_0 (f7 f40 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1))) (f30 (f31 f32 ?v0) (f30 (f31 f32 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f8 f33 ?v0))) (let ((?v_1 (f7 ?v_0 ?v1))) (= (f7 ?v_0 (f7 f40 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1))) (f7 (f8 f9 ?v0) (f7 (f8 f9 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S11) (?v1 S3)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f20 f21 ?v0))) (= (f19 ?v_0 (f7 f40 (f7 (f8 f9 ?v_1) ?v1))) (f22 (f23 f24 ?v0) (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S9) (?v1 S3)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f26 f27 ?v0))) (= (f25 ?v_0 (f7 f40 (f7 (f8 f9 ?v_1) ?v1))) (f12 (f28 f29 ?v0) (f25 (f26 f27 (f25 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f7 f40 (f7 (f8 f9 ?v_1) ?v1))) (f30 (f31 f32 ?v0) (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f8 f33 ?v0))) (= (f7 ?v_0 (f7 f40 (f7 (f8 f9 ?v_1) ?v1))) (f7 (f8 f9 ?v0) (f7 (f8 f33 (f7 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f10 f11 (f12 f13 (f12 f14 f15))))) (= (f7 (f8 f33 (f7 (f8 f41 ?v0) ?v1)) ?v_0) (f7 (f8 f41 (f7 (f8 f41 (f7 (f8 f33 ?v0) ?v_0)) (f7 (f8 f33 ?v1) ?v_0))) (f7 (f8 f9 (f7 (f8 f9 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_1 (f12 f13 (f12 f14 f15)))) (let ((?v_0 (f10 f11 ?v_1))) (= (f19 (f20 f21 (f22 (f23 f42 ?v0) ?v1)) ?v_0) (f22 (f23 f42 (f22 (f23 f42 (f19 (f20 f21 ?v0) ?v_0)) (f19 (f20 f21 ?v1) ?v_0))) (f22 (f23 f24 (f22 (f23 f24 (f34 f35 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_1 (f12 f13 (f12 f14 f15)))) (let ((?v_0 (f10 f11 ?v_1))) (= (f25 (f26 f27 (f12 (f28 f43 ?v0) ?v1)) ?v_0) (f12 (f28 f43 (f12 (f28 f43 (f25 (f26 f27 ?v0) ?v_0)) (f25 (f26 f27 ?v1) ?v_0))) (f12 (f28 f29 (f12 (f28 f29 (f12 f36 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_1 (f12 f13 (f12 f14 f15)))) (let ((?v_0 (f10 f11 ?v_1))) (= (f3 (f4 f5 (f30 (f31 f44 ?v0) ?v1)) ?v_0) (f30 (f31 f44 (f30 (f31 f44 (f3 (f4 f5 ?v0) ?v_0)) (f3 (f4 f5 ?v1) ?v_0))) (f30 (f31 f32 (f30 (f31 f32 (f37 f38 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S11) (?v1 S3)) (let ((?v_0 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1))) (= (f19 (f20 f21 (f22 f45 ?v0)) ?v_0) (f19 (f20 f21 ?v0) ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S3)) (let ((?v_0 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1))) (= (f25 (f26 f27 (f12 f46 ?v0)) ?v_0) (f25 (f26 f27 ?v0) ?v_0)))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1))) (= (f3 (f4 f5 (f30 f47 ?v0)) ?v_0) (f3 (f4 f5 ?v0) ?v_0)))))
(assert (forall ((?v0 S9)) (= (= (f25 (f26 f27 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) f48) (= ?v0 f48))))
(assert (forall ((?v0 S11)) (= (= (f19 (f20 f21 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) f49) (= ?v0 f49))))
(assert (forall ((?v0 S4)) (= (= (f3 (f4 f5 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) f50) (= ?v0 f50))))
(assert (= (f7 (f8 f33 f51) (f10 f11 (f12 f13 (f12 f14 f15)))) f51))
(assert (= (f25 (f26 f27 f48) (f10 f11 (f12 f13 (f12 f14 f15)))) f48))
(assert (= (f19 (f20 f21 f49) (f10 f11 (f12 f13 (f12 f14 f15)))) f49))
(assert (= (f3 (f4 f5 f50) (f10 f11 (f12 f13 (f12 f14 f15)))) f50))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v0) (f7 (f8 f41 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f7 (f8 f41 ?v0) ?v0))))
(assert (not (= (f52 (f34 f35 (f12 f14 f15))) f1)))
(assert (not (= (f53 (f12 f36 (f12 f14 f15))) f1)))
(assert (not (= (f54 (f37 f38 (f12 f14 f15))) f1)))
(assert (= (f7 (f8 f33 f55) (f10 f11 (f12 f13 (f12 f14 f15)))) f55))
(assert (= (f25 (f26 f27 f56) (f10 f11 (f12 f13 (f12 f14 f15)))) f56))
(assert (= (f19 (f20 f21 f57) (f10 f11 (f12 f13 (f12 f14 f15)))) f57))
(assert (= (f3 (f4 f5 f58) (f10 f11 (f12 f13 (f12 f14 f15)))) f58))
(assert (= (f59 f51) f1))
(assert (= (f53 f48) f1))
(assert (= (f54 f50) f1))
(assert (= (f52 f49) f1))
(assert (not (= (f59 f55) f1)))
(assert (not (= (f53 f56) f1)))
(assert (not (= (f54 f58) f1)))
(assert (not (= (f52 f57) f1)))
(assert (forall ((?v0 S3)) (= (f7 f40 ?v0) (f7 (f8 f41 f55) ?v0))))
(assert (forall ((?v0 S3)) (= (f7 f40 ?v0) (f7 (f8 f41 ?v0) f55))))
(assert (forall ((?v0 S3)) (= (= (f59 ?v0) f1) (= ?v0 f51))))
(assert (forall ((?v0 S9)) (= (= (f53 ?v0) f1) (= ?v0 f48))))
(assert (forall ((?v0 S4)) (= (= (f54 ?v0) f1) (= ?v0 f50))))
(assert (forall ((?v0 S11)) (= (= (f52 ?v0) f1) (= ?v0 f49))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f41 f51) ?v0) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f28 f43 f48) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f30 (f31 f44 f50) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f22 (f23 f42 f49) ?v0) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f28 f29 f56) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f7 (f8 f33 f51) ?v0) (ite (= ?v0 f51) f55 f51))))
(assert (forall ((?v0 S3)) (= (f25 (f26 f27 f48) ?v0) (ite (= ?v0 f51) f56 f48))))
(assert (forall ((?v0 S3)) (= (f19 (f20 f21 f49) ?v0) (ite (= ?v0 f51) f57 f49))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f50) ?v0) (ite (= ?v0 f51) f58 f50))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f41 ?v0) f51) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f28 f43 ?v0) f48) ?v0)))
(assert (forall ((?v0 S4)) (= (f30 (f31 f44 ?v0) f50) ?v0)))
(assert (forall ((?v0 S11)) (= (f22 (f23 f42 ?v0) f49) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f28 f29 ?v0) f56) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f41 ?v0) ?v1) (f7 (f8 f41 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f30 (f31 f44 ?v0) ?v1) (f30 (f31 f44 ?v1) ?v0))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f22 (f23 f42 ?v0) ?v1) (f22 (f23 f42 ?v1) ?v0))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 (f28 f43 ?v0) ?v1) (f12 (f28 f43 ?v1) ?v0))))
(check-sat)
(exit)