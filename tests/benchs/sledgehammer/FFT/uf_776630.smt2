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
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 () S3)
(declare-fun f6 (S5 S2) S2)
(declare-fun f7 (S6 S2) S5)
(declare-fun f8 () S6)
(declare-fun f9 () S6)
(declare-fun f10 (S7 S8) S2)
(declare-fun f11 () S7)
(declare-fun f12 (S9 S8) S8)
(declare-fun f13 () S9)
(declare-fun f14 () S9)
(declare-fun f15 () S8)
(declare-fun f16 () S2)
(declare-fun f17 () S3)
(declare-fun f18 (S10 S3) S3)
(declare-fun f19 (S11 S2) S10)
(declare-fun f20 () S11)
(declare-fun f21 () S2)
(declare-fun f22 () S2)
(declare-fun f23 (S12 S4) S4)
(declare-fun f24 (S13 S4) S12)
(declare-fun f25 () S13)
(declare-fun f26 () S6)
(declare-fun f27 () S13)
(declare-fun f28 (S14 S4) S3)
(declare-fun f29 () S14)
(declare-fun f30 () S13)
(declare-fun f31 () S4)
(declare-fun f32 () S3)
(declare-fun f33 (S2 S2) S1)
(declare-fun f34 () S13)
(declare-fun f35 (S15 S8) S4)
(declare-fun f36 () S15)
(declare-fun f37 (S16 S2) S8)
(declare-fun f38 (S17 S8) S16)
(declare-fun f39 () S17)
(declare-fun f40 (S18 S8) S9)
(declare-fun f41 () S18)
(declare-fun f42 () S18)
(declare-fun f43 () S18)
(declare-fun f44 () S9)
(declare-fun f45 () S6)
(declare-fun f46 () S8)
(declare-fun f47 (S8 S8) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f3 f5 (f6 (f7 f8 (f6 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v0)) f16)))))
(assert (forall ((?v0 S2)) (= (f3 f17 ?v0) (f3 f5 (f6 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v0)))))
(assert (let ((?v_0 (f6 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) f21)) (?v_2 (f19 f20 f21)) (?v_1 (f6 (f7 f26 f22) f21))) (not (= (f3 (f18 (f19 f20 ?v_0) f5) f22) (f23 (f24 f25 (f3 (f18 ?v_2 f17) ?v_1)) (f23 (f24 f27 (f3 (f28 f29 (f23 (f24 f30 f31) (f3 f32 ?v_0))) ?v_1)) (f3 (f18 ?v_2 f4) ?v_1)))))))
(assert (= (f33 f21 f22) f1))
(assert (= (f3 f32 f16) f31))
(assert (forall ((?v0 S2)) (= (f3 (f28 f29 (f3 f32 ?v0)) ?v0) f31)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15))))) (?v_1 (f7 f9 ?v1))) (= (f3 (f28 f29 (f3 f32 (f6 ?v_0 ?v0))) (f6 ?v_1 (f6 ?v_0 ?v2))) (f3 (f28 f29 (f3 f32 ?v0)) (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_1 (f12 f13 (f12 f14 f15)))) (let ((?v_0 (f10 f11 ?v_1))) (= (f3 (f28 f29 (f23 (f24 f25 ?v0) ?v1)) ?v_0) (f23 (f24 f25 (f23 (f24 f34 (f3 (f28 f29 ?v0) ?v_0)) (f3 (f28 f29 ?v1) ?v_0))) (f23 (f24 f27 (f23 (f24 f27 (f35 f36 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_1 (f12 f13 (f12 f14 f15)))) (let ((?v_0 (f10 f11 ?v_1))) (= (f37 (f38 f39 (f12 (f40 f41 ?v0) ?v1)) ?v_0) (f12 (f40 f41 (f12 (f40 f42 (f37 (f38 f39 ?v0) ?v_0)) (f37 (f38 f39 ?v1) ?v_0))) (f12 (f40 f43 (f12 (f40 f43 (f12 f44 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_1 (f12 f13 (f12 f14 f15)))) (let ((?v_0 (f10 f11 ?v_1))) (= (f3 (f28 f29 (f23 (f24 f34 ?v0) ?v1)) ?v_0) (f23 (f24 f34 (f23 (f24 f34 (f3 (f28 f29 ?v0) ?v_0)) (f3 (f28 f29 ?v1) ?v_0))) (f23 (f24 f27 (f23 (f24 f27 (f35 f36 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f10 f11 (f12 f13 (f12 f14 f15))))) (= (f6 (f7 f45 (f6 (f7 f8 ?v0) ?v1)) ?v_0) (f6 (f7 f8 (f6 (f7 f8 (f6 (f7 f45 ?v0) ?v_0)) (f6 (f7 f45 ?v1) ?v_0))) (f6 (f7 f9 (f6 (f7 f9 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_1 (f12 f13 (f12 f14 f15)))) (let ((?v_0 (f10 f11 ?v_1))) (= (f37 (f38 f39 (f12 (f40 f42 ?v0) ?v1)) ?v_0) (f12 (f40 f42 (f12 (f40 f42 (f37 (f38 f39 ?v0) ?v_0)) (f37 (f38 f39 ?v1) ?v_0))) (f12 (f40 f43 (f12 (f40 f43 (f12 f44 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f7 f45 ?v0))) (let ((?v_1 (f6 ?v_0 ?v1))) (= (f6 ?v_0 (f6 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1)) (f6 (f7 f9 ?v_1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f28 f29 ?v0))) (let ((?v_1 (f3 ?v_0 ?v1))) (= (f3 ?v_0 (f6 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1)) (f23 (f24 f27 ?v_1) ?v_1))))))
(assert (forall ((?v0 S8) (?v1 S2)) (let ((?v_0 (f38 f39 ?v0))) (let ((?v_1 (f37 ?v_0 ?v1))) (= (f37 ?v_0 (f6 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1)) (f12 (f40 f43 ?v_1) ?v_1))))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f10 f11 ?v0))) (= (f6 (f7 f45 ?v_0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f6 (f7 f9 ?v_0) ?v_0)))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f35 f36 ?v0))) (= (f3 (f28 f29 ?v_0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f23 (f24 f27 ?v_0) ?v_0)))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f12 f44 ?v0))) (= (f37 (f38 f39 ?v_0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f12 (f40 f43 ?v_0) ?v_0)))))
(assert (= (f6 (f7 f8 f16) f16) (f10 f11 (f12 f13 (f12 f14 f15)))))
(assert (forall ((?v0 S2)) (= (f6 (f7 f9 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f6 (f7 f8 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f6 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v0) (f6 (f7 f8 ?v0) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f7 f45 ?v0))) (= (f6 ?v_0 (f6 (f7 f9 ?v_1) ?v1)) (f6 (f7 f45 (f6 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f28 f29 ?v0))) (= (f3 ?v_0 (f6 (f7 f9 ?v_1) ?v1)) (f3 (f28 f29 (f3 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S8) (?v1 S2)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f38 f39 ?v0))) (= (f37 ?v_0 (f6 (f7 f9 ?v_1) ?v1)) (f37 (f38 f39 (f37 ?v_0 ?v1)) ?v_1)))))
(assert (= (f3 (f28 f29 f31) (f10 f11 (f12 f13 (f12 f14 f15)))) f31))
(assert (= (f6 (f7 f45 f16) (f10 f11 (f12 f13 (f12 f14 f15)))) f16))
(assert (= (f37 (f38 f39 f46) (f10 f11 (f12 f13 (f12 f14 f15)))) f46))
(assert (forall ((?v0 S2)) (= (f6 (f7 f9 ?v0) ?v0) (f6 (f7 f45 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))))))
(assert (forall ((?v0 S4)) (= (f23 (f24 f27 ?v0) ?v0) (f3 (f28 f29 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))))))
(assert (forall ((?v0 S8)) (= (f12 (f40 f43 ?v0) ?v0) (f37 (f38 f39 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))))))
(assert (forall ((?v0 S2)) (= (f6 (f7 f45 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f6 (f7 f9 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f3 (f28 f29 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f23 (f24 f27 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f37 (f38 f39 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f12 (f40 f43 ?v0) ?v0))))
(assert (= (f23 (f24 f34 f31) f31) (f35 f36 (f12 f13 (f12 f14 f15)))))
(assert (= (f12 (f40 f42 f46) f46) (f12 f44 (f12 f13 (f12 f14 f15)))))
(assert (forall ((?v0 S8)) (= (f12 f14 ?v0) (f12 (f40 f42 (f12 (f40 f42 f46) ?v0)) ?v0))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (let ((?v_0 (f38 f39 ?v0))) (= (f37 ?v_0 (f6 (f7 f8 ?v1) ?v2)) (f12 (f40 f43 (f37 ?v_0 ?v1)) (f37 ?v_0 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f47 (f12 f44 ?v0) (f12 f44 ?v1)) f1) (= (f47 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8)) (= (f12 (f40 f41 ?v0) f15) ?v0)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f40 f41 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f12 (f40 f41 ?v0) ?v1)))))
(assert (forall ((?v0 S8)) (= (f12 (f40 f42 ?v0) f15) ?v0)))
(assert (forall ((?v0 S8)) (= (f12 (f40 f42 f15) ?v0) ?v0)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f40 f42 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f12 (f40 f42 ?v0) ?v1)))))
(assert (forall ((?v0 S8)) (= (f12 f13 ?v0) (f12 (f40 f42 ?v0) ?v0))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (let ((?v_0 (f38 f39 ?v0))) (= (f37 (f38 f39 (f37 ?v_0 ?v1)) ?v2) (f37 ?v_0 (f6 (f7 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S8)) (= (f12 (f40 f43 f15) ?v0) f15)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f40 f43 (f12 f13 ?v0)) ?v1) (f12 f13 (f12 (f40 f43 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f40 f43 (f12 f14 ?v0)) ?v1) (f12 (f40 f42 (f12 f13 (f12 (f40 f43 ?v0) ?v1))) ?v1))))
(assert (= f46 (f12 f44 (f12 f14 f15))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f40 f41 (f12 f14 ?v0)) (f12 f14 ?v1)) (f12 f13 (f12 (f40 f41 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f40 f41 (f12 f14 ?v0)) (f12 f13 ?v1)) (f12 f14 (f12 (f40 f41 ?v0) ?v1)))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f40 f41 f15))) (= (f12 ?v_0 (f12 f13 ?v0)) (f12 f13 (f12 ?v_0 ?v0))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f40 f42 (f12 f14 ?v0)) (f12 f13 ?v1)) (f12 f14 (f12 (f40 f42 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f40 f42 (f12 f13 ?v0)) (f12 f14 ?v1)) (f12 f14 (f12 (f40 f42 ?v0) ?v1)))))
(assert (forall ((?v0 S8)) (= (= (f47 (f12 f44 ?v0) f46) f1) (= (f47 ?v0 (f12 f14 f15)) f1))))
(assert (forall ((?v0 S8)) (= (= (f47 f46 (f12 f44 ?v0)) f1) (= (f47 (f12 f14 f15) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f7 f9 ?v0))) (= (f6 (f7 f9 (f6 ?v_0 ?v1)) (f6 (f7 f9 ?v2) ?v3)) (f6 (f7 f9 (f6 ?v_0 ?v2)) (f6 (f7 f9 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f24 f27 ?v0))) (= (f23 (f24 f27 (f23 ?v_0 ?v1)) (f23 (f24 f27 ?v2) ?v3)) (f23 (f24 f27 (f23 ?v_0 ?v2)) (f23 (f24 f27 ?v1) ?v3))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f40 f43 ?v0))) (= (f12 (f40 f43 (f12 ?v_0 ?v1)) (f12 (f40 f43 ?v2) ?v3)) (f12 (f40 f43 (f12 ?v_0 ?v2)) (f12 (f40 f43 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_1 (f7 f9 (f6 (f7 f9 ?v0) ?v1))) (?v_0 (f7 f9 ?v2))) (= (f6 ?v_1 (f6 ?v_0 ?v3)) (f6 ?v_0 (f6 ?v_1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_1 (f24 f27 (f23 (f24 f27 ?v0) ?v1))) (?v_0 (f24 f27 ?v2))) (= (f23 ?v_1 (f23 ?v_0 ?v3)) (f23 ?v_0 (f23 ?v_1 ?v3))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_1 (f40 f43 (f12 (f40 f43 ?v0) ?v1))) (?v_0 (f40 f43 ?v2))) (= (f12 ?v_1 (f12 ?v_0 ?v3)) (f12 ?v_0 (f12 ?v_1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f7 f9 ?v0)) (?v_1 (f6 (f7 f9 ?v2) ?v3))) (= (f6 (f7 f9 (f6 ?v_0 ?v1)) ?v_1) (f6 ?v_0 (f6 (f7 f9 ?v1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f24 f27 ?v0)) (?v_1 (f23 (f24 f27 ?v2) ?v3))) (= (f23 (f24 f27 (f23 ?v_0 ?v1)) ?v_1) (f23 ?v_0 (f23 (f24 f27 ?v1) ?v_1))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f40 f43 ?v0)) (?v_1 (f12 (f40 f43 ?v2) ?v3))) (= (f12 (f40 f43 (f12 ?v_0 ?v1)) ?v_1) (f12 ?v_0 (f12 (f40 f43 ?v1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f7 f9 ?v0))) (= (f6 (f7 f9 (f6 ?v_0 ?v1)) ?v2) (f6 (f7 f9 (f6 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f27 ?v0))) (= (f23 (f24 f27 (f23 ?v_0 ?v1)) ?v2) (f23 (f24 f27 (f23 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f40 f43 ?v0))) (= (f12 (f40 f43 (f12 ?v_0 ?v1)) ?v2) (f12 (f40 f43 (f12 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f7 f9 ?v0))) (= (f6 (f7 f9 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f7 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f27 ?v0))) (= (f23 (f24 f27 (f23 ?v_0 ?v1)) ?v2) (f23 ?v_0 (f23 (f24 f27 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f40 f43 ?v0))) (= (f12 (f40 f43 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f40 f43 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f7 f9 ?v0))) (= (f6 ?v_0 (f6 (f7 f9 ?v1) ?v2)) (f6 (f7 f9 (f6 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f27 ?v0))) (= (f23 ?v_0 (f23 (f24 f27 ?v1) ?v2)) (f23 (f24 f27 (f23 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f40 f43 ?v0))) (= (f12 ?v_0 (f12 (f40 f43 ?v1) ?v2)) (f12 (f40 f43 (f12 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f7 f9 ?v0)) (?v_0 (f7 f9 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f24 f27 ?v0)) (?v_0 (f24 f27 ?v1))) (= (f23 ?v_1 (f23 ?v_0 ?v2)) (f23 ?v_0 (f23 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f40 f43 ?v0)) (?v_0 (f40 f43 ?v1))) (= (f12 ?v_1 (f12 ?v_0 ?v2)) (f12 ?v_0 (f12 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f6 (f7 f9 ?v0) ?v1) (f6 (f7 f9 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f23 (f24 f27 ?v0) ?v1) (f23 (f24 f27 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f40 f43 ?v0) ?v1) (f12 (f40 f43 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f24 f34 ?v0))) (= (f23 (f24 f34 (f23 ?v_0 ?v1)) (f23 (f24 f34 ?v2) ?v3)) (f23 (f24 f34 (f23 ?v_0 ?v2)) (f23 (f24 f34 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 (f7 f8 (f6 ?v_0 ?v1)) (f6 (f7 f8 ?v2) ?v3)) (f6 (f7 f8 (f6 ?v_0 ?v2)) (f6 (f7 f8 ?v1) ?v3))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f40 f42 ?v0))) (= (f12 (f40 f42 (f12 ?v_0 ?v1)) (f12 (f40 f42 ?v2) ?v3)) (f12 (f40 f42 (f12 ?v_0 ?v2)) (f12 (f40 f42 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f34 ?v0))) (= (f23 (f24 f34 (f23 ?v_0 ?v1)) ?v2) (f23 (f24 f34 (f23 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 (f7 f8 (f6 ?v_0 ?v1)) ?v2) (f6 (f7 f8 (f6 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f40 f42 ?v0))) (= (f12 (f40 f42 (f12 ?v_0 ?v1)) ?v2) (f12 (f40 f42 (f12 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f34 ?v0))) (= (f23 (f24 f34 (f23 ?v_0 ?v1)) ?v2) (f23 ?v_0 (f23 (f24 f34 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 (f7 f8 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f7 f8 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f40 f42 ?v0))) (= (f12 (f40 f42 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f40 f42 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f34 ?v0))) (= (f23 ?v_0 (f23 (f24 f34 ?v1) ?v2)) (f23 (f24 f34 (f23 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 ?v_0 (f6 (f7 f8 ?v1) ?v2)) (f6 (f7 f8 (f6 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f40 f42 ?v0))) (= (f12 ?v_0 (f12 (f40 f42 ?v1) ?v2)) (f12 (f40 f42 (f12 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f24 f34 ?v0)) (?v_0 (f24 f34 ?v1))) (= (f23 ?v_1 (f23 ?v_0 ?v2)) (f23 ?v_0 (f23 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f7 f8 ?v0)) (?v_0 (f7 f8 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f40 f42 ?v0)) (?v_0 (f40 f42 ?v1))) (= (f12 ?v_1 (f12 ?v_0 ?v2)) (f12 ?v_0 (f12 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f23 (f24 f34 ?v0) ?v1) (f23 (f24 f34 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f6 (f7 f8 ?v0) ?v1) (f6 (f7 f8 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f40 f42 ?v0) ?v1) (f12 (f40 f42 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f35 f36 ?v0) (f35 f36 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f12 f44 ?v0) (f12 f44 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S4)) (let ((?v_0 (f35 f36 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S2)) (let ((?v_0 (f10 f11 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f12 f44 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f12 f14 ?v0) (f12 f14 ?v1)) (= ?v0 ?v1))))
(assert (= (= f15 f15) true))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f12 f13 ?v0) (f12 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f24 f27 ?v0)) (?v_1 (f24 f27 ?v2))) (= (= (f23 (f24 f34 (f23 ?v_0 ?v1)) (f23 ?v_1 ?v3)) (f23 (f24 f34 (f23 ?v_0 ?v3)) (f23 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f7 f9 ?v0)) (?v_1 (f7 f9 ?v2))) (= (= (f6 (f7 f8 (f6 ?v_0 ?v1)) (f6 ?v_1 ?v3)) (f6 (f7 f8 (f6 ?v_0 ?v3)) (f6 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f40 f43 ?v0)) (?v_1 (f40 f43 ?v2))) (= (= (f12 (f40 f42 (f12 ?v_0 ?v1)) (f12 ?v_1 ?v3)) (f12 (f40 f42 (f12 ?v_0 ?v3)) (f12 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f23 (f24 f34 (f23 (f24 f27 ?v0) ?v1)) (f23 (f24 f27 ?v2) ?v1)) (f23 (f24 f27 (f23 (f24 f34 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f6 (f7 f8 (f6 (f7 f9 ?v0) ?v1)) (f6 (f7 f9 ?v2) ?v1)) (f6 (f7 f9 (f6 (f7 f8 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (f12 (f40 f42 (f12 (f40 f43 ?v0) ?v1)) (f12 (f40 f43 ?v2) ?v1)) (f12 (f40 f43 (f12 (f40 f42 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f23 (f24 f27 (f23 (f24 f34 ?v0) ?v1)) ?v2) (f23 (f24 f34 (f23 (f24 f27 ?v0) ?v2)) (f23 (f24 f27 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f6 (f7 f9 (f6 (f7 f8 ?v0) ?v1)) ?v2) (f6 (f7 f8 (f6 (f7 f9 ?v0) ?v2)) (f6 (f7 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (f12 (f40 f43 (f12 (f40 f42 ?v0) ?v1)) ?v2) (f12 (f40 f42 (f12 (f40 f43 ?v0) ?v2)) (f12 (f40 f43 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f24 f27 ?v0)) (?v_1 (f24 f27 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f23 (f24 f34 (f23 ?v_0 ?v2)) (f23 ?v_1 ?v3)) (f23 (f24 f34 (f23 ?v_0 ?v3)) (f23 ?v_1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f7 f9 ?v0)) (?v_1 (f7 f9 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f6 (f7 f8 (f6 ?v_0 ?v2)) (f6 ?v_1 ?v3)) (f6 (f7 f8 (f6 ?v_0 ?v3)) (f6 ?v_1 ?v2))))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f40 f43 ?v0)) (?v_1 (f40 f43 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f12 (f40 f42 (f12 ?v_0 ?v2)) (f12 ?v_1 ?v3)) (f12 (f40 f42 (f12 ?v_0 ?v3)) (f12 ?v_1 ?v2))))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f27 ?v0))) (= (f23 ?v_0 (f23 (f24 f34 ?v1) ?v2)) (f23 (f24 f34 (f23 ?v_0 ?v1)) (f23 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f7 f9 ?v0))) (= (f6 ?v_0 (f6 (f7 f8 ?v1) ?v2)) (f6 (f7 f8 (f6 ?v_0 ?v1)) (f6 ?v_0 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f40 f43 ?v0))) (= (f12 ?v_0 (f12 (f40 f42 ?v1) ?v2)) (f12 (f40 f42 (f12 ?v_0 ?v1)) (f12 ?v_0 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S4)) (= (f23 (f24 f27 (f35 f36 ?v0)) (f23 (f24 f27 (f35 f36 ?v1)) ?v2)) (f23 (f24 f27 (f35 f36 (f12 (f40 f43 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (f12 (f40 f43 (f12 f44 ?v0)) (f12 (f40 f43 (f12 f44 ?v1)) ?v2)) (f12 (f40 f43 (f12 f44 (f12 (f40 f43 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f23 (f24 f27 (f35 f36 ?v0)) (f35 f36 ?v1)) (f35 f36 (f12 (f40 f43 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f40 f43 (f12 f44 ?v0)) (f12 f44 ?v1)) (f12 f44 (f12 (f40 f43 ?v0) ?v1)))))
(check-sat)
(exit)