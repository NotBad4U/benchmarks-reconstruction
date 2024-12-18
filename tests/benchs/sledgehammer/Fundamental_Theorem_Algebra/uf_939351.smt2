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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 (S3 S2) S2)
(declare-fun f5 () S3)
(declare-fun f6 (S4 S2) S3)
(declare-fun f7 () S4)
(declare-fun f8 (S5 S6) S2)
(declare-fun f9 () S5)
(declare-fun f10 (S7 S6) S6)
(declare-fun f11 (S8 S9) S7)
(declare-fun f12 () S8)
(declare-fun f13 () S9)
(declare-fun f14 (S10 S11) S6)
(declare-fun f15 () S10)
(declare-fun f16 (S12 S11) S11)
(declare-fun f17 () S12)
(declare-fun f18 (S13 S11) S12)
(declare-fun f19 () S13)
(declare-fun f20 () S11)
(declare-fun f21 () S11)
(declare-fun f22 () S3)
(declare-fun f23 () S2)
(declare-fun f24 () S4)
(declare-fun f25 () S6)
(declare-fun f26 (S14 S15) S2)
(declare-fun f27 () S14)
(declare-fun f28 (S16 S15) S15)
(declare-fun f29 () S16)
(declare-fun f30 () S16)
(declare-fun f31 () S15)
(declare-fun f32 () S2)
(declare-fun f33 (S17 S11) S2)
(declare-fun f34 () S17)
(declare-fun f35 () S12)
(declare-fun f36 (S12) S1)
(declare-fun f37 () S2)
(declare-fun f38 (S18 S6) S7)
(declare-fun f39 () S18)
(declare-fun f40 (S2 S2) S1)
(declare-fun f41 (S11 S11) S1)
(declare-fun f42 () S4)
(declare-fun f43 () S2)
(declare-fun f44 () S3)
(declare-fun f45 (S19 S15) S6)
(declare-fun f46 () S19)
(declare-fun f47 () S18)
(declare-fun f48 () S2)
(declare-fun f49 () S6)
(declare-fun f50 (S15 S15) S1)
(declare-fun f51 () S16)
(declare-fun f52 () S15)
(declare-fun f53 (S20 S15) S16)
(declare-fun f54 () S20)
(declare-fun f55 () S15)
(declare-fun f56 () S6)
(declare-fun f57 (S15 S15) S1)
(declare-fun f58 (S21 S15) S11)
(declare-fun f59 () S21)
(declare-fun f60 (S11 S11) S1)
(declare-fun f61 () S18)
(declare-fun f62 () S11)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f11 f12 f13)) (?v_1 (f4 f22 f23))) (not (= (f3 (f4 f5 (f4 (f6 f7 (f8 f9 (f10 ?v_0 (f14 f15 (f16 f17 (f16 (f18 f19 f20) f21)))))) ?v_1)) (f4 (f6 f24 (f4 f5 (f4 (f6 f7 (f8 f9 (f10 ?v_0 f25))) ?v_1))) (f26 f27 (f28 f29 (f28 f30 f31))))) f1))))
(assert (let ((?v_0 (f16 (f18 f19 f20) f21))) (= (f3 (f4 f5 (f4 (f6 f7 (f8 f9 (f10 (f11 f12 f13) (f14 f15 (f16 f17 ?v_0))))) (f4 f22 f23))) (f4 (f6 f24 f32) (f33 f34 (f16 f35 ?v_0)))) f1)))
(assert (= (f3 (f4 (f6 f24 f32) (f33 f34 (f16 f35 (f16 (f18 f19 f20) f21)))) (f4 (f6 f24 (f4 f5 (f4 (f6 f7 (f8 f9 (f10 (f11 f12 f13) f25))) (f4 f22 f23)))) (f26 f27 (f28 f29 (f28 f30 f31))))) f1))
(assert (= (f36 f17) f1))
(assert (= (f3 (f4 (f6 f24 (f26 f27 (f28 f29 (f28 f30 f31)))) (f4 f5 (f4 (f6 f7 (f8 f9 (f10 (f11 f12 f13) f25))) (f4 f22 f23)))) (f33 f34 f21)) f1))
(assert (let ((?v_0 (f16 (f18 f19 f20) f21))) (= (f3 (f4 f5 (f4 (f6 f7 (f8 f9 (f10 (f11 f12 f13) (f14 f15 (f16 f17 ?v_0))))) (f4 f22 f23))) (f4 (f6 f24 f32) (f33 f34 (f16 f35 ?v_0)))) f1)))
(assert (= (f3 (f4 (f6 f24 f32) (f33 f34 (f16 f35 (f16 (f18 f19 f20) f21)))) (f4 (f6 f24 (f4 f5 (f4 (f6 f7 (f8 f9 (f10 (f11 f12 f13) f25))) (f4 f22 f23)))) (f26 f27 (f28 f29 (f28 f30 f31))))) f1))
(assert (= (f3 f37 (f4 f5 (f4 (f6 f7 (f8 f9 (f10 (f11 f12 f13) f25))) (f4 f22 f23)))) f1))
(assert (= (f3 (f4 (f6 f24 (f26 f27 (f28 f29 (f28 f30 f31)))) (f4 f5 (f4 (f6 f7 (f8 f9 (f10 (f11 f12 f13) f25))) (f4 f22 f23)))) (f33 f34 (f16 f35 (f16 (f18 f19 f20) f21)))) f1))
(assert (exists ((?v0 S11)) (= (f3 (f4 (f6 f24 (f26 f27 (f28 f29 (f28 f30 f31)))) (f4 f5 (f4 (f6 f7 (f8 f9 (f10 (f11 f12 f13) f25))) (f4 f22 f23)))) (f33 f34 ?v0)) f1)))
(assert (=> (forall ((?v0 S11)) (=> (= (f3 (f4 (f6 f24 (f26 f27 (f28 f29 (f28 f30 f31)))) (f4 f5 (f4 (f6 f7 (f8 f9 (f10 (f11 f12 f13) f25))) (f4 f22 f23)))) (f33 f34 ?v0)) f1) false)) false))
(assert (let ((?v_0 (f11 f12 f13))) (let ((?v_1 (f10 ?v_0 f25))) (= (f3 (f8 f9 (f10 (f38 f39 (f10 ?v_0 (f14 f15 (f16 f17 (f16 (f18 f19 f20) f21))))) ?v_1)) (f4 (f6 f24 (f4 f5 (f4 (f6 f7 (f8 f9 ?v_1)) (f4 f22 f23)))) (f26 f27 (f28 f29 (f28 f30 f31))))) f1))))
(assert (= (f3 f37 (f4 (f6 f24 (f4 f5 (f4 (f6 f7 (f8 f9 (f10 (f11 f12 f13) f25))) (f4 f22 f23)))) (f26 f27 (f28 f29 (f28 f30 f31))))) f1))
(assert (= (f40 (f4 f22 f23) (f8 f9 (f10 (f11 f12 f13) (f14 f15 (f16 f17 (f16 (f18 f19 f20) f21)))))) f1))
(assert (forall ((?v0 S11)) (= (f40 (f4 f22 f23) (f8 f9 (f10 (f11 f12 f13) (f14 f15 ?v0)))) f1)))
(assert (let ((?v_0 (f16 (f18 f19 f20) f21))) (= (f41 ?v_0 (f16 f17 ?v_0)) f1)))
(assert (forall ((?v0 S11)) (= (f3 (f8 f9 (f10 (f11 f12 f13) (f14 f15 ?v0))) (f4 (f6 f42 (f4 f22 f23)) (f4 (f6 f24 f32) (f33 f34 (f16 f35 ?v0))))) f1)))
(assert (forall ((?v0 S6)) (let ((?v_0 (f11 f12 f13))) (let ((?v_1 (f10 ?v_0 f25))) (=> (= (f3 (f8 f9 (f10 (f38 f39 ?v0) f25)) f43) f1) (= (f3 (f8 f9 (f10 (f38 f39 (f10 ?v_0 ?v0)) ?v_1)) (f4 (f6 f24 (f4 f5 (f4 (f6 f7 (f8 f9 ?v_1)) (f4 f22 f23)))) (f26 f27 (f28 f29 (f28 f30 f31))))) f1))))))
(assert (let ((?v_0 (f16 f17 (f16 (f18 f19 f20) f21)))) (= (f3 (f8 f9 (f10 (f11 f12 f13) (f14 f15 ?v_0))) (f4 (f6 f42 (f4 f22 f23)) (f4 (f6 f24 f32) (f33 f34 (f16 f35 ?v_0))))) f1)))
(assert (let ((?v_0 (f16 (f18 f19 f20) f21))) (= (f3 (f8 f9 (f10 (f11 f12 f13) (f14 f15 (f16 f17 ?v_0)))) (f4 (f6 f42 (f4 f22 f23)) (f4 (f6 f24 f32) (f33 f34 (f16 f35 ?v_0))))) f1)))
(assert (forall ((?v0 S15)) (let ((?v_0 (f26 f27 ?v0))) (= (f4 f44 ?v_0) (f4 f5 ?v_0)))))
(assert (forall ((?v0 S15)) (= (f8 f9 (f45 f46 ?v0)) (f4 f5 (f26 f27 ?v0)))))
(assert (forall ((?v0 S2)) (= (f4 (f6 f24 ?v0) (f26 f27 (f28 f30 f31))) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f38 f47 ?v0) (f45 f46 (f28 f30 f31))) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f6 f24 ?v0) (f26 f27 (f28 f30 f31))) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f38 f47 ?v0) (f45 f46 (f28 f30 f31))) ?v0)))
(assert (= (f40 f32 f32) f1))
(assert (= (f3 f37 f43) f1))
(assert (= (f40 f37 f32) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f40 ?v0 ?v1) f1) (=> (= (f3 ?v1 (f4 (f6 f42 ?v0) ?v2)) f1) (= (f3 (f4 f5 (f4 (f6 f7 ?v1) ?v0)) ?v2) f1)))))
(assert (forall ((?v0 S11)) (=> (= (f41 f20 ?v0) f1) (= (f3 (f8 f9 (f10 (f38 f39 (f14 f15 (f16 f17 ?v0))) f25)) f43) f1))))
(assert (forall ((?v0 S2)) (=> (= (f3 f37 ?v0) f1) (exists ((?v1 S11)) (forall ((?v2 S11)) (=> (= (f41 ?v1 ?v2) f1) (= (f3 (f8 f9 (f10 (f38 f39 (f14 f15 (f16 f17 ?v2))) f25)) ?v0) f1)))))))
(assert (= (f3 f37 (f33 f34 (f16 f35 (f16 (f18 f19 f20) f21)))) f1))
(assert (forall ((?v0 S6)) (let ((?v_1 (f11 f12 f13))) (let ((?v_2 (f10 ?v_1 f25)) (?v_0 (f8 f9 (f10 (f38 f39 ?v0) f25)))) (=> (and (= (f3 f37 ?v_0) f1) (= (f3 ?v_0 f43) f1)) (= (f3 (f8 f9 (f10 (f38 f39 (f10 ?v_1 ?v0)) ?v_2)) (f4 (f6 f24 (f4 f5 (f4 (f6 f7 (f8 f9 ?v_2)) (f4 f22 f23)))) (f26 f27 (f28 f29 (f28 f30 f31))))) f1))))))
(assert (let ((?v_1 (f16 (f18 f19 f20) f21)) (?v_0 (f6 f24 f32))) (= (f40 (f4 ?v_0 (f33 f34 (f16 f35 (f16 f17 ?v_1)))) (f4 ?v_0 (f33 f34 (f16 f35 ?v_1)))) f1)))
(assert (= (f40 f37 f48) f1))
(assert (let ((?v_2 (f16 (f18 f19 f20) f21)) (?v_1 (f6 f24 f32)) (?v_0 (f6 f42 (f4 f22 f23)))) (= (f40 (f4 ?v_0 (f4 ?v_1 (f33 f34 (f16 f35 (f16 f17 ?v_2))))) (f4 ?v_0 (f4 ?v_1 (f33 f34 (f16 f35 ?v_2))))) f1)))
(assert (forall ((?v0 S11)) (= (f40 (f8 f9 (f14 f15 ?v0)) f48) f1)))
(assert (exists ((?v0 S11)) (forall ((?v1 S11)) (=> (= (f41 ?v0 ?v1) f1) (= (f3 (f8 f9 (f10 (f38 f39 (f14 f15 (f16 f17 ?v1))) f25)) f43) f1)))))
(assert (exists ((?v0 S2)) (and (= (f3 f37 ?v0) f1) (forall ((?v1 S6)) (let ((?v_1 (f11 f12 f13))) (let ((?v_2 (f10 ?v_1 f25)) (?v_0 (f8 f9 (f10 (f38 f39 ?v1) f25)))) (=> (and (= (f3 f37 ?v_0) f1) (= (f3 ?v_0 ?v0) f1)) (= (f3 (f8 f9 (f10 (f38 f39 (f10 ?v_1 ?v1)) ?v_2)) (f4 (f6 f24 (f4 f5 (f4 (f6 f7 (f8 f9 ?v_2)) (f4 f22 f23)))) (f26 f27 (f28 f29 (f28 f30 f31))))) f1))))))))
(assert (=> (forall ((?v0 S11)) (=> (forall ((?v1 S11)) (=> (= (f41 ?v0 ?v1) f1) (= (f3 (f8 f9 (f10 (f38 f39 (f14 f15 (f16 f17 ?v1))) f25)) f43) f1))) false)) false))
(assert (=> (forall ((?v0 S2)) (=> (= (f3 f37 ?v0) f1) (=> (forall ((?v1 S6)) (let ((?v_1 (f11 f12 f13))) (let ((?v_2 (f10 ?v_1 f25)) (?v_0 (f8 f9 (f10 (f38 f39 ?v1) f25)))) (=> (and (= (f3 f37 ?v_0) f1) (= (f3 ?v_0 ?v0) f1)) (= (f3 (f8 f9 (f10 (f38 f39 (f10 ?v_1 ?v1)) ?v_2)) (f4 (f6 f24 (f4 f5 (f4 (f6 f7 (f8 f9 ?v_2)) (f4 f22 f23)))) (f26 f27 (f28 f29 (f28 f30 f31))))) f1))))) false))) false))
(assert (forall ((?v0 S2)) (= (f40 f37 (f4 f44 ?v0)) f1)))
(assert (forall ((?v0 S6)) (= (f40 f37 (f8 f9 ?v0)) f1)))
(assert (= (f4 f44 f37) f37))
(assert (= (f8 f9 f49) f37))
(assert (forall ((?v0 S2)) (= (= (f4 f44 ?v0) f37) (= ?v0 f37))))
(assert (forall ((?v0 S6)) (= (= (f8 f9 ?v0) f37) (= ?v0 f49))))
(assert (forall ((?v0 S2)) (= (= (f40 (f4 f44 ?v0) f37) f1) (= ?v0 f37))))
(assert (forall ((?v0 S6)) (= (= (f40 (f8 f9 ?v0) f37) f1) (= ?v0 f49))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (= (f50 (f28 f51 ?v0) (f28 f51 ?v1)) f1) (= (f50 ?v0 ?v1) f1))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (= (f40 (f26 f27 ?v0) (f26 f27 ?v1)) f1) (= (f50 ?v0 ?v1) f1))))
(assert (forall ((?v0 S15)) (= (= (f50 (f28 f51 ?v0) f52) f1) (= (f50 ?v0 f31) f1))))
(assert (forall ((?v0 S15)) (= (= (f40 (f26 f27 ?v0) f37) f1) (= (f50 ?v0 f31) f1))))
(assert (forall ((?v0 S15)) (= (= (f50 f52 (f28 f51 ?v0)) f1) (= (f50 f31 ?v0) f1))))
(assert (forall ((?v0 S15)) (= (= (f40 f37 (f26 f27 ?v0)) f1) (= (f50 f31 ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f6 f42 ?v0) ?v0) f37) (= ?v0 f37))))
(assert (forall ((?v0 S15)) (= (= (f28 (f53 f54 ?v0) ?v0) f52) (= ?v0 f52))))
(assert (forall ((?v0 S2)) (= (f4 f44 ?v0) (f4 f5 ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f6 f24 f37) ?v0) f37)))
(assert (forall ((?v0 S6)) (= (f10 (f38 f47 f49) ?v0) f49)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f40 (f8 f9 (f10 (f38 f39 ?v0) ?v1)) (f4 (f6 f42 (f8 f9 ?v0)) (f8 f9 ?v1))) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f40 (f4 f44 (f4 (f6 f7 ?v0) ?v1)) (f4 (f6 f42 (f4 f44 ?v0)) (f4 f44 ?v1))) f1)))
(assert (forall ((?v0 S2)) (= (= (f3 f37 (f4 f44 ?v0)) f1) (not (= ?v0 f37)))))
(assert (forall ((?v0 S6)) (= (= (f3 f37 (f8 f9 ?v0)) f1) (not (= ?v0 f49)))))
(assert (forall ((?v0 S15)) (= (= (f50 (f28 f51 ?v0) f55) f1) (= (f50 ?v0 (f28 f30 f31)) f1))))
(assert (forall ((?v0 S15)) (= (= (f40 (f26 f27 ?v0) f32) f1) (= (f50 ?v0 (f28 f30 f31)) f1))))
(assert (forall ((?v0 S15)) (= (= (f50 f55 (f28 f51 ?v0)) f1) (= (f50 (f28 f30 f31) ?v0) f1))))
(assert (forall ((?v0 S15)) (= (= (f40 f32 (f26 f27 ?v0)) f1) (= (f50 (f28 f30 f31) ?v0) f1))))
(assert (= (f4 f44 f32) f32))
(assert (= (f8 f9 f56) f32))
(assert (forall ((?v0 S15) (?v1 S15)) (let ((?v_1 (f28 f51 ?v0)) (?v_0 (f28 f51 ?v1))) (= (= (f50 ?v_1 ?v_0) f1) (not (= (f57 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S15) (?v1 S15)) (let ((?v_1 (f26 f27 ?v0)) (?v_0 (f26 f27 ?v1))) (= (= (f40 ?v_1 ?v_0) f1) (not (= (f3 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S15) (?v1 S15)) (let ((?v_1 (f58 f59 ?v0)) (?v_0 (f58 f59 ?v1))) (= (= (f41 ?v_1 ?v_0) f1) (not (= (f60 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 (f6 f42 ?v0) ?v0) f37) f1) (= (f3 ?v0 f37) f1))))
(assert (forall ((?v0 S15)) (= (= (f57 (f28 (f53 f54 ?v0) ?v0) f52) f1) (= (f57 ?v0 f52) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f40 (f4 f44 (f4 (f6 f42 ?v0) ?v1)) (f4 (f6 f42 (f4 f44 ?v0)) (f4 f44 ?v1))) f1)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f40 (f8 f9 (f10 (f38 f61 ?v0) ?v1)) (f4 (f6 f42 (f8 f9 ?v0)) (f8 f9 ?v1))) f1)))
(assert (= (f28 f51 f31) f52))
(assert (= (f26 f27 f31) f37))
(assert (= (f58 f59 f31) f62))
(assert (= (f45 f46 f31) f49))
(assert (= (f28 f51 f31) f52))
(assert (= (f26 f27 f31) f37))
(assert (= (f45 f46 f31) f49))
(assert (forall ((?v0 S2)) (not (= (f3 (f4 f44 ?v0) f37) f1))))
(assert (forall ((?v0 S6)) (not (= (f3 (f8 f9 ?v0) f37) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (f40 (f4 f44 (f4 (f6 f7 (f4 (f6 f42 ?v0) ?v1)) (f4 (f6 f42 ?v2) ?v3))) (f4 (f6 f42 (f4 f44 (f4 (f6 f7 ?v0) ?v2))) (f4 f44 (f4 (f6 f7 ?v1) ?v3)))) f1)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (f40 (f8 f9 (f10 (f38 f39 (f10 (f38 f61 ?v0) ?v1)) (f10 (f38 f61 ?v2) ?v3))) (f4 (f6 f42 (f8 f9 (f10 (f38 f39 ?v0) ?v2))) (f8 f9 (f10 (f38 f39 ?v1) ?v3)))) f1)))
(assert (forall ((?v0 S15)) (= (= (f57 (f28 f51 ?v0) f52) f1) (= (f57 ?v0 f31) f1))))
(assert (forall ((?v0 S15)) (= (= (f3 (f26 f27 ?v0) f37) f1) (= (f57 ?v0 f31) f1))))
(assert (forall ((?v0 S15)) (= (= (f57 f52 (f28 f51 ?v0)) f1) (= (f57 f31 ?v0) f1))))
(assert (forall ((?v0 S15)) (= (= (f3 f37 (f26 f27 ?v0)) f1) (= (f57 f31 ?v0) f1))))
(assert (forall ((?v0 S15)) (let ((?v_0 (f26 f27 ?v0))) (= (f26 f27 (f28 f29 ?v0)) (f4 (f6 f42 (f4 (f6 f42 f37) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S15)) (let ((?v_0 (f28 f51 ?v0))) (= (f28 f51 (f28 f29 ?v0)) (f28 (f53 f54 (f28 (f53 f54 f52) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S15)) (let ((?v_0 (f45 f46 ?v0))) (= (f45 f46 (f28 f29 ?v0)) (f10 (f38 f61 (f10 (f38 f61 f49) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S2)) (= (f4 (f6 f24 ?v0) (f26 f27 f31)) f37)))
(assert (forall ((?v0 S6)) (= (f10 (f38 f47 ?v0) (f45 f46 f31)) f49)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f40 (f4 (f6 f7 (f4 f44 ?v0)) (f4 f44 ?v1)) (f4 f44 (f4 (f6 f42 ?v0) ?v1))) f1)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f40 (f4 (f6 f7 (f8 f9 ?v0)) (f8 f9 ?v1)) (f8 f9 (f10 (f38 f61 ?v0) ?v1))) f1)))
(check-sat)
(exit)
