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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S4 S5) S2)
(declare-fun f6 (S6 S7) S4)
(declare-fun f7 (S8 S7) S6)
(declare-fun f8 () S8)
(declare-fun f9 () S7)
(declare-fun f10 () S7)
(declare-fun f11 (S9 S5) S5)
(declare-fun f12 (S10 S11) S9)
(declare-fun f13 () S10)
(declare-fun f14 () S11)
(declare-fun f15 (S12 S5) S9)
(declare-fun f16 () S12)
(declare-fun f17 (S13 S11) S5)
(declare-fun f18 () S13)
(declare-fun f19 () S11)
(declare-fun f20 () S3)
(declare-fun f21 () S7)
(declare-fun f22 () S7)
(declare-fun f23 () S5)
(declare-fun f24 (S5 S14) S1)
(declare-fun f25 (S14) S14)
(declare-fun f26 (S15 S16) S14)
(declare-fun f27 (S7) S15)
(declare-fun f28 () S7)
(declare-fun f29 (S17 S16) S16)
(declare-fun f30 (S18 S3) S17)
(declare-fun f31 () S18)
(declare-fun f32 (S19 S16) S17)
(declare-fun f33 () S19)
(declare-fun f34 () S17)
(declare-fun f35 () S16)
(declare-fun f36 (S20 S2) S17)
(declare-fun f37 () S20)
(declare-fun f38 () S16)
(declare-fun f39 (S7 S21) S1)
(declare-fun f40 () S21)
(declare-fun f41 (S16 S22) S1)
(declare-fun f42 () S22)
(declare-fun f43 () S7)
(declare-fun f44 (S2 S3) S1)
(declare-fun f45 () S7)
(declare-fun f46 (S23 S7) S11)
(declare-fun f47 () S23)
(declare-fun f48 () S11)
(declare-fun f49 (S24 S7) S5)
(declare-fun f50 () S24)
(declare-fun f51 () S13)
(declare-fun f52 () S11)
(declare-fun f53 (S16) S3)
(declare-fun f54 (S14) S14)
(declare-fun f55 (S7 S7 S5 S16) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f17 f18 f19))) (= (= (f3 f4 ?v0) f1) (not (= ?v0 (f5 (f6 (f7 f8 f9) f10) (f11 (f12 f13 f14) (f11 (f15 f16 ?v_0) ?v_0)))))))))
(assert (forall ((?v0 S2)) (= (= (f3 f20 ?v0) f1) (not (= ?v0 (f5 (f6 (f7 f8 f21) f22) f23))))))
(assert (let ((?v_0 (f17 f18 f19))) (not (=> (and (= f9 f21) (and (= f10 f22) (= (f11 (f12 f13 f14) (f11 (f15 f16 ?v_0) ?v_0)) f23))) (not (= (f24 f23 (f25 (f26 (f27 f28) (f29 (f30 f31 f20) (f29 (f32 f33 (f29 f34 f35)) (f29 (f36 f37 (f5 (f6 (f7 f8 f21) f22) f23)) f38)))))) f1))))))
(assert (not (= (f39 f9 f40) f1)))
(assert (not (= (f39 f10 f40) f1)))
(assert (= (f41 f35 f42) f1))
(assert (not (= f21 f43)))
(assert (= (f44 (f5 (f6 (f7 f8 f45) f21) (f11 (f12 f13 (f46 f47 f21)) (f11 (f15 f16 (f17 f18 f48)) (f11 (f15 f16 (f49 f50 f22)) (f11 (f15 f16 (f17 f51 f52)) f23))))) (f53 f35)) f1))
(assert (= (f44 (f5 (f6 (f7 f8 f21) f43) (f11 (f15 f16 (f49 f50 f21)) (f11 (f15 f16 (f49 f50 f22)) (f17 f18 f48)))) (f53 f35)) f1))
(assert (not (= (f24 (f17 f51 f14) (f54 (f26 (f27 f28) f35))) f1)))
(assert (let ((?v_0 (f17 f18 f19))) (let ((?v_1 (f11 (f12 f13 f14) (f11 (f15 f16 ?v_0) ?v_0)))) (=> (= (f44 (f5 (f6 (f7 f8 f9) f10) ?v_1) (f53 f35)) f1) (not (= (f24 ?v_1 (f25 (f26 (f27 f28) (f29 (f30 f31 f4) (f29 f34 f35))))) f1))))))
(assert (= (f41 f38 f42) f1))
(assert (forall ((?v0 S16)) (let ((?v_0 (f27 f28))) (= (f26 ?v_0 ?v0) (f26 ?v_0 (f29 f34 ?v0))))))
(assert (forall ((?v0 S7) (?v1 S16) (?v2 S11) (?v3 S7) (?v4 S5) (?v5 S11)) (let ((?v_0 (f17 f51 ?v2)) (?v_3 (f26 (f27 f28) ?v1))) (let ((?v_1 (f15 f16 ?v_0)) (?v_5 (f53 ?v1)) (?v_2 (f17 f18 ?v5))) (let ((?v_4 (f11 (f12 f13 ?v2) (f11 (f15 f16 ?v_2) ?v_2)))) (=> (not (= (f39 ?v0 f40) f1)) (=> (= (f41 ?v1 f42) f1) (=> (not (= (f24 ?v_0 (f54 ?v_3)) f1)) (=> (= (f44 (f5 (f6 (f7 f8 f43) ?v3) (f11 (f12 f13 (f46 f47 ?v3)) (f11 (f15 f16 ?v4) (f11 (f15 f16 (f49 f50 ?v0)) (f11 ?v_1 (f11 (f12 f13 (f46 f47 ?v0)) (f11 ?v_1 (f49 f50 ?v3)))))))) ?v_5) f1) (=> (= (f24 ?v_4 (f25 ?v_3)) f1) (= (f44 (f5 (f6 (f7 f8 ?v3) ?v0) ?v_4) ?v_5) f1)))))))))))
(assert (forall ((?v0 S16) (?v1 S7)) (=> (= (f41 ?v0 f42) f1) (= (= (f24 (f17 f51 (f46 f47 ?v1)) (f54 (f26 (f27 f28) ?v0))) f1) (= (f39 ?v1 f40) f1)))))
(assert (forall ((?v0 S16) (?v1 S7)) (=> (= (f41 ?v0 f42) f1) (= (= (f24 (f17 f51 (f46 f47 ?v1)) (f25 (f26 (f27 f28) ?v0))) f1) (= (f39 ?v1 f40) f1)))))
(assert (forall ((?v0 S16) (?v1 S7) (?v2 S7) (?v3 S11) (?v4 S7) (?v5 S11) (?v6 S5)) (let ((?v_1 (f17 f18 ?v3)) (?v_0 (f15 f16 (f49 f50 ?v4))) (?v_2 (f53 ?v0)) (?v_3 (f7 f8 ?v1))) (=> (= (f41 ?v0 f42) f1) (=> (not (= ?v1 f43)) (=> (= (f44 (f5 (f6 (f7 f8 ?v2) ?v1) (f11 (f12 f13 (f46 f47 ?v1)) (f11 (f15 f16 ?v_1) (f11 ?v_0 (f11 (f15 f16 (f17 f51 ?v5)) ?v6))))) ?v_2) f1) (=> (= (f44 (f5 (f6 ?v_3 f43) (f11 (f15 f16 (f49 f50 ?v1)) (f11 ?v_0 ?v_1))) ?v_2) f1) (= (f41 (f29 (f36 f37 (f5 (f6 ?v_3 ?v4) ?v6)) ?v0) f42) f1))))))))
(assert (forall ((?v0 S16) (?v1 S11) (?v2 S7) (?v3 S5) (?v4 S7) (?v5 S5) (?v6 S11)) (let ((?v_0 (f17 f51 ?v1)) (?v_1 (f26 (f27 f28) ?v0)) (?v_3 (f53 ?v0)) (?v_2 (f11 (f12 f13 ?v1) (f17 f18 ?v6)))) (=> (= (f41 ?v0 f42) f1) (=> (not (= (f24 ?v_0 (f54 ?v_1)) f1)) (=> (= (f44 (f5 (f6 (f7 f8 f43) ?v2) (f11 (f12 f13 (f46 f47 ?v2)) (f11 (f15 f16 ?v3) (f11 (f15 f16 (f49 f50 ?v4)) (f11 (f15 f16 ?v_0) ?v5))))) ?v_3) f1) (=> (= (f24 ?v_2 (f25 ?v_1)) f1) (= (f44 (f5 (f6 (f7 f8 ?v4) ?v2) ?v_2) ?v_3) f1))))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S16) (?v3 S7) (?v4 S11) (?v5 S7) (?v6 S5)) (let ((?v_0 (f17 f18 ?v1))) (let ((?v_4 (f11 (f12 f13 ?v0) (f11 (f15 f16 ?v_0) ?v_0))) (?v_3 (f26 (f27 f28) ?v2))) (let ((?v_1 (f25 ?v_3)) (?v_2 (f17 f51 ?v0))) (=> (= (f24 ?v_4 ?v_1) f1) (=> (= (f24 (f11 (f12 f13 (f46 f47 ?v3)) (f11 (f15 f16 (f17 f18 ?v4)) (f11 (f15 f16 (f49 f50 ?v5)) (f11 (f15 f16 ?v_2) ?v6)))) ?v_1) f1) (=> (not (= (f24 ?v_2 (f54 ?v_3)) f1)) (=> (not (= (f39 ?v3 f40) f1)) (=> (not (= (f39 ?v5 f40) f1)) (=> (= (f41 ?v2 f42) f1) (= (f44 (f5 (f6 (f7 f8 ?v3) ?v5) ?v_4) (f53 ?v2)) f1))))))))))))
(assert (forall ((?v0 S7) (?v1 S5) (?v2 S7) (?v3 S11) (?v4 S5) (?v5 S16)) (let ((?v_0 (f11 (f12 f13 (f46 f47 ?v0)) (f11 (f15 f16 ?v1) (f11 (f15 f16 (f49 f50 ?v2)) (f11 (f15 f16 (f17 f51 ?v3)) ?v4)))))) (=> (= (f24 ?v_0 (f25 (f26 (f27 f28) ?v5))) f1) (=> (not (= (f39 ?v0 f40) f1)) (=> (= (f41 ?v5 f42) f1) (= (f44 (f5 (f6 (f7 f8 f43) ?v0) ?v_0) (f53 ?v5)) f1)))))))
(assert (forall ((?v0 S7) (?v1 S5) (?v2 S5) (?v3 S5) (?v4 S5) (?v5 S16)) (=> (= (f44 (f5 (f6 (f7 f8 f43) ?v0) (f11 (f12 f13 (f46 f47 ?v0)) (f11 (f15 f16 ?v1) (f11 (f15 f16 ?v2) (f11 (f15 f16 ?v3) ?v4))))) (f53 ?v5)) f1) (= (f24 ?v3 (f25 (f26 (f27 f28) ?v5))) f1))))
(assert (forall ((?v0 S7) (?v1 S5) (?v2 S7) (?v3 S11) (?v4 S5) (?v5 S16) (?v6 S7) (?v7 S5) (?v8 S7) (?v9 S5)) (let ((?v_0 (f7 f8 f43)) (?v_1 (f15 f16 (f17 f51 ?v3))) (?v_2 (f53 ?v5))) (=> (= (f44 (f5 (f6 ?v_0 ?v0) (f11 (f12 f13 (f46 f47 ?v0)) (f11 (f15 f16 ?v1) (f11 (f15 f16 (f49 f50 ?v2)) (f11 ?v_1 ?v4))))) ?v_2) f1) (=> (= (f44 (f5 (f6 ?v_0 ?v6) (f11 (f12 f13 (f46 f47 ?v6)) (f11 (f15 f16 ?v7) (f11 (f15 f16 (f49 f50 ?v8)) (f11 ?v_1 ?v9))))) ?v_2) f1) (=> (= (f41 ?v5 f42) f1) (and (= ?v0 ?v6) (and (= ?v1 ?v7) (and (= ?v2 ?v8) (= ?v4 ?v9))))))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S11) (?v3 S5) (?v4 S5) (?v5 S5) (?v6 S5) (?v7 S16)) (=> (= (f44 (f5 (f6 (f7 f8 ?v0) ?v1) (f11 (f12 f13 ?v2) (f11 (f15 f16 ?v3) (f11 (f15 f16 ?v4) (f11 (f15 f16 ?v5) ?v6))))) (f53 ?v7)) f1) (= (f24 ?v6 (f25 (f26 (f27 f28) ?v7))) f1))))
(assert (forall ((?v0 S16) (?v1 S11) (?v2 S7) (?v3 S5) (?v4 S7) (?v5 S5) (?v6 S11)) (let ((?v_0 (f17 f51 ?v1)) (?v_1 (f26 (f27 f28) ?v0))) (=> (= (f41 ?v0 f42) f1) (=> (not (= (f24 ?v_0 (f54 ?v_1)) f1)) (=> (= (f44 (f5 (f6 (f7 f8 f43) ?v2) (f11 (f12 f13 (f46 f47 ?v2)) (f11 (f15 f16 ?v3) (f11 (f15 f16 (f49 f50 ?v4)) (f11 (f15 f16 ?v_0) ?v5))))) (f53 ?v0)) f1) (=> (= (f24 (f11 (f12 f13 ?v1) (f17 f18 ?v6)) (f25 ?v_1)) f1) (exists ((?v7 S7)) (= (f44 (f5 (f6 (f7 f8 ?v7) ?v4) ?v5) (f53 ?v0)) f1)))))))))
(assert (forall ((?v0 S7) (?v1 S11) (?v2 S7) (?v3 S16)) (=> (= (f24 (f11 (f12 f13 (f46 f47 ?v0)) (f11 (f15 f16 (f17 f51 ?v1)) (f49 f50 ?v2))) (f25 (f26 (f27 f28) ?v3))) f1) (=> (not (= (f39 ?v0 f40) f1)) (=> (= (f41 ?v3 f42) f1) (exists ((?v4 S5)) (let ((?v_0 (f15 f16 (f17 f51 ?v1)))) (= (f44 (f5 (f6 (f7 f8 f43) ?v2) (f11 (f12 f13 (f46 f47 ?v2)) (f11 (f15 f16 ?v4) (f11 (f15 f16 (f49 f50 ?v0)) (f11 ?v_0 (f11 (f12 f13 (f46 f47 ?v0)) (f11 ?v_0 (f49 f50 ?v2)))))))) (f53 ?v3)) f1))))))))
(assert (forall ((?v0 S7) (?v1 S16)) (=> (= (f39 ?v0 f40) f1) (= (f24 (f17 f51 (f46 f47 ?v0)) (f26 (f27 f28) ?v1)) f1))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S16) (?v3 S7) (?v4 S5) (?v5 S7) (?v6 S5)) (let ((?v_3 (f11 (f12 f13 ?v0) (f17 f18 ?v1))) (?v_2 (f26 (f27 f28) ?v2))) (let ((?v_0 (f25 ?v_2)) (?v_1 (f17 f51 ?v0))) (=> (= (f24 ?v_3 ?v_0) f1) (=> (= (f24 (f11 (f12 f13 (f46 f47 ?v3)) (f11 (f15 f16 ?v4) (f11 (f15 f16 (f49 f50 ?v5)) (f11 (f15 f16 ?v_1) ?v6)))) ?v_0) f1) (=> (not (= (f24 ?v_1 (f54 ?v_2)) f1)) (=> (not (= (f39 ?v3 f40) f1)) (=> (not (= (f39 ?v5 f40) f1)) (=> (= (f41 ?v2 f42) f1) (= (f55 ?v5 ?v3 ?v_3 ?v2) f1)))))))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S11) (?v3 S11) (?v4 S16)) (let ((?v_0 (f11 (f12 f13 ?v2) (f17 f18 ?v3)))) (=> (= (f44 (f5 (f6 (f7 f8 ?v0) ?v1) ?v_0) (f53 ?v4)) f1) (=> (not (= (f24 (f17 f51 ?v2) (f54 (f26 (f27 f28) ?v4))) f1)) (=> (not (= (f39 ?v1 f40) f1)) (=> (not (= (f39 ?v0 f40) f1)) (=> (= (f41 ?v4 f42) f1) (= (f55 ?v0 ?v1 ?v_0 ?v4) f1)))))))))
(assert (forall ((?v0 S7) (?v1 S16)) (= (f24 (f17 f51 (f46 f47 ?v0)) (f26 (f27 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S7) (?v1 S5) (?v2 S16)) (let ((?v_0 (f54 (f26 (f27 f28) ?v2)))) (=> (= (f24 (f11 (f12 f13 (f46 f47 ?v0)) ?v1) ?v_0) f1) (=> (= (f39 ?v0 f40) f1) (= (f24 ?v1 ?v_0) f1))))))
(assert (= (f39 f28 f40) f1))
(assert (forall ((?v0 S5) (?v1 S7) (?v2 S7) (?v3 S5) (?v4 S16)) (let ((?v_0 (f27 f28))) (=> (not (= (f24 ?v0 (f54 (f26 ?v_0 (f29 (f36 f37 (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) ?v4)))) f1)) (not (= (f24 ?v0 (f54 (f26 ?v_0 ?v4))) f1))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S5) (?v3 S16)) (=> (= (f44 (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) (f53 ?v3)) f1) (=> (=> (= (f24 ?v2 (f25 (f26 (f27 f28) ?v3))) f1) false) false))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S5) (?v3 S16)) (=> (= (f44 (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) (f53 ?v3)) f1) (= (f24 ?v2 (f54 (f26 (f27 f28) ?v3))) f1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S14)) (let ((?v_0 (f25 ?v2))) (=> (= (f24 (f11 (f15 f16 ?v0) ?v1) ?v_0) f1) (=> (=> (= (f24 ?v0 ?v_0) f1) (=> (= (f24 ?v1 ?v_0) f1) false)) false)))))
(assert (forall ((?v0 S5) (?v1 S14)) (=> (= (f24 ?v0 ?v1) f1) (= (f24 ?v0 (f54 ?v1)) f1))))
(assert (forall ((?v0 S5) (?v1 S14)) (=> (= (f24 ?v0 ?v1) f1) (= (f24 ?v0 (f25 ?v1)) f1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S14)) (let ((?v_0 (f54 ?v2))) (=> (= (f24 (f11 (f15 f16 ?v0) ?v1) ?v_0) f1) (=> (=> (= (f24 ?v0 ?v_0) f1) (=> (= (f24 ?v1 ?v_0) f1) false)) false)))))
(assert (forall ((?v0 S5) (?v1 S14)) (let ((?v_0 (f54 ?v1))) (=> (= (f24 ?v0 (f54 ?v_0)) f1) (= (f24 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S14)) (let ((?v_0 (f54 ?v0))) (= (f54 ?v_0) ?v_0))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (= (= (f11 (f15 f16 ?v0) ?v1) (f11 (f15 f16 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f17 f51 ?v0) (f17 f51 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S14)) (let ((?v_0 (f25 ?v1))) (=> (= (f24 ?v0 (f25 ?v_0)) f1) (= (f24 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S14)) (let ((?v_0 (f25 ?v0))) (= (f25 ?v_0) ?v_0))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S11) (?v3 S5)) (= (= (f11 (f12 f13 ?v0) ?v1) (f11 (f12 f13 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f17 f18 ?v0) (f17 f18 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f49 f50 ?v0) (f49 f50 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S5) (?v3 S7) (?v4 S7) (?v5 S5)) (= (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f46 f47 ?v0) (f46 f47 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S14)) (let ((?v_0 (f54 ?v2))) (=> (= (f24 (f11 (f15 f16 ?v0) ?v1) ?v_0) f1) (= (f24 ?v1 ?v_0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S14)) (let ((?v_0 (f54 ?v2))) (=> (= (f24 (f11 (f15 f16 ?v0) ?v1) ?v_0) f1) (= (f24 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S11)) (not (= (f11 (f15 f16 ?v0) ?v1) (f17 f51 ?v2)))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S5)) (not (= (f17 f51 ?v0) (f11 (f15 f16 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S14)) (=> (= (f24 ?v0 (f54 ?v1)) f1) (= (f24 ?v0 (f25 ?v1)) f1))))
(assert (forall ((?v0 S5) (?v1 S14)) (=> (not (= (f24 ?v0 (f25 ?v1)) f1)) (not (= (f24 ?v0 (f54 ?v1)) f1)))))
(assert (forall ((?v0 S5) (?v1 S14)) (let ((?v_0 (= (f24 ?v0 (f25 ?v1)) f1))) (= (or (= (f24 ?v0 (f54 ?v1)) f1) ?v_0) ?v_0))))
(assert (forall ((?v0 S5) (?v1 S14)) (let ((?v_0 (= (f24 ?v0 (f54 ?v1)) f1))) (= (and ?v_0 (= (f24 ?v0 (f25 ?v1)) f1)) ?v_0))))
(assert (forall ((?v0 S14)) (= (f25 (f54 ?v0)) (f25 ?v0))))
(assert (forall ((?v0 S14)) (let ((?v_0 (f25 ?v0))) (= (f54 ?v_0) ?v_0))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S14)) (let ((?v_0 (f25 ?v2))) (=> (= (f24 (f11 (f15 f16 ?v0) ?v1) ?v_0) f1) (= (f24 ?v1 ?v_0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S14)) (let ((?v_0 (f25 ?v2))) (=> (= (f24 (f11 (f15 f16 ?v0) ?v1) ?v_0) f1) (= (f24 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S11) (?v3 S5)) (not (= (f11 (f15 f16 ?v0) ?v1) (f11 (f12 f13 ?v2) ?v3)))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S5) (?v3 S5)) (not (= (f11 (f12 f13 ?v0) ?v1) (f11 (f15 f16 ?v2) ?v3)))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S11)) (not (= (f11 (f12 f13 ?v0) ?v1) (f17 f51 ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S5)) (not (= (f17 f51 ?v0) (f11 (f12 f13 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S14)) (let ((?v_0 (f25 ?v2))) (=> (= (f24 (f11 (f12 f13 ?v0) ?v1) ?v_0) f1) (=> (=> (= (f24 ?v1 ?v_0) f1) false) false)))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S14)) (let ((?v_0 (f25 ?v2))) (=> (= (f24 (f11 (f12 f13 ?v0) ?v1) ?v_0) f1) (= (f24 ?v1 ?v_0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S11)) (not (= (f11 (f15 f16 ?v0) ?v1) (f17 f18 ?v2)))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S5)) (not (= (f17 f18 ?v0) (f11 (f15 f16 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11)) (not (= (f17 f18 ?v0) (f17 f51 ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (not (= (f17 f51 ?v0) (f17 f18 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S7)) (not (= (f11 (f15 f16 ?v0) ?v1) (f49 f50 ?v2)))))
(assert (forall ((?v0 S7) (?v1 S5) (?v2 S5)) (not (= (f49 f50 ?v0) (f11 (f15 f16 ?v1) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S11)) (not (= (f49 f50 ?v0) (f17 f51 ?v1)))))
(check-sat)
(exit)