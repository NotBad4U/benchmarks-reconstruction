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
(declare-sort S32 0)
(declare-sort S33 0)
(declare-sort S34 0)
(declare-sort S35 0)
(declare-sort S36 0)
(declare-sort S37 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 () S3)
(declare-fun f6 (S4 S2 S5) S1)
(declare-fun f7 (S7 S5) S4)
(declare-fun f8 (S8 S6) S7)
(declare-fun f9 (S9 S4) S8)
(declare-fun f10 () S9)
(declare-fun f11 () S5)
(declare-fun f12 (S10 S6) S2)
(declare-fun f13 (S11 S2) S10)
(declare-fun f14 (S12 S2) S11)
(declare-fun f15 () S12)
(declare-fun f16 () S3)
(declare-fun f17 (S13 S3) S3)
(declare-fun f18 (S3) S13)
(declare-fun f19 (S16 S15) S1)
(declare-fun f20 (S17 S5) S16)
(declare-fun f21 (S4 S2 S14) S17)
(declare-fun f22 (S4 S14 S15) S1)
(declare-fun f23 (S3 S14) S1)
(declare-fun f24 () S14)
(declare-fun f25 () S14)
(declare-fun f26 () S4)
(declare-fun f27 () S6)
(declare-fun f28 (S18 S14) S2)
(declare-fun f29 (S19 S2) S18)
(declare-fun f30 (S20 S21) S19)
(declare-fun f31 () S20)
(declare-fun f32 () S21)
(declare-fun f33 () S10)
(declare-fun f34 () S6)
(declare-fun f35 () S5)
(declare-fun f36 () S2)
(declare-fun f37 () S2)
(declare-fun f38 () S2)
(declare-fun f39 () S6)
(declare-fun f40 (S22 S5) S5)
(declare-fun f41 (S23 S5) S22)
(declare-fun f42 () S23)
(declare-fun f43 () S4)
(declare-fun f44 (S4 S6) S5)
(declare-fun f45 (S24 S14) S14)
(declare-fun f46 (S25 S2) S24)
(declare-fun f47 () S25)
(declare-fun f48 () S2)
(declare-fun f49 (S26 S2) S2)
(declare-fun f50 (S21 S2) S26)
(declare-fun f51 () S5)
(declare-fun f52 () S5)
(declare-fun f53 (S27 S15) S15)
(declare-fun f54 (S28 S5) S27)
(declare-fun f55 () S28)
(declare-fun f56 (S31 S29) S29)
(declare-fun f57 (S32 S30) S31)
(declare-fun f58 () S32)
(declare-fun f59 (S34 S30) S30)
(declare-fun f60 (S35 S33) S34)
(declare-fun f61 () S35)
(declare-fun f62 () S15)
(declare-fun f63 (S36 S15) S22)
(declare-fun f64 (S37 S23) S36)
(declare-fun f65 () S37)
(declare-fun f66 () S11)
(declare-fun f67 () S6)
(declare-fun f68 (S1 S17 S15) S1)
(declare-fun f69 () S26)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (and (= (f3 f5 ?v0) f1) (forall ((?v1 S4) (?v2 S5) (?v3 S2) (?v4 S6)) (=> (= (f6 (f7 (f8 (f9 f10 ?v1) ?v4) f11) ?v0 ?v2) f1) (=> (= (f3 f5 ?v3) f1) (=> (= (f6 ?v1 ?v3 f11) f1) (= (f3 f5 (f12 (f13 (f14 f15 ?v0) ?v3) ?v4)) f1)))))))))
(assert (forall ((?v0 S2)) (= (= (f3 f16 ?v0) f1) (forall ((?v1 S4) (?v2 S5) (?v3 S2) (?v4 S6)) (=> (= (f6 (f7 (f8 (f9 f10 ?v1) ?v4) f11) ?v0 ?v2) f1) (=> (= (f3 f5 ?v3) f1) (=> (= (f6 ?v1 ?v3 f11) f1) (= (f3 f5 (f12 (f13 (f14 f15 ?v0) ?v3) ?v4)) f1))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (= (= (f3 (f17 (f18 ?v0) ?v1) ?v2) f1) (and (= (f3 ?v0 ?v2) f1) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S14) (?v3 S5) (?v4 S15)) (= (= (f19 (f20 (f21 ?v0 ?v1 ?v2) ?v3) ?v4) f1) (and (= (f6 ?v0 ?v1 ?v3) f1) (= (f22 ?v0 ?v2 ?v4) f1)))))
(assert (not (= (f23 f16 f24) f1)))
(assert (= (f23 f4 f25) f1))
(assert (= (f6 (f7 (f8 (f9 f10 f26) f27) f11) (f28 (f29 (f30 f31 f32) (f12 f33 f34)) f25) f35) f1))
(assert (= (f3 f5 f36) f1))
(assert (= (f6 f26 f36 f11) f1))
(assert (= (f3 f5 f36) f1))
(assert (= (f3 f5 f37) f1))
(assert (= (f6 f26 f36 f11) f1))
(assert (= (f3 f5 f38) f1))
(assert (= f34 f39))
(assert (= (f23 f4 f25) f1))
(assert (= (f6 (f7 (f8 (f9 f10 f26) f27) f11) (f28 (f29 (f30 f31 f32) (f12 f33 f34)) f25) f35) f1))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S2) (?v3 S4) (?v4 S6) (?v5 S5) (?v6 S2)) (=> (= f11 (f40 (f41 f42 ?v0) ?v1)) (=> (= (f3 f5 ?v2) f1) (=> (= (f6 (f7 (f8 (f9 f10 ?v3) ?v4) ?v0) ?v2 ?v5) f1) (=> (= (f3 f5 ?v6) f1) (=> (= (f6 ?v3 ?v6 ?v0) f1) (= (f3 f5 (f12 (f13 (f14 f15 ?v2) ?v6) ?v4)) f1))))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S2) (?v3 S4) (?v4 S6) (?v5 S5) (?v6 S2)) (=> (= f11 (f40 (f41 f42 ?v0) ?v1)) (=> (= (f3 f5 ?v2) f1) (=> (= (f6 (f7 (f8 (f9 f10 ?v3) ?v4) ?v1) ?v2 ?v5) f1) (=> (= (f3 f5 ?v6) f1) (=> (= (f6 ?v3 ?v6 ?v1) f1) (= (f3 f5 (f12 (f13 (f14 f15 ?v2) ?v6) ?v4)) f1))))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S5) (?v3 S4) (?v4 S2) (?v5 S5) (?v6 S6)) (=> (= (f6 ?v0 ?v1 ?v2) f1) (=> (= (f6 ?v3 ?v4 ?v5) f1) (=> (= ?v0 (f7 (f8 (f9 f10 ?v3) ?v6) ?v5)) (= (f6 ?v3 (f12 (f13 (f14 f15 ?v1) ?v4) ?v6) ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6)) (=> (= (f3 f5 ?v0) f1) (= (f3 f5 (f12 (f13 (f14 f15 ?v0) (f12 f33 ?v1)) ?v2)) f1))))
(assert (= (f6 f43 f38 f11) f1))
(assert (forall ((?v0 S6)) (= (f3 f5 (f12 f33 ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S14)) (= (= (f23 (f17 (f18 ?v0) ?v1) ?v2) f1) (and (= (f23 ?v0 ?v2) f1) (= (f23 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S4) (?v3 S5)) (=> (= ?v0 ?v1) (= (f44 (f7 (f8 (f9 f10 ?v2) ?v0) ?v3) ?v1) ?v3))))
(assert (= f25 (f45 (f46 f47 f48) f24)))
(assert (forall ((?v0 S4) (?v1 S6) (?v2 S5)) (=> (= (f44 ?v0 ?v1) ?v2) (= (f6 ?v0 (f12 f33 ?v1) ?v2) f1))))
(assert (forall ((?v0 S4) (?v1 S6) (?v2 S5)) (=> (= (f6 ?v0 (f12 f33 ?v1) ?v2) f1) (=> (=> (= (f44 ?v0 ?v1) ?v2) false) false))))
(assert (= (f3 f5 (f49 (f50 f32 f38) (f12 (f13 (f14 f15 f48) f38) f39))) f1))
(assert (= (f6 (f7 (f8 (f9 f10 f43) f39) f11) f48 f51) f1))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S5) (?v3 S5) (?v4 S2)) (=> (= (f6 ?v0 ?v1 (f40 (f41 f42 ?v2) ?v3)) f1) (=> (= (f6 ?v0 ?v4 ?v2) f1) (= (f6 ?v0 (f49 (f50 f32 ?v1) ?v4) ?v3) f1)))))
(assert (= (f6 (f7 (f8 (f9 f10 f43) f39) f11) (f28 (f29 (f30 f31 f32) (f12 f33 f34)) f25) f52) f1))
(assert (forall ((?v0 S15) (?v1 S5)) (not (= ?v0 (f53 (f54 f55 ?v1) ?v0)))))
(assert (forall ((?v0 S14) (?v1 S2)) (not (= ?v0 (f45 (f46 f47 ?v1) ?v0)))))
(assert (forall ((?v0 S29) (?v1 S30)) (not (= ?v0 (f56 (f57 f58 ?v1) ?v0)))))
(assert (forall ((?v0 S30) (?v1 S33)) (not (= ?v0 (f59 (f60 f61 ?v1) ?v0)))))
(assert (forall ((?v0 S5) (?v1 S15)) (not (= (f53 (f54 f55 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S14)) (not (= (f45 (f46 f47 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S30) (?v1 S29)) (not (= (f56 (f57 f58 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S33) (?v1 S30)) (not (= (f59 (f60 f61 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (= (= (f40 (f41 f42 ?v0) ?v1) (f40 (f41 f42 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5) (?v1 S15) (?v2 S5) (?v3 S15)) (= (= (f53 (f54 f55 ?v0) ?v1) (f53 (f54 f55 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2) (?v3 S14)) (= (= (f45 (f46 f47 ?v0) ?v1) (f45 (f46 f47 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S30) (?v1 S29) (?v2 S30) (?v3 S29)) (= (= (f56 (f57 f58 ?v0) ?v1) (f56 (f57 f58 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S33) (?v1 S30) (?v2 S33) (?v3 S30)) (= (= (f59 (f60 f61 ?v0) ?v1) (f59 (f60 f61 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S21) (?v1 S2) (?v2 S2) (?v3 S14)) (let ((?v_0 (f30 f31 ?v0))) (= (f28 (f29 ?v_0 ?v1) (f45 (f46 f47 ?v2) ?v3)) (f28 (f29 ?v_0 (f49 (f50 ?v0 ?v1) ?v2)) ?v3)))))
(assert (forall ((?v0 S4) (?v1 S6) (?v2 S14) (?v3 S5) (?v4 S5)) (let ((?v_0 (f28 (f29 (f30 f31 f32) (f12 f33 ?v1)) ?v2))) (=> (= (f6 ?v0 ?v_0 ?v3) f1) (=> (= (f6 ?v0 ?v_0 ?v4) f1) (= ?v3 ?v4))))))
(assert (forall ((?v0 S2) (?v1 S6)) (=> (= (f3 f5 ?v0) f1) (= (f3 f5 (f49 (f50 f32 ?v0) (f12 f33 ?v1))) f1))))
(assert (= (f6 (f7 (f8 (f9 f10 f43) f39) f11) (f28 (f29 (f30 f31 f32) (f49 (f50 f32 (f12 f33 f34)) f48)) f24) f52) f1))
(assert (forall ((?v0 S14) (?v1 S6)) (=> (= (f23 f5 ?v0) f1) (= (f3 f5 (f28 (f29 (f30 f31 f32) (f12 f33 ?v1)) ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S5)) (=> (= (f6 ?v0 (f49 (f50 f32 ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S5)) (=> (= (f6 ?v0 ?v1 (f40 (f41 f42 ?v4) ?v3)) f1) (=> (= (f6 ?v0 ?v2 ?v4) f1) false))) false))))
(assert (= (f22 (f7 (f8 (f9 f10 f43) f39) f11) f24 f62) f1))
(assert (= (f6 (f7 (f8 (f9 f10 f43) f39) f11) (f49 (f50 f32 (f12 f33 f34)) f48) (f40 (f63 (f64 f65 f42) f62) f52)) f1))
(assert (forall ((?v0 S6) (?v1 S14) (?v2 S6) (?v3 S14)) (let ((?v_0 (f30 f31 f32))) (= (= (f28 (f29 ?v_0 (f12 f33 ?v0)) ?v1) (f28 (f29 ?v_0 (f12 f33 ?v2)) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (= (f3 f5 (f12 (f13 (f14 f15 (f49 (f50 f32 (f12 (f13 f66 f38) f67)) (f12 f33 f67))) (f12 (f13 (f14 f15 f48) f38) f39)) f67)) f1))
(assert (=> (forall ((?v0 S15)) (let ((?v_0 (f7 (f8 (f9 f10 f43) f39) f11))) (=> (= (f6 ?v_0 (f49 (f50 f32 (f12 f33 f34)) f48) (f40 (f63 (f64 f65 f42) ?v0) f52)) f1) (=> (= (f22 ?v_0 f24 ?v0) f1) false)))) false))
(assert (forall ((?v0 S6) (?v1 S2)) (= (f12 (f13 (f14 f15 (f12 f33 ?v0)) ?v1) ?v0) ?v1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S6)) (= (f12 (f13 (f14 f15 (f49 (f50 f32 ?v0) ?v1)) ?v2) ?v3) (f49 (f50 f32 (f12 (f13 (f14 f15 ?v0) ?v2) ?v3)) (f12 (f13 (f14 f15 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S6)) (=> (= (f3 f5 ?v0) f1) (= (f3 f5 (f12 (f13 f66 ?v0) ?v1)) f1))))
(assert (= (f6 (f7 (f8 (f9 f10 f43) f39) f11) (f12 f33 f34) (f40 (f41 f42 f51) (f40 (f63 (f64 f65 f42) f62) f52))) f1))
(assert (= f11 (f40 (f41 f42 f51) (f40 (f63 (f64 f65 f42) f62) f52))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S5) (?v3 S6) (?v4 S5)) (=> (= (f6 ?v0 ?v1 ?v2) f1) (= (f6 (f7 (f8 (f9 f10 ?v0) ?v3) ?v4) (f12 (f13 f66 ?v1) ?v3) ?v2) f1))))
(assert (= (f6 f43 f38 (f40 (f41 f42 f51) (f40 (f63 (f64 f65 f42) f62) f52))) f1))
(assert (=> (forall ((?v0 S5)) (let ((?v_0 (f7 (f8 (f9 f10 f43) f39) f11))) (=> (= (f6 ?v_0 (f12 f33 f34) (f40 (f41 f42 ?v0) (f40 (f63 (f64 f65 f42) f62) f52))) f1) (=> (= (f6 ?v_0 f48 ?v0) f1) false)))) false))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (= (f12 (f13 f66 (f49 (f50 f32 ?v0) ?v1)) ?v2) (f49 (f50 f32 (f12 (f13 f66 ?v0) ?v2)) (f12 (f13 f66 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S2)) (= (f12 (f13 (f14 f15 (f12 (f13 f66 ?v0) ?v1)) ?v2) ?v1) ?v0)))
(assert (forall ((?v0 S23) (?v1 S5) (?v2 S15) (?v3 S5)) (let ((?v_0 (f64 f65 ?v0))) (= (f40 (f63 ?v_0 (f53 (f54 f55 ?v1) ?v2)) ?v3) (f40 (f41 ?v0 ?v1) (f40 (f63 ?v_0 ?v2) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S15) (?v3 S5) (?v4 S14)) (=> (= (f6 ?v0 ?v1 (f40 (f63 (f64 f65 f42) ?v2) ?v3)) f1) (=> (= (f22 ?v0 ?v4 ?v2) f1) (= (f6 ?v0 (f28 (f29 (f30 f31 f32) ?v1) ?v4) ?v3) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f49 (f50 f32 ?v0) ?v1) (f49 (f50 f32 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f12 f33 ?v0) (f12 f33 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (not (= (f49 (f50 f32 ?v0) ?v1) (f12 f33 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S2)) (not (= (f12 f33 ?v0) (f49 (f50 f32 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (let ((?v_0 (f30 f31 f32))) (= (= (f28 (f29 ?v_0 ?v0) ?v1) (f28 (f29 ?v_0 ?v2) ?v1)) (= ?v0 ?v2)))))
(assert (forall ((?v0 S4) (?v1 S6) (?v2 S14) (?v3 S14) (?v4 S5) (?v5 S15) (?v6 S5)) (let ((?v_0 (f30 f31 f32))) (let ((?v_1 (f28 (f29 ?v_0 (f12 f33 ?v1)) ?v2))) (=> (= (f6 ?v0 (f28 (f29 ?v_0 ?v_1) ?v3) ?v4) f1) (=> (= (f22 ?v0 ?v2 ?v5) f1) (=> (= (f6 ?v0 ?v_1 ?v6) f1) (exists ((?v7 S15)) (and (= ?v6 (f40 (f63 (f64 f65 f42) ?v7) ?v4)) (= (f22 ?v0 ?v3 ?v7) f1))))))))))
(assert (forall ((?v0 S4) (?v1 S6) (?v2 S14) (?v3 S5)) (=> (= (f6 ?v0 (f28 (f29 (f30 f31 f32) (f12 f33 ?v1)) ?v2) ?v3) f1) (=> (forall ((?v4 S15)) (=> (= (f6 ?v0 (f12 f33 ?v1) (f40 (f63 (f64 f65 f42) ?v4) ?v3)) f1) (=> (= (f22 ?v0 ?v2 ?v4) f1) false))) false))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S14) (?v3 S5)) (=> (= (f6 ?v0 (f28 (f29 (f30 f31 f32) ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S15)) (=> (= (f6 ?v0 ?v1 (f40 (f63 (f64 f65 f42) ?v4) ?v3)) f1) (=> (= (f22 ?v0 ?v2 ?v4) f1) false))) false))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S14) (?v3 S5)) (=> (= (f6 ?v0 (f28 (f29 (f30 f31 f32) ?v1) ?v2) ?v3) f1) (exists ((?v4 S15)) (and (= (f6 ?v0 ?v1 (f40 (f63 (f64 f65 f42) ?v4) ?v3)) f1) (= (f22 ?v0 ?v2 ?v4) f1))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S14) (?v3 S15)) (= (= (f22 ?v0 (f45 (f46 f47 ?v1) ?v2) ?v3) f1) (= (f68 f2 (f21 ?v0 ?v1 ?v2) ?v3) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S14)) (let ((?v_0 (f30 f31 f32))) (=> (= (f3 f5 (f28 (f29 ?v_0 (f12 (f13 (f14 f15 ?v0) ?v1) f67)) ?v2)) f1) (=> (= (f3 f5 ?v1) f1) (= (f3 f5 (f28 (f29 ?v_0 (f49 (f50 f32 (f49 f69 ?v0)) ?v1)) ?v2)) f1))))))
(assert (forall ((?v0 S4) (?v1 S5) (?v2 S2) (?v3 S5)) (=> (= (f6 (f7 (f8 (f9 f10 ?v0) f67) ?v1) ?v2 ?v3) f1) (= (f6 ?v0 (f49 f69 ?v2) (f40 (f41 f42 ?v1) ?v3)) f1))))
(check-sat)
(exit)