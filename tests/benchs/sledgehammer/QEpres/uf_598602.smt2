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
(declare-sort S38 0)
(declare-sort S39 0)
(declare-sort S40 0)
(declare-sort S41 0)
(declare-sort S42 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 (S6 S5) S1)
(declare-fun f7 (S7 S5) S6)
(declare-fun f8 () S7)
(declare-fun f9 (S9 S8) S1)
(declare-fun f10 (S10 S8) S9)
(declare-fun f11 () S10)
(declare-fun f12 () S1)
(declare-fun f13 () S8)
(declare-fun f14 (S11 S8) S8)
(declare-fun f15 (S12 S13) S11)
(declare-fun f16 () S12)
(declare-fun f17 () S13)
(declare-fun f18 (S14 S15) S13)
(declare-fun f19 () S14)
(declare-fun f20 () S15)
(declare-fun f21 (S13 S13 S8) S15)
(declare-fun f22 () S13)
(declare-fun f23 () S13)
(declare-fun f24 (S17 S2) S2)
(declare-fun f25 (S18 S16) S17)
(declare-fun f26 () S18)
(declare-fun f27 (S19 S5) S5)
(declare-fun f28 (S20 S2) S19)
(declare-fun f29 () S20)
(declare-fun f30 (S21 S13) S13)
(declare-fun f31 () S21)
(declare-fun f32 (S2) S1)
(declare-fun f33 (S5) S1)
(declare-fun f34 (S8) S1)
(declare-fun f35 (S16) S3)
(declare-fun f36 (S2) S6)
(declare-fun f37 (S13) S9)
(declare-fun f38 (S22 S16) S1)
(declare-fun f39 (S2) S22)
(declare-fun f40 (S5) S3)
(declare-fun f41 (S23 S13) S1)
(declare-fun f42 (S8) S23)
(declare-fun f43 (S24 S2) S17)
(declare-fun f44 () S24)
(declare-fun f45 (S25 S5) S19)
(declare-fun f46 () S25)
(declare-fun f47 (S26 S8) S11)
(declare-fun f48 () S26)
(declare-fun f49 () S5)
(declare-fun f50 () S2)
(declare-fun f51 () S8)
(declare-fun f52 (S27 S16) S22)
(declare-fun f53 (S27) S4)
(declare-fun f54 (S4) S7)
(declare-fun f55 (S28 S13) S23)
(declare-fun f56 (S28) S10)
(declare-fun f57 (S13) S1)
(declare-fun f58 (S22) S3)
(declare-fun f59 (S3) S6)
(declare-fun f60 (S23) S9)
(declare-fun f61 (S13 S23) S1)
(declare-fun f62 () S23)
(declare-fun f63 (S22) S3)
(declare-fun f64 (S3) S6)
(declare-fun f65 (S23) S9)
(declare-fun f66 () S7)
(declare-fun f67 () S4)
(declare-fun f68 () S10)
(declare-fun f69 () S20)
(declare-fun f70 () S18)
(declare-fun f71 () S12)
(declare-fun f72 (S30 S29) S31)
(declare-fun f73 () S30)
(declare-fun f74 (S31 S8) S5)
(declare-fun f75 (S33 S32) S34)
(declare-fun f76 () S33)
(declare-fun f77 (S34 S8) S2)
(declare-fun f78 (S36 S35) S37)
(declare-fun f79 () S36)
(declare-fun f80 (S37 S5) S8)
(declare-fun f81 (S39 S38) S35)
(declare-fun f82 () S39)
(declare-fun f83 (S35 S2) S8)
(declare-fun f84 (S8) S1)
(declare-fun f85 (S40 S5) S2)
(declare-fun f86 () S40)
(declare-fun f87 (S41 S2) S16)
(declare-fun f88 () S41)
(declare-fun f89 (S42 S8) S13)
(declare-fun f90 () S42)
(declare-fun f91 () S25)
(declare-fun f92 () S24)
(declare-fun f93 () S26)
(declare-fun f94 () S11)
(declare-fun f95 (S3) S6)
(declare-fun f96 (S22) S3)
(declare-fun f97 (S23) S9)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f6 (f7 f8 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f9 (f10 f11 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (not (= f12 f1)))
(assert (forall ((?v0 S8)) (=> (= f13 (f14 (f15 f16 f17) ?v0)) (= f12 f1))))
(assert (= (f18 f19 f20) f17))
(assert (= f20 (f21 f22 f23 f13)))
(assert (= (f18 f19 f20) f17))
(assert (= f20 (f21 f22 f23 f13)))
(assert (forall ((?v0 S2) (?v1 S16)) (not (= ?v0 (f24 (f25 f26 ?v1) ?v0)))))
(assert (forall ((?v0 S5) (?v1 S2)) (not (= ?v0 (f27 (f28 f29 ?v1) ?v0)))))
(assert (forall ((?v0 S8) (?v1 S13)) (not (= ?v0 (f14 (f15 f16 ?v1) ?v0)))))
(assert (forall ((?v0 S16) (?v1 S2)) (not (= (f24 (f25 f26 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S5)) (not (= (f27 (f28 f29 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S13) (?v1 S8)) (not (= (f14 (f15 f16 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S16) (?v1 S2) (?v2 S16) (?v3 S2)) (= (= (f24 (f25 f26 ?v0) ?v1) (f24 (f25 f26 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2) (?v3 S5)) (= (= (f27 (f28 f29 ?v0) ?v1) (f27 (f28 f29 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S13) (?v1 S8) (?v2 S13) (?v3 S8)) (= (= (f14 (f15 f16 ?v0) ?v1) (f14 (f15 f16 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S13)) (= (= f17 ?v0) (= ?v0 f17))))
(assert (= (f30 f31 f17) f17))
(assert (forall ((?v0 S16) (?v1 S2)) (= (= (f32 (f24 (f25 f26 ?v0) ?v1)) f1) false)))
(assert (forall ((?v0 S2) (?v1 S5)) (= (= (f33 (f27 (f28 f29 ?v0) ?v1)) f1) false)))
(assert (forall ((?v0 S13) (?v1 S8)) (= (= (f34 (f14 (f15 f16 ?v0) ?v1)) f1) false)))
(assert (forall ((?v0 S16) (?v1 S2)) (= (f3 (f35 ?v0) (f24 (f25 f26 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S5)) (= (f6 (f36 ?v0) (f27 (f28 f29 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S13) (?v1 S8)) (= (f9 (f37 ?v0) (f14 (f15 f16 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S16) (?v1 S2) (?v2 S16)) (= (= (f38 (f39 (f24 (f25 f26 ?v0) ?v1)) ?v2) f1) (or (= ?v0 ?v2) (= (f38 (f39 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2)) (= (= (f3 (f40 (f27 (f28 f29 ?v0) ?v1)) ?v2) f1) (or (= ?v0 ?v2) (= (f3 (f40 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S8) (?v2 S13)) (= (= (f41 (f42 (f14 (f15 f16 ?v0) ?v1)) ?v2) f1) (or (= ?v0 ?v2) (= (f41 (f42 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S16) (?v1 S2) (?v2 S16) (?v3 S2)) (let ((?v_0 (f25 f26 ?v0)) (?v_1 (f25 f26 ?v2))) (= (f24 (f43 f44 (f24 ?v_0 ?v1)) (f24 ?v_1 ?v3)) (f24 ?v_0 (f24 ?v_1 (f24 (f43 f44 ?v1) ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2) (?v3 S5)) (let ((?v_0 (f28 f29 ?v0)) (?v_1 (f28 f29 ?v2))) (= (f27 (f45 f46 (f27 ?v_0 ?v1)) (f27 ?v_1 ?v3)) (f27 ?v_0 (f27 ?v_1 (f27 (f45 f46 ?v1) ?v3)))))))
(assert (forall ((?v0 S13) (?v1 S8) (?v2 S13) (?v3 S8)) (let ((?v_0 (f15 f16 ?v0)) (?v_1 (f15 f16 ?v2))) (= (f14 (f47 f48 (f14 ?v_0 ?v1)) (f14 ?v_1 ?v3)) (f14 ?v_0 (f14 ?v_1 (f14 (f47 f48 ?v1) ?v3)))))))
(assert (forall ((?v0 S16) (?v1 S2) (?v2 S16)) (let ((?v_0 (f35 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f24 (f25 f26 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2)) (let ((?v_0 (f36 ?v0))) (=> (= (f6 ?v_0 ?v1) f1) (= (f6 ?v_0 (f27 (f28 f29 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S13) (?v1 S8) (?v2 S13)) (let ((?v_0 (f37 ?v0))) (=> (= (f9 ?v_0 ?v1) f1) (= (f9 ?v_0 (f14 (f15 f16 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f30 f31 ?v0) (f30 f31 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S8) (?v3 S13) (?v4 S13) (?v5 S8)) (= (= (f21 ?v0 ?v1 ?v2) (f21 ?v3 ?v4 ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S16) (?v1 S2)) (= (= (f3 (f35 ?v0) ?v1) f1) (or (exists ((?v2 S16) (?v3 S2)) (and (= ?v0 ?v2) (= ?v1 (f24 (f25 f26 ?v2) ?v3)))) (exists ((?v2 S16) (?v3 S2) (?v4 S16)) (and (= ?v0 ?v2) (and (= ?v1 (f24 (f25 f26 ?v4) ?v3)) (= (f3 (f35 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S2) (?v1 S5)) (= (= (f6 (f36 ?v0) ?v1) f1) (or (exists ((?v2 S2) (?v3 S5)) (and (= ?v0 ?v2) (= ?v1 (f27 (f28 f29 ?v2) ?v3)))) (exists ((?v2 S2) (?v3 S5) (?v4 S2)) (and (= ?v0 ?v2) (and (= ?v1 (f27 (f28 f29 ?v4) ?v3)) (= (f6 (f36 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S13) (?v1 S8)) (= (= (f9 (f37 ?v0) ?v1) f1) (or (exists ((?v2 S13) (?v3 S8)) (and (= ?v0 ?v2) (= ?v1 (f14 (f15 f16 ?v2) ?v3)))) (exists ((?v2 S13) (?v3 S8) (?v4 S13)) (and (= ?v0 ?v2) (and (= ?v1 (f14 (f15 f16 ?v4) ?v3)) (= (f9 (f37 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S2) (?v1 S5)) (let ((?v_0 (f27 (f28 f29 ?v0) ?v1))) (= (f27 (f45 f46 ?v_0) f49) ?v_0))))
(assert (forall ((?v0 S16) (?v1 S2)) (let ((?v_0 (f24 (f25 f26 ?v0) ?v1))) (= (f24 (f43 f44 ?v_0) f50) ?v_0))))
(assert (forall ((?v0 S13) (?v1 S8)) (let ((?v_0 (f14 (f15 f16 ?v0) ?v1))) (= (f14 (f47 f48 ?v_0) f51) ?v_0))))
(assert (forall ((?v0 S27) (?v1 S16) (?v2 S16) (?v3 S2) (?v4 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f38 (f52 ?v0 ?v1) ?v2) f1) (=> (= (f3 (f4 ?v_0 ?v3) ?v4) f1) (= (f3 (f4 ?v_0 (f24 (f25 f26 ?v1) ?v3)) (f24 (f25 f26 ?v2) ?v4)) f1))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S5) (?v4 S5)) (let ((?v_0 (f54 ?v0))) (=> (= (f3 (f4 ?v0 ?v1) ?v2) f1) (=> (= (f6 (f7 ?v_0 ?v3) ?v4) f1) (= (f6 (f7 ?v_0 (f27 (f28 f29 ?v1) ?v3)) (f27 (f28 f29 ?v2) ?v4)) f1))))))
(assert (forall ((?v0 S28) (?v1 S13) (?v2 S13) (?v3 S8) (?v4 S8)) (let ((?v_0 (f56 ?v0))) (=> (= (f41 (f55 ?v0 ?v1) ?v2) f1) (=> (= (f9 (f10 ?v_0 ?v3) ?v4) f1) (= (f9 (f10 ?v_0 (f14 (f15 f16 ?v1) ?v3)) (f14 (f15 f16 ?v2) ?v4)) f1))))))
(assert (not (= (f57 f17) f1)))
(assert (forall ((?v0 S22) (?v1 S16) (?v2 S2)) (let ((?v_0 (f58 ?v0))) (= (= (f3 ?v_0 (f24 (f25 f26 ?v1) ?v2)) f1) (or (= (f38 ?v0 ?v1) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S5)) (let ((?v_0 (f59 ?v0))) (= (= (f6 ?v_0 (f27 (f28 f29 ?v1) ?v2)) f1) (or (= (f3 ?v0 ?v1) f1) (= (f6 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S23) (?v1 S13) (?v2 S8)) (let ((?v_0 (f60 ?v0))) (= (= (f9 ?v_0 (f14 (f15 f16 ?v1) ?v2)) f1) (or (= (f41 ?v0 ?v1) f1) (= (f9 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13)) (= (f61 (f30 f31 ?v0) f62) f1)))
(assert (forall ((?v0 S22) (?v1 S16) (?v2 S2)) (let ((?v_0 (f63 ?v0))) (= (= (f3 ?v_0 (f24 (f25 f26 ?v1) ?v2)) f1) (and (= (f38 ?v0 ?v1) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S5)) (let ((?v_0 (f64 ?v0))) (= (= (f6 ?v_0 (f27 (f28 f29 ?v1) ?v2)) f1) (and (= (f3 ?v0 ?v1) f1) (= (f6 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S23) (?v1 S13) (?v2 S8)) (let ((?v_0 (f65 ?v0))) (= (= (f9 ?v_0 (f14 (f15 f16 ?v1) ?v2)) f1) (and (= (f41 ?v0 ?v1) f1) (= (f9 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3)) (= (= (f6 (f59 ?v0) f49) f1) false)))
(assert (forall ((?v0 S22)) (= (= (f3 (f58 ?v0) f50) f1) false)))
(assert (forall ((?v0 S23)) (= (= (f9 (f60 ?v0) f51) f1) false)))
(assert (forall ((?v0 S3)) (= (= (f6 (f64 ?v0) f49) f1) true)))
(assert (forall ((?v0 S22)) (= (= (f3 (f63 ?v0) f50) f1) true)))
(assert (forall ((?v0 S23)) (= (= (f9 (f65 ?v0) f51) f1) true)))
(assert (forall ((?v0 S4)) (= (f6 (f7 (f54 ?v0) f49) f49) f1)))
(assert (forall ((?v0 S27)) (= (f3 (f4 (f53 ?v0) f50) f50) f1)))
(assert (forall ((?v0 S28)) (= (f9 (f10 (f56 ?v0) f51) f51) f1)))
(assert (forall ((?v0 S2) (?v1 S5)) (not (= f49 (f27 (f28 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S16) (?v1 S2)) (not (= f50 (f24 (f25 f26 ?v0) ?v1)))))
(assert (forall ((?v0 S13) (?v1 S8)) (not (= f51 (f14 (f15 f16 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S5)) (not (= (f27 (f28 f29 ?v0) ?v1) f49))))
(assert (forall ((?v0 S16) (?v1 S2)) (not (= (f24 (f25 f26 ?v0) ?v1) f50))))
(assert (forall ((?v0 S13) (?v1 S8)) (not (= (f14 (f15 f16 ?v0) ?v1) f51))))
(assert (= (f61 f17 f62) f1))
(assert (forall ((?v0 S5)) (= (= ?v0 f49) (= (f33 ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= ?v0 f50) (= (f32 ?v0) f1))))
(assert (forall ((?v0 S8)) (= (= ?v0 f51) (= (f34 ?v0) f1))))
(assert (forall ((?v0 S5)) (= (f27 (f45 f46 ?v0) f49) ?v0)))
(assert (forall ((?v0 S2)) (= (f24 (f43 f44 ?v0) f50) ?v0)))
(assert (forall ((?v0 S8)) (= (f14 (f47 f48 ?v0) f51) ?v0)))
(assert (forall ((?v0 S5)) (= (f27 (f45 f46 f49) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f24 (f43 f44 f50) ?v0) ?v0)))
(assert (forall ((?v0 S8)) (= (f14 (f47 f48 f51) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (= (f3 (f40 f49) ?v0) f1) false)))
(assert (forall ((?v0 S16)) (= (= (f38 (f39 f50) ?v0) f1) false)))
(assert (forall ((?v0 S13)) (= (= (f41 (f42 f51) ?v0) f1) false)))
(assert (forall ((?v0 S5)) (= (= (f33 ?v0) f1) (= ?v0 f49))))
(assert (forall ((?v0 S2)) (= (= (f32 ?v0) f1) (= ?v0 f50))))
(assert (forall ((?v0 S8)) (= (= (f34 ?v0) f1) (= ?v0 f51))))
(assert (= (= (f33 f49) f1) true))
(assert (= (= (f32 f50) f1) true))
(assert (= (= (f34 f51) f1) true))
(assert (forall ((?v0 S13)) (=> (= (f61 ?v0 f62) f1) (=> (forall ((?v1 S13)) (=> (= ?v0 (f30 f31 ?v1)) false)) false))))
(assert (forall ((?v0 S13) (?v1 S23)) (=> (= (f61 ?v0 f62) f1) (=> (forall ((?v2 S13)) (= (f41 ?v1 (f30 f31 ?v2)) f1)) (= (f41 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S5)) (= (not (= ?v0 f49)) (exists ((?v1 S2) (?v2 S5)) (= ?v0 (f27 (f28 f29 ?v1) ?v2))))))
(assert (forall ((?v0 S2)) (= (not (= ?v0 f50)) (exists ((?v1 S16) (?v2 S2)) (= ?v0 (f24 (f25 f26 ?v1) ?v2))))))
(assert (forall ((?v0 S8)) (= (not (= ?v0 f51)) (exists ((?v1 S13) (?v2 S8)) (= ?v0 (f14 (f15 f16 ?v1) ?v2))))))
(assert (forall ((?v0 S5)) (=> (=> (= ?v0 f49) false) (=> (forall ((?v1 S2) (?v2 S5)) (=> (= ?v0 (f27 (f28 f29 ?v1) ?v2)) false)) false))))
(assert (forall ((?v0 S2)) (=> (=> (= ?v0 f50) false) (=> (forall ((?v1 S16) (?v2 S2)) (=> (= ?v0 (f24 (f25 f26 ?v1) ?v2)) false)) false))))
(assert (forall ((?v0 S8)) (=> (=> (= ?v0 f51) false) (=> (forall ((?v1 S13) (?v2 S8)) (=> (= ?v0 (f14 (f15 f16 ?v1) ?v2)) false)) false))))
(assert (forall ((?v0 S5)) (= (= (f6 (f7 f66 ?v0) f49) f1) (= (f33 ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f67 ?v0) f50) f1) (= (f32 ?v0) f1))))
(assert (forall ((?v0 S8)) (= (= (f9 (f10 f68 ?v0) f51) f1) (= (f34 ?v0) f1))))
(assert (forall ((?v0 S4) (?v1 S5) (?v2 S5)) (= (= (f6 (f7 (f54 ?v0) ?v1) ?v2) f1) (or (and (= ?v1 f49) (= ?v2 f49)) (exists ((?v3 S2) (?v4 S2) (?v5 S5) (?v6 S5)) (and (= ?v1 (f27 (f28 f29 ?v3) ?v5)) (and (= ?v2 (f27 (f28 f29 ?v4) ?v6)) (and (= (f3 (f4 ?v0 ?v3) ?v4) f1) (= (f6 (f7 (f54 ?v0) ?v5) ?v6) f1)))))))))
(assert (forall ((?v0 S27) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f53 ?v0) ?v1) ?v2) f1) (or (and (= ?v1 f50) (= ?v2 f50)) (exists ((?v3 S16) (?v4 S16) (?v5 S2) (?v6 S2)) (and (= ?v1 (f24 (f25 f26 ?v3) ?v5)) (and (= ?v2 (f24 (f25 f26 ?v4) ?v6)) (and (= (f38 (f52 ?v0 ?v3) ?v4) f1) (= (f3 (f4 (f53 ?v0) ?v5) ?v6) f1)))))))))
(assert (forall ((?v0 S28) (?v1 S8) (?v2 S8)) (= (= (f9 (f10 (f56 ?v0) ?v1) ?v2) f1) (or (and (= ?v1 f51) (= ?v2 f51)) (exists ((?v3 S13) (?v4 S13) (?v5 S8) (?v6 S8)) (and (= ?v1 (f14 (f15 f16 ?v3) ?v5)) (and (= ?v2 (f14 (f15 f16 ?v4) ?v6)) (and (= (f41 (f55 ?v0 ?v3) ?v4) f1) (= (f9 (f10 (f56 ?v0) ?v5) ?v6) f1)))))))))
(assert (forall ((?v0 S2)) (= (f27 (f28 f69 ?v0) f49) (f27 (f28 f29 ?v0) f49))))
(assert (forall ((?v0 S16)) (= (f24 (f25 f70 ?v0) f50) (f24 (f25 f26 ?v0) f50))))
(assert (forall ((?v0 S13)) (= (f14 (f15 f71 ?v0) f51) (f14 (f15 f16 ?v0) f51))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f9 (f10 f68 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f67 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f6 (f7 f66 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (not (= ?v0 f49)) (=> (forall ((?v2 S2)) (= (f6 ?v1 (f27 (f28 f29 ?v2) f49)) f1)) (=> (forall ((?v2 S2) (?v3 S5)) (=> (not (= ?v3 f49)) (=> (= (f6 ?v1 ?v3) f1) (= (f6 ?v1 (f27 (f28 f29 ?v2) ?v3)) f1)))) (= (f6 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (not (= ?v0 f50)) (=> (forall ((?v2 S16)) (= (f3 ?v1 (f24 (f25 f26 ?v2) f50)) f1)) (=> (forall ((?v2 S16) (?v3 S2)) (=> (not (= ?v3 f50)) (=> (= (f3 ?v1 ?v3) f1) (= (f3 ?v1 (f24 (f25 f26 ?v2) ?v3)) f1)))) (= (f3 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S8) (?v1 S9)) (=> (not (= ?v0 f51)) (=> (forall ((?v2 S13)) (= (f9 ?v1 (f14 (f15 f16 ?v2) f51)) f1)) (=> (forall ((?v2 S13) (?v3 S8)) (=> (not (= ?v3 f51)) (=> (= (f9 ?v1 ?v3) f1) (= (f9 ?v1 (f14 (f15 f16 ?v2) ?v3)) f1)))) (= (f9 ?v1 ?v0) f1))))))
(assert (= f68 f11))
(assert (= f67 f5))
(assert (= f66 f8))
(assert (forall ((?v0 S8)) (= (= (f9 (f10 f68 ?v0) ?v0) f1) true)))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f67 ?v0) ?v0) f1) true)))
(assert (forall ((?v0 S5)) (= (= (f6 (f7 f66 ?v0) ?v0) f1) true)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f9 (f10 f68 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f67 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f6 (f7 f66 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (= f11 f68))
(assert (= f5 f67))
(assert (= f8 f66))
(assert (forall ((?v0 S29)) (= (f74 (f72 f73 ?v0) f51) f49)))
(assert (forall ((?v0 S32)) (= (f77 (f75 f76 ?v0) f51) f50)))
(assert (forall ((?v0 S35)) (= (f80 (f78 f79 ?v0) f49) f51)))
(assert (forall ((?v0 S38)) (= (f83 (f81 f82 ?v0) f50) f51)))
(assert (forall ((?v0 S13)) (= (f84 (f14 (f15 f16 ?v0) f51)) f1)))
(assert (forall ((?v0 S2) (?v1 S5)) (= (f85 f86 (f27 (f28 f29 ?v0) ?v1)) (ite (= ?v1 f49) ?v0 (f85 f86 ?v1)))))
(assert (forall ((?v0 S16) (?v1 S2)) (= (f87 f88 (f24 (f25 f26 ?v0) ?v1)) (ite (= ?v1 f50) ?v0 (f87 f88 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S8)) (= (f89 f90 (f14 (f15 f16 ?v0) ?v1)) (ite (= ?v1 f51) ?v0 (f89 f90 ?v1)))))
(assert (= (f84 f51) f1))
(assert (forall ((?v0 S5) (?v1 S2)) (=> (= ?v0 f49) (= (f85 f86 (f27 (f28 f29 ?v1) ?v0)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S16)) (=> (= ?v0 f50) (= (f87 f88 (f24 (f25 f26 ?v1) ?v0)) ?v1))))
(assert (forall ((?v0 S8) (?v1 S13)) (=> (= ?v0 f51) (= (f89 f90 (f14 (f15 f16 ?v1) ?v0)) ?v1))))
(assert (forall ((?v0 S5) (?v1 S2)) (=> (not (= ?v0 f49)) (= (f85 f86 (f27 (f28 f29 ?v1) ?v0)) (f85 f86 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S16)) (=> (not (= ?v0 f50)) (= (f87 f88 (f24 (f25 f26 ?v1) ?v0)) (f87 f88 ?v0)))))
(assert (forall ((?v0 S8) (?v1 S13)) (=> (not (= ?v0 f51)) (= (f89 f90 (f14 (f15 f16 ?v1) ?v0)) (f89 f90 ?v0)))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (f85 f86 (f27 (f45 f91 ?v0) (f27 (f28 f29 ?v1) f49))) ?v1)))
(assert (forall ((?v0 S2) (?v1 S16)) (= (f87 f88 (f24 (f43 f92 ?v0) (f24 (f25 f26 ?v1) f50))) ?v1)))
(assert (forall ((?v0 S8) (?v1 S13)) (= (f89 f90 (f14 (f47 f93 ?v0) (f14 (f15 f16 ?v1) f51))) ?v1)))
(assert (forall ((?v0 S8)) (=> (not (= ?v0 f51)) (=> (= (f84 ?v0) f1) (= (f84 (f14 f94 ?v0)) f1)))))
(assert (forall ((?v0 S3)) (= (= (f6 (f95 ?v0) f49) f1) false)))
(assert (forall ((?v0 S22)) (= (= (f3 (f96 ?v0) f50) f1) false)))
(assert (forall ((?v0 S23)) (= (= (f9 (f97 ?v0) f51) f1) false)))
(check-sat)
(exit)