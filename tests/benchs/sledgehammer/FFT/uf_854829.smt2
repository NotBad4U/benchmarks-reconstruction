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
(declare-sort S43 0)
(declare-sort S44 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S4) S4)
(declare-fun f6 (S6 S4) S5)
(declare-fun f7 () S6)
(declare-fun f8 (S7 S8) S4)
(declare-fun f9 (S9 S3) S7)
(declare-fun f10 () S9)
(declare-fun f11 (S10 S4) S3)
(declare-fun f12 () S10)
(declare-fun f13 (S2 S2) S1)
(declare-fun f14 () S2)
(declare-fun f15 () S3)
(declare-fun f16 () S2)
(declare-fun f17 (S11 S2) S2)
(declare-fun f18 (S12 S2) S11)
(declare-fun f19 () S12)
(declare-fun f20 () S6)
(declare-fun f21 () S4)
(declare-fun f22 (S2 S2) S8)
(declare-fun f23 () S2)
(declare-fun f24 () S3)
(declare-fun f25 () S3)
(declare-fun f26 () S3)
(declare-fun f27 (S13 S2) S3)
(declare-fun f28 (S14 S3) S13)
(declare-fun f29 () S14)
(declare-fun f30 () S12)
(declare-fun f31 (S15 S2) S16)
(declare-fun f32 (S17 S2) S15)
(declare-fun f33 (S18 S15) S17)
(declare-fun f34 () S18)
(declare-fun f35 (S19 S11) S12)
(declare-fun f36 () S19)
(declare-fun f37 (S20 S2) S21)
(declare-fun f38 (S22 S2) S20)
(declare-fun f39 (S23 S20) S22)
(declare-fun f40 () S23)
(declare-fun f41 (S24 S15) S15)
(declare-fun f42 (S25 S2) S24)
(declare-fun f43 () S25)
(declare-fun f44 (S26 S4) S13)
(declare-fun f45 (S27 S4) S26)
(declare-fun f46 () S27)
(declare-fun f47 () S6)
(declare-fun f48 () S6)
(declare-fun f49 (S28 S16) S17)
(declare-fun f50 (S29 S16) S28)
(declare-fun f51 () S29)
(declare-fun f52 (S30 S16) S16)
(declare-fun f53 (S31 S16) S30)
(declare-fun f54 () S31)
(declare-fun f55 () S31)
(declare-fun f56 (S32 S16) S15)
(declare-fun f57 () S32)
(declare-fun f58 () S31)
(declare-fun f59 (S33 S21) S22)
(declare-fun f60 (S34 S21) S33)
(declare-fun f61 () S34)
(declare-fun f62 (S35 S21) S21)
(declare-fun f63 (S36 S21) S35)
(declare-fun f64 () S36)
(declare-fun f65 () S36)
(declare-fun f66 (S37 S21) S20)
(declare-fun f67 () S37)
(declare-fun f68 () S36)
(declare-fun f69 () S27)
(declare-fun f70 () S29)
(declare-fun f71 () S34)
(declare-fun f72 (S2 S2) S1)
(declare-fun f73 () S16)
(declare-fun f74 () S31)
(declare-fun f75 () S16)
(declare-fun f76 () S4)
(declare-fun f77 (S38 S8) S16)
(declare-fun f78 (S39 S15) S38)
(declare-fun f79 () S39)
(declare-fun f80 (S40 S8) S21)
(declare-fun f81 (S41 S20) S40)
(declare-fun f82 () S41)
(declare-fun f83 () S2)
(declare-fun f84 () S12)
(declare-fun f85 () S12)
(declare-fun f86 () S21)
(declare-fun f87 (S16 S16) S1)
(declare-fun f88 (S21 S21) S1)
(declare-fun f89 () S21)
(declare-fun f90 (S42 S8) S2)
(declare-fun f91 (S43 S11) S42)
(declare-fun f92 () S43)
(declare-fun f93 (S8 S2) S1)
(declare-fun f94 (S44 S2) S8)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f3 f15 f16))) (= (f3 f4 ?v0) (f5 (f6 f7 (f8 (f9 f10 (f11 f12 (ite (= (f13 f14 ?v0) f1) (f3 (f11 f12 ?v_0) (f17 (f18 f19 ?v0) f14)) (f3 (f11 f12 (f5 (f6 f20 f21) ?v_0)) (f17 (f18 f19 f14) ?v0))))) (f22 f23 f16))) (f3 f24 ?v0))))))
(assert (forall ((?v0 S2)) (= (f3 f25 ?v0) (f5 (f6 f7 (f8 (f9 f10 (f11 f12 (f3 (f11 f12 (f5 (f6 f20 f21) (f3 f15 f16))) (f17 (f18 f19 f14) ?v0)))) (f22 f23 f16))) (f3 f24 ?v0)))))
(assert (forall ((?v0 S2)) (= (f3 f26 ?v0) (f5 (f6 f7 (f8 (f9 f10 (f11 f12 (f3 (f11 f12 (f3 f15 f16)) (f17 (f18 f19 ?v0) f14)))) (f22 f23 f16))) (f3 f24 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (= (f3 (f27 (f28 f29 ?v0) ?v1) ?v2) (f3 ?v0 (f17 (f18 f30 ?v2) ?v1)))))
(assert (forall ((?v0 S15) (?v1 S2) (?v2 S2)) (= (f31 (f32 (f33 f34 ?v0) ?v1) ?v2) (f31 ?v0 (f17 (f18 f30 ?v2) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S2)) (= (f17 (f18 (f35 f36 ?v0) ?v1) ?v2) (f17 ?v0 (f17 (f18 f30 ?v2) ?v1)))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S2)) (= (f37 (f38 (f39 f40 ?v0) ?v1) ?v2) (f37 ?v0 (f17 (f18 f30 ?v2) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S15) (?v2 S2)) (= (f31 (f41 (f42 f43 ?v0) ?v1) ?v2) (f31 ?v1 (f17 (f18 f30 ?v2) ?v0)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2) (?v3 S2)) (let ((?v_0 (f11 f12 ?v0))) (= (f3 (f27 (f44 (f45 f46 ?v0) ?v1) ?v2) ?v3) (f5 (f6 f47 (f5 (f6 f7 (f3 (f11 f12 (f5 (f6 f48 ?v0) ?v1)) (f17 (f18 f19 ?v2) ?v3))) (f3 ?v_0 ?v3))) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S2) (?v3 S2)) (let ((?v_0 (f56 f57 ?v0))) (= (f31 (f32 (f49 (f50 f51 ?v0) ?v1) ?v2) ?v3) (f52 (f53 f54 (f52 (f53 f55 (f31 (f56 f57 (f52 (f53 f58 ?v0) ?v1)) (f17 (f18 f19 ?v2) ?v3))) (f31 ?v_0 ?v3))) (f31 ?v_0 ?v2))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S2) (?v3 S2)) (let ((?v_0 (f66 f67 ?v0))) (= (f37 (f38 (f59 (f60 f61 ?v0) ?v1) ?v2) ?v3) (f62 (f63 f64 (f62 (f63 f65 (f37 (f66 f67 (f62 (f63 f68 ?v0) ?v1)) (f17 (f18 f19 ?v2) ?v3))) (f37 ?v_0 ?v3))) (f37 ?v_0 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2) (?v3 S2)) (let ((?v_0 (f11 f12 ?v0)) (?v_1 (f17 (f18 f19 ?v2) ?v3))) (= (f3 (f27 (f44 (f45 f69 ?v0) ?v1) ?v2) ?v3) (f5 (f6 f7 (f3 ?v_0 ?v3)) (f5 (f6 f47 (f3 (f11 f12 (f5 (f6 f48 ?v0) ?v1)) ?v_1)) (f3 ?v_0 ?v_1)))))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S2) (?v3 S2)) (let ((?v_0 (f56 f57 ?v0)) (?v_1 (f17 (f18 f19 ?v2) ?v3))) (= (f31 (f32 (f49 (f50 f70 ?v0) ?v1) ?v2) ?v3) (f52 (f53 f55 (f31 ?v_0 ?v3)) (f52 (f53 f54 (f31 (f56 f57 (f52 (f53 f58 ?v0) ?v1)) ?v_1)) (f31 ?v_0 ?v_1)))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S2) (?v3 S2)) (let ((?v_0 (f66 f67 ?v0)) (?v_1 (f17 (f18 f19 ?v2) ?v3))) (= (f37 (f38 (f59 (f60 f71 ?v0) ?v1) ?v2) ?v3) (f62 (f63 f65 (f37 ?v_0 ?v3)) (f62 (f63 f64 (f37 (f66 f67 (f62 (f63 f68 ?v0) ?v1)) ?v_1)) (f37 ?v_0 ?v_1)))))))
(assert (not (= (f8 (f9 f10 f4) (f22 f23 f16)) (f5 (f6 f48 (f8 (f9 f10 f25) (f22 f23 f14))) (f8 (f9 f10 f26) (f22 f14 f16))))))
(assert (= (f72 f14 f16) f1))
(assert (= (f72 f14 f16) f1))
(assert (forall ((?v0 S2)) (= (f72 (f17 (f18 f19 f14) ?v0) f16) f1)))
(assert (forall ((?v0 S2)) (=> (= (f72 ?v0 f16) f1) (= (f72 (f17 (f18 f19 ?v0) f14) f16) f1))))
(assert (= (f3 f15 f23) f21))
(assert (forall ((?v0 S2)) (= (f3 (f11 f12 (f3 f15 ?v0)) ?v0) f21)))
(assert (forall ((?v0 S16) (?v1 S2) (?v2 S2)) (let ((?v_0 (f56 f57 ?v0))) (=> (not (= ?v0 f73)) (= (f52 (f53 f74 (f31 ?v_0 ?v1)) (f31 ?v_0 ?v2)) (ite (= (f13 ?v2 ?v1) f1) (f31 ?v_0 (f17 (f18 f19 ?v1) ?v2)) (f31 (f56 f57 (f52 (f53 f74 f75) ?v0)) (f17 (f18 f19 ?v2) ?v1))))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f12 ?v0))) (=> (not (= ?v0 f76)) (= (f5 (f6 f20 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2)) (ite (= (f13 ?v2 ?v1) f1) (f3 ?v_0 (f17 (f18 f19 ?v1) ?v2)) (f3 (f11 f12 (f5 (f6 f20 f21) ?v0)) (f17 (f18 f19 ?v2) ?v1))))))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S2)) (let ((?v_0 (f22 f23 ?v2))) (= (f77 (f78 f79 (f32 (f49 (f50 f51 ?v0) ?v1) ?v2)) ?v_0) (f77 (f78 f79 (f32 (f49 (f50 f70 ?v0) ?v1) ?v2)) ?v_0)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2)) (let ((?v_0 (f22 f23 ?v2))) (= (f8 (f9 f10 (f27 (f44 (f45 f46 ?v0) ?v1) ?v2)) ?v_0) (f8 (f9 f10 (f27 (f44 (f45 f69 ?v0) ?v1) ?v2)) ?v_0)))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S2)) (let ((?v_0 (f22 f23 ?v2))) (= (f80 (f81 f82 (f38 (f59 (f60 f61 ?v0) ?v1) ?v2)) ?v_0) (f80 (f81 f82 (f38 (f59 (f60 f71 ?v0) ?v1) ?v2)) ?v_0)))))
(assert (forall ((?v0 S16) (?v1 S2)) (let ((?v_0 (f56 f57 ?v0))) (=> (not (= ?v0 f75)) (= (f77 (f78 f79 ?v_0) (f22 f23 ?v1)) (f52 (f53 f74 (f52 (f53 f54 (f31 ?v_0 ?v1)) f75)) (f52 (f53 f54 ?v0) f75)))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f11 f12 ?v0))) (=> (not (= ?v0 f21)) (= (f8 (f9 f10 ?v_0) (f22 f23 ?v1)) (f5 (f6 f20 (f5 (f6 f47 (f3 ?v_0 ?v1)) f21)) (f5 (f6 f47 ?v0) f21)))))))
(assert (forall ((?v0 S2)) (= (f13 f23 ?v0) f1)))
(assert (forall ((?v0 S16) (?v1 S2) (?v2 S2)) (let ((?v_0 (f56 f57 ?v0))) (=> (not (= ?v0 f73)) (=> (= (f13 ?v1 ?v2) f1) (= (f31 ?v_0 (f17 (f18 f19 ?v2) ?v1)) (f52 (f53 f74 (f31 ?v_0 ?v2)) (f31 ?v_0 ?v1))))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f12 ?v0))) (=> (not (= ?v0 f76)) (=> (= (f13 ?v1 ?v2) f1) (= (f3 ?v_0 (f17 (f18 f19 ?v2) ?v1)) (f5 (f6 f20 (f3 ?v_0 ?v2)) (f3 ?v_0 ?v1))))))))
(assert (forall ((?v0 S16) (?v1 S2)) (let ((?v_0 (f56 f57 ?v0))) (= (f31 ?v_0 ?v1) (ite (= ?v1 f23) f75 (f52 (f53 f55 ?v0) (f31 ?v_0 (f17 (f18 f19 ?v1) f83))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f18 f84 ?v0))) (= (f17 ?v_0 ?v1) (ite (= ?v1 f23) f83 (f17 (f18 f85 ?v0) (f17 ?v_0 (f17 (f18 f19 ?v1) f83))))))))
(assert (forall ((?v0 S21) (?v1 S2)) (let ((?v_0 (f66 f67 ?v0))) (= (f37 ?v_0 ?v1) (ite (= ?v1 f23) f86 (f62 (f63 f65 ?v0) (f37 ?v_0 (f17 (f18 f19 ?v1) f83))))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f11 f12 ?v0))) (= (f3 ?v_0 ?v1) (ite (= ?v1 f23) f21 (f5 (f6 f7 ?v0) (f3 ?v_0 (f17 (f18 f19 ?v1) f83))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S16)) (let ((?v_0 (f56 f57 ?v2))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f87 f73 ?v2) f1) (=> (= (f87 ?v2 f75) f1) (= (f87 (f31 ?v_0 ?v1) (f31 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f84 ?v2))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 f23 ?v2) f1) (=> (= (f13 ?v2 f83) f1) (= (f13 (f17 ?v_0 ?v1) (f17 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S21)) (let ((?v_0 (f66 f67 ?v2))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f88 f89 ?v2) f1) (=> (= (f88 ?v2 f86) f1) (= (f88 (f37 ?v_0 ?v1) (f37 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16) (?v3 S16) (?v4 S16)) (=> (= (f87 ?v0 ?v1) f1) (=> (= (f87 ?v2 ?v1) f1) (=> (= (f87 f73 ?v3) f1) (=> (= (f87 f73 ?v4) f1) (=> (= (f52 (f53 f58 ?v3) ?v4) f75) (= (f87 (f52 (f53 f58 (f52 (f53 f55 ?v3) ?v0)) (f52 (f53 f55 ?v4) ?v2)) ?v1) f1))))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21) (?v3 S21) (?v4 S21)) (=> (= (f88 ?v0 ?v1) f1) (=> (= (f88 ?v2 ?v1) f1) (=> (= (f88 f89 ?v3) f1) (=> (= (f88 f89 ?v4) f1) (=> (= (f62 (f63 f68 ?v3) ?v4) f86) (= (f88 (f62 (f63 f68 (f62 (f63 f65 ?v3) ?v0)) (f62 (f63 f65 ?v4) ?v2)) ?v1) f1))))))))
(assert (forall ((?v0 S15) (?v1 S2) (?v2 S2)) (let ((?v_0 (f78 f79 ?v0))) (= (f77 ?v_0 (f22 f23 (f17 (f18 f30 ?v1) ?v2))) (f52 (f53 f58 (f77 (f78 f79 (f32 (f33 f34 ?v0) ?v2)) (f22 f23 ?v1))) (f77 ?v_0 (f22 f23 ?v2)))))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S2)) (let ((?v_0 (f91 f92 ?v0))) (= (f90 ?v_0 (f22 f23 (f17 (f18 f30 ?v1) ?v2))) (f17 (f18 f30 (f90 (f91 f92 (f18 (f35 f36 ?v0) ?v2)) (f22 f23 ?v1))) (f90 ?v_0 (f22 f23 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f9 f10 ?v0))) (= (f8 ?v_0 (f22 f23 (f17 (f18 f30 ?v1) ?v2))) (f5 (f6 f48 (f8 (f9 f10 (f27 (f28 f29 ?v0) ?v2)) (f22 f23 ?v1))) (f8 ?v_0 (f22 f23 ?v2)))))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S2)) (let ((?v_0 (f81 f82 ?v0))) (= (f80 ?v_0 (f22 f23 (f17 (f18 f30 ?v1) ?v2))) (f62 (f63 f68 (f80 (f81 f82 (f38 (f39 f40 ?v0) ?v2)) (f22 f23 ?v1))) (f80 ?v_0 (f22 f23 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S15)) (let ((?v_0 (f78 f79 ?v3))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 ?v1 ?v2) f1) (= (f52 (f53 f54 (f77 ?v_0 (f22 ?v0 ?v2))) (f77 ?v_0 (f22 ?v0 ?v1))) (f77 ?v_0 (f22 ?v1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S3)) (let ((?v_0 (f9 f10 ?v3))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 ?v1 ?v2) f1) (= (f5 (f6 f47 (f8 ?v_0 (f22 ?v0 ?v2))) (f8 ?v_0 (f22 ?v0 ?v1))) (f8 ?v_0 (f22 ?v1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S20)) (let ((?v_0 (f81 f82 ?v3))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 ?v1 ?v2) f1) (= (f62 (f63 f64 (f80 ?v_0 (f22 ?v0 ?v2))) (f80 ?v_0 (f22 ?v0 ?v1))) (f80 ?v_0 (f22 ?v1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S15)) (let ((?v_0 (f78 f79 ?v3))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 ?v1 ?v2) f1) (= (f52 (f53 f58 (f77 ?v_0 (f22 ?v0 ?v1))) (f77 ?v_0 (f22 ?v1 ?v2))) (f77 ?v_0 (f22 ?v0 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S11)) (let ((?v_0 (f91 f92 ?v3))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 ?v1 ?v2) f1) (= (f17 (f18 f30 (f90 ?v_0 (f22 ?v0 ?v1))) (f90 ?v_0 (f22 ?v1 ?v2))) (f90 ?v_0 (f22 ?v0 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S3)) (let ((?v_0 (f9 f10 ?v3))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 ?v1 ?v2) f1) (= (f5 (f6 f48 (f8 ?v_0 (f22 ?v0 ?v1))) (f8 ?v_0 (f22 ?v1 ?v2))) (f8 ?v_0 (f22 ?v0 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S20)) (let ((?v_0 (f81 f82 ?v3))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 ?v1 ?v2) f1) (= (f62 (f63 f68 (f80 ?v_0 (f22 ?v0 ?v1))) (f80 ?v_0 (f22 ?v1 ?v2))) (f80 ?v_0 (f22 ?v0 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S16)) (let ((?v_0 (f56 f57 ?v2))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f87 f75 ?v2) f1) (= (f87 (f31 ?v_0 ?v0) (f31 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f84 ?v2))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 f83 ?v2) f1) (= (f13 (f17 ?v_0 ?v0) (f17 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S21)) (let ((?v_0 (f66 f67 ?v2))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f88 f86 ?v2) f1) (= (f88 (f37 ?v_0 ?v0) (f37 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16) (?v3 S16) (?v4 S16)) (let ((?v_0 (f53 f55 ?v0))) (= (f52 (f53 f74 (f52 (f53 f54 (f52 ?v_0 ?v1)) (f52 (f53 f55 ?v2) ?v3))) ?v4) (f52 (f53 f58 (f52 ?v_0 (f52 (f53 f74 (f52 (f53 f54 ?v1) ?v3)) ?v4))) (f52 (f53 f55 (f52 (f53 f74 (f52 (f53 f54 ?v0) ?v2)) ?v4)) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4) (?v4 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f20 (f5 (f6 f47 (f5 ?v_0 ?v1)) (f5 (f6 f7 ?v2) ?v3))) ?v4) (f5 (f6 f48 (f5 ?v_0 (f5 (f6 f20 (f5 (f6 f47 ?v1) ?v3)) ?v4))) (f5 (f6 f7 (f5 (f6 f20 (f5 (f6 f47 ?v0) ?v2)) ?v4)) ?v3))))))
(assert (forall ((?v0 S2)) (=> (= (f72 ?v0 f23) f1) false)))
(assert (forall ((?v0 S2)) (not (= (f72 ?v0 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (not (= (f72 (f17 (f18 f30 ?v0) ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (not (= (f72 (f17 (f18 f30 ?v0) ?v1) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= ?v0 ?v1)) (or (= (f72 ?v0 ?v1) f1) (= (f72 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (f17 (f18 f85 f83) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= f83 (f17 (f18 f85 ?v0) ?v1)) (and (= ?v0 f83) (= ?v1 f83)))))
(assert (forall ((?v0 S2)) (= (f17 (f18 f85 ?v0) f83) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f17 (f18 f30 ?v0) ?v1) (f17 (f18 f30 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f18 f30 ?v0)) (?v_0 (f18 f30 ?v1))) (= (f17 ?v_1 (f17 ?v_0 ?v2)) (f17 ?v_0 (f17 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f85 ?v0))) (= (f17 ?v_0 (f17 (f18 f30 ?v1) ?v2)) (f17 (f18 f30 (f17 ?v_0 ?v1)) (f17 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f17 (f18 f85 ?v0) ?v1) f83) (and (= ?v0 f83) (= ?v1 f83)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f30 ?v0))) (= (f17 (f18 f30 (f17 ?v_0 ?v1)) ?v2) (f17 ?v_0 (f17 (f18 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f17 (f18 f85 (f17 (f18 f30 ?v0) ?v1)) ?v2) (f17 (f18 f30 (f17 (f18 f85 ?v0) ?v2)) (f17 (f18 f85 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f30 ?v0))) (= (= (f17 ?v_0 ?v1) (f17 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f17 (f18 f30 ?v0) ?v1) (f17 (f18 f30 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f30 ?v0))) (= (= (f72 (f17 ?v_0 ?v1) (f17 ?v_0 ?v2)) f1) (= (f72 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S16) (?v1 S2)) (let ((?v_0 (f56 f57 ?v0))) (=> (not (= ?v0 f75)) (= (f77 (f78 f79 ?v_0) (f22 f23 ?v1)) (f52 (f53 f74 (f52 (f53 f54 (f31 ?v_0 ?v1)) f75)) (f52 (f53 f54 ?v0) f75)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f72 ?v0 ?v1) f1) false) (=> (=> (= (f72 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S2)) (=> (= (f72 ?v0 ?v0) f1) false)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f72 ?v0 ?v1) f1) (not (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f72 ?v0 ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f72 ?v0 ?v1) f1) (= (f72 ?v0 (f17 (f18 f30 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f72 ?v0 ?v1) f1) (= (f72 ?v0 (f17 (f18 f30 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f72 ?v0 ?v1) f1) (= (f72 (f17 (f18 f30 ?v0) ?v2) (f17 (f18 f30 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f72 ?v0 ?v1) f1) (=> (= (f72 ?v2 ?v3) f1) (= (f72 (f17 (f18 f30 ?v0) ?v2) (f17 (f18 f30 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f72 ?v0 ?v1) f1) (=> (= (f17 (f18 f30 ?v2) ?v1) (f17 (f18 f30 ?v0) ?v3)) (= (f72 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= ?v0 (f17 (f18 f85 ?v0) ?v1)) (or (= ?v1 f83) (= ?v0 f23)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f72 (f17 (f18 f30 ?v0) ?v1) ?v2) f1) (= (f72 ?v0 ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S44)) (let ((?v_0 (= (f93 (f94 ?v2 ?v1) ?v0) f1))) (=> (=> (= (f72 ?v0 ?v1) f1) ?v_0) (=> (=> (= ?v0 ?v1) ?v_0) (=> (=> (= (f72 ?v1 ?v0) f1) ?v_0) ?v_0))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f84 ?v0))) (=> (= (f72 f23 ?v0) f1) (=> (= (f72 (f17 ?v_0 ?v1) (f17 ?v_0 ?v2)) f1) (= (f72 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f72 f23 (f17 (f18 f84 ?v0) ?v1)) f1) (or (= (f72 f23 ?v0) f1) (= ?v1 f23)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f72 f23 (f17 (f18 f30 ?v0) ?v1)) f1) (or (= (f72 f23 ?v0) f1) (= (f72 f23 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f85 ?v2))) (=> (= (f72 ?v0 ?v1) f1) (=> (= (f72 f23 ?v2) f1) (= (f72 (f17 ?v_0 ?v0) (f17 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f72 ?v0 ?v1) f1) (=> (= (f72 f23 ?v2) f1) (= (f72 (f17 (f18 f85 ?v0) ?v2) (f17 (f18 f85 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f72 (f17 (f18 f85 ?v0) ?v1) (f17 (f18 f85 ?v2) ?v1)) f1) (and (= (f72 f23 ?v1) f1) (= (f72 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f85 ?v0))) (= (= (f72 (f17 ?v_0 ?v1) (f17 ?v_0 ?v2)) f1) (and (= (f72 f23 ?v0) f1) (= (f72 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f72 f23 (f17 (f18 f85 ?v0) ?v1)) f1) (and (= (f72 f23 ?v0) f1) (= (f72 f23 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f72 ?v0 ?v1) f1)) (= (f17 (f18 f30 ?v1) (f17 (f18 f19 ?v0) ?v1)) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f72 ?v0 (f17 (f18 f19 ?v1) ?v2)) f1) (= (f72 (f17 (f18 f30 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S15)) (let ((?v_0 (f78 f79 ?v2))) (= (f77 (f78 f79 (f41 (f42 f43 ?v0) ?v2)) (f22 f23 ?v1)) (f52 (f53 f54 (f77 ?v_0 (f22 f23 (f17 (f18 f30 ?v1) ?v0)))) (f77 ?v_0 (f22 f23 ?v0)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S15)) (let ((?v_0 (f78 f79 ?v2))) (= (f77 ?v_0 (f22 f23 (f17 (f18 f30 ?v1) ?v0))) (f52 (f53 f58 (f77 (f78 f79 (f41 (f42 f43 ?v0) ?v2)) (f22 f23 ?v1))) (f77 ?v_0 (f22 f23 ?v0)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f17 (f18 f30 ?v0) ?v1) ?v0) (= ?v1 f23))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f17 (f18 f30 ?v0) ?v1) f23) (and (= ?v0 f23) (= ?v1 f23)))))
(check-sat)
(exit)