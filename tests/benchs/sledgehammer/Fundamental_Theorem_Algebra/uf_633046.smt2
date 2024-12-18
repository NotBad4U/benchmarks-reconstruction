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
(declare-sort S45 0)
(declare-sort S46 0)
(declare-sort S47 0)
(declare-sort S48 0)
(declare-sort S49 0)
(declare-sort S50 0)
(declare-sort S51 0)
(declare-sort S52 0)
(declare-sort S53 0)
(declare-sort S54 0)
(declare-sort S55 0)
(declare-sort S56 0)
(declare-sort S57 0)
(declare-sort S58 0)
(declare-sort S59 0)
(declare-sort S60 0)
(declare-sort S61 0)
(declare-sort S62 0)
(declare-sort S63 0)
(declare-sort S64 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S5) S2)
(declare-fun f5 () S4)
(declare-fun f6 (S6 S3) S5)
(declare-fun f7 (S7 S5) S6)
(declare-fun f8 () S7)
(declare-fun f9 () S5)
(declare-fun f10 () S3)
(declare-fun f11 () S3)
(declare-fun f12 (S8 S3) S2)
(declare-fun f13 () S8)
(declare-fun f14 (S9 S5) S5)
(declare-fun f15 (S10 S5) S9)
(declare-fun f16 () S10)
(declare-fun f17 (S13 S12) S12)
(declare-fun f18 (S14 S11) S13)
(declare-fun f19 () S14)
(declare-fun f20 (S15 S11) S11)
(declare-fun f21 (S16 S11) S15)
(declare-fun f22 () S16)
(declare-fun f23 (S17 S12) S13)
(declare-fun f24 () S17)
(declare-fun f25 (S19 S18) S18)
(declare-fun f26 (S20 S12) S19)
(declare-fun f27 () S20)
(declare-fun f28 (S21 S18) S19)
(declare-fun f29 () S21)
(declare-fun f30 (S24 S23) S23)
(declare-fun f31 (S25 S22) S24)
(declare-fun f32 () S25)
(declare-fun f33 (S26 S22) S22)
(declare-fun f34 (S27 S22) S26)
(declare-fun f35 () S27)
(declare-fun f36 (S28 S23) S24)
(declare-fun f37 () S28)
(declare-fun f38 (S29 S23) S9)
(declare-fun f39 () S29)
(declare-fun f40 () S10)
(declare-fun f41 () S28)
(declare-fun f42 () S17)
(declare-fun f43 (S31 S30) S5)
(declare-fun f44 (S32 S3) S31)
(declare-fun f45 () S32)
(declare-fun f46 (S33 S30) S11)
(declare-fun f47 (S34 S12) S33)
(declare-fun f48 () S34)
(declare-fun f49 (S35 S30) S22)
(declare-fun f50 (S36 S23) S35)
(declare-fun f51 () S36)
(declare-fun f52 (S37 S30) S23)
(declare-fun f53 (S38 S5) S37)
(declare-fun f54 () S38)
(declare-fun f55 (S39 S30) S12)
(declare-fun f56 (S40 S18) S39)
(declare-fun f57 () S40)
(declare-fun f58 (S12) S1)
(declare-fun f59 (S41 S3) S9)
(declare-fun f60 () S41)
(declare-fun f61 (S42 S12) S15)
(declare-fun f62 () S42)
(declare-fun f63 (S43 S23) S26)
(declare-fun f64 () S43)
(declare-fun f65 (S44 S5) S24)
(declare-fun f66 () S44)
(declare-fun f67 (S45 S18) S13)
(declare-fun f68 () S45)
(declare-fun f69 (S46 S30) S3)
(declare-fun f70 (S47 S5) S46)
(declare-fun f71 () S47)
(declare-fun f72 (S48 S11) S39)
(declare-fun f73 () S48)
(declare-fun f74 (S49 S22) S37)
(declare-fun f75 () S49)
(declare-fun f76 (S50 S23) S31)
(declare-fun f77 () S50)
(declare-fun f78 (S51 S30) S18)
(declare-fun f79 (S52 S12) S51)
(declare-fun f80 () S52)
(declare-fun f81 () S41)
(declare-fun f82 () S42)
(declare-fun f83 () S43)
(declare-fun f84 () S44)
(declare-fun f85 () S45)
(declare-fun f86 () S5)
(declare-fun f87 (S53 S12) S11)
(declare-fun f88 (S54 S11) S53)
(declare-fun f89 () S54)
(declare-fun f90 () S11)
(declare-fun f91 (S55 S5) S23)
(declare-fun f92 (S56 S23) S55)
(declare-fun f93 () S56)
(declare-fun f94 () S23)
(declare-fun f95 (S57 S18) S12)
(declare-fun f96 (S58 S12) S57)
(declare-fun f97 () S58)
(declare-fun f98 () S12)
(declare-fun f99 (S11) S1)
(declare-fun f100 () S18)
(declare-fun f101 (S59 S60) S60)
(declare-fun f102 (S61 S11) S59)
(declare-fun f103 () S61)
(declare-fun f104 () S60)
(declare-fun f105 () S22)
(declare-fun f106 () S3)
(declare-fun f107 (S62 S60) S33)
(declare-fun f108 () S62)
(declare-fun f109 (S63 S30) S60)
(declare-fun f110 (S64 S11) S63)
(declare-fun f111 () S64)
(declare-fun f112 () S61)
(declare-fun f113 () S16)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 f5 (f6 (f7 f8 f9) f10)) f11) (f3 (f4 f5 f9) (f3 (f12 f13 f10) f11)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3)) (= (f3 (f4 f5 (f14 (f15 f16 ?v0) ?v1)) ?v2) (f3 (f12 f13 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (= (f17 (f18 f19 (f20 (f21 f22 ?v0) ?v1)) ?v2) (f17 (f23 f24 (f17 (f18 f19 ?v0) ?v2)) (f17 (f18 f19 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S18)) (= (f25 (f26 f27 (f17 (f23 f24 ?v0) ?v1)) ?v2) (f25 (f28 f29 (f25 (f26 f27 ?v0) ?v2)) (f25 (f26 f27 ?v1) ?v2)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S23)) (= (f30 (f31 f32 (f33 (f34 f35 ?v0) ?v1)) ?v2) (f30 (f36 f37 (f30 (f31 f32 ?v0) ?v2)) (f30 (f31 f32 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S5)) (= (f14 (f38 f39 (f30 (f36 f37 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f14 (f38 f39 ?v0) ?v2)) (f14 (f38 f39 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (f17 (f23 f24 ?v0) ?v1) (f17 (f23 f24 ?v1) ?v0))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f25 (f28 f29 ?v0) ?v1) (f25 (f28 f29 ?v1) ?v0))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_1 (f23 f24 ?v0)) (?v_0 (f23 f24 ?v1))) (= (f17 ?v_1 (f17 ?v_0 ?v2)) (f17 ?v_0 (f17 ?v_1 ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_1 (f28 f29 ?v0)) (?v_0 (f28 f29 ?v1))) (= (f25 ?v_1 (f25 ?v_0 ?v2)) (f25 ?v_0 (f25 ?v_1 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (= (f17 ?v_0 (f17 (f23 f24 ?v1) ?v2)) (f17 (f23 f24 (f17 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (= (f25 ?v_0 (f25 (f28 f29 ?v1) ?v2)) (f25 (f28 f29 (f25 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (= (f17 (f23 f24 (f17 ?v_0 ?v1)) ?v2) (f17 ?v_0 (f17 (f23 f24 ?v1) ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (= (f25 (f28 f29 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f28 f29 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f13 ?v0))) (= (f3 (f12 f13 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f12 f13 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (= (f17 (f23 f24 (f17 ?v_0 ?v1)) ?v2) (f17 ?v_0 (f17 (f23 f24 ?v1) ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (= (f25 (f28 f29 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f28 f29 ?v1) ?v2))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f36 f37 ?v0))) (= (f30 (f36 f37 (f30 ?v_0 ?v1)) ?v2) (f30 ?v_0 (f30 (f36 f37 ?v1) ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f15 f16 ?v0))) (= (f14 (f15 f16 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f16 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (= (f17 (f23 f24 (f17 ?v_0 ?v1)) ?v2) (f17 (f23 f24 (f17 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (= (f25 (f28 f29 (f25 ?v_0 ?v1)) ?v2) (f25 (f28 f29 (f25 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (= (= (f17 ?v_0 ?v1) (f17 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (= (= (f25 ?v_0 ?v1) (f25 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (= (= (f17 (f23 f24 ?v0) ?v1) (f17 (f23 f24 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (= (= (f25 (f28 f29 ?v0) ?v1) (f25 (f28 f29 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (let ((?v_0 (f23 f24 ?v0))) (= (f17 (f23 f24 (f17 ?v_0 ?v1)) (f17 (f23 f24 ?v2) ?v3)) (f17 (f23 f24 (f17 ?v_0 ?v2)) (f17 (f23 f24 ?v1) ?v3))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18) (?v3 S18)) (let ((?v_0 (f28 f29 ?v0))) (= (f25 (f28 f29 (f25 ?v_0 ?v1)) (f25 (f28 f29 ?v2) ?v3)) (f25 (f28 f29 (f25 ?v_0 ?v2)) (f25 (f28 f29 ?v1) ?v3))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (=> (= (f17 ?v_0 ?v1) (f17 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (=> (= (f25 ?v_0 ?v1) (f25 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= (f17 (f23 f24 ?v0) ?v1) (f17 (f23 f24 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f25 (f28 f29 ?v0) ?v1) (f25 (f28 f29 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (=> (= (f17 ?v_0 ?v1) (f17 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (=> (= (f25 ?v_0 ?v1) (f25 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3)) (= (f3 (f4 f5 (f14 (f15 f40 ?v0) ?v1)) ?v2) (f3 (f4 f5 ?v0) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S5)) (= (f14 (f38 f39 (f30 (f36 f41 ?v0) ?v1)) ?v2) (f14 (f38 f39 ?v0) (f14 (f38 f39 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S18)) (= (f25 (f26 f27 (f17 (f23 f42 ?v0) ?v1)) ?v2) (f25 (f26 f27 ?v0) (f25 (f26 f27 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S30) (?v2 S3)) (= (f14 (f15 f16 (f43 (f44 f45 ?v0) ?v1)) (f43 (f44 f45 ?v2) ?v1)) (f43 (f44 f45 (f3 (f12 f13 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S12) (?v1 S30) (?v2 S12)) (= (f20 (f21 f22 (f46 (f47 f48 ?v0) ?v1)) (f46 (f47 f48 ?v2) ?v1)) (f46 (f47 f48 (f17 (f23 f24 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S23) (?v1 S30) (?v2 S23)) (= (f33 (f34 f35 (f49 (f50 f51 ?v0) ?v1)) (f49 (f50 f51 ?v2) ?v1)) (f49 (f50 f51 (f30 (f36 f37 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S5) (?v1 S30) (?v2 S5)) (= (f30 (f36 f37 (f52 (f53 f54 ?v0) ?v1)) (f52 (f53 f54 ?v2) ?v1)) (f52 (f53 f54 (f14 (f15 f16 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S18) (?v1 S30) (?v2 S18)) (= (f17 (f23 f24 (f55 (f56 f57 ?v0) ?v1)) (f55 (f56 f57 ?v2) ?v1)) (f55 (f56 f57 (f25 (f28 f29 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f58 ?v0) f1) (=> (= (f58 ?v1) f1) (= (f58 (f17 (f23 f24 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S5)) (= (f14 (f59 f60 (f3 (f12 f13 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f14 (f59 f60 ?v0) ?v2)) (f14 (f59 f60 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S11)) (= (f20 (f61 f62 (f17 (f23 f24 ?v0) ?v1)) ?v2) (f20 (f21 f22 (f20 (f61 f62 ?v0) ?v2)) (f20 (f61 f62 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S22)) (= (f33 (f63 f64 (f30 (f36 f37 ?v0) ?v1)) ?v2) (f33 (f34 f35 (f33 (f63 f64 ?v0) ?v2)) (f33 (f63 f64 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S23)) (= (f30 (f65 f66 (f14 (f15 f16 ?v0) ?v1)) ?v2) (f30 (f36 f37 (f30 (f65 f66 ?v0) ?v2)) (f30 (f65 f66 ?v1) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S12)) (= (f17 (f67 f68 (f25 (f28 f29 ?v0) ?v1)) ?v2) (f17 (f23 f24 (f17 (f67 f68 ?v0) ?v2)) (f17 (f67 f68 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S30)) (= (f69 (f70 f71 (f14 (f15 f16 ?v0) ?v1)) ?v2) (f3 (f12 f13 (f69 (f70 f71 ?v0) ?v2)) (f69 (f70 f71 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S30)) (= (f55 (f72 f73 (f20 (f21 f22 ?v0) ?v1)) ?v2) (f17 (f23 f24 (f55 (f72 f73 ?v0) ?v2)) (f55 (f72 f73 ?v1) ?v2)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S30)) (= (f52 (f74 f75 (f33 (f34 f35 ?v0) ?v1)) ?v2) (f30 (f36 f37 (f52 (f74 f75 ?v0) ?v2)) (f52 (f74 f75 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S30)) (= (f43 (f76 f77 (f30 (f36 f37 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f43 (f76 f77 ?v0) ?v2)) (f43 (f76 f77 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S30)) (= (f78 (f79 f80 (f17 (f23 f24 ?v0) ?v1)) ?v2) (f25 (f28 f29 (f78 (f79 f80 ?v0) ?v2)) (f78 (f79 f80 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S5) (?v2 S3) (?v3 S5)) (= (f14 (f15 f16 (f14 (f59 f81 ?v0) ?v1)) (f14 (f59 f81 ?v2) ?v3)) (f14 (f59 f81 (f3 (f12 f13 ?v0) ?v2)) (f14 (f15 f16 ?v1) ?v3)))))
(assert (forall ((?v0 S12) (?v1 S11) (?v2 S12) (?v3 S11)) (= (f20 (f21 f22 (f20 (f61 f82 ?v0) ?v1)) (f20 (f61 f82 ?v2) ?v3)) (f20 (f61 f82 (f17 (f23 f24 ?v0) ?v2)) (f20 (f21 f22 ?v1) ?v3)))))
(assert (forall ((?v0 S23) (?v1 S22) (?v2 S23) (?v3 S22)) (= (f33 (f34 f35 (f33 (f63 f83 ?v0) ?v1)) (f33 (f63 f83 ?v2) ?v3)) (f33 (f63 f83 (f30 (f36 f37 ?v0) ?v2)) (f33 (f34 f35 ?v1) ?v3)))))
(assert (forall ((?v0 S5) (?v1 S23) (?v2 S5) (?v3 S23)) (= (f30 (f36 f37 (f30 (f65 f84 ?v0) ?v1)) (f30 (f65 f84 ?v2) ?v3)) (f30 (f65 f84 (f14 (f15 f16 ?v0) ?v2)) (f30 (f36 f37 ?v1) ?v3)))))
(assert (forall ((?v0 S18) (?v1 S12) (?v2 S18) (?v3 S12)) (= (f17 (f23 f24 (f17 (f67 f85 ?v0) ?v1)) (f17 (f67 f85 ?v2) ?v3)) (f17 (f67 f85 (f25 (f28 f29 ?v0) ?v2)) (f17 (f23 f24 ?v1) ?v3)))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 f86) ?v0) f86)))
(assert (forall ((?v0 S12)) (= (f87 (f88 f89 f90) ?v0) f90)))
(assert (forall ((?v0 S5)) (= (f91 (f92 f93 f94) ?v0) f94)))
(assert (forall ((?v0 S18)) (= (f95 (f96 f97 f98) ?v0) f98)))
(assert (forall ((?v0 S23)) (= (f30 (f36 f37 f94) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f20 (f21 f22 f90) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f17 (f23 f24 f98) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (f14 (f15 f16 f86) ?v0) ?v0)))
(assert (forall ((?v0 S23)) (= (f30 (f36 f37 ?v0) f94) ?v0)))
(assert (forall ((?v0 S11)) (= (f20 (f21 f22 ?v0) f90) ?v0)))
(assert (forall ((?v0 S12)) (= (f17 (f23 f24 ?v0) f98) ?v0)))
(assert (forall ((?v0 S5)) (= (f14 (f15 f16 ?v0) f86) ?v0)))
(assert (not (= (f99 f90) f1)))
(assert (not (= (f58 f98) f1)))
(assert (= (f17 (f67 f85 f100) f98) f98))
(assert (= (f101 (f102 f103 f90) f104) f104))
(assert (= (f33 (f63 f83 f94) f105) f105))
(assert (= (f30 (f65 f84 f86) f94) f94))
(assert (= (f20 (f61 f82 f98) f90) f90))
(assert (= (f14 (f59 f81 f106) f86) f86))
(assert (forall ((?v0 S30)) (= (f78 (f79 f80 f98) ?v0) f100)))
(assert (forall ((?v0 S30)) (= (f46 (f107 f108 f104) ?v0) f90)))
(assert (forall ((?v0 S30)) (= (f52 (f74 f75 f105) ?v0) f94)))
(assert (forall ((?v0 S30)) (= (f43 (f76 f77 f94) ?v0) f86)))
(assert (forall ((?v0 S30)) (= (f55 (f72 f73 f90) ?v0) f98)))
(assert (forall ((?v0 S30)) (= (f69 (f70 f71 f86) ?v0) f106)))
(assert (forall ((?v0 S30)) (= (f55 (f56 f57 f100) ?v0) f98)))
(assert (forall ((?v0 S30)) (= (f109 (f110 f111 f90) ?v0) f104)))
(assert (forall ((?v0 S30)) (= (f49 (f50 f51 f94) ?v0) f105)))
(assert (forall ((?v0 S30)) (= (f52 (f53 f54 f86) ?v0) f94)))
(assert (forall ((?v0 S30)) (= (f46 (f47 f48 f98) ?v0) f90)))
(assert (forall ((?v0 S30)) (= (f43 (f44 f45 f106) ?v0) f86)))
(assert (forall ((?v0 S12)) (= (f17 (f67 f68 f100) ?v0) f98)))
(assert (forall ((?v0 S60)) (= (f101 (f102 f112 f90) ?v0) f104)))
(assert (forall ((?v0 S22)) (= (f33 (f63 f64 f94) ?v0) f105)))
(assert (forall ((?v0 S23)) (= (f30 (f65 f66 f86) ?v0) f94)))
(assert (forall ((?v0 S11)) (= (f20 (f61 f62 f98) ?v0) f90)))
(assert (forall ((?v0 S5)) (= (f14 (f59 f60 f106) ?v0) f86)))
(assert (forall ((?v0 S11)) (= (f20 (f21 f113 f90) ?v0) f90)))
(assert (forall ((?v0 S23)) (= (f30 (f36 f41 f94) ?v0) f94)))
(assert (forall ((?v0 S12)) (= (f17 (f23 f42 f98) ?v0) f98)))
(assert (forall ((?v0 S5)) (= (f14 (f15 f40 f86) ?v0) f86)))
(assert (forall ((?v0 S18)) (= (= f100 ?v0) (= ?v0 f100))))
(assert (forall ((?v0 S3)) (= (= f106 ?v0) (= ?v0 f106))))
(assert (forall ((?v0 S11)) (= (= f90 ?v0) (= ?v0 f90))))
(assert (forall ((?v0 S23)) (= (= f94 ?v0) (= ?v0 f94))))
(assert (forall ((?v0 S5)) (= (= f86 ?v0) (= ?v0 f86))))
(assert (forall ((?v0 S12)) (= (= f98 ?v0) (= ?v0 f98))))
(check-sat)
(exit)
