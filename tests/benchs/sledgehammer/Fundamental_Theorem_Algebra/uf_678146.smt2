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
(declare-sort S65 0)
(declare-sort S66 0)
(declare-sort S67 0)
(declare-sort S68 0)
(declare-sort S69 0)
(declare-sort S70 0)
(declare-sort S71 0)
(declare-sort S72 0)
(declare-sort S73 0)
(declare-sort S74 0)
(declare-sort S75 0)
(declare-sort S76 0)
(declare-sort S77 0)
(declare-sort S78 0)
(declare-sort S79 0)
(declare-sort S80 0)
(declare-sort S81 0)
(declare-sort S82 0)
(declare-sort S83 0)
(declare-sort S84 0)
(declare-sort S85 0)
(declare-sort S86 0)
(declare-sort S87 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 () S2)
(declare-fun f6 (S6 S5) S5)
(declare-fun f7 (S7 S2) S6)
(declare-fun f8 () S7)
(declare-fun f9 (S8 S5) S6)
(declare-fun f10 () S8)
(declare-fun f11 () S5)
(declare-fun f12 (S9 S2) S2)
(declare-fun f13 (S10 S2) S9)
(declare-fun f14 () S10)
(declare-fun f15 (S13 S12) S12)
(declare-fun f16 (S14 S11) S13)
(declare-fun f17 () S14)
(declare-fun f18 (S15 S11) S11)
(declare-fun f19 (S16 S11) S15)
(declare-fun f20 () S16)
(declare-fun f21 (S17 S12) S13)
(declare-fun f22 () S17)
(declare-fun f23 (S20 S19) S19)
(declare-fun f24 (S21 S18) S20)
(declare-fun f25 () S21)
(declare-fun f26 (S22 S18) S18)
(declare-fun f27 (S23 S18) S22)
(declare-fun f28 () S23)
(declare-fun f29 (S24 S19) S20)
(declare-fun f30 () S24)
(declare-fun f31 (S27 S26) S26)
(declare-fun f32 (S28 S25) S27)
(declare-fun f33 () S28)
(declare-fun f34 (S29 S25) S25)
(declare-fun f35 (S30 S25) S29)
(declare-fun f36 () S30)
(declare-fun f37 (S31 S26) S27)
(declare-fun f38 () S31)
(declare-fun f39 (S32 S26) S9)
(declare-fun f40 () S32)
(declare-fun f41 (S33 S4) S4)
(declare-fun f42 (S34 S19) S33)
(declare-fun f43 () S34)
(declare-fun f44 (S35 S4) S33)
(declare-fun f45 () S35)
(declare-fun f46 (S37 S36) S36)
(declare-fun f47 (S38 S12) S37)
(declare-fun f48 () S38)
(declare-fun f49 (S39 S36) S37)
(declare-fun f50 () S39)
(declare-fun f51 (S40 S5) S2)
(declare-fun f52 (S41 S2) S40)
(declare-fun f53 () S41)
(declare-fun f54 (S42 S12) S11)
(declare-fun f55 (S43 S11) S42)
(declare-fun f56 () S43)
(declare-fun f57 (S44 S19) S18)
(declare-fun f58 (S45 S18) S44)
(declare-fun f59 () S45)
(declare-fun f60 (S46 S26) S25)
(declare-fun f61 (S47 S25) S46)
(declare-fun f62 () S47)
(declare-fun f63 (S48 S2) S26)
(declare-fun f64 (S49 S26) S48)
(declare-fun f65 () S49)
(declare-fun f66 (S50 S4) S19)
(declare-fun f67 (S51 S19) S50)
(declare-fun f68 () S51)
(declare-fun f69 (S52 S36) S12)
(declare-fun f70 (S53 S12) S52)
(declare-fun f71 () S53)
(declare-fun f72 () S17)
(declare-fun f73 () S24)
(declare-fun f74 () S10)
(declare-fun f75 (S54 S4) S50)
(declare-fun f76 () S54)
(declare-fun f77 (S55 S4) S12)
(declare-fun f78 (S56 S36) S55)
(declare-fun f79 () S56)
(declare-fun f80 (S57 S4) S26)
(declare-fun f81 (S58 S2) S57)
(declare-fun f82 () S58)
(declare-fun f83 (S59 S4) S2)
(declare-fun f84 (S60 S5) S59)
(declare-fun f85 () S60)
(declare-fun f86 (S61 S36) S13)
(declare-fun f87 () S61)
(declare-fun f88 (S62 S4) S20)
(declare-fun f89 () S62)
(declare-fun f90 (S63 S2) S27)
(declare-fun f91 () S63)
(declare-fun f92 (S64 S5) S9)
(declare-fun f93 () S64)
(declare-fun f94 () S34)
(declare-fun f95 (S65 S4) S36)
(declare-fun f96 (S66 S12) S65)
(declare-fun f97 () S66)
(declare-fun f98 (S67 S26) S59)
(declare-fun f99 () S67)
(declare-fun f100 (S68 S4) S5)
(declare-fun f101 (S69 S2) S68)
(declare-fun f102 () S69)
(declare-fun f103 () S62)
(declare-fun f104 () S61)
(declare-fun f105 () S63)
(declare-fun f106 () S64)
(declare-fun f107 () S2)
(declare-fun f108 () S12)
(declare-fun f109 () S19)
(declare-fun f110 (S12) S1)
(declare-fun f111 () S5)
(declare-fun f112 () S26)
(declare-fun f113 (S70 S12) S15)
(declare-fun f114 () S70)
(declare-fun f115 () S11)
(declare-fun f116 (S71 S19) S22)
(declare-fun f117 () S71)
(declare-fun f118 () S18)
(declare-fun f119 () S36)
(declare-fun f120 () S4)
(declare-fun f121 (S72 S11) S55)
(declare-fun f122 () S72)
(declare-fun f123 (S73 S18) S50)
(declare-fun f124 () S73)
(declare-fun f125 (S74 S4) S11)
(declare-fun f126 (S75 S12) S74)
(declare-fun f127 () S75)
(declare-fun f128 (S76 S4) S18)
(declare-fun f129 (S77 S19) S76)
(declare-fun f130 () S77)
(declare-fun f131 () S70)
(declare-fun f132 () S71)
(declare-fun f133 (S78 S2) S1)
(declare-fun f134 (S79 S19) S1)
(declare-fun f135 (S80 S12) S1)
(declare-fun f136 () S53)
(declare-fun f137 () S51)
(declare-fun f138 () S41)
(declare-fun f139 (S81 S26) S4)
(declare-fun f140 (S82 S2) S81)
(declare-fun f141 () S82)
(declare-fun f142 (S83 S11) S4)
(declare-fun f143 (S84 S12) S83)
(declare-fun f144 () S84)
(declare-fun f145 (S85 S12) S4)
(declare-fun f146 (S86 S36) S85)
(declare-fun f147 () S86)
(declare-fun f148 (S87 S5) S3)
(declare-fun f149 () S87)
(assert (not (= f1 f2)))
(assert (not (exists ((?v0 S2)) (and (= (f3 f4 ?v0) (f3 f4 f5)) (forall ((?v1 S5)) (= (f6 (f7 f8 ?v0) ?v1) (f6 (f7 f8 f5) (f6 (f9 f10 f11) ?v1))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S5)) (= (f6 (f7 f8 (f12 (f13 f14 ?v0) ?v1)) ?v2) (f6 (f9 f10 (f6 (f7 f8 ?v0) ?v2)) (f6 (f7 f8 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (= (f15 (f16 f17 (f18 (f19 f20 ?v0) ?v1)) ?v2) (f15 (f21 f22 (f15 (f16 f17 ?v0) ?v2)) (f15 (f16 f17 ?v1) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S19)) (= (f23 (f24 f25 (f26 (f27 f28 ?v0) ?v1)) ?v2) (f23 (f29 f30 (f23 (f24 f25 ?v0) ?v2)) (f23 (f24 f25 ?v1) ?v2)))))
(assert (forall ((?v0 S25) (?v1 S25) (?v2 S26)) (= (f31 (f32 f33 (f34 (f35 f36 ?v0) ?v1)) ?v2) (f31 (f37 f38 (f31 (f32 f33 ?v0) ?v2)) (f31 (f32 f33 ?v1) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S2)) (= (f12 (f39 f40 (f31 (f37 f38 ?v0) ?v1)) ?v2) (f12 (f13 f14 (f12 (f39 f40 ?v0) ?v2)) (f12 (f39 f40 ?v1) ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S4)) (= (f41 (f42 f43 (f23 (f29 f30 ?v0) ?v1)) ?v2) (f41 (f44 f45 (f41 (f42 f43 ?v0) ?v2)) (f41 (f42 f43 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S36)) (= (f46 (f47 f48 (f15 (f21 f22 ?v0) ?v1)) ?v2) (f46 (f49 f50 (f46 (f47 f48 ?v0) ?v2)) (f46 (f47 f48 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S5)) (= (f6 (f7 f8 (f51 (f52 f53 ?v0) ?v1)) ?v2) (f6 (f7 f8 ?v0) (f6 (f9 f10 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S12)) (= (f15 (f16 f17 (f54 (f55 f56 ?v0) ?v1)) ?v2) (f15 (f16 f17 ?v0) (f15 (f21 f22 ?v1) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S19) (?v2 S19)) (= (f23 (f24 f25 (f57 (f58 f59 ?v0) ?v1)) ?v2) (f23 (f24 f25 ?v0) (f23 (f29 f30 ?v1) ?v2)))))
(assert (forall ((?v0 S25) (?v1 S26) (?v2 S26)) (= (f31 (f32 f33 (f60 (f61 f62 ?v0) ?v1)) ?v2) (f31 (f32 f33 ?v0) (f31 (f37 f38 ?v1) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S2) (?v2 S2)) (= (f12 (f39 f40 (f63 (f64 f65 ?v0) ?v1)) ?v2) (f12 (f39 f40 ?v0) (f12 (f13 f14 ?v1) ?v2)))))
(assert (forall ((?v0 S19) (?v1 S4) (?v2 S4)) (= (f41 (f42 f43 (f66 (f67 f68 ?v0) ?v1)) ?v2) (f41 (f42 f43 ?v0) (f41 (f44 f45 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S36) (?v2 S36)) (= (f46 (f47 f48 (f69 (f70 f71 ?v0) ?v1)) ?v2) (f46 (f47 f48 ?v0) (f46 (f49 f50 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f7 f8 ?v0) (f7 f8 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f16 f17 ?v0) (f16 f17 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f47 f48 ?v0) (f47 f48 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f6 (f9 f10 ?v0) ?v1) (f6 (f9 f10 ?v1) ?v0))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (f15 (f21 f22 ?v0) ?v1) (f15 (f21 f22 ?v1) ?v0))))
(assert (forall ((?v0 S19) (?v1 S19)) (= (f23 (f29 f30 ?v0) ?v1) (f23 (f29 f30 ?v1) ?v0))))
(assert (forall ((?v0 S26) (?v1 S26)) (= (f31 (f37 f38 ?v0) ?v1) (f31 (f37 f38 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f41 (f44 f45 ?v0) ?v1) (f41 (f44 f45 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f12 (f13 f14 ?v0) ?v1) (f12 (f13 f14 ?v1) ?v0))))
(assert (forall ((?v0 S36) (?v1 S36)) (= (f46 (f49 f50 ?v0) ?v1) (f46 (f49 f50 ?v1) ?v0))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_1 (f9 f10 ?v0)) (?v_0 (f9 f10 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_1 (f21 f22 ?v0)) (?v_0 (f21 f22 ?v1))) (= (f15 ?v_1 (f15 ?v_0 ?v2)) (f15 ?v_0 (f15 ?v_1 ?v2))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_1 (f29 f30 ?v0)) (?v_0 (f29 f30 ?v1))) (= (f23 ?v_1 (f23 ?v_0 ?v2)) (f23 ?v_0 (f23 ?v_1 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_1 (f37 f38 ?v0)) (?v_0 (f37 f38 ?v1))) (= (f31 ?v_1 (f31 ?v_0 ?v2)) (f31 ?v_0 (f31 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f44 f45 ?v0)) (?v_0 (f44 f45 ?v1))) (= (f41 ?v_1 (f41 ?v_0 ?v2)) (f41 ?v_0 (f41 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f13 f14 ?v0)) (?v_0 (f13 f14 ?v1))) (= (f12 ?v_1 (f12 ?v_0 ?v2)) (f12 ?v_0 (f12 ?v_1 ?v2))))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (let ((?v_1 (f49 f50 ?v0)) (?v_0 (f49 f50 ?v1))) (= (f46 ?v_1 (f46 ?v_0 ?v2)) (f46 ?v_0 (f46 ?v_1 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (f6 ?v_0 (f6 (f9 f10 ?v1) ?v2)) (f6 (f9 f10 (f6 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f21 f22 ?v0))) (= (f15 ?v_0 (f15 (f21 f22 ?v1) ?v2)) (f15 (f21 f22 (f15 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f29 f30 ?v0))) (= (f23 ?v_0 (f23 (f29 f30 ?v1) ?v2)) (f23 (f29 f30 (f23 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f37 f38 ?v0))) (= (f31 ?v_0 (f31 (f37 f38 ?v1) ?v2)) (f31 (f37 f38 (f31 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f44 f45 ?v0))) (= (f41 ?v_0 (f41 (f44 f45 ?v1) ?v2)) (f41 (f44 f45 (f41 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (f12 ?v_0 (f12 (f13 f14 ?v1) ?v2)) (f12 (f13 f14 (f12 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (let ((?v_0 (f49 f50 ?v0))) (= (f46 ?v_0 (f46 (f49 f50 ?v1) ?v2)) (f46 (f49 f50 (f46 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (f6 (f9 f10 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f9 f10 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f21 f22 ?v0))) (= (f15 (f21 f22 (f15 ?v_0 ?v1)) ?v2) (f15 ?v_0 (f15 (f21 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f29 f30 ?v0))) (= (f23 (f29 f30 (f23 ?v_0 ?v1)) ?v2) (f23 ?v_0 (f23 (f29 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f37 f38 ?v0))) (= (f31 (f37 f38 (f31 ?v_0 ?v1)) ?v2) (f31 ?v_0 (f31 (f37 f38 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f44 f45 ?v0))) (= (f41 (f44 f45 (f41 ?v_0 ?v1)) ?v2) (f41 ?v_0 (f41 (f44 f45 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (f12 (f13 f14 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f13 f14 ?v1) ?v2))))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (let ((?v_0 (f49 f50 ?v0))) (= (f46 (f49 f50 (f46 ?v_0 ?v1)) ?v2) (f46 ?v_0 (f46 (f49 f50 ?v1) ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (f6 (f9 f10 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f9 f10 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f21 f22 ?v0))) (= (f15 (f21 f22 (f15 ?v_0 ?v1)) ?v2) (f15 ?v_0 (f15 (f21 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f29 f30 ?v0))) (= (f23 (f29 f30 (f23 ?v_0 ?v1)) ?v2) (f23 ?v_0 (f23 (f29 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f37 f38 ?v0))) (= (f31 (f37 f38 (f31 ?v_0 ?v1)) ?v2) (f31 ?v_0 (f31 (f37 f38 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f44 f45 ?v0))) (= (f41 (f44 f45 (f41 ?v_0 ?v1)) ?v2) (f41 ?v_0 (f41 (f44 f45 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (f12 (f13 f14 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f13 f14 ?v1) ?v2))))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (let ((?v_0 (f49 f50 ?v0))) (= (f46 (f49 f50 (f46 ?v_0 ?v1)) ?v2) (f46 ?v_0 (f46 (f49 f50 ?v1) ?v2))))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (let ((?v_0 (f49 f50 ?v0))) (= (f46 (f49 f50 (f46 ?v_0 ?v1)) ?v2) (f46 (f49 f50 (f46 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (f12 (f13 f14 (f12 ?v_0 ?v1)) ?v2) (f12 (f13 f14 (f12 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f44 f45 ?v0))) (= (f41 (f44 f45 (f41 ?v_0 ?v1)) ?v2) (f41 (f44 f45 (f41 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (f6 (f9 f10 (f6 ?v_0 ?v1)) ?v2) (f6 (f9 f10 (f6 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (let ((?v_0 (f49 f50 ?v0))) (= (= (f46 ?v_0 ?v1) (f46 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (= (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f44 f45 ?v0))) (= (= (f41 ?v_0 ?v1) (f41 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (= (f6 ?v_0 ?v1) (f6 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (= (= (f46 (f49 f50 ?v0) ?v1) (f46 (f49 f50 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f12 (f13 f14 ?v0) ?v1) (f12 (f13 f14 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (= (f41 (f44 f45 ?v0) ?v1) (f41 (f44 f45 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (= (= (f6 (f9 f10 ?v0) ?v1) (f6 (f9 f10 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36) (?v3 S36)) (let ((?v_0 (f49 f50 ?v0))) (= (f46 (f49 f50 (f46 ?v_0 ?v1)) (f46 (f49 f50 ?v2) ?v3)) (f46 (f49 f50 (f46 ?v_0 ?v2)) (f46 (f49 f50 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (f12 (f13 f14 (f12 ?v_0 ?v1)) (f12 (f13 f14 ?v2) ?v3)) (f12 (f13 f14 (f12 ?v_0 ?v2)) (f12 (f13 f14 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f44 f45 ?v0))) (= (f41 (f44 f45 (f41 ?v_0 ?v1)) (f41 (f44 f45 ?v2) ?v3)) (f41 (f44 f45 (f41 ?v_0 ?v2)) (f41 (f44 f45 ?v1) ?v3))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (f6 (f9 f10 (f6 ?v_0 ?v1)) (f6 (f9 f10 ?v2) ?v3)) (f6 (f9 f10 (f6 ?v_0 ?v2)) (f6 (f9 f10 ?v1) ?v3))))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (=> (= (f46 (f49 f50 ?v0) ?v1) (f46 (f49 f50 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f12 (f13 f14 ?v0) ?v1) (f12 (f13 f14 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (=> (= (f41 (f44 f45 ?v0) ?v1) (f41 (f44 f45 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f6 (f9 f10 ?v0) ?v1) (f6 (f9 f10 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (let ((?v_0 (f49 f50 ?v0))) (=> (= (f46 ?v_0 ?v1) (f46 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (=> (= (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f44 f45 ?v0))) (=> (= (f41 ?v_0 ?v1) (f41 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (=> (= (f6 ?v_0 ?v1) (f6 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (let ((?v_0 (f49 f50 ?v0))) (=> (= (f46 ?v_0 ?v1) (f46 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (=> (= (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f44 f45 ?v0))) (=> (= (f41 ?v_0 ?v1) (f41 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (=> (= (f6 ?v_0 ?v1) (f6 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S36)) (= (f46 (f47 f48 (f15 (f21 f72 ?v0) ?v1)) ?v2) (f46 (f47 f48 ?v0) (f46 (f47 f48 ?v1) ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S4)) (= (f41 (f42 f43 (f23 (f29 f73 ?v0) ?v1)) ?v2) (f41 (f42 f43 ?v0) (f41 (f42 f43 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S5)) (= (f6 (f7 f8 (f12 (f13 f74 ?v0) ?v1)) ?v2) (f6 (f7 f8 ?v0) (f6 (f7 f8 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f23 (f29 f30 (f66 (f75 f76 ?v0) ?v1)) (f66 (f75 f76 ?v2) ?v1)) (f66 (f75 f76 (f41 (f44 f45 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S36) (?v1 S4) (?v2 S36)) (= (f15 (f21 f22 (f77 (f78 f79 ?v0) ?v1)) (f77 (f78 f79 ?v2) ?v1)) (f77 (f78 f79 (f46 (f49 f50 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S2)) (= (f31 (f37 f38 (f80 (f81 f82 ?v0) ?v1)) (f80 (f81 f82 ?v2) ?v1)) (f80 (f81 f82 (f12 (f13 f14 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S5) (?v1 S4) (?v2 S5)) (= (f12 (f13 f14 (f83 (f84 f85 ?v0) ?v1)) (f83 (f84 f85 ?v2) ?v1)) (f83 (f84 f85 (f6 (f9 f10 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S12)) (= (f15 (f86 f87 (f46 (f49 f50 ?v0) ?v1)) ?v2) (f15 (f21 f22 (f15 (f86 f87 ?v0) ?v2)) (f15 (f86 f87 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S19)) (= (f23 (f88 f89 (f41 (f44 f45 ?v0) ?v1)) ?v2) (f23 (f29 f30 (f23 (f88 f89 ?v0) ?v2)) (f23 (f88 f89 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S26)) (= (f31 (f90 f91 (f12 (f13 f14 ?v0) ?v1)) ?v2) (f31 (f37 f38 (f31 (f90 f91 ?v0) ?v2)) (f31 (f90 f91 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S2)) (= (f12 (f92 f93 (f6 (f9 f10 ?v0) ?v1)) ?v2) (f12 (f13 f14 (f12 (f92 f93 ?v0) ?v2)) (f12 (f92 f93 ?v1) ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S4)) (= (f41 (f42 f94 (f23 (f29 f30 ?v0) ?v1)) ?v2) (f41 (f44 f45 (f41 (f42 f94 ?v0) ?v2)) (f41 (f42 f94 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S4)) (= (f95 (f96 f97 (f15 (f21 f22 ?v0) ?v1)) ?v2) (f46 (f49 f50 (f95 (f96 f97 ?v0) ?v2)) (f95 (f96 f97 ?v1) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S4)) (= (f83 (f98 f99 (f31 (f37 f38 ?v0) ?v1)) ?v2) (f12 (f13 f14 (f83 (f98 f99 ?v0) ?v2)) (f83 (f98 f99 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S4)) (= (f100 (f101 f102 (f12 (f13 f14 ?v0) ?v1)) ?v2) (f6 (f9 f10 (f100 (f101 f102 ?v0) ?v2)) (f100 (f101 f102 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S19) (?v2 S4) (?v3 S19)) (= (f23 (f29 f30 (f23 (f88 f103 ?v0) ?v1)) (f23 (f88 f103 ?v2) ?v3)) (f23 (f88 f103 (f41 (f44 f45 ?v0) ?v2)) (f23 (f29 f30 ?v1) ?v3)))))
(assert (forall ((?v0 S36) (?v1 S12) (?v2 S36) (?v3 S12)) (= (f15 (f21 f22 (f15 (f86 f104 ?v0) ?v1)) (f15 (f86 f104 ?v2) ?v3)) (f15 (f86 f104 (f46 (f49 f50 ?v0) ?v2)) (f15 (f21 f22 ?v1) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S26) (?v2 S2) (?v3 S26)) (= (f31 (f37 f38 (f31 (f90 f105 ?v0) ?v1)) (f31 (f90 f105 ?v2) ?v3)) (f31 (f90 f105 (f12 (f13 f14 ?v0) ?v2)) (f31 (f37 f38 ?v1) ?v3)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S5) (?v3 S2)) (= (f12 (f13 f14 (f12 (f92 f106 ?v0) ?v1)) (f12 (f92 f106 ?v2) ?v3)) (f12 (f92 f106 (f6 (f9 f10 ?v0) ?v2)) (f12 (f13 f14 ?v1) ?v3)))))
(assert (forall ((?v0 S5)) (= (f51 (f52 f53 f107) ?v0) f107)))
(assert (forall ((?v0 S36)) (= (f69 (f70 f71 f108) ?v0) f108)))
(assert (forall ((?v0 S4)) (= (f66 (f67 f68 f109) ?v0) f109)))
(assert (forall ((?v0 S2) (?v1 S5)) (= (= (f51 (f52 f53 ?v0) ?v1) f107) (= ?v0 f107))))
(assert (forall ((?v0 S12) (?v1 S36)) (= (= (f69 (f70 f71 ?v0) ?v1) f108) (= ?v0 f108))))
(assert (forall ((?v0 S19) (?v1 S4)) (= (= (f66 (f67 f68 ?v0) ?v1) f109) (= ?v0 f109))))
(assert (forall ((?v0 S2)) (= (f12 (f13 f14 f107) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f15 (f21 f22 f108) ?v0) ?v0)))
(assert (forall ((?v0 S19)) (= (f23 (f29 f30 f109) ?v0) ?v0)))
(assert (not (= (f110 f108) f1)))
(assert (= (f12 (f92 f106 f111) f107) f107))
(assert (= (f31 (f90 f105 f107) f112) f112))
(assert (= (f18 (f113 f114 f108) f115) f115))
(assert (= (f26 (f116 f117 f109) f118) f118))
(assert (= (f15 (f86 f104 f119) f108) f108))
(assert (= (f23 (f88 f103 f120) f109) f109))
(assert (forall ((?v0 S4)) (= (f100 (f101 f102 f107) ?v0) f111)))
(assert (forall ((?v0 S4)) (= (f83 (f98 f99 f112) ?v0) f107)))
(assert (forall ((?v0 S4)) (= (f77 (f121 f122 f115) ?v0) f108)))
(assert (forall ((?v0 S4)) (= (f66 (f123 f124 f118) ?v0) f109)))
(assert (forall ((?v0 S4)) (= (f95 (f96 f97 f108) ?v0) f119)))
(assert (forall ((?v0 S4)) (= (f41 (f42 f94 f109) ?v0) f120)))
(assert (forall ((?v0 S4)) (= (f83 (f84 f85 f111) ?v0) f107)))
(assert (forall ((?v0 S4)) (= (f80 (f81 f82 f107) ?v0) f112)))
(assert (forall ((?v0 S4)) (= (f125 (f126 f127 f108) ?v0) f115)))
(assert (forall ((?v0 S4)) (= (f128 (f129 f130 f109) ?v0) f118)))
(assert (forall ((?v0 S4)) (= (f77 (f78 f79 f119) ?v0) f108)))
(assert (forall ((?v0 S4)) (= (f66 (f75 f76 f120) ?v0) f109)))
(assert (forall ((?v0 S2)) (= (f12 (f92 f93 f111) ?v0) f107)))
(assert (forall ((?v0 S26)) (= (f31 (f90 f91 f107) ?v0) f112)))
(assert (forall ((?v0 S11)) (= (f18 (f113 f131 f108) ?v0) f115)))
(assert (forall ((?v0 S18)) (= (f26 (f116 f132 f109) ?v0) f118)))
(assert (forall ((?v0 S12)) (= (f15 (f86 f87 f119) ?v0) f108)))
(assert (forall ((?v0 S19)) (= (f23 (f88 f89 f120) ?v0) f109)))
(assert (forall ((?v0 S2)) (= (f12 (f13 f74 f107) ?v0) f107)))
(assert (forall ((?v0 S12)) (= (f15 (f21 f72 f108) ?v0) f108)))
(assert (forall ((?v0 S19)) (= (f23 (f29 f73 f109) ?v0) f109)))
(assert (forall ((?v0 S5)) (= (= f111 ?v0) (= ?v0 f111))))
(assert (forall ((?v0 S2)) (= (= f107 ?v0) (= ?v0 f107))))
(assert (forall ((?v0 S12)) (= (= f108 ?v0) (= ?v0 f108))))
(assert (forall ((?v0 S19)) (= (= f109 ?v0) (= ?v0 f109))))
(assert (forall ((?v0 S36)) (= (= f119 ?v0) (= ?v0 f119))))
(assert (forall ((?v0 S4)) (= (= f120 ?v0) (= ?v0 f120))))
(assert (forall ((?v0 S5)) (= (f12 (f92 f93 ?v0) f107) f107)))
(assert (forall ((?v0 S36)) (= (f15 (f86 f87 ?v0) f108) f108)))
(assert (forall ((?v0 S4)) (= (f23 (f88 f89 ?v0) f109) f109)))
(assert (forall ((?v0 S19) (?v1 S19)) (= (= ?v0 ?v1) (forall ((?v2 S4)) (= (f41 (f42 f94 ?v0) ?v2) (f41 (f42 f94 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= ?v0 ?v1) (forall ((?v2 S4)) (= (f95 (f96 f97 ?v0) ?v2) (f95 (f96 f97 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 ?v1) (forall ((?v2 S4)) (= (f100 (f101 f102 ?v0) ?v2) (f100 (f101 f102 ?v1) ?v2))))))
(assert (forall ((?v0 S19) (?v1 S19)) (= (= (f42 f94 ?v0) (f42 f94 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f96 f97 ?v0) (f96 f97 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f101 f102 ?v0) (f101 f102 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S4)) (= (= (f83 (f84 f85 ?v0) ?v1) f107) (= ?v0 f111))))
(assert (forall ((?v0 S2) (?v1 S4)) (= (= (f80 (f81 f82 ?v0) ?v1) f112) (= ?v0 f107))))
(assert (forall ((?v0 S12) (?v1 S4)) (= (= (f125 (f126 f127 ?v0) ?v1) f115) (= ?v0 f108))))
(assert (forall ((?v0 S19) (?v1 S4)) (= (= (f128 (f129 f130 ?v0) ?v1) f118) (= ?v0 f109))))
(assert (forall ((?v0 S36) (?v1 S4)) (= (= (f77 (f78 f79 ?v0) ?v1) f108) (= ?v0 f119))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f66 (f75 f76 ?v0) ?v1) f109) (= ?v0 f120))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (= (f12 (f92 f106 ?v0) ?v1) f107) (and (= ?v0 f111) (= ?v1 f107)))))
(assert (forall ((?v0 S2) (?v1 S26)) (= (= (f31 (f90 f105 ?v0) ?v1) f112) (and (= ?v0 f107) (= ?v1 f112)))))
(assert (forall ((?v0 S12) (?v1 S11)) (= (= (f18 (f113 f114 ?v0) ?v1) f115) (and (= ?v0 f108) (= ?v1 f115)))))
(assert (forall ((?v0 S19) (?v1 S18)) (= (= (f26 (f116 f117 ?v0) ?v1) f118) (and (= ?v0 f109) (= ?v1 f118)))))
(assert (forall ((?v0 S36) (?v1 S12)) (= (= (f15 (f86 f104 ?v0) ?v1) f108) (and (= ?v0 f119) (= ?v1 f108)))))
(assert (forall ((?v0 S4) (?v1 S19)) (= (= (f23 (f88 f103 ?v0) ?v1) f109) (and (= ?v0 f120) (= ?v1 f109)))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (= (f12 (f92 f93 ?v0) ?v1) f107) (or (= ?v0 f111) (= ?v1 f107)))))
(assert (forall ((?v0 S2) (?v1 S26)) (= (= (f31 (f90 f91 ?v0) ?v1) f112) (or (= ?v0 f107) (= ?v1 f112)))))
(assert (forall ((?v0 S12) (?v1 S11)) (= (= (f18 (f113 f131 ?v0) ?v1) f115) (or (= ?v0 f108) (= ?v1 f115)))))
(assert (forall ((?v0 S36) (?v1 S12)) (= (= (f15 (f86 f87 ?v0) ?v1) f108) (or (= ?v0 f119) (= ?v1 f108)))))
(assert (forall ((?v0 S5) (?v1 S4) (?v2 S4)) (= (f100 (f101 f102 (f83 (f84 f85 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f111))))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S4)) (= (f83 (f98 f99 (f80 (f81 f82 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f107))))
(assert (forall ((?v0 S12) (?v1 S4) (?v2 S4)) (= (f77 (f121 f122 (f125 (f126 f127 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f108))))
(assert (forall ((?v0 S19) (?v1 S4) (?v2 S4)) (= (f66 (f123 f124 (f128 (f129 f130 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f109))))
(assert (forall ((?v0 S36) (?v1 S4) (?v2 S4)) (= (f95 (f96 f97 (f77 (f78 f79 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f119))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f41 (f42 f94 (f66 (f75 f76 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f120))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (= (f66 (f75 f76 ?v0) ?v1) (f66 (f75 f76 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S36) (?v1 S4) (?v2 S36)) (= (= (f77 (f78 f79 ?v0) ?v1) (f77 (f78 f79 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S5) (?v1 S4) (?v2 S5)) (= (= (f83 (f84 f85 ?v0) ?v1) (f83 (f84 f85 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S5) (?v3 S2)) (= (= (f12 (f92 f106 ?v0) ?v1) (f12 (f92 f106 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S19) (?v2 S4) (?v3 S19)) (= (= (f23 (f88 f103 ?v0) ?v1) (f23 (f88 f103 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S36) (?v1 S12) (?v2 S36) (?v3 S12)) (= (= (f15 (f86 f104 ?v0) ?v1) (f15 (f86 f104 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S5)) (=> (= (f12 (f92 f93 ?v0) ?v1) (f12 (f92 f106 ?v2) ?v1)) (= ?v1 f107))))
(assert (forall ((?v0 S4) (?v1 S19) (?v2 S4)) (=> (= (f23 (f88 f89 ?v0) ?v1) (f23 (f88 f103 ?v2) ?v1)) (= ?v1 f109))))
(assert (forall ((?v0 S36) (?v1 S12) (?v2 S36)) (=> (= (f15 (f86 f87 ?v0) ?v1) (f15 (f86 f104 ?v2) ?v1)) (= ?v1 f108))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S5)) (=> (= (f12 (f13 f14 (f12 (f92 f93 ?v0) ?v1)) (f12 (f92 f106 ?v2) ?v1)) f107) (= ?v1 f107))))
(assert (forall ((?v0 S4) (?v1 S19) (?v2 S4)) (=> (= (f23 (f29 f30 (f23 (f88 f89 ?v0) ?v1)) (f23 (f88 f103 ?v2) ?v1)) f109) (= ?v1 f109))))
(assert (forall ((?v0 S36) (?v1 S12) (?v2 S36)) (=> (= (f15 (f21 f22 (f15 (f86 f87 ?v0) ?v1)) (f15 (f86 f104 ?v2) ?v1)) f108) (= ?v1 f108))))
(assert (forall ((?v0 S2)) (= (f12 (f39 f40 f112) ?v0) f107)))
(assert (forall ((?v0 S12)) (= (f15 (f16 f17 f115) ?v0) f108)))
(assert (forall ((?v0 S19)) (= (f23 (f24 f25 f118) ?v0) f109)))
(assert (forall ((?v0 S36)) (= (f46 (f47 f48 f108) ?v0) f119)))
(assert (forall ((?v0 S4)) (= (f41 (f42 f43 f109) ?v0) f120)))
(assert (forall ((?v0 S5)) (= (f6 (f7 f8 f107) ?v0) f111)))
(assert (forall ((?v0 S5) (?v1 S5)) (let ((?v_0 (f12 (f92 f106 ?v0) f107))) (= (f51 (f52 f53 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_0 (f23 (f88 f103 ?v0) f109))) (= (f66 (f67 f68 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S36) (?v1 S36)) (let ((?v_0 (f15 (f86 f104 ?v0) f108))) (= (f69 (f70 f71 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S5)) (let ((?v_0 (f92 f106 ?v0)) (?v_1 (f51 (f52 f53 ?v1) ?v2))) (= (f51 (f52 f53 (f12 ?v_0 ?v1)) ?v2) (f12 (f13 f14 (f12 (f92 f93 ?v2) ?v_1)) (f12 ?v_0 ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S19) (?v2 S4)) (let ((?v_0 (f88 f103 ?v0)) (?v_1 (f66 (f67 f68 ?v1) ?v2))) (= (f66 (f67 f68 (f23 ?v_0 ?v1)) ?v2) (f23 (f29 f30 (f23 (f88 f89 ?v2) ?v_1)) (f23 ?v_0 ?v_1))))))
(assert (forall ((?v0 S36) (?v1 S12) (?v2 S36)) (let ((?v_0 (f86 f104 ?v0)) (?v_1 (f69 (f70 f71 ?v1) ?v2))) (= (f69 (f70 f71 (f15 ?v_0 ?v1)) ?v2) (f15 (f21 f22 (f15 (f86 f87 ?v2) ?v_1)) (f15 ?v_0 ?v_1))))))
(assert (forall ((?v0 S2)) (= (f12 (f13 f14 f107) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f15 (f21 f22 f108) ?v0) ?v0)))
(assert (forall ((?v0 S19)) (= (f23 (f29 f30 f109) ?v0) ?v0)))
(assert (forall ((?v0 S36)) (= (f46 (f49 f50 f119) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f41 (f44 f45 f120) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (f6 (f9 f10 f111) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f12 (f13 f14 f107) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f15 (f21 f22 f108) ?v0) ?v0)))
(assert (forall ((?v0 S19)) (= (f23 (f29 f30 f109) ?v0) ?v0)))
(assert (forall ((?v0 S36)) (= (f46 (f49 f50 f119) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f41 (f44 f45 f120) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (f6 (f9 f10 f111) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f12 (f13 f14 f107) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f15 (f21 f22 f108) ?v0) ?v0)))
(assert (forall ((?v0 S19)) (= (f23 (f29 f30 f109) ?v0) ?v0)))
(assert (forall ((?v0 S36)) (= (f46 (f49 f50 f119) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f41 (f44 f45 f120) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (f6 (f9 f10 f111) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (= f108 (f15 (f21 f22 ?v0) ?v0)) (= ?v0 f108))))
(assert (forall ((?v0 S36)) (= (= f119 (f46 (f49 f50 ?v0) ?v0)) (= ?v0 f119))))
(assert (forall ((?v0 S2)) (= (f12 (f13 f14 ?v0) f107) ?v0)))
(assert (forall ((?v0 S12)) (= (f15 (f21 f22 ?v0) f108) ?v0)))
(assert (forall ((?v0 S19)) (= (f23 (f29 f30 ?v0) f109) ?v0)))
(assert (forall ((?v0 S36)) (= (f46 (f49 f50 ?v0) f119) ?v0)))
(assert (forall ((?v0 S4)) (= (f41 (f44 f45 ?v0) f120) ?v0)))
(assert (forall ((?v0 S5)) (= (f6 (f9 f10 ?v0) f111) ?v0)))
(assert (forall ((?v0 S2)) (= (f12 (f13 f14 ?v0) f107) ?v0)))
(assert (forall ((?v0 S12)) (= (f15 (f21 f22 ?v0) f108) ?v0)))
(assert (forall ((?v0 S19)) (= (f23 (f29 f30 ?v0) f109) ?v0)))
(assert (forall ((?v0 S36)) (= (f46 (f49 f50 ?v0) f119) ?v0)))
(assert (forall ((?v0 S4)) (= (f41 (f44 f45 ?v0) f120) ?v0)))
(assert (forall ((?v0 S5)) (= (f6 (f9 f10 ?v0) f111) ?v0)))
(assert (forall ((?v0 S2)) (= (f12 (f13 f14 ?v0) f107) ?v0)))
(assert (forall ((?v0 S12)) (= (f15 (f21 f22 ?v0) f108) ?v0)))
(assert (forall ((?v0 S19)) (= (f23 (f29 f30 ?v0) f109) ?v0)))
(assert (forall ((?v0 S36)) (= (f46 (f49 f50 ?v0) f119) ?v0)))
(assert (forall ((?v0 S4)) (= (f41 (f44 f45 ?v0) f120) ?v0)))
(assert (forall ((?v0 S5)) (= (f6 (f9 f10 ?v0) f111) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 (f12 (f13 f14 ?v0) ?v1)) (= ?v1 f107))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= ?v0 (f15 (f21 f22 ?v0) ?v1)) (= ?v1 f108))))
(assert (forall ((?v0 S36) (?v1 S36)) (= (= ?v0 (f46 (f49 f50 ?v0) ?v1)) (= ?v1 f119))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= ?v0 (f41 (f44 f45 ?v0) ?v1)) (= ?v1 f120))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= ?v0 (f6 (f9 f10 ?v0) ?v1)) (= ?v1 f111))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2)) (let ((?v_0 (f92 f93 ?v0))) (= (f12 ?v_0 (f12 (f13 f14 ?v1) ?v2)) (f12 (f13 f14 (f12 ?v_0 ?v1)) (f12 ?v_0 ?v2))))))
(assert (forall ((?v0 S36) (?v1 S12) (?v2 S12)) (let ((?v_0 (f86 f87 ?v0))) (= (f15 ?v_0 (f15 (f21 f22 ?v1) ?v2)) (f15 (f21 f22 (f15 ?v_0 ?v1)) (f15 ?v_0 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S19) (?v2 S19)) (let ((?v_0 (f88 f89 ?v0))) (= (f23 ?v_0 (f23 (f29 f30 ?v1) ?v2)) (f23 (f29 f30 (f23 ?v_0 ?v1)) (f23 ?v_0 ?v2))))))
(assert (forall ((?v0 S12)) (= (= (f47 f48 ?v0) (f47 f48 f108)) (= ?v0 f108))))
(assert (forall ((?v0 S2)) (= (= (f7 f8 ?v0) (f7 f8 f107)) (= ?v0 f107))))
(assert (forall ((?v0 S2)) (= (f12 (f13 f14 ?v0) f107) ?v0)))
(assert (forall ((?v0 S12)) (= (f15 (f21 f22 ?v0) f108) ?v0)))
(assert (forall ((?v0 S19)) (= (f23 (f29 f30 ?v0) f109) ?v0)))
(assert (forall ((?v0 S78) (?v1 S2)) (=> (= (f133 ?v0 f107) f1) (=> (forall ((?v2 S5) (?v3 S2)) (=> (= (f133 ?v0 ?v3) f1) (= (f133 ?v0 (f12 (f92 f106 ?v2) ?v3)) f1))) (= (f133 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S79) (?v1 S19)) (=> (= (f134 ?v0 f109) f1) (=> (forall ((?v2 S4) (?v3 S19)) (=> (= (f134 ?v0 ?v3) f1) (= (f134 ?v0 (f23 (f88 f103 ?v2) ?v3)) f1))) (= (f134 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S80) (?v1 S12)) (=> (= (f135 ?v0 f108) f1) (=> (forall ((?v2 S36) (?v3 S12)) (=> (= (f135 ?v0 ?v3) f1) (= (f135 ?v0 (f15 (f86 f104 ?v2) ?v3)) f1))) (= (f135 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S36) (?v2 S12) (?v3 S36)) (=> (= (f15 (f21 f22 ?v0) (f15 (f86 f87 ?v1) ?v2)) (f15 (f86 f104 ?v3) ?v2)) (and (= ?v3 (f46 (f47 f48 ?v0) ?v1)) (= ?v2 (f69 (f70 f136 ?v0) ?v1))))))
(assert (forall ((?v0 S19) (?v1 S4) (?v2 S19) (?v3 S4)) (=> (= (f23 (f29 f30 ?v0) (f23 (f88 f89 ?v1) ?v2)) (f23 (f88 f103 ?v3) ?v2)) (and (= ?v3 (f41 (f42 f43 ?v0) ?v1)) (= ?v2 (f66 (f67 f137 ?v0) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2) (?v3 S5)) (=> (= (f12 (f13 f14 ?v0) (f12 (f92 f93 ?v1) ?v2)) (f12 (f92 f106 ?v3) ?v2)) (and (= ?v3 (f6 (f7 f8 ?v0) ?v1)) (= ?v2 (f51 (f52 f138 ?v0) ?v1))))))
(assert (forall ((?v0 S12) (?v1 S36)) (let ((?v_0 (f69 (f70 f136 ?v0) ?v1))) (= (f15 (f21 f22 ?v0) (f15 (f86 f87 ?v1) ?v_0)) (f15 (f86 f104 (f46 (f47 f48 ?v0) ?v1)) ?v_0)))))
(assert (forall ((?v0 S19) (?v1 S4)) (let ((?v_0 (f66 (f67 f137 ?v0) ?v1))) (= (f23 (f29 f30 ?v0) (f23 (f88 f89 ?v1) ?v_0)) (f23 (f88 f103 (f41 (f42 f43 ?v0) ?v1)) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S5)) (let ((?v_0 (f51 (f52 f138 ?v0) ?v1))) (= (f12 (f13 f14 ?v0) (f12 (f92 f93 ?v1) ?v_0)) (f12 (f92 f106 (f6 (f7 f8 ?v0) ?v1)) ?v_0)))))
(assert (forall ((?v0 S26) (?v1 S2)) (= (= (f12 (f39 f40 ?v0) ?v1) f107) (or (= ?v0 f112) (not (= (f139 (f140 f141 ?v1) ?v0) f120))))))
(assert (forall ((?v0 S11) (?v1 S12)) (= (= (f15 (f16 f17 ?v0) ?v1) f108) (or (= ?v0 f115) (not (= (f142 (f143 f144 ?v1) ?v0) f120))))))
(assert (forall ((?v0 S12) (?v1 S36)) (= (= (f46 (f47 f48 ?v0) ?v1) f119) (or (= ?v0 f108) (not (= (f145 (f146 f147 ?v1) ?v0) f120))))))
(assert (forall ((?v0 S2) (?v1 S5)) (= (= (f6 (f7 f8 ?v0) ?v1) f111) (or (= ?v0 f107) (not (= (f3 (f148 f149 ?v1) ?v0) f120))))))
(assert (forall ((?v0 S12)) (= (= (f15 (f21 f22 ?v0) ?v0) f108) (= ?v0 f108))))
(assert (forall ((?v0 S36)) (= (= (f46 (f49 f50 ?v0) ?v0) f119) (= ?v0 f119))))
(check-sat)
(exit)