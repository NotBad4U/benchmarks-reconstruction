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
(declare-sort S88 0)
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
(declare-fun f25 (S20 S19) S19)
(declare-fun f26 (S21 S18) S20)
(declare-fun f27 () S21)
(declare-fun f28 (S22 S18) S18)
(declare-fun f29 (S23 S18) S22)
(declare-fun f30 () S23)
(declare-fun f31 (S24 S19) S20)
(declare-fun f32 () S24)
(declare-fun f33 (S27 S26) S26)
(declare-fun f34 (S28 S25) S27)
(declare-fun f35 () S28)
(declare-fun f36 (S29 S25) S25)
(declare-fun f37 (S30 S25) S29)
(declare-fun f38 () S30)
(declare-fun f39 (S31 S26) S27)
(declare-fun f40 () S31)
(declare-fun f41 (S32 S26) S9)
(declare-fun f42 () S32)
(declare-fun f43 (S34 S33) S33)
(declare-fun f44 (S35 S19) S34)
(declare-fun f45 () S35)
(declare-fun f46 (S36 S33) S34)
(declare-fun f47 () S36)
(declare-fun f48 (S38 S37) S37)
(declare-fun f49 (S39 S12) S38)
(declare-fun f50 () S39)
(declare-fun f51 (S40 S37) S38)
(declare-fun f52 () S40)
(declare-fun f53 () S10)
(declare-fun f54 () S16)
(declare-fun f55 () S23)
(declare-fun f56 () S31)
(declare-fun f57 () S24)
(declare-fun f58 () S17)
(declare-fun f59 (S41 S33) S5)
(declare-fun f60 (S42 S3) S41)
(declare-fun f61 () S42)
(declare-fun f62 (S43 S33) S18)
(declare-fun f63 (S44 S19) S43)
(declare-fun f64 () S44)
(declare-fun f65 (S45 S33) S11)
(declare-fun f66 (S46 S12) S45)
(declare-fun f67 () S46)
(declare-fun f68 (S47 S33) S25)
(declare-fun f69 (S48 S26) S47)
(declare-fun f70 () S48)
(declare-fun f71 (S49 S33) S26)
(declare-fun f72 (S50 S5) S49)
(declare-fun f73 () S50)
(declare-fun f74 (S51 S33) S12)
(declare-fun f75 (S52 S37) S51)
(declare-fun f76 () S52)
(declare-fun f77 (S53 S33) S19)
(declare-fun f78 (S54 S33) S53)
(declare-fun f79 () S54)
(declare-fun f80 (S12) S1)
(declare-fun f81 (S55 S3) S9)
(declare-fun f82 () S55)
(declare-fun f83 (S56 S12) S15)
(declare-fun f84 () S56)
(declare-fun f85 (S57 S19) S22)
(declare-fun f86 () S57)
(declare-fun f87 (S58 S26) S29)
(declare-fun f88 () S58)
(declare-fun f89 (S59 S5) S27)
(declare-fun f90 () S59)
(declare-fun f91 (S60 S33) S20)
(declare-fun f92 () S60)
(declare-fun f93 (S61 S37) S13)
(declare-fun f94 () S61)
(declare-fun f95 (S62 S33) S3)
(declare-fun f96 (S63 S5) S62)
(declare-fun f97 () S63)
(declare-fun f98 (S64 S18) S53)
(declare-fun f99 () S64)
(declare-fun f100 (S65 S11) S51)
(declare-fun f101 () S65)
(declare-fun f102 (S66 S25) S49)
(declare-fun f103 () S66)
(declare-fun f104 (S67 S26) S41)
(declare-fun f105 () S67)
(declare-fun f106 (S68 S33) S37)
(declare-fun f107 (S69 S12) S68)
(declare-fun f108 () S69)
(declare-fun f109 () S35)
(declare-fun f110 () S55)
(declare-fun f111 () S57)
(declare-fun f112 () S56)
(declare-fun f113 () S58)
(declare-fun f114 () S59)
(declare-fun f115 () S61)
(declare-fun f116 () S60)
(declare-fun f117 () S5)
(declare-fun f118 (S70 S19) S18)
(declare-fun f119 (S71 S18) S70)
(declare-fun f120 () S71)
(declare-fun f121 () S18)
(declare-fun f122 (S72 S12) S11)
(declare-fun f123 (S73 S11) S72)
(declare-fun f124 () S73)
(declare-fun f125 () S11)
(declare-fun f126 (S74 S5) S26)
(declare-fun f127 (S75 S26) S74)
(declare-fun f128 () S75)
(declare-fun f129 () S26)
(declare-fun f130 (S76 S37) S12)
(declare-fun f131 (S77 S12) S76)
(declare-fun f132 () S77)
(declare-fun f133 () S12)
(declare-fun f134 (S78 S19) S53)
(declare-fun f135 () S78)
(declare-fun f136 () S19)
(declare-fun f137 (S11) S1)
(declare-fun f138 () S33)
(declare-fun f139 () S37)
(declare-fun f140 (S18 S79) S79)
(declare-fun f141 () S79)
(declare-fun f142 (S11 S80) S80)
(declare-fun f143 () S80)
(declare-fun f144 () S25)
(declare-fun f145 () S3)
(declare-fun f146 (S81 S80) S45)
(declare-fun f147 () S81)
(declare-fun f148 (S82 S19) S1)
(declare-fun f149 (S83 S12) S1)
(declare-fun f150 (S84 S5) S1)
(declare-fun f151 () S77)
(declare-fun f152 () S78)
(declare-fun f153 () S7)
(declare-fun f154 (S85 S11) S33)
(declare-fun f155 (S86 S12) S85)
(declare-fun f156 () S86)
(declare-fun f157 (S87 S12) S33)
(declare-fun f158 (S88 S37) S87)
(declare-fun f159 () S88)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 f5 (f6 (f7 f8 f9) f10)) f11) (f3 (f4 f5 f9) (f3 (f12 f13 f10) f11)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3)) (= (f3 (f4 f5 (f14 (f15 f16 ?v0) ?v1)) ?v2) (f3 (f12 f13 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (= (f17 (f18 f19 (f20 (f21 f22 ?v0) ?v1)) ?v2) (f17 (f23 f24 (f17 (f18 f19 ?v0) ?v2)) (f17 (f18 f19 ?v1) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S19)) (= (f25 (f26 f27 (f28 (f29 f30 ?v0) ?v1)) ?v2) (f25 (f31 f32 (f25 (f26 f27 ?v0) ?v2)) (f25 (f26 f27 ?v1) ?v2)))))
(assert (forall ((?v0 S25) (?v1 S25) (?v2 S26)) (= (f33 (f34 f35 (f36 (f37 f38 ?v0) ?v1)) ?v2) (f33 (f39 f40 (f33 (f34 f35 ?v0) ?v2)) (f33 (f34 f35 ?v1) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S5)) (= (f14 (f41 f42 (f33 (f39 f40 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f14 (f41 f42 ?v0) ?v2)) (f14 (f41 f42 ?v1) ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S33)) (= (f43 (f44 f45 (f25 (f31 f32 ?v0) ?v1)) ?v2) (f43 (f46 f47 (f43 (f44 f45 ?v0) ?v2)) (f43 (f44 f45 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S37)) (= (f48 (f49 f50 (f17 (f23 f24 ?v0) ?v1)) ?v2) (f48 (f51 f52 (f48 (f49 f50 ?v0) ?v2)) (f48 (f49 f50 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f18 f19 ?v0) (f18 f19 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f49 f50 ?v0) (f49 f50 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (f17 (f23 f24 ?v0) ?v1) (f17 (f23 f24 ?v1) ?v0))))
(assert (forall ((?v0 S19) (?v1 S19)) (= (f25 (f31 f32 ?v0) ?v1) (f25 (f31 f32 ?v1) ?v0))))
(assert (forall ((?v0 S33) (?v1 S33)) (= (f43 (f46 f47 ?v0) ?v1) (f43 (f46 f47 ?v1) ?v0))))
(assert (forall ((?v0 S37) (?v1 S37)) (= (f48 (f51 f52 ?v0) ?v1) (f48 (f51 f52 ?v1) ?v0))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_1 (f23 f24 ?v0)) (?v_0 (f23 f24 ?v1))) (= (f17 ?v_1 (f17 ?v_0 ?v2)) (f17 ?v_0 (f17 ?v_1 ?v2))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_1 (f31 f32 ?v0)) (?v_0 (f31 f32 ?v1))) (= (f25 ?v_1 (f25 ?v_0 ?v2)) (f25 ?v_0 (f25 ?v_1 ?v2))))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (let ((?v_1 (f46 f47 ?v0)) (?v_0 (f46 f47 ?v1))) (= (f43 ?v_1 (f43 ?v_0 ?v2)) (f43 ?v_0 (f43 ?v_1 ?v2))))))
(assert (forall ((?v0 S37) (?v1 S37) (?v2 S37)) (let ((?v_1 (f51 f52 ?v0)) (?v_0 (f51 f52 ?v1))) (= (f48 ?v_1 (f48 ?v_0 ?v2)) (f48 ?v_0 (f48 ?v_1 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (= (f17 ?v_0 (f17 (f23 f24 ?v1) ?v2)) (f17 (f23 f24 (f17 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f31 f32 ?v0))) (= (f25 ?v_0 (f25 (f31 f32 ?v1) ?v2)) (f25 (f31 f32 (f25 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (let ((?v_0 (f46 f47 ?v0))) (= (f43 ?v_0 (f43 (f46 f47 ?v1) ?v2)) (f43 (f46 f47 (f43 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S37) (?v1 S37) (?v2 S37)) (let ((?v_0 (f51 f52 ?v0))) (= (f48 ?v_0 (f48 (f51 f52 ?v1) ?v2)) (f48 (f51 f52 (f48 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (= (f17 (f23 f24 (f17 ?v_0 ?v1)) ?v2) (f17 ?v_0 (f17 (f23 f24 ?v1) ?v2))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f31 f32 ?v0))) (= (f25 (f31 f32 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f31 f32 ?v1) ?v2))))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (let ((?v_0 (f46 f47 ?v0))) (= (f43 (f46 f47 (f43 ?v_0 ?v1)) ?v2) (f43 ?v_0 (f43 (f46 f47 ?v1) ?v2))))))
(assert (forall ((?v0 S37) (?v1 S37) (?v2 S37)) (let ((?v_0 (f51 f52 ?v0))) (= (f48 (f51 f52 (f48 ?v_0 ?v1)) ?v2) (f48 ?v_0 (f48 (f51 f52 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f13 ?v0))) (= (f3 (f12 f13 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f12 f13 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (= (f17 (f23 f24 (f17 ?v_0 ?v1)) ?v2) (f17 ?v_0 (f17 (f23 f24 ?v1) ?v2))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f31 f32 ?v0))) (= (f25 (f31 f32 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f31 f32 ?v1) ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f39 f40 ?v0))) (= (f33 (f39 f40 (f33 ?v_0 ?v1)) ?v2) (f33 ?v_0 (f33 (f39 f40 ?v1) ?v2))))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (let ((?v_0 (f46 f47 ?v0))) (= (f43 (f46 f47 (f43 ?v_0 ?v1)) ?v2) (f43 ?v_0 (f43 (f46 f47 ?v1) ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f15 f16 ?v0))) (= (f14 (f15 f16 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f16 ?v1) ?v2))))))
(assert (forall ((?v0 S37) (?v1 S37) (?v2 S37)) (let ((?v_0 (f51 f52 ?v0))) (= (f48 (f51 f52 (f48 ?v_0 ?v1)) ?v2) (f48 ?v_0 (f48 (f51 f52 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (= (f17 (f23 f24 (f17 ?v_0 ?v1)) ?v2) (f17 (f23 f24 (f17 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f31 f32 ?v0))) (= (f25 (f31 f32 (f25 ?v_0 ?v1)) ?v2) (f25 (f31 f32 (f25 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (let ((?v_0 (f46 f47 ?v0))) (= (f43 (f46 f47 (f43 ?v_0 ?v1)) ?v2) (f43 (f46 f47 (f43 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S37) (?v1 S37) (?v2 S37)) (let ((?v_0 (f51 f52 ?v0))) (= (f48 (f51 f52 (f48 ?v_0 ?v1)) ?v2) (f48 (f51 f52 (f48 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (= (= (f17 ?v_0 ?v1) (f17 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f31 f32 ?v0))) (= (= (f25 ?v_0 ?v1) (f25 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (let ((?v_0 (f46 f47 ?v0))) (= (= (f43 ?v_0 ?v1) (f43 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S37) (?v1 S37) (?v2 S37)) (let ((?v_0 (f51 f52 ?v0))) (= (= (f48 ?v_0 ?v1) (f48 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (= (= (f17 (f23 f24 ?v0) ?v1) (f17 (f23 f24 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (= (= (f25 (f31 f32 ?v0) ?v1) (f25 (f31 f32 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (= (= (f43 (f46 f47 ?v0) ?v1) (f43 (f46 f47 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S37) (?v1 S37) (?v2 S37)) (= (= (f48 (f51 f52 ?v0) ?v1) (f48 (f51 f52 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (let ((?v_0 (f23 f24 ?v0))) (= (f17 (f23 f24 (f17 ?v_0 ?v1)) (f17 (f23 f24 ?v2) ?v3)) (f17 (f23 f24 (f17 ?v_0 ?v2)) (f17 (f23 f24 ?v1) ?v3))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19) (?v3 S19)) (let ((?v_0 (f31 f32 ?v0))) (= (f25 (f31 f32 (f25 ?v_0 ?v1)) (f25 (f31 f32 ?v2) ?v3)) (f25 (f31 f32 (f25 ?v_0 ?v2)) (f25 (f31 f32 ?v1) ?v3))))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33) (?v3 S33)) (let ((?v_0 (f46 f47 ?v0))) (= (f43 (f46 f47 (f43 ?v_0 ?v1)) (f43 (f46 f47 ?v2) ?v3)) (f43 (f46 f47 (f43 ?v_0 ?v2)) (f43 (f46 f47 ?v1) ?v3))))))
(assert (forall ((?v0 S37) (?v1 S37) (?v2 S37) (?v3 S37)) (let ((?v_0 (f51 f52 ?v0))) (= (f48 (f51 f52 (f48 ?v_0 ?v1)) (f48 (f51 f52 ?v2) ?v3)) (f48 (f51 f52 (f48 ?v_0 ?v2)) (f48 (f51 f52 ?v1) ?v3))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (=> (= (f17 ?v_0 ?v1) (f17 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f31 f32 ?v0))) (=> (= (f25 ?v_0 ?v1) (f25 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (let ((?v_0 (f46 f47 ?v0))) (=> (= (f43 ?v_0 ?v1) (f43 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S37) (?v1 S37) (?v2 S37)) (let ((?v_0 (f51 f52 ?v0))) (=> (= (f48 ?v_0 ?v1) (f48 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= (f17 (f23 f24 ?v0) ?v1) (f17 (f23 f24 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (=> (= (f25 (f31 f32 ?v0) ?v1) (f25 (f31 f32 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (=> (= (f43 (f46 f47 ?v0) ?v1) (f43 (f46 f47 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S37) (?v1 S37) (?v2 S37)) (=> (= (f48 (f51 f52 ?v0) ?v1) (f48 (f51 f52 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 f24 ?v0))) (=> (= (f17 ?v_0 ?v1) (f17 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f31 f32 ?v0))) (=> (= (f25 ?v_0 ?v1) (f25 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (let ((?v_0 (f46 f47 ?v0))) (=> (= (f43 ?v_0 ?v1) (f43 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S37) (?v1 S37) (?v2 S37)) (let ((?v_0 (f51 f52 ?v0))) (=> (= (f48 ?v_0 ?v1) (f48 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3)) (= (f3 (f4 f5 (f14 (f15 f53 ?v0) ?v1)) ?v2) (f3 (f4 f5 ?v0) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (= (f17 (f18 f19 (f20 (f21 f54 ?v0) ?v1)) ?v2) (f17 (f18 f19 ?v0) (f17 (f18 f19 ?v1) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S19)) (= (f25 (f26 f27 (f28 (f29 f55 ?v0) ?v1)) ?v2) (f25 (f26 f27 ?v0) (f25 (f26 f27 ?v1) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S5)) (= (f14 (f41 f42 (f33 (f39 f56 ?v0) ?v1)) ?v2) (f14 (f41 f42 ?v0) (f14 (f41 f42 ?v1) ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S33)) (= (f43 (f44 f45 (f25 (f31 f57 ?v0) ?v1)) ?v2) (f43 (f44 f45 ?v0) (f43 (f44 f45 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S37)) (= (f48 (f49 f50 (f17 (f23 f58 ?v0) ?v1)) ?v2) (f48 (f49 f50 ?v0) (f48 (f49 f50 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S33) (?v2 S3)) (= (f14 (f15 f16 (f59 (f60 f61 ?v0) ?v1)) (f59 (f60 f61 ?v2) ?v1)) (f59 (f60 f61 (f3 (f12 f13 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S19) (?v1 S33) (?v2 S19)) (= (f28 (f29 f30 (f62 (f63 f64 ?v0) ?v1)) (f62 (f63 f64 ?v2) ?v1)) (f62 (f63 f64 (f25 (f31 f32 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S12) (?v1 S33) (?v2 S12)) (= (f20 (f21 f22 (f65 (f66 f67 ?v0) ?v1)) (f65 (f66 f67 ?v2) ?v1)) (f65 (f66 f67 (f17 (f23 f24 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S26) (?v1 S33) (?v2 S26)) (= (f36 (f37 f38 (f68 (f69 f70 ?v0) ?v1)) (f68 (f69 f70 ?v2) ?v1)) (f68 (f69 f70 (f33 (f39 f40 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S5) (?v1 S33) (?v2 S5)) (= (f33 (f39 f40 (f71 (f72 f73 ?v0) ?v1)) (f71 (f72 f73 ?v2) ?v1)) (f71 (f72 f73 (f14 (f15 f16 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S37) (?v1 S33) (?v2 S37)) (= (f17 (f23 f24 (f74 (f75 f76 ?v0) ?v1)) (f74 (f75 f76 ?v2) ?v1)) (f74 (f75 f76 (f48 (f51 f52 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (= (f25 (f31 f32 (f77 (f78 f79 ?v0) ?v1)) (f77 (f78 f79 ?v2) ?v1)) (f77 (f78 f79 (f43 (f46 f47 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f80 ?v0) f1) (=> (= (f80 ?v1) f1) (= (f80 (f17 (f23 f24 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S5)) (= (f14 (f81 f82 (f3 (f12 f13 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f14 (f81 f82 ?v0) ?v2)) (f14 (f81 f82 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S11)) (= (f20 (f83 f84 (f17 (f23 f24 ?v0) ?v1)) ?v2) (f20 (f21 f22 (f20 (f83 f84 ?v0) ?v2)) (f20 (f83 f84 ?v1) ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S18)) (= (f28 (f85 f86 (f25 (f31 f32 ?v0) ?v1)) ?v2) (f28 (f29 f30 (f28 (f85 f86 ?v0) ?v2)) (f28 (f85 f86 ?v1) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S25)) (= (f36 (f87 f88 (f33 (f39 f40 ?v0) ?v1)) ?v2) (f36 (f37 f38 (f36 (f87 f88 ?v0) ?v2)) (f36 (f87 f88 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S26)) (= (f33 (f89 f90 (f14 (f15 f16 ?v0) ?v1)) ?v2) (f33 (f39 f40 (f33 (f89 f90 ?v0) ?v2)) (f33 (f89 f90 ?v1) ?v2)))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S19)) (= (f25 (f91 f92 (f43 (f46 f47 ?v0) ?v1)) ?v2) (f25 (f31 f32 (f25 (f91 f92 ?v0) ?v2)) (f25 (f91 f92 ?v1) ?v2)))))
(assert (forall ((?v0 S37) (?v1 S37) (?v2 S12)) (= (f17 (f93 f94 (f48 (f51 f52 ?v0) ?v1)) ?v2) (f17 (f23 f24 (f17 (f93 f94 ?v0) ?v2)) (f17 (f93 f94 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S33)) (= (f95 (f96 f97 (f14 (f15 f16 ?v0) ?v1)) ?v2) (f3 (f12 f13 (f95 (f96 f97 ?v0) ?v2)) (f95 (f96 f97 ?v1) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S33)) (= (f77 (f98 f99 (f28 (f29 f30 ?v0) ?v1)) ?v2) (f25 (f31 f32 (f77 (f98 f99 ?v0) ?v2)) (f77 (f98 f99 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S33)) (= (f74 (f100 f101 (f20 (f21 f22 ?v0) ?v1)) ?v2) (f17 (f23 f24 (f74 (f100 f101 ?v0) ?v2)) (f74 (f100 f101 ?v1) ?v2)))))
(assert (forall ((?v0 S25) (?v1 S25) (?v2 S33)) (= (f71 (f102 f103 (f36 (f37 f38 ?v0) ?v1)) ?v2) (f33 (f39 f40 (f71 (f102 f103 ?v0) ?v2)) (f71 (f102 f103 ?v1) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S33)) (= (f59 (f104 f105 (f33 (f39 f40 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f59 (f104 f105 ?v0) ?v2)) (f59 (f104 f105 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S33)) (= (f106 (f107 f108 (f17 (f23 f24 ?v0) ?v1)) ?v2) (f48 (f51 f52 (f106 (f107 f108 ?v0) ?v2)) (f106 (f107 f108 ?v1) ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S33)) (= (f43 (f44 f109 (f25 (f31 f32 ?v0) ?v1)) ?v2) (f43 (f46 f47 (f43 (f44 f109 ?v0) ?v2)) (f43 (f44 f109 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S5) (?v2 S3) (?v3 S5)) (= (f14 (f15 f16 (f14 (f81 f110 ?v0) ?v1)) (f14 (f81 f110 ?v2) ?v3)) (f14 (f81 f110 (f3 (f12 f13 ?v0) ?v2)) (f14 (f15 f16 ?v1) ?v3)))))
(assert (forall ((?v0 S19) (?v1 S18) (?v2 S19) (?v3 S18)) (= (f28 (f29 f30 (f28 (f85 f111 ?v0) ?v1)) (f28 (f85 f111 ?v2) ?v3)) (f28 (f85 f111 (f25 (f31 f32 ?v0) ?v2)) (f28 (f29 f30 ?v1) ?v3)))))
(assert (forall ((?v0 S12) (?v1 S11) (?v2 S12) (?v3 S11)) (= (f20 (f21 f22 (f20 (f83 f112 ?v0) ?v1)) (f20 (f83 f112 ?v2) ?v3)) (f20 (f83 f112 (f17 (f23 f24 ?v0) ?v2)) (f20 (f21 f22 ?v1) ?v3)))))
(assert (forall ((?v0 S26) (?v1 S25) (?v2 S26) (?v3 S25)) (= (f36 (f37 f38 (f36 (f87 f113 ?v0) ?v1)) (f36 (f87 f113 ?v2) ?v3)) (f36 (f87 f113 (f33 (f39 f40 ?v0) ?v2)) (f36 (f37 f38 ?v1) ?v3)))))
(assert (forall ((?v0 S5) (?v1 S26) (?v2 S5) (?v3 S26)) (= (f33 (f39 f40 (f33 (f89 f114 ?v0) ?v1)) (f33 (f89 f114 ?v2) ?v3)) (f33 (f89 f114 (f14 (f15 f16 ?v0) ?v2)) (f33 (f39 f40 ?v1) ?v3)))))
(assert (forall ((?v0 S37) (?v1 S12) (?v2 S37) (?v3 S12)) (= (f17 (f23 f24 (f17 (f93 f115 ?v0) ?v1)) (f17 (f93 f115 ?v2) ?v3)) (f17 (f93 f115 (f48 (f51 f52 ?v0) ?v2)) (f17 (f23 f24 ?v1) ?v3)))))
(assert (forall ((?v0 S33) (?v1 S19) (?v2 S33) (?v3 S19)) (= (f25 (f31 f32 (f25 (f91 f116 ?v0) ?v1)) (f25 (f91 f116 ?v2) ?v3)) (f25 (f91 f116 (f43 (f46 f47 ?v0) ?v2)) (f25 (f31 f32 ?v1) ?v3)))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 f117) ?v0) f117)))
(assert (forall ((?v0 S19)) (= (f118 (f119 f120 f121) ?v0) f121)))
(assert (forall ((?v0 S12)) (= (f122 (f123 f124 f125) ?v0) f125)))
(assert (forall ((?v0 S5)) (= (f126 (f127 f128 f129) ?v0) f129)))
(assert (forall ((?v0 S37)) (= (f130 (f131 f132 f133) ?v0) f133)))
(assert (forall ((?v0 S33)) (= (f77 (f134 f135 f136) ?v0) f136)))
(assert (forall ((?v0 S26)) (= (f33 (f39 f40 f129) ?v0) ?v0)))
(assert (forall ((?v0 S18)) (= (f28 (f29 f30 f121) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f20 (f21 f22 f125) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f17 (f23 f24 f133) ?v0) ?v0)))
(assert (forall ((?v0 S19)) (= (f25 (f31 f32 f136) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (f14 (f15 f16 f117) ?v0) ?v0)))
(assert (forall ((?v0 S26)) (= (f33 (f39 f40 ?v0) f129) ?v0)))
(assert (forall ((?v0 S18)) (= (f28 (f29 f30 ?v0) f121) ?v0)))
(assert (forall ((?v0 S11)) (= (f20 (f21 f22 ?v0) f125) ?v0)))
(assert (forall ((?v0 S12)) (= (f17 (f23 f24 ?v0) f133) ?v0)))
(assert (forall ((?v0 S19)) (= (f25 (f31 f32 ?v0) f136) ?v0)))
(assert (forall ((?v0 S5)) (= (f14 (f15 f16 ?v0) f117) ?v0)))
(assert (not (= (f137 f125) f1)))
(assert (not (= (f80 f133) f1)))
(assert (= (f25 (f91 f116 f138) f136) f136))
(assert (= (f17 (f93 f115 f139) f133) f133))
(assert (= (f140 f121 f141) f141))
(assert (= (f142 f125 f143) f143))
(assert (= (f36 (f87 f113 f129) f144) f144))
(assert (= (f33 (f89 f114 f117) f129) f129))
(assert (= (f20 (f83 f112 f133) f125) f125))
(assert (= (f28 (f85 f111 f136) f121) f121))
(assert (= (f14 (f81 f110 f145) f117) f117))
(assert (forall ((?v0 S33)) (= (f106 (f107 f108 f133) ?v0) f139)))
(assert (forall ((?v0 S33)) (= (f43 (f44 f109 f136) ?v0) f138)))
(assert (forall ((?v0 S33)) (= (f65 (f146 f147 f143) ?v0) f125)))
(assert (forall ((?v0 S33)) (= (f71 (f102 f103 f144) ?v0) f129)))
(assert (forall ((?v0 S33)) (= (f59 (f104 f105 f129) ?v0) f117)))
(assert (forall ((?v0 S33)) (= (f74 (f100 f101 f125) ?v0) f133)))
(assert (forall ((?v0 S33)) (= (f77 (f98 f99 f121) ?v0) f136)))
(assert (forall ((?v0 S33)) (= (f95 (f96 f97 f117) ?v0) f145)))
(assert (forall ((?v0 S33)) (= (f59 (f60 f61 f145) ?v0) f117)))
(assert (forall ((?v0 S33)) (= (f62 (f63 f64 f136) ?v0) f121)))
(assert (forall ((?v0 S33)) (= (f65 (f66 f67 f133) ?v0) f125)))
(assert (forall ((?v0 S33)) (= (f71 (f72 f73 f117) ?v0) f129)))
(assert (forall ((?v0 S33)) (= (f74 (f75 f76 f139) ?v0) f133)))
(assert (forall ((?v0 S33)) (= (f77 (f78 f79 f138) ?v0) f136)))
(assert (forall ((?v0 S5)) (= (f14 (f81 f82 f145) ?v0) f117)))
(assert (forall ((?v0 S18)) (= (f28 (f85 f86 f136) ?v0) f121)))
(assert (forall ((?v0 S11)) (= (f20 (f83 f84 f133) ?v0) f125)))
(assert (forall ((?v0 S26)) (= (f33 (f89 f90 f117) ?v0) f129)))
(assert (forall ((?v0 S12)) (= (f17 (f93 f94 f139) ?v0) f133)))
(assert (forall ((?v0 S19)) (= (f25 (f91 f92 f138) ?v0) f136)))
(assert (forall ((?v0 S5)) (= (f14 (f15 f53 f117) ?v0) f117)))
(assert (forall ((?v0 S19)) (= (f25 (f31 f57 f136) ?v0) f136)))
(assert (forall ((?v0 S12)) (= (f17 (f23 f58 f133) ?v0) f133)))
(assert (forall ((?v0 S19)) (= (= f136 ?v0) (= ?v0 f136))))
(assert (forall ((?v0 S12)) (= (= f133 ?v0) (= ?v0 f133))))
(assert (forall ((?v0 S3)) (= (= f145 ?v0) (= ?v0 f145))))
(assert (forall ((?v0 S5)) (= (= f117 ?v0) (= ?v0 f117))))
(assert (forall ((?v0 S37)) (= (= f139 ?v0) (= ?v0 f139))))
(assert (forall ((?v0 S33)) (= (= f138 ?v0) (= ?v0 f138))))
(assert (forall ((?v0 S3)) (= (f14 (f81 f82 ?v0) f117) f117)))
(assert (forall ((?v0 S37)) (= (f17 (f93 f94 ?v0) f133) f133)))
(assert (forall ((?v0 S33)) (= (f25 (f91 f92 ?v0) f136) f136)))
(assert (forall ((?v0 S19) (?v1 S19)) (= (= ?v0 ?v1) (forall ((?v2 S33)) (= (f43 (f44 f109 ?v0) ?v2) (f43 (f44 f109 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= ?v0 ?v1) (forall ((?v2 S33)) (= (f106 (f107 f108 ?v0) ?v2) (f106 (f107 f108 ?v1) ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= ?v0 ?v1) (forall ((?v2 S33)) (= (f95 (f96 f97 ?v0) ?v2) (f95 (f96 f97 ?v1) ?v2))))))
(assert (forall ((?v0 S19) (?v1 S19)) (= (= (f44 f109 ?v0) (f44 f109 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f107 f108 ?v0) (f107 f108 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f96 f97 ?v0) (f96 f97 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S33)) (= (= (f59 (f60 f61 ?v0) ?v1) f117) (= ?v0 f145))))
(assert (forall ((?v0 S19) (?v1 S33)) (= (= (f62 (f63 f64 ?v0) ?v1) f121) (= ?v0 f136))))
(assert (forall ((?v0 S12) (?v1 S33)) (= (= (f65 (f66 f67 ?v0) ?v1) f125) (= ?v0 f133))))
(assert (forall ((?v0 S5) (?v1 S33)) (= (= (f71 (f72 f73 ?v0) ?v1) f129) (= ?v0 f117))))
(assert (forall ((?v0 S37) (?v1 S33)) (= (= (f74 (f75 f76 ?v0) ?v1) f133) (= ?v0 f139))))
(assert (forall ((?v0 S33) (?v1 S33)) (= (= (f77 (f78 f79 ?v0) ?v1) f136) (= ?v0 f138))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f14 (f81 f110 ?v0) ?v1) f117) (and (= ?v0 f145) (= ?v1 f117)))))
(assert (forall ((?v0 S19) (?v1 S18)) (= (= (f28 (f85 f111 ?v0) ?v1) f121) (and (= ?v0 f136) (= ?v1 f121)))))
(assert (forall ((?v0 S12) (?v1 S11)) (= (= (f20 (f83 f112 ?v0) ?v1) f125) (and (= ?v0 f133) (= ?v1 f125)))))
(assert (forall ((?v0 S5) (?v1 S26)) (= (= (f33 (f89 f114 ?v0) ?v1) f129) (and (= ?v0 f117) (= ?v1 f129)))))
(assert (forall ((?v0 S37) (?v1 S12)) (= (= (f17 (f93 f115 ?v0) ?v1) f133) (and (= ?v0 f139) (= ?v1 f133)))))
(assert (forall ((?v0 S33) (?v1 S19)) (= (= (f25 (f91 f116 ?v0) ?v1) f136) (and (= ?v0 f138) (= ?v1 f136)))))
(assert (forall ((?v0 S12) (?v1 S11)) (= (= (f20 (f83 f84 ?v0) ?v1) f125) (or (= ?v0 f133) (= ?v1 f125)))))
(assert (forall ((?v0 S37) (?v1 S12)) (= (= (f17 (f93 f94 ?v0) ?v1) f133) (or (= ?v0 f139) (= ?v1 f133)))))
(assert (forall ((?v0 S3) (?v1 S33) (?v2 S33)) (= (f95 (f96 f97 (f59 (f60 f61 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f145))))
(assert (forall ((?v0 S19) (?v1 S33) (?v2 S33)) (= (f77 (f98 f99 (f62 (f63 f64 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f136))))
(assert (forall ((?v0 S12) (?v1 S33) (?v2 S33)) (= (f74 (f100 f101 (f65 (f66 f67 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f133))))
(assert (forall ((?v0 S5) (?v1 S33) (?v2 S33)) (= (f59 (f104 f105 (f71 (f72 f73 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f117))))
(assert (forall ((?v0 S37) (?v1 S33) (?v2 S33)) (= (f106 (f107 f108 (f74 (f75 f76 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f139))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (= (f43 (f44 f109 (f77 (f78 f79 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f138))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33)) (= (= (f77 (f78 f79 ?v0) ?v1) (f77 (f78 f79 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S37) (?v1 S33) (?v2 S37)) (= (= (f74 (f75 f76 ?v0) ?v1) (f74 (f75 f76 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S3) (?v1 S33) (?v2 S3)) (= (= (f59 (f60 f61 ?v0) ?v1) (f59 (f60 f61 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S33) (?v1 S19) (?v2 S33) (?v3 S19)) (= (= (f25 (f91 f116 ?v0) ?v1) (f25 (f91 f116 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S37) (?v1 S12) (?v2 S37) (?v3 S12)) (= (= (f17 (f93 f115 ?v0) ?v1) (f17 (f93 f115 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S5) (?v2 S3) (?v3 S5)) (= (= (f14 (f81 f110 ?v0) ?v1) (f14 (f81 f110 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S33) (?v1 S19) (?v2 S33)) (=> (= (f25 (f91 f92 ?v0) ?v1) (f25 (f91 f116 ?v2) ?v1)) (= ?v1 f136))))
(assert (forall ((?v0 S37) (?v1 S12) (?v2 S37)) (=> (= (f17 (f93 f94 ?v0) ?v1) (f17 (f93 f115 ?v2) ?v1)) (= ?v1 f133))))
(assert (forall ((?v0 S3) (?v1 S5) (?v2 S3)) (=> (= (f14 (f81 f82 ?v0) ?v1) (f14 (f81 f110 ?v2) ?v1)) (= ?v1 f117))))
(assert (forall ((?v0 S19)) (= (f25 (f26 f27 f121) ?v0) f136)))
(assert (forall ((?v0 S12)) (= (f17 (f18 f19 f125) ?v0) f133)))
(assert (forall ((?v0 S5)) (= (f14 (f41 f42 f129) ?v0) f117)))
(assert (forall ((?v0 S37)) (= (f48 (f49 f50 f133) ?v0) f139)))
(assert (forall ((?v0 S33)) (= (f43 (f44 f45 f136) ?v0) f138)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f117) ?v0) f145)))
(assert (forall ((?v0 S33) (?v1 S33)) (let ((?v_0 (f25 (f91 f116 ?v0) f136))) (= (f77 (f134 f135 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S37) (?v1 S37)) (let ((?v_0 (f17 (f93 f115 ?v0) f133))) (= (f130 (f131 f132 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f14 (f81 f110 ?v0) f117))) (= (f6 (f7 f8 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S5)) (= (f14 (f15 f16 f117) ?v0) ?v0)))
(assert (forall ((?v0 S19)) (= (f25 (f31 f32 f136) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f17 (f23 f24 f133) ?v0) ?v0)))
(assert (forall ((?v0 S37)) (= (f48 (f51 f52 f139) ?v0) ?v0)))
(assert (forall ((?v0 S33)) (= (f43 (f46 f47 f138) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f12 f13 f145) ?v0) ?v0)))
(assert (forall ((?v0 S19)) (= (f25 (f31 f32 f136) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f17 (f23 f24 f133) ?v0) ?v0)))
(assert (forall ((?v0 S37)) (= (f48 (f51 f52 f139) ?v0) ?v0)))
(assert (forall ((?v0 S33)) (= (f43 (f46 f47 f138) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (f14 (f15 f16 f117) ?v0) ?v0)))
(assert (forall ((?v0 S19)) (= (f25 (f31 f32 f136) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f17 (f23 f24 f133) ?v0) ?v0)))
(assert (forall ((?v0 S37)) (= (f48 (f51 f52 f139) ?v0) ?v0)))
(assert (forall ((?v0 S33)) (= (f43 (f46 f47 f138) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f12 f13 f145) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (= f133 (f17 (f23 f24 ?v0) ?v0)) (= ?v0 f133))))
(assert (forall ((?v0 S37)) (= (= f139 (f48 (f51 f52 ?v0) ?v0)) (= ?v0 f139))))
(assert (forall ((?v0 S5)) (= (f14 (f15 f16 ?v0) f117) ?v0)))
(assert (forall ((?v0 S19)) (= (f25 (f31 f32 ?v0) f136) ?v0)))
(assert (forall ((?v0 S12)) (= (f17 (f23 f24 ?v0) f133) ?v0)))
(assert (forall ((?v0 S37)) (= (f48 (f51 f52 ?v0) f139) ?v0)))
(assert (forall ((?v0 S33)) (= (f43 (f46 f47 ?v0) f138) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f12 f13 ?v0) f145) ?v0)))
(assert (forall ((?v0 S19)) (= (f25 (f31 f32 ?v0) f136) ?v0)))
(assert (forall ((?v0 S12)) (= (f17 (f23 f24 ?v0) f133) ?v0)))
(assert (forall ((?v0 S37)) (= (f48 (f51 f52 ?v0) f139) ?v0)))
(assert (forall ((?v0 S33)) (= (f43 (f46 f47 ?v0) f138) ?v0)))
(assert (forall ((?v0 S5)) (= (f14 (f15 f16 ?v0) f117) ?v0)))
(assert (forall ((?v0 S19)) (= (f25 (f31 f32 ?v0) f136) ?v0)))
(assert (forall ((?v0 S12)) (= (f17 (f23 f24 ?v0) f133) ?v0)))
(assert (forall ((?v0 S37)) (= (f48 (f51 f52 ?v0) f139) ?v0)))
(assert (forall ((?v0 S33)) (= (f43 (f46 f47 ?v0) f138) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f12 f13 ?v0) f145) ?v0)))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= ?v0 (f17 (f23 f24 ?v0) ?v1)) (= ?v1 f133))))
(assert (forall ((?v0 S37) (?v1 S37)) (= (= ?v0 (f48 (f51 f52 ?v0) ?v1)) (= ?v1 f139))))
(assert (forall ((?v0 S33) (?v1 S33)) (= (= ?v0 (f43 (f46 f47 ?v0) ?v1)) (= ?v1 f138))))
(assert (forall ((?v0 S33) (?v1 S19) (?v2 S33)) (let ((?v_0 (f91 f116 ?v0)) (?v_1 (f77 (f134 f135 ?v1) ?v2))) (= (f77 (f134 f135 (f25 ?v_0 ?v1)) ?v2) (f25 (f31 f32 (f25 (f91 f92 ?v2) ?v_1)) (f25 ?v_0 ?v_1))))))
(assert (forall ((?v0 S37) (?v1 S12) (?v2 S37)) (let ((?v_0 (f93 f115 ?v0)) (?v_1 (f130 (f131 f132 ?v1) ?v2))) (= (f130 (f131 f132 (f17 ?v_0 ?v1)) ?v2) (f17 (f23 f24 (f17 (f93 f94 ?v2) ?v_1)) (f17 ?v_0 ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S5) (?v2 S3)) (let ((?v_0 (f81 f110 ?v0)) (?v_1 (f6 (f7 f8 ?v1) ?v2))) (= (f6 (f7 f8 (f14 ?v_0 ?v1)) ?v2) (f14 (f15 f16 (f14 (f81 f82 ?v2) ?v_1)) (f14 ?v_0 ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S5) (?v2 S5)) (let ((?v_0 (f81 f82 ?v0))) (= (f14 ?v_0 (f14 (f15 f16 ?v1) ?v2)) (f14 (f15 f16 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2))))))
(assert (forall ((?v0 S37) (?v1 S12) (?v2 S12)) (let ((?v_0 (f93 f94 ?v0))) (= (f17 ?v_0 (f17 (f23 f24 ?v1) ?v2)) (f17 (f23 f24 (f17 ?v_0 ?v1)) (f17 ?v_0 ?v2))))))
(assert (forall ((?v0 S33) (?v1 S19) (?v2 S19)) (let ((?v_0 (f91 f92 ?v0))) (= (f25 ?v_0 (f25 (f31 f32 ?v1) ?v2)) (f25 (f31 f32 (f25 ?v_0 ?v1)) (f25 ?v_0 ?v2))))))
(assert (forall ((?v0 S12)) (= (= (f49 f50 ?v0) (f49 f50 f133)) (= ?v0 f133))))
(assert (forall ((?v0 S82) (?v1 S19)) (=> (= (f148 ?v0 f136) f1) (=> (forall ((?v2 S33) (?v3 S19)) (=> (= (f148 ?v0 ?v3) f1) (= (f148 ?v0 (f25 (f91 f116 ?v2) ?v3)) f1))) (= (f148 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S83) (?v1 S12)) (=> (= (f149 ?v0 f133) f1) (=> (forall ((?v2 S37) (?v3 S12)) (=> (= (f149 ?v0 ?v3) f1) (= (f149 ?v0 (f17 (f93 f115 ?v2) ?v3)) f1))) (= (f149 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S84) (?v1 S5)) (=> (= (f150 ?v0 f117) f1) (=> (forall ((?v2 S3) (?v3 S5)) (=> (= (f150 ?v0 ?v3) f1) (= (f150 ?v0 (f14 (f81 f110 ?v2) ?v3)) f1))) (= (f150 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S37) (?v2 S12) (?v3 S37)) (=> (= (f17 (f23 f24 ?v0) (f17 (f93 f94 ?v1) ?v2)) (f17 (f93 f115 ?v3) ?v2)) (and (= ?v3 (f48 (f49 f50 ?v0) ?v1)) (= ?v2 (f130 (f131 f151 ?v0) ?v1))))))
(assert (forall ((?v0 S19) (?v1 S33) (?v2 S19) (?v3 S33)) (=> (= (f25 (f31 f32 ?v0) (f25 (f91 f92 ?v1) ?v2)) (f25 (f91 f116 ?v3) ?v2)) (and (= ?v3 (f43 (f44 f45 ?v0) ?v1)) (= ?v2 (f77 (f134 f152 ?v0) ?v1))))))
(assert (forall ((?v0 S5) (?v1 S3) (?v2 S5) (?v3 S3)) (=> (= (f14 (f15 f16 ?v0) (f14 (f81 f82 ?v1) ?v2)) (f14 (f81 f110 ?v3) ?v2)) (and (= ?v3 (f3 (f4 f5 ?v0) ?v1)) (= ?v2 (f6 (f7 f153 ?v0) ?v1))))))
(assert (forall ((?v0 S12) (?v1 S37)) (let ((?v_0 (f130 (f131 f151 ?v0) ?v1))) (= (f17 (f23 f24 ?v0) (f17 (f93 f94 ?v1) ?v_0)) (f17 (f93 f115 (f48 (f49 f50 ?v0) ?v1)) ?v_0)))))
(assert (forall ((?v0 S19) (?v1 S33)) (let ((?v_0 (f77 (f134 f152 ?v0) ?v1))) (= (f25 (f31 f32 ?v0) (f25 (f91 f92 ?v1) ?v_0)) (f25 (f91 f116 (f43 (f44 f45 ?v0) ?v1)) ?v_0)))))
(assert (forall ((?v0 S5) (?v1 S3)) (let ((?v_0 (f6 (f7 f153 ?v0) ?v1))) (= (f14 (f15 f16 ?v0) (f14 (f81 f82 ?v1) ?v_0)) (f14 (f81 f110 (f3 (f4 f5 ?v0) ?v1)) ?v_0)))))
(assert (forall ((?v0 S11) (?v1 S12)) (= (= (f17 (f18 f19 ?v0) ?v1) f133) (or (= ?v0 f125) (not (= (f154 (f155 f156 ?v1) ?v0) f138))))))
(assert (forall ((?v0 S12) (?v1 S37)) (= (= (f48 (f49 f50 ?v0) ?v1) f139) (or (= ?v0 f133) (not (= (f157 (f158 f159 ?v1) ?v0) f138))))))
(assert (forall ((?v0 S12)) (= (= (f17 (f23 f24 ?v0) ?v0) f133) (= ?v0 f133))))
(assert (forall ((?v0 S37)) (= (= (f48 (f51 f52 ?v0) ?v0) f139) (= ?v0 f139))))
(assert (forall ((?v0 S19) (?v1 S19)) (=> (forall ((?v2 S33)) (= (f43 (f44 f109 ?v0) ?v2) (f43 (f44 f109 ?v1) ?v2))) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (forall ((?v2 S33)) (= (f106 (f107 f108 ?v0) ?v2) (f106 (f107 f108 ?v1) ?v2))) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (forall ((?v2 S33)) (= (f95 (f96 f97 ?v0) ?v2) (f95 (f96 f97 ?v1) ?v2))) (= ?v0 ?v1))))
(assert (forall ((?v0 S19)) (=> (forall ((?v1 S33) (?v2 S19)) (=> (= ?v0 (f25 (f91 f116 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S12)) (=> (forall ((?v1 S37) (?v2 S12)) (=> (= ?v0 (f17 (f93 f115 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S5)) (=> (forall ((?v1 S3) (?v2 S5)) (=> (= ?v0 (f14 (f81 f110 ?v1) ?v2)) false)) false)))
(check-sat)
(exit)