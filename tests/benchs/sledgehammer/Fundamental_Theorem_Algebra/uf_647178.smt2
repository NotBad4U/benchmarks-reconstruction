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
(declare-sort S89 0)
(declare-sort S90 0)
(declare-sort S91 0)
(declare-sort S92 0)
(declare-sort S93 0)
(declare-sort S94 0)
(declare-sort S95 0)
(declare-sort S96 0)
(declare-sort S97 0)
(declare-sort S98 0)
(declare-sort S99 0)
(declare-sort S100 0)
(declare-sort S101 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () S2)
(declare-fun f4 () S2)
(declare-fun f5 (S3 S4) S2)
(declare-fun f6 (S5 S2) S3)
(declare-fun f7 () S5)
(declare-fun f8 () S4)
(declare-fun f9 (S7 S6) S8)
(declare-fun f10 (S9 S8) S7)
(declare-fun f11 () S9)
(declare-fun f12 () S8)
(declare-fun f13 (S11 S10) S12)
(declare-fun f14 (S13 S12) S11)
(declare-fun f15 () S13)
(declare-fun f16 () S12)
(declare-fun f17 (S15 S14) S16)
(declare-fun f18 (S17 S16) S15)
(declare-fun f19 () S17)
(declare-fun f20 () S16)
(declare-fun f21 (S18 S2) S14)
(declare-fun f22 (S19 S14) S18)
(declare-fun f23 () S19)
(declare-fun f24 () S14)
(declare-fun f25 (S21 S20) S10)
(declare-fun f26 (S22 S10) S21)
(declare-fun f27 () S22)
(declare-fun f28 () S10)
(declare-fun f29 (S24 S23) S6)
(declare-fun f30 (S25 S6) S24)
(declare-fun f31 () S25)
(declare-fun f32 () S6)
(declare-fun f33 () S23)
(declare-fun f34 () S20)
(declare-fun f35 () S4)
(declare-fun f36 (S26 S2) S2)
(declare-fun f37 (S27 S4) S26)
(declare-fun f38 () S27)
(declare-fun f39 (S28 S8) S8)
(declare-fun f40 (S29 S6) S28)
(declare-fun f41 () S29)
(declare-fun f42 (S30 S12) S12)
(declare-fun f43 (S31 S10) S30)
(declare-fun f44 () S31)
(declare-fun f45 (S32 S16) S16)
(declare-fun f46 (S33 S14) S32)
(declare-fun f47 () S33)
(declare-fun f48 (S34 S14) S14)
(declare-fun f49 (S35 S2) S34)
(declare-fun f50 () S35)
(declare-fun f51 (S36 S10) S10)
(declare-fun f52 (S37 S20) S36)
(declare-fun f53 () S37)
(declare-fun f54 (S38 S6) S6)
(declare-fun f55 (S39 S23) S38)
(declare-fun f56 () S39)
(declare-fun f57 (S40 S23) S14)
(declare-fun f58 (S41 S2) S40)
(declare-fun f59 () S41)
(declare-fun f60 (S42 S23) S10)
(declare-fun f61 (S43 S20) S42)
(declare-fun f62 () S43)
(declare-fun f63 (S44 S23) S24)
(declare-fun f64 () S44)
(declare-fun f65 (S45 S23) S2)
(declare-fun f66 (S46 S4) S45)
(declare-fun f67 () S46)
(declare-fun f68 (S8 S23) S47)
(declare-fun f69 () S47)
(declare-fun f70 (S12 S23) S48)
(declare-fun f71 () S48)
(declare-fun f72 (S16 S23) S49)
(declare-fun f73 () S49)
(declare-fun f74 (S50 S23) S16)
(declare-fun f75 (S51 S14) S50)
(declare-fun f76 () S51)
(declare-fun f77 (S52 S23) S12)
(declare-fun f78 (S53 S10) S52)
(declare-fun f79 () S53)
(declare-fun f80 (S54 S23) S8)
(declare-fun f81 (S55 S6) S54)
(declare-fun f82 () S55)
(declare-fun f83 (S56 S8) S38)
(declare-fun f84 () S56)
(declare-fun f85 (S57 S12) S36)
(declare-fun f86 () S57)
(declare-fun f87 (S58 S16) S34)
(declare-fun f88 () S58)
(declare-fun f89 (S59 S4) S4)
(declare-fun f90 (S60 S2) S59)
(declare-fun f91 () S60)
(declare-fun f92 (S61 S14) S26)
(declare-fun f93 () S61)
(declare-fun f94 (S62 S20) S20)
(declare-fun f95 (S63 S10) S62)
(declare-fun f96 () S63)
(declare-fun f97 (S64 S23) S23)
(declare-fun f98 (S65 S6) S64)
(declare-fun f99 () S65)
(declare-fun f100 (S66 S8) S24)
(declare-fun f101 () S66)
(declare-fun f102 (S67 S12) S42)
(declare-fun f103 () S67)
(declare-fun f104 (S68 S16) S40)
(declare-fun f105 () S68)
(declare-fun f106 (S69 S23) S4)
(declare-fun f107 (S70 S2) S69)
(declare-fun f108 () S70)
(declare-fun f109 (S71 S14) S45)
(declare-fun f110 () S71)
(declare-fun f111 (S72 S23) S20)
(declare-fun f112 (S73 S10) S72)
(declare-fun f113 () S73)
(declare-fun f114 () S65)
(declare-fun f115 () S29)
(declare-fun f116 () S31)
(declare-fun f117 () S33)
(declare-fun f118 () S35)
(declare-fun f119 () S37)
(declare-fun f120 () S39)
(declare-fun f121 () S27)
(declare-fun f122 (S74 S6) S38)
(declare-fun f123 () S74)
(declare-fun f124 (S75 S10) S36)
(declare-fun f125 () S75)
(declare-fun f126 (S76 S14) S34)
(declare-fun f127 () S76)
(declare-fun f128 (S77 S2) S26)
(declare-fun f129 () S77)
(declare-fun f130 (S78 S6) S1)
(declare-fun f131 (S79 S10) S1)
(declare-fun f132 (S80 S14) S1)
(declare-fun f133 (S81 S2) S1)
(declare-fun f134 (S82 S12) S23)
(declare-fun f135 (S83 S10) S82)
(declare-fun f136 () S83)
(declare-fun f137 (S84 S10) S23)
(declare-fun f138 (S85 S20) S84)
(declare-fun f139 () S85)
(declare-fun f140 () S22)
(declare-fun f141 () S25)
(declare-fun f142 () S19)
(declare-fun f143 () S5)
(declare-fun f144 (S86 S64) S64)
(declare-fun f145 (S87 S23) S86)
(declare-fun f146 () S87)
(declare-fun f147 (S88 S72) S72)
(declare-fun f148 (S89 S20) S88)
(declare-fun f149 () S89)
(declare-fun f150 (S90 S45) S45)
(declare-fun f151 (S91 S2) S90)
(declare-fun f152 () S91)
(declare-fun f153 (S92 S69) S69)
(declare-fun f154 (S93 S4) S92)
(declare-fun f155 () S93)
(declare-fun f156 () S74)
(declare-fun f157 () S75)
(declare-fun f158 () S76)
(declare-fun f159 () S77)
(declare-fun f160 () S64)
(declare-fun f161 (S94 S8) S23)
(declare-fun f162 () S94)
(declare-fun f163 () S82)
(declare-fun f164 (S95 S16) S23)
(declare-fun f165 () S95)
(declare-fun f166 (S96 S2) S23)
(declare-fun f167 () S96)
(declare-fun f168 (S97 S14) S23)
(declare-fun f169 () S97)
(declare-fun f170 () S84)
(declare-fun f171 (S98 S6) S23)
(declare-fun f172 () S98)
(declare-fun f173 (S99 S23) S64)
(declare-fun f174 () S99)
(declare-fun f175 (S100 S20) S62)
(declare-fun f176 () S100)
(declare-fun f177 (S10) S79)
(declare-fun f178 (S101 S4) S59)
(declare-fun f179 () S101)
(declare-fun f180 (S6) S78)
(assert (not (= f1 f2)))
(assert (not (= f3 f4)))
(assert (= (f5 (f6 f7 f3) f8) f4))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 f4) ?v0) f4)))
(assert (forall ((?v0 S6)) (= (f9 (f10 f11 f12) ?v0) f12)))
(assert (forall ((?v0 S10)) (= (f13 (f14 f15 f16) ?v0) f16)))
(assert (forall ((?v0 S14)) (= (f17 (f18 f19 f20) ?v0) f20)))
(assert (forall ((?v0 S2)) (= (f21 (f22 f23 f24) ?v0) f24)))
(assert (forall ((?v0 S20)) (= (f25 (f26 f27 f28) ?v0) f28)))
(assert (forall ((?v0 S23)) (= (f29 (f30 f31 f32) ?v0) f32)))
(assert (forall ((?v0 S23)) (= (= f33 ?v0) (= ?v0 f33))))
(assert (forall ((?v0 S20)) (= (= f34 ?v0) (= ?v0 f34))))
(assert (forall ((?v0 S2)) (= (= f4 ?v0) (= ?v0 f4))))
(assert (forall ((?v0 S8)) (= (= f12 ?v0) (= ?v0 f12))))
(assert (forall ((?v0 S12)) (= (= f16 ?v0) (= ?v0 f16))))
(assert (forall ((?v0 S16)) (= (= f20 ?v0) (= ?v0 f20))))
(assert (forall ((?v0 S4)) (= (= f35 ?v0) (= ?v0 f35))))
(assert (forall ((?v0 S14)) (= (= f24 ?v0) (= ?v0 f24))))
(assert (forall ((?v0 S10)) (= (= f28 ?v0) (= ?v0 f28))))
(assert (forall ((?v0 S6)) (= (= f32 ?v0) (= ?v0 f32))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_0 (f36 (f37 f38 ?v0) f4))) (= (f5 (f6 f7 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f39 (f40 f41 ?v0) f12))) (= (f9 (f10 f11 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f42 (f43 f44 ?v0) f16))) (= (f13 (f14 f15 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S14) (?v1 S14)) (let ((?v_0 (f45 (f46 f47 ?v0) f20))) (= (f17 (f18 f19 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f48 (f49 f50 ?v0) f24))) (= (f21 (f22 f23 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S20) (?v1 S20)) (let ((?v_0 (f51 (f52 f53 ?v0) f28))) (= (f25 (f26 f27 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S23) (?v1 S23)) (let ((?v_0 (f54 (f55 f56 ?v0) f32))) (= (f29 (f30 f31 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S23)) (= (f57 (f58 f59 f4) ?v0) f24)))
(assert (forall ((?v0 S23)) (= (f60 (f61 f62 f34) ?v0) f28)))
(assert (forall ((?v0 S23)) (= (f29 (f63 f64 f33) ?v0) f32)))
(assert (forall ((?v0 S23)) (= (f65 (f66 f67 f35) ?v0) f4)))
(assert (forall ((?v0 S23)) (= (f68 f12 ?v0) f69)))
(assert (forall ((?v0 S23)) (= (f70 f16 ?v0) f71)))
(assert (forall ((?v0 S23)) (= (f72 f20 ?v0) f73)))
(assert (forall ((?v0 S23)) (= (f74 (f75 f76 f24) ?v0) f20)))
(assert (forall ((?v0 S23)) (= (f77 (f78 f79 f28) ?v0) f16)))
(assert (forall ((?v0 S23)) (= (f80 (f81 f82 f32) ?v0) f12)))
(assert (forall ((?v0 S6) (?v1 S23)) (= (= (f80 (f81 f82 ?v0) ?v1) f12) (= ?v0 f32))))
(assert (forall ((?v0 S10) (?v1 S23)) (= (= (f77 (f78 f79 ?v0) ?v1) f16) (= ?v0 f28))))
(assert (forall ((?v0 S14) (?v1 S23)) (= (= (f74 (f75 f76 ?v0) ?v1) f20) (= ?v0 f24))))
(assert (forall ((?v0 S4) (?v1 S23)) (= (= (f65 (f66 f67 ?v0) ?v1) f4) (= ?v0 f35))))
(assert (forall ((?v0 S2) (?v1 S23)) (= (= (f57 (f58 f59 ?v0) ?v1) f24) (= ?v0 f4))))
(assert (forall ((?v0 S20) (?v1 S23)) (= (= (f60 (f61 f62 ?v0) ?v1) f28) (= ?v0 f34))))
(assert (forall ((?v0 S23) (?v1 S23)) (= (= (f29 (f63 f64 ?v0) ?v1) f32) (= ?v0 f33))))
(assert (forall ((?v0 S6)) (= (f54 (f83 f84 f12) ?v0) f32)))
(assert (forall ((?v0 S10)) (= (f51 (f85 f86 f16) ?v0) f28)))
(assert (forall ((?v0 S14)) (= (f48 (f87 f88 f20) ?v0) f24)))
(assert (forall ((?v0 S4)) (= (f89 (f90 f91 f4) ?v0) f35)))
(assert (forall ((?v0 S2)) (= (f36 (f92 f93 f24) ?v0) f4)))
(assert (forall ((?v0 S20)) (= (f94 (f95 f96 f28) ?v0) f34)))
(assert (forall ((?v0 S23)) (= (f97 (f98 f99 f32) ?v0) f33)))
(assert (forall ((?v0 S23)) (= (f29 (f100 f101 f12) ?v0) f32)))
(assert (forall ((?v0 S23)) (= (f60 (f102 f103 f16) ?v0) f28)))
(assert (forall ((?v0 S23)) (= (f57 (f104 f105 f20) ?v0) f24)))
(assert (forall ((?v0 S23)) (= (f106 (f107 f108 f4) ?v0) f35)))
(assert (forall ((?v0 S23)) (= (f65 (f109 f110 f24) ?v0) f4)))
(assert (forall ((?v0 S23)) (= (f111 (f112 f113 f28) ?v0) f34)))
(assert (forall ((?v0 S23)) (= (f97 (f98 f114 f32) ?v0) f33)))
(assert (forall ((?v0 S8)) (= (f39 (f40 f115 f32) ?v0) f12)))
(assert (forall ((?v0 S12)) (= (f42 (f43 f116 f28) ?v0) f16)))
(assert (forall ((?v0 S16)) (= (f45 (f46 f117 f24) ?v0) f20)))
(assert (forall ((?v0 S14)) (= (f48 (f49 f118 f4) ?v0) f24)))
(assert (forall ((?v0 S10)) (= (f51 (f52 f119 f34) ?v0) f28)))
(assert (forall ((?v0 S6)) (= (f54 (f55 f120 f33) ?v0) f32)))
(assert (forall ((?v0 S2)) (= (f36 (f37 f121 f35) ?v0) f4)))
(assert (forall ((?v0 S10) (?v1 S12)) (= (= (f42 (f43 f116 ?v0) ?v1) f16) (or (= ?v0 f28) (= ?v1 f16)))))
(assert (forall ((?v0 S20) (?v1 S10)) (= (= (f51 (f52 f119 ?v0) ?v1) f28) (or (= ?v0 f34) (= ?v1 f28)))))
(assert (= (f39 (f40 f41 f32) f12) f12))
(assert (= (f42 (f43 f44 f28) f16) f16))
(assert (= (f45 (f46 f47 f24) f20) f20))
(assert (= (f48 (f49 f50 f4) f24) f24))
(assert (= (f51 (f52 f53 f34) f28) f28))
(assert (= (f54 (f55 f56 f33) f32) f32))
(assert (= (f36 (f37 f38 f35) f4) f4))
(assert (forall ((?v0 S6) (?v1 S8)) (= (= (f39 (f40 f41 ?v0) ?v1) f12) (and (= ?v0 f32) (= ?v1 f12)))))
(assert (forall ((?v0 S10) (?v1 S12)) (= (= (f42 (f43 f44 ?v0) ?v1) f16) (and (= ?v0 f28) (= ?v1 f16)))))
(assert (forall ((?v0 S14) (?v1 S16)) (= (= (f45 (f46 f47 ?v0) ?v1) f20) (and (= ?v0 f24) (= ?v1 f20)))))
(assert (forall ((?v0 S4) (?v1 S2)) (= (= (f36 (f37 f38 ?v0) ?v1) f4) (and (= ?v0 f35) (= ?v1 f4)))))
(assert (forall ((?v0 S2) (?v1 S14)) (= (= (f48 (f49 f50 ?v0) ?v1) f24) (and (= ?v0 f4) (= ?v1 f24)))))
(assert (forall ((?v0 S20) (?v1 S10)) (= (= (f51 (f52 f53 ?v0) ?v1) f28) (and (= ?v0 f34) (= ?v1 f28)))))
(assert (forall ((?v0 S23) (?v1 S6)) (= (= (f54 (f55 f56 ?v0) ?v1) f32) (and (= ?v0 f33) (= ?v1 f32)))))
(assert (forall ((?v0 S6)) (= (f54 (f122 f123 f32) ?v0) f32)))
(assert (forall ((?v0 S10)) (= (f51 (f124 f125 f28) ?v0) f28)))
(assert (forall ((?v0 S14)) (= (f48 (f126 f127 f24) ?v0) f24)))
(assert (forall ((?v0 S2)) (= (f36 (f128 f129 f4) ?v0) f4)))
(assert (forall ((?v0 S23)) (= (f29 (f63 f64 ?v0) f33) (f54 (f55 f56 ?v0) f32))))
(assert (forall ((?v0 S20)) (= (f60 (f61 f62 ?v0) f33) (f51 (f52 f53 ?v0) f28))))
(assert (forall ((?v0 S2)) (= (f57 (f58 f59 ?v0) f33) (f48 (f49 f50 ?v0) f24))))
(assert (forall ((?v0 S4)) (= (f65 (f66 f67 ?v0) f33) (f36 (f37 f38 ?v0) f4))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= ?v0 ?v1) (forall ((?v2 S23)) (= (f97 (f98 f114 ?v0) ?v2) (f97 (f98 f114 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= ?v0 ?v1) (forall ((?v2 S23)) (= (f111 (f112 f113 ?v0) ?v2) (f111 (f112 f113 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= ?v0 ?v1) (forall ((?v2 S23)) (= (f65 (f109 f110 ?v0) ?v2) (f65 (f109 f110 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 ?v1) (forall ((?v2 S23)) (= (f106 (f107 f108 ?v0) ?v2) (f106 (f107 f108 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f95 f96 ?v0) (f95 f96 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f98 f114 ?v0) (f98 f114 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f112 f113 ?v0) (f112 f113 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f109 f110 ?v0) (f109 f110 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f107 f108 ?v0) (f107 f108 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S23) (?v1 S6)) (= (f97 (f98 f114 (f54 (f55 f56 ?v0) ?v1)) f33) ?v0)))
(assert (forall ((?v0 S20) (?v1 S10)) (= (f111 (f112 f113 (f51 (f52 f53 ?v0) ?v1)) f33) ?v0)))
(assert (forall ((?v0 S2) (?v1 S14)) (= (f65 (f109 f110 (f48 (f49 f50 ?v0) ?v1)) f33) ?v0)))
(assert (forall ((?v0 S4) (?v1 S2)) (= (f106 (f107 f108 (f36 (f37 f38 ?v0) ?v1)) f33) ?v0)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S20)) (= (f94 (f95 f96 (f51 (f124 f125 ?v0) ?v1)) ?v2) (f94 (f95 f96 ?v0) (f94 (f95 f96 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S23)) (= (f97 (f98 f99 (f54 (f122 f123 ?v0) ?v1)) ?v2) (f97 (f98 f99 ?v0) (f97 (f98 f99 ?v1) ?v2)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (f36 (f92 f93 (f48 (f126 f127 ?v0) ?v1)) ?v2) (f36 (f92 f93 ?v0) (f36 (f92 f93 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S4)) (= (f89 (f90 f91 (f36 (f128 f129 ?v0) ?v1)) ?v2) (f89 (f90 f91 ?v0) (f89 (f90 f91 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S23) (?v2 S23)) (= (f106 (f107 f108 (f65 (f66 f67 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f35))))
(assert (forall ((?v0 S6) (?v1 S23) (?v2 S23)) (= (f29 (f100 f101 (f80 (f81 f82 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f32))))
(assert (forall ((?v0 S10) (?v1 S23) (?v2 S23)) (= (f60 (f102 f103 (f77 (f78 f79 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f28))))
(assert (forall ((?v0 S14) (?v1 S23) (?v2 S23)) (= (f57 (f104 f105 (f74 (f75 f76 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f24))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S23)) (= (f65 (f109 f110 (f57 (f58 f59 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f4))))
(assert (forall ((?v0 S20) (?v1 S23) (?v2 S23)) (= (f111 (f112 f113 (f60 (f61 f62 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f34))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (= (f97 (f98 f114 (f29 (f63 f64 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f33))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (= (= (f29 (f63 f64 ?v0) ?v1) (f29 (f63 f64 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S20) (?v1 S23) (?v2 S20)) (= (= (f60 (f61 f62 ?v0) ?v1) (f60 (f61 f62 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S2)) (= (= (f57 (f58 f59 ?v0) ?v1) (f57 (f58 f59 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S4) (?v1 S23) (?v2 S4)) (= (= (f65 (f66 f67 ?v0) ?v1) (f65 (f66 f67 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S4) (?v3 S2)) (= (= (f36 (f37 f38 ?v0) ?v1) (f36 (f37 f38 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S23) (?v1 S6) (?v2 S23) (?v3 S6)) (= (= (f54 (f55 f56 ?v0) ?v1) (f54 (f55 f56 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S20) (?v1 S10) (?v2 S20) (?v3 S10)) (= (= (f51 (f52 f53 ?v0) ?v1) (f51 (f52 f53 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2) (?v3 S14)) (= (= (f48 (f49 f50 ?v0) ?v1) (f48 (f49 f50 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S23) (?v1 S6) (?v2 S23)) (=> (= (f54 (f55 f120 ?v0) ?v1) (f54 (f55 f56 ?v2) ?v1)) (= ?v1 f32))))
(assert (forall ((?v0 S20) (?v1 S10) (?v2 S20)) (=> (= (f51 (f52 f119 ?v0) ?v1) (f51 (f52 f53 ?v2) ?v1)) (= ?v1 f28))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (=> (= (f48 (f49 f118 ?v0) ?v1) (f48 (f49 f50 ?v2) ?v1)) (= ?v1 f24))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S4)) (=> (= (f36 (f37 f121 ?v0) ?v1) (f36 (f37 f38 ?v2) ?v1)) (= ?v1 f4))))
(assert (forall ((?v0 S20)) (= (f51 (f52 f119 ?v0) f28) f28)))
(assert (forall ((?v0 S23)) (= (f54 (f55 f120 ?v0) f32) f32)))
(assert (forall ((?v0 S2)) (= (f48 (f49 f118 ?v0) f24) f24)))
(assert (forall ((?v0 S4)) (= (f36 (f37 f121 ?v0) f4) f4)))
(assert (forall ((?v0 S10)) (= (= (f95 f96 ?v0) (f95 f96 f28)) (= ?v0 f28))))
(assert (forall ((?v0 S78) (?v1 S6)) (=> (= (f130 ?v0 f32) f1) (=> (forall ((?v2 S23) (?v3 S6)) (=> (= (f130 ?v0 ?v3) f1) (= (f130 ?v0 (f54 (f55 f56 ?v2) ?v3)) f1))) (= (f130 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S79) (?v1 S10)) (=> (= (f131 ?v0 f28) f1) (=> (forall ((?v2 S20) (?v3 S10)) (=> (= (f131 ?v0 ?v3) f1) (= (f131 ?v0 (f51 (f52 f53 ?v2) ?v3)) f1))) (= (f131 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S80) (?v1 S14)) (=> (= (f132 ?v0 f24) f1) (=> (forall ((?v2 S2) (?v3 S14)) (=> (= (f132 ?v0 ?v3) f1) (= (f132 ?v0 (f48 (f49 f50 ?v2) ?v3)) f1))) (= (f132 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S81) (?v1 S2)) (=> (= (f133 ?v0 f4) f1) (=> (forall ((?v2 S4) (?v3 S2)) (=> (= (f133 ?v0 ?v3) f1) (= (f133 ?v0 (f36 (f37 f38 ?v2) ?v3)) f1))) (= (f133 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S10)) (= (= (f51 (f85 f86 ?v0) ?v1) f28) (or (= ?v0 f16) (not (= (f134 (f135 f136 ?v1) ?v0) f33))))))
(assert (forall ((?v0 S10) (?v1 S20)) (= (= (f94 (f95 f96 ?v0) ?v1) f34) (or (= ?v0 f28) (not (= (f137 (f138 f139 ?v1) ?v0) f33))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (forall ((?v2 S23)) (= (f97 (f98 f114 ?v0) ?v2) (f97 (f98 f114 ?v1) ?v2))) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (forall ((?v2 S23)) (= (f111 (f112 f113 ?v0) ?v2) (f111 (f112 f113 ?v1) ?v2))) (= ?v0 ?v1))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (forall ((?v2 S23)) (= (f65 (f109 f110 ?v0) ?v2) (f65 (f109 f110 ?v1) ?v2))) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (forall ((?v2 S23)) (= (f106 (f107 f108 ?v0) ?v2) (f106 (f107 f108 ?v1) ?v2))) (= ?v0 ?v1))))
(assert (forall ((?v0 S2)) (=> (forall ((?v1 S4) (?v2 S2)) (=> (= ?v0 (f36 (f37 f38 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S23) (?v2 S6)) (=> (= ?v0 (f54 (f55 f56 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S10)) (=> (forall ((?v1 S20) (?v2 S10)) (=> (= ?v0 (f51 (f52 f53 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S14)) (=> (forall ((?v1 S2) (?v2 S14)) (=> (= ?v0 (f48 (f49 f50 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S20) (?v1 S10) (?v2 S20)) (= (f25 (f26 f140 (f51 (f52 f53 ?v0) ?v1)) ?v2) (f51 (f52 f53 (f94 (f95 f96 ?v1) ?v2)) (f25 (f26 f140 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S6) (?v2 S23)) (= (f29 (f30 f141 (f54 (f55 f56 ?v0) ?v1)) ?v2) (f54 (f55 f56 (f97 (f98 f99 ?v1) ?v2)) (f29 (f30 f141 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (= (f21 (f22 f142 (f48 (f49 f50 ?v0) ?v1)) ?v2) (f48 (f49 f50 (f36 (f92 f93 ?v1) ?v2)) (f21 (f22 f142 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S4)) (= (f5 (f6 f143 (f36 (f37 f38 ?v0) ?v1)) ?v2) (f36 (f37 f38 (f89 (f90 f91 ?v1) ?v2)) (f5 (f6 f143 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S6)) (= (f98 f114 (f54 (f55 f56 ?v0) ?v1)) (f144 (f145 f146 ?v0) (f98 f114 ?v1)))))
(assert (forall ((?v0 S20) (?v1 S10)) (= (f112 f113 (f51 (f52 f53 ?v0) ?v1)) (f147 (f148 f149 ?v0) (f112 f113 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S14)) (= (f109 f110 (f48 (f49 f50 ?v0) ?v1)) (f150 (f151 f152 ?v0) (f109 f110 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S2)) (= (f107 f108 (f36 (f37 f38 ?v0) ?v1)) (f153 (f154 f155 ?v0) (f107 f108 ?v1)))))
(assert (forall ((?v0 S23) (?v1 S6) (?v2 S23)) (let ((?v_0 (f55 f56 ?v0)) (?v_1 (f29 (f30 f31 ?v1) ?v2))) (= (f29 (f30 f31 (f54 ?v_0 ?v1)) ?v2) (f54 (f122 f156 (f54 (f55 f120 ?v2) ?v_1)) (f54 ?v_0 ?v_1))))))
(assert (forall ((?v0 S20) (?v1 S10) (?v2 S20)) (let ((?v_0 (f52 f53 ?v0)) (?v_1 (f25 (f26 f27 ?v1) ?v2))) (= (f25 (f26 f27 (f51 ?v_0 ?v1)) ?v2) (f51 (f124 f157 (f51 (f52 f119 ?v2) ?v_1)) (f51 ?v_0 ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (let ((?v_0 (f49 f50 ?v0)) (?v_1 (f21 (f22 f23 ?v1) ?v2))) (= (f21 (f22 f23 (f48 ?v_0 ?v1)) ?v2) (f48 (f126 f158 (f48 (f49 f118 ?v2) ?v_1)) (f48 ?v_0 ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S4)) (let ((?v_0 (f37 f38 ?v0)) (?v_1 (f5 (f6 f7 ?v1) ?v2))) (= (f5 (f6 f7 (f36 ?v_0 ?v1)) ?v2) (f36 (f128 f159 (f36 (f37 f121 ?v2) ?v_1)) (f36 ?v_0 ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S23)) (let ((?v_0 (f66 f67 ?v0))) (= (f65 ?v_0 (f97 f160 ?v1)) (f36 (f37 f38 f35) (f65 ?v_0 ?v1))))))
(assert (forall ((?v0 S6) (?v1 S23)) (let ((?v_0 (f81 f82 ?v0))) (= (f80 ?v_0 (f97 f160 ?v1)) (f39 (f40 f41 f32) (f80 ?v_0 ?v1))))))
(assert (forall ((?v0 S10) (?v1 S23)) (let ((?v_0 (f78 f79 ?v0))) (= (f77 ?v_0 (f97 f160 ?v1)) (f42 (f43 f44 f28) (f77 ?v_0 ?v1))))))
(assert (forall ((?v0 S14) (?v1 S23)) (let ((?v_0 (f75 f76 ?v0))) (= (f74 ?v_0 (f97 f160 ?v1)) (f45 (f46 f47 f24) (f74 ?v_0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S23)) (let ((?v_0 (f58 f59 ?v0))) (= (f57 ?v_0 (f97 f160 ?v1)) (f48 (f49 f50 f4) (f57 ?v_0 ?v1))))))
(assert (forall ((?v0 S20) (?v1 S23)) (let ((?v_0 (f61 f62 ?v0))) (= (f60 ?v_0 (f97 f160 ?v1)) (f51 (f52 f53 f34) (f60 ?v_0 ?v1))))))
(assert (forall ((?v0 S23) (?v1 S23)) (let ((?v_0 (f63 f64 ?v0))) (= (f29 ?v_0 (f97 f160 ?v1)) (f54 (f55 f56 f33) (f29 ?v_0 ?v1))))))
(assert (forall ((?v0 S23) (?v1 S6) (?v2 S23)) (=> (= (f54 (f122 f156 (f54 (f55 f120 ?v0) ?v1)) (f54 (f55 f56 ?v2) ?v1)) f32) (= ?v1 f32))))
(assert (forall ((?v0 S20) (?v1 S10) (?v2 S20)) (=> (= (f51 (f124 f157 (f51 (f52 f119 ?v0) ?v1)) (f51 (f52 f53 ?v2) ?v1)) f28) (= ?v1 f28))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (=> (= (f48 (f126 f158 (f48 (f49 f118 ?v0) ?v1)) (f48 (f49 f50 ?v2) ?v1)) f24) (= ?v1 f24))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S4)) (=> (= (f36 (f128 f159 (f36 (f37 f121 ?v0) ?v1)) (f36 (f37 f38 ?v2) ?v1)) f4) (= ?v1 f4))))
(assert (forall ((?v0 S8)) (=> (not (= ?v0 f12)) (not (= (f29 (f100 f101 ?v0) (f161 f162 ?v0)) f32)))))
(assert (forall ((?v0 S12)) (=> (not (= ?v0 f16)) (not (= (f60 (f102 f103 ?v0) (f134 f163 ?v0)) f28)))))
(assert (forall ((?v0 S16)) (=> (not (= ?v0 f20)) (not (= (f57 (f104 f105 ?v0) (f164 f165 ?v0)) f24)))))
(assert (forall ((?v0 S2)) (=> (not (= ?v0 f4)) (not (= (f106 (f107 f108 ?v0) (f166 f167 ?v0)) f35)))))
(assert (forall ((?v0 S14)) (=> (not (= ?v0 f24)) (not (= (f65 (f109 f110 ?v0) (f168 f169 ?v0)) f4)))))
(assert (forall ((?v0 S10)) (=> (not (= ?v0 f28)) (not (= (f111 (f112 f113 ?v0) (f137 f170 ?v0)) f34)))))
(assert (forall ((?v0 S6)) (=> (not (= ?v0 f32)) (not (= (f97 (f98 f114 ?v0) (f171 f172 ?v0)) f33)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f128 f159 ?v0))) (= (f36 (f128 f159 (f36 ?v_0 ?v1)) ?v2) (f36 ?v_0 (f36 (f128 f159 ?v1) ?v2))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f173 f174 ?v0))) (= (f97 (f173 f174 (f97 ?v_0 ?v1)) ?v2) (f97 ?v_0 (f97 (f173 f174 ?v1) ?v2))))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S20)) (let ((?v_0 (f175 f176 ?v0))) (= (f94 (f175 f176 (f94 ?v_0 ?v1)) ?v2) (f94 ?v_0 (f94 (f175 f176 ?v1) ?v2))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f173 f174 ?v0))) (= (= (f97 ?v_0 ?v1) (f97 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S20)) (let ((?v_0 (f175 f176 ?v0))) (= (= (f94 ?v_0 ?v1) (f94 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (= (= (f97 (f173 f174 ?v0) ?v1) (f97 (f173 f174 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S20)) (= (= (f94 (f175 f176 ?v0) ?v1) (f94 (f175 f176 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f173 f174 ?v0))) (=> (= (f97 ?v_0 ?v1) (f97 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S20)) (let ((?v_0 (f175 f176 ?v0))) (=> (= (f94 ?v_0 ?v1) (f94 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f173 f174 ?v0))) (=> (= (f97 ?v_0 ?v1) (f97 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S20)) (let ((?v_0 (f175 f176 ?v0))) (=> (= (f94 ?v_0 ?v1) (f94 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (=> (= (f97 (f173 f174 ?v0) ?v1) (f97 (f173 f174 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S20)) (=> (= (f94 (f175 f176 ?v0) ?v1) (f94 (f175 f176 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f111 (f112 f113 ?v0) (f137 f170 ?v0)) (f111 (f112 f113 ?v1) (f137 f170 ?v1))) (=> (= (f131 (f177 ?v0) ?v1) f1) (=> (= (f131 (f177 ?v1) ?v0) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S4) (?v3 S2)) (= (f36 (f128 f159 (f36 (f37 f38 ?v0) ?v1)) (f36 (f37 f38 ?v2) ?v3)) (f36 (f37 f38 (f89 (f178 f179 ?v0) ?v2)) (f36 (f128 f159 ?v1) ?v3)))))
(assert (forall ((?v0 S23) (?v1 S6) (?v2 S23) (?v3 S6)) (= (f54 (f122 f156 (f54 (f55 f56 ?v0) ?v1)) (f54 (f55 f56 ?v2) ?v3)) (f54 (f55 f56 (f97 (f173 f174 ?v0) ?v2)) (f54 (f122 f156 ?v1) ?v3)))))
(assert (forall ((?v0 S20) (?v1 S10) (?v2 S20) (?v3 S10)) (= (f51 (f124 f157 (f51 (f52 f53 ?v0) ?v1)) (f51 (f52 f53 ?v2) ?v3)) (f51 (f52 f53 (f94 (f175 f176 ?v0) ?v2)) (f51 (f124 f157 ?v1) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2) (?v3 S14)) (= (f48 (f126 f158 (f48 (f49 f50 ?v0) ?v1)) (f48 (f49 f50 ?v2) ?v3)) (f48 (f49 f50 (f36 (f128 f159 ?v0) ?v2)) (f48 (f126 f158 ?v1) ?v3)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2)) (= (f36 (f37 f121 (f89 (f178 f179 ?v0) ?v1)) ?v2) (f36 (f128 f159 (f36 (f37 f121 ?v0) ?v2)) (f36 (f37 f121 ?v1) ?v2)))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S10)) (= (f51 (f52 f119 (f94 (f175 f176 ?v0) ?v1)) ?v2) (f51 (f124 f157 (f51 (f52 f119 ?v0) ?v2)) (f51 (f52 f119 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S6)) (= (f54 (f55 f120 (f97 (f173 f174 ?v0) ?v1)) ?v2) (f54 (f122 f156 (f54 (f55 f120 ?v0) ?v2)) (f54 (f55 f120 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S14)) (= (f48 (f49 f118 (f36 (f128 f159 ?v0) ?v1)) ?v2) (f48 (f126 f158 (f48 (f49 f118 ?v0) ?v2)) (f48 (f49 f118 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S23)) (= (f97 (f98 f114 (f54 (f122 f156 ?v0) ?v1)) ?v2) (f97 (f173 f174 (f97 (f98 f114 ?v0) ?v2)) (f97 (f98 f114 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S23)) (= (f111 (f112 f113 (f51 (f124 f157 ?v0) ?v1)) ?v2) (f94 (f175 f176 (f111 (f112 f113 ?v0) ?v2)) (f111 (f112 f113 ?v1) ?v2)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S23)) (= (f65 (f109 f110 (f48 (f126 f158 ?v0) ?v1)) ?v2) (f36 (f128 f159 (f65 (f109 f110 ?v0) ?v2)) (f65 (f109 f110 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S23)) (= (f106 (f107 f108 (f36 (f128 f159 ?v0) ?v1)) ?v2) (f89 (f178 f179 (f106 (f107 f108 ?v0) ?v2)) (f106 (f107 f108 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S20)) (= (f94 (f95 f96 (f51 (f124 f157 ?v0) ?v1)) ?v2) (f94 (f175 f176 (f94 (f95 f96 ?v0) ?v2)) (f94 (f95 f96 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S23)) (= (f97 (f98 f99 (f54 (f122 f156 ?v0) ?v1)) ?v2) (f97 (f173 f174 (f97 (f98 f99 ?v0) ?v2)) (f97 (f98 f99 ?v1) ?v2)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (f36 (f92 f93 (f48 (f126 f158 ?v0) ?v1)) ?v2) (f36 (f128 f159 (f36 (f92 f93 ?v0) ?v2)) (f36 (f92 f93 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S4)) (= (f89 (f90 f91 (f36 (f128 f159 ?v0) ?v1)) ?v2) (f89 (f178 f179 (f89 (f90 f91 ?v0) ?v2)) (f89 (f90 f91 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (= (f54 (f122 f156 (f29 (f63 f64 ?v0) ?v1)) (f29 (f63 f64 ?v2) ?v1)) (f29 (f63 f64 (f97 (f173 f174 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S20) (?v1 S23) (?v2 S20)) (= (f51 (f124 f157 (f60 (f61 f62 ?v0) ?v1)) (f60 (f61 f62 ?v2) ?v1)) (f60 (f61 f62 (f94 (f175 f176 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S2)) (= (f48 (f126 f158 (f57 (f58 f59 ?v0) ?v1)) (f57 (f58 f59 ?v2) ?v1)) (f57 (f58 f59 (f36 (f128 f159 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S4) (?v1 S23) (?v2 S4)) (= (f36 (f128 f159 (f65 (f66 f67 ?v0) ?v1)) (f65 (f66 f67 ?v2) ?v1)) (f65 (f66 f67 (f89 (f178 f179 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S6) (?v1 S23)) (= (= (f29 (f30 f141 ?v0) ?v1) f32) (= (f171 f172 ?v0) f33))))
(assert (forall ((?v0 S10) (?v1 S20)) (= (= (f25 (f26 f140 ?v0) ?v1) f28) (= (f137 f170 ?v0) f33))))
(assert (forall ((?v0 S14) (?v1 S2)) (= (= (f21 (f22 f142 ?v0) ?v1) f24) (= (f168 f169 ?v0) f33))))
(assert (forall ((?v0 S2) (?v1 S4)) (= (= (f5 (f6 f143 ?v0) ?v1) f4) (= (f166 f167 ?v0) f33))))
(assert (forall ((?v0 S6) (?v1 S23)) (=> (not (= ?v0 f32)) (= (f171 f172 (f54 (f55 f56 ?v1) ?v0)) (f97 f160 (f171 f172 ?v0))))))
(assert (forall ((?v0 S10) (?v1 S20)) (=> (not (= ?v0 f28)) (= (f137 f170 (f51 (f52 f53 ?v1) ?v0)) (f97 f160 (f137 f170 ?v0))))))
(assert (forall ((?v0 S14) (?v1 S2)) (=> (not (= ?v0 f24)) (= (f168 f169 (f48 (f49 f50 ?v1) ?v0)) (f97 f160 (f168 f169 ?v0))))))
(assert (forall ((?v0 S2) (?v1 S4)) (=> (not (= ?v0 f4)) (= (f166 f167 (f36 (f37 f38 ?v1) ?v0)) (f97 f160 (f166 f167 ?v0))))))
(assert (forall ((?v0 S23) (?v1 S6)) (= (f171 f172 (f54 (f55 f56 ?v0) ?v1)) (ite (= ?v1 f32) f33 (f97 f160 (f171 f172 ?v1))))))
(assert (forall ((?v0 S20) (?v1 S10)) (= (f137 f170 (f51 (f52 f53 ?v0) ?v1)) (ite (= ?v1 f28) f33 (f97 f160 (f137 f170 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S14)) (= (f168 f169 (f48 (f49 f50 ?v0) ?v1)) (ite (= ?v1 f24) f33 (f97 f160 (f168 f169 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (= (f166 f167 (f36 (f37 f38 ?v0) ?v1)) (ite (= ?v1 f4) f33 (f97 f160 (f166 f167 ?v1))))))
(assert (forall ((?v0 S6)) (= (f54 (f122 f156 f32) ?v0) ?v0)))
(assert (forall ((?v0 S10)) (= (f51 (f124 f157 f28) ?v0) ?v0)))
(assert (forall ((?v0 S14)) (= (f48 (f126 f158 f24) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f89 (f178 f179 f35) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f36 (f128 f159 f4) ?v0) ?v0)))
(assert (forall ((?v0 S20)) (= (f94 (f175 f176 f34) ?v0) ?v0)))
(assert (forall ((?v0 S23)) (= (f97 (f173 f174 f33) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f54 (f122 f156 f32) ?v0) ?v0)))
(assert (forall ((?v0 S10)) (= (f51 (f124 f157 f28) ?v0) ?v0)))
(assert (forall ((?v0 S14)) (= (f48 (f126 f158 f24) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f89 (f178 f179 f35) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f36 (f128 f159 f4) ?v0) ?v0)))
(assert (forall ((?v0 S20)) (= (f94 (f175 f176 f34) ?v0) ?v0)))
(assert (forall ((?v0 S23)) (= (f97 (f173 f174 f33) ?v0) ?v0)))
(assert (forall ((?v0 S10)) (= (= f28 (f51 (f124 f157 ?v0) ?v0)) (= ?v0 f28))))
(assert (forall ((?v0 S20)) (= (= f34 (f94 (f175 f176 ?v0) ?v0)) (= ?v0 f34))))
(assert (forall ((?v0 S6)) (= (f54 (f122 f156 ?v0) f32) ?v0)))
(assert (forall ((?v0 S10)) (= (f51 (f124 f157 ?v0) f28) ?v0)))
(assert (forall ((?v0 S14)) (= (f48 (f126 f158 ?v0) f24) ?v0)))
(assert (forall ((?v0 S4)) (= (f89 (f178 f179 ?v0) f35) ?v0)))
(assert (forall ((?v0 S2)) (= (f36 (f128 f159 ?v0) f4) ?v0)))
(assert (forall ((?v0 S20)) (= (f94 (f175 f176 ?v0) f34) ?v0)))
(assert (forall ((?v0 S23)) (= (f97 (f173 f174 ?v0) f33) ?v0)))
(assert (forall ((?v0 S6)) (= (f54 (f122 f156 ?v0) f32) ?v0)))
(assert (forall ((?v0 S10)) (= (f51 (f124 f157 ?v0) f28) ?v0)))
(assert (forall ((?v0 S14)) (= (f48 (f126 f158 ?v0) f24) ?v0)))
(assert (forall ((?v0 S4)) (= (f89 (f178 f179 ?v0) f35) ?v0)))
(assert (forall ((?v0 S2)) (= (f36 (f128 f159 ?v0) f4) ?v0)))
(assert (forall ((?v0 S20)) (= (f94 (f175 f176 ?v0) f34) ?v0)))
(assert (forall ((?v0 S23)) (= (f97 (f173 f174 ?v0) f33) ?v0)))
(assert (= (f171 f172 f32) f33))
(assert (= (f137 f170 f28) f33))
(assert (= (f168 f169 f24) f33))
(assert (= (f166 f167 f4) f33))
(assert (forall ((?v0 S20) (?v1 S10) (?v2 S10)) (=> (= (f131 (f177 (f51 (f52 f119 ?v0) ?v1)) ?v2) f1) (= (f131 (f177 ?v1) ?v2) f1))))
(assert (forall ((?v0 S23) (?v1 S6) (?v2 S6)) (=> (= (f130 (f180 (f54 (f55 f120 ?v0) ?v1)) ?v2) f1) (= (f130 (f180 ?v1) ?v2) f1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S20)) (let ((?v_0 (f177 ?v0))) (=> (= (f131 ?v_0 ?v1) f1) (= (f131 ?v_0 (f51 (f52 f119 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S23)) (let ((?v_0 (f180 ?v0))) (=> (= (f130 ?v_0 ?v1) f1) (= (f130 ?v_0 (f54 (f55 f120 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S6)) (= (f54 (f122 f156 f32) ?v0) ?v0)))
(assert (forall ((?v0 S10)) (= (f51 (f124 f157 f28) ?v0) ?v0)))
(assert (forall ((?v0 S14)) (= (f48 (f126 f158 f24) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f36 (f128 f159 f4) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f54 (f122 f156 ?v0) f32) ?v0)))
(assert (forall ((?v0 S10)) (= (f51 (f124 f157 ?v0) f28) ?v0)))
(assert (forall ((?v0 S14)) (= (f48 (f126 f158 ?v0) f24) ?v0)))
(assert (forall ((?v0 S2)) (= (f36 (f128 f159 ?v0) f4) ?v0)))
(check-sat)
(exit)