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
(declare-sort S102 0)
(declare-sort S103 0)
(declare-sort S104 0)
(declare-sort S105 0)
(declare-sort S106 0)
(declare-sort S107 0)
(declare-sort S108 0)
(declare-sort S109 0)
(declare-sort S110 0)
(declare-sort S111 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 () S2)
(declare-fun f5 () S3)
(declare-fun f6 (S5 S3) S3)
(declare-fun f7 (S6 S7) S5)
(declare-fun f8 () S6)
(declare-fun f9 (S4 S7) S7)
(declare-fun f10 () S7)
(declare-fun f11 () S3)
(declare-fun f12 (S4) S1)
(declare-fun f13 (S9 S8) S8)
(declare-fun f14 (S10 S11) S9)
(declare-fun f15 () S10)
(declare-fun f16 () S11)
(declare-fun f17 () S8)
(declare-fun f18 (S13 S12) S12)
(declare-fun f19 (S14 S15) S13)
(declare-fun f20 () S14)
(declare-fun f21 () S15)
(declare-fun f22 () S12)
(declare-fun f23 (S16 S17) S5)
(declare-fun f24 () S16)
(declare-fun f25 () S17)
(declare-fun f26 (S19 S18) S18)
(declare-fun f27 (S20 S21) S19)
(declare-fun f28 () S20)
(declare-fun f29 () S21)
(declare-fun f30 () S18)
(declare-fun f31 (S23 S22) S22)
(declare-fun f32 (S24 S25) S23)
(declare-fun f33 () S24)
(declare-fun f34 () S25)
(declare-fun f35 () S22)
(declare-fun f36 (S27 S26) S26)
(declare-fun f37 (S28 S29) S27)
(declare-fun f38 () S28)
(declare-fun f39 () S29)
(declare-fun f40 () S26)
(declare-fun f41 (S30 S17) S17)
(declare-fun f42 (S31 S26) S30)
(declare-fun f43 () S31)
(declare-fun f44 (S32 S15) S15)
(declare-fun f45 (S33 S22) S32)
(declare-fun f46 () S33)
(declare-fun f47 (S34 S11) S11)
(declare-fun f48 (S35 S18) S34)
(declare-fun f49 () S35)
(declare-fun f50 (S36 S8) S34)
(declare-fun f51 () S36)
(declare-fun f52 (S37 S12) S32)
(declare-fun f53 () S37)
(declare-fun f54 (S38 S3) S30)
(declare-fun f55 () S38)
(declare-fun f56 (S39 S21) S21)
(declare-fun f57 (S40 S18) S39)
(declare-fun f58 () S40)
(declare-fun f59 (S41 S25) S25)
(declare-fun f60 (S42 S22) S41)
(declare-fun f61 () S42)
(declare-fun f62 (S43 S29) S29)
(declare-fun f63 (S44 S26) S43)
(declare-fun f64 () S44)
(declare-fun f65 (S45 S17) S27)
(declare-fun f66 () S45)
(declare-fun f67 (S46 S15) S23)
(declare-fun f68 () S46)
(declare-fun f69 (S47 S11) S19)
(declare-fun f70 () S47)
(declare-fun f71 (S48 S7) S3)
(declare-fun f72 (S49 S3) S48)
(declare-fun f73 () S49)
(declare-fun f74 (S50 S11) S18)
(declare-fun f75 (S51 S18) S50)
(declare-fun f76 () S51)
(declare-fun f77 (S52 S15) S22)
(declare-fun f78 (S53 S22) S52)
(declare-fun f79 () S53)
(declare-fun f80 (S54 S17) S26)
(declare-fun f81 (S55 S26) S54)
(declare-fun f82 () S55)
(declare-fun f83 (S56 S3) S17)
(declare-fun f84 (S57 S17) S56)
(declare-fun f85 () S57)
(declare-fun f86 (S58 S12) S15)
(declare-fun f87 (S59 S15) S58)
(declare-fun f88 () S59)
(declare-fun f89 (S60 S8) S11)
(declare-fun f90 (S61 S11) S60)
(declare-fun f91 () S61)
(declare-fun f92 (S62 S3) S8)
(declare-fun f93 (S63 S7) S62)
(declare-fun f94 () S63)
(declare-fun f95 (S64 S15) S8)
(declare-fun f96 (S65 S12) S64)
(declare-fun f97 () S65)
(declare-fun f98 (S66 S17) S8)
(declare-fun f99 (S67 S3) S66)
(declare-fun f100 () S67)
(declare-fun f101 (S68 S25) S8)
(declare-fun f102 (S69 S22) S68)
(declare-fun f103 () S69)
(declare-fun f104 (S70 S29) S8)
(declare-fun f105 (S71 S26) S70)
(declare-fun f106 () S71)
(declare-fun f107 (S72 S26) S8)
(declare-fun f108 (S73 S17) S72)
(declare-fun f109 () S73)
(declare-fun f110 (S74 S22) S8)
(declare-fun f111 (S75 S15) S74)
(declare-fun f112 () S75)
(declare-fun f113 (S76 S3) S1)
(declare-fun f114 (S77 S18) S1)
(declare-fun f115 (S78 S22) S1)
(declare-fun f116 (S79 S26) S1)
(declare-fun f117 (S80 S17) S1)
(declare-fun f118 (S81 S15) S1)
(declare-fun f119 (S82 S11) S1)
(declare-fun f120 () S62)
(declare-fun f121 (S83 S18) S8)
(declare-fun f122 () S83)
(declare-fun f123 () S74)
(declare-fun f124 () S72)
(declare-fun f125 () S66)
(declare-fun f126 () S64)
(declare-fun f127 (S84 S11) S8)
(declare-fun f128 () S84)
(declare-fun f129 () S49)
(declare-fun f130 () S53)
(declare-fun f131 () S55)
(declare-fun f132 () S51)
(declare-fun f133 () S61)
(declare-fun f134 () S57)
(declare-fun f135 () S59)
(declare-fun f136 (S85 S7) S86)
(declare-fun f137 () S85)
(declare-fun f138 (S86 S8) S3)
(declare-fun f139 (S87 S11) S88)
(declare-fun f140 () S87)
(declare-fun f141 (S88 S8) S18)
(declare-fun f142 (S89 S15) S90)
(declare-fun f143 () S89)
(declare-fun f144 (S90 S8) S22)
(declare-fun f145 (S91 S17) S92)
(declare-fun f146 () S91)
(declare-fun f147 (S92 S8) S26)
(declare-fun f148 (S93 S3) S94)
(declare-fun f149 () S93)
(declare-fun f150 (S94 S8) S17)
(declare-fun f151 (S95 S12) S96)
(declare-fun f152 () S95)
(declare-fun f153 (S96 S8) S15)
(declare-fun f154 (S97 S8) S60)
(declare-fun f155 () S97)
(declare-fun f156 (S98 S3) S5)
(declare-fun f157 () S98)
(declare-fun f158 (S99 S22) S23)
(declare-fun f159 () S99)
(declare-fun f160 (S100 S26) S27)
(declare-fun f161 () S100)
(declare-fun f162 (S101 S18) S19)
(declare-fun f163 () S101)
(declare-fun f164 (S102 S11) S34)
(declare-fun f165 () S102)
(declare-fun f166 (S103 S17) S30)
(declare-fun f167 () S103)
(declare-fun f168 (S104 S15) S32)
(declare-fun f169 () S104)
(declare-fun f170 () S62)
(declare-fun f171 () S83)
(declare-fun f172 () S74)
(declare-fun f173 () S72)
(declare-fun f174 () S66)
(declare-fun f175 () S64)
(declare-fun f176 () S84)
(declare-fun f177 (S105 S8) S21)
(declare-fun f178 (S106 S18) S105)
(declare-fun f179 () S106)
(declare-fun f180 (S107 S8) S25)
(declare-fun f181 (S108 S22) S107)
(declare-fun f182 () S108)
(declare-fun f183 (S109 S8) S29)
(declare-fun f184 (S110 S26) S109)
(declare-fun f185 () S110)
(declare-fun f186 (S11) S82)
(declare-fun f187 (S8 S8) S1)
(declare-fun f188 (S15) S81)
(declare-fun f189 (S12 S12) S1)
(declare-fun f190 (S21 S21) S1)
(declare-fun f191 (S18) S77)
(declare-fun f192 (S25 S25) S1)
(declare-fun f193 (S22) S78)
(declare-fun f194 (S111 S21) S8)
(declare-fun f195 () S111)
(declare-fun f196 () S68)
(declare-fun f197 () S70)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f3 f4 f5))) (not (= ?v_0 (f3 f4 (f6 (f7 f8 (f9 ?v_0 f10)) f11))))))
(assert (forall ((?v0 S7)) (let ((?v_0 (f3 f4 f5))) (= (f9 ?v_0 ?v0) (f9 ?v_0 f10)))))
(assert (forall ((?v0 S7)) (let ((?v_0 (f3 f4 f5))) (= (f9 ?v_0 ?v0) (f9 ?v_0 f10)))))
(assert (= (f12 (f3 f4 f5)) f1))
(assert (forall ((?v0 S7)) (= (f9 (f3 f4 f11) ?v0) f10)))
(assert (forall ((?v0 S8)) (= (f13 (f14 f15 f16) ?v0) f17)))
(assert (forall ((?v0 S12)) (= (f18 (f19 f20 f21) ?v0) f22)))
(assert (forall ((?v0 S3)) (= (f6 (f23 f24 f25) ?v0) f11)))
(assert (forall ((?v0 S18)) (= (f26 (f27 f28 f29) ?v0) f30)))
(assert (forall ((?v0 S22)) (= (f31 (f32 f33 f34) ?v0) f35)))
(assert (forall ((?v0 S26)) (= (f36 (f37 f38 f39) ?v0) f40)))
(assert (forall ((?v0 S17)) (= (f41 (f42 f43 f40) ?v0) f25)))
(assert (forall ((?v0 S15)) (= (f44 (f45 f46 f35) ?v0) f21)))
(assert (forall ((?v0 S11)) (= (f47 (f48 f49 f30) ?v0) f16)))
(assert (= (f6 (f7 f8 f10) f11) f11))
(assert (= (f47 (f50 f51 f17) f16) f16))
(assert (= (f44 (f52 f53 f22) f21) f21))
(assert (= (f41 (f54 f55 f11) f25) f25))
(assert (= (f56 (f57 f58 f30) f29) f29))
(assert (= (f59 (f60 f61 f35) f34) f34))
(assert (= (f62 (f63 f64 f40) f39) f39))
(assert (= (f36 (f65 f66 f25) f40) f40))
(assert (= (f31 (f67 f68 f21) f35) f35))
(assert (= (f26 (f69 f70 f16) f30) f30))
(assert (forall ((?v0 S7) (?v1 S3)) (= (= (f6 (f7 f8 ?v0) ?v1) f11) (and (= ?v0 f10) (= ?v1 f11)))))
(assert (forall ((?v0 S8) (?v1 S11)) (= (= (f47 (f50 f51 ?v0) ?v1) f16) (and (= ?v0 f17) (= ?v1 f16)))))
(assert (forall ((?v0 S12) (?v1 S15)) (= (= (f44 (f52 f53 ?v0) ?v1) f21) (and (= ?v0 f22) (= ?v1 f21)))))
(assert (forall ((?v0 S3) (?v1 S17)) (= (= (f41 (f54 f55 ?v0) ?v1) f25) (and (= ?v0 f11) (= ?v1 f25)))))
(assert (forall ((?v0 S18) (?v1 S21)) (= (= (f56 (f57 f58 ?v0) ?v1) f29) (and (= ?v0 f30) (= ?v1 f29)))))
(assert (forall ((?v0 S22) (?v1 S25)) (= (= (f59 (f60 f61 ?v0) ?v1) f34) (and (= ?v0 f35) (= ?v1 f34)))))
(assert (forall ((?v0 S26) (?v1 S29)) (= (= (f62 (f63 f64 ?v0) ?v1) f39) (and (= ?v0 f40) (= ?v1 f39)))))
(assert (forall ((?v0 S17) (?v1 S26)) (= (= (f36 (f65 f66 ?v0) ?v1) f40) (and (= ?v0 f25) (= ?v1 f40)))))
(assert (forall ((?v0 S15) (?v1 S22)) (= (= (f31 (f67 f68 ?v0) ?v1) f35) (and (= ?v0 f21) (= ?v1 f35)))))
(assert (forall ((?v0 S11) (?v1 S18)) (= (= (f26 (f69 f70 ?v0) ?v1) f30) (and (= ?v0 f16) (= ?v1 f30)))))
(assert (forall ((?v0 S3)) (= (= (f3 f4 ?v0) (f3 f4 f11)) (= ?v0 f11))))
(assert (forall ((?v0 S22)) (= (= (f45 f46 ?v0) (f45 f46 f35)) (= ?v0 f35))))
(assert (forall ((?v0 S15)) (= (= (f19 f20 ?v0) (f19 f20 f21)) (= ?v0 f21))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f6 (f7 f8 ?v0) f11))) (= (f71 (f72 f73 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f26 (f69 f70 ?v0) f30))) (= (f74 (f75 f76 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S15) (?v1 S15)) (let ((?v_0 (f31 (f67 f68 ?v0) f35))) (= (f77 (f78 f79 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S17) (?v1 S17)) (let ((?v_0 (f36 (f65 f66 ?v0) f40))) (= (f80 (f81 f82 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f41 (f54 f55 ?v0) f25))) (= (f83 (f84 f85 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f44 (f52 f53 ?v0) f21))) (= (f86 (f87 f88 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f47 (f50 f51 ?v0) f16))) (= (f89 (f90 f91 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 f4 ?v0) (f3 f4 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S22) (?v1 S22)) (= (= (f45 f46 ?v0) (f45 f46 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (= (f19 f20 ?v0) (f19 f20 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S7)) (= (= (f9 (f3 f4 ?v0) ?v1) f10) (or (= ?v0 f11) (not (= (f92 (f93 f94 ?v1) ?v0) f17))))))
(assert (forall ((?v0 S15) (?v1 S12)) (= (= (f18 (f19 f20 ?v0) ?v1) f22) (or (= ?v0 f21) (not (= (f95 (f96 f97 ?v1) ?v0) f17))))))
(assert (forall ((?v0 S17) (?v1 S3)) (= (= (f6 (f23 f24 ?v0) ?v1) f11) (or (= ?v0 f25) (not (= (f98 (f99 f100 ?v1) ?v0) f17))))))
(assert (forall ((?v0 S25) (?v1 S22)) (= (= (f31 (f32 f33 ?v0) ?v1) f35) (or (= ?v0 f34) (not (= (f101 (f102 f103 ?v1) ?v0) f17))))))
(assert (forall ((?v0 S29) (?v1 S26)) (= (= (f36 (f37 f38 ?v0) ?v1) f40) (or (= ?v0 f39) (not (= (f104 (f105 f106 ?v1) ?v0) f17))))))
(assert (forall ((?v0 S26) (?v1 S17)) (= (= (f41 (f42 f43 ?v0) ?v1) f25) (or (= ?v0 f40) (not (= (f107 (f108 f109 ?v1) ?v0) f17))))))
(assert (forall ((?v0 S22) (?v1 S15)) (= (= (f44 (f45 f46 ?v0) ?v1) f21) (or (= ?v0 f35) (not (= (f110 (f111 f112 ?v1) ?v0) f17))))))
(assert (forall ((?v0 S7) (?v1 S3) (?v2 S7) (?v3 S3)) (= (= (f6 (f7 f8 ?v0) ?v1) (f6 (f7 f8 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S11) (?v1 S18) (?v2 S11) (?v3 S18)) (= (= (f26 (f69 f70 ?v0) ?v1) (f26 (f69 f70 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S15) (?v1 S22) (?v2 S15) (?v3 S22)) (= (= (f31 (f67 f68 ?v0) ?v1) (f31 (f67 f68 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S17) (?v1 S26) (?v2 S17) (?v3 S26)) (= (= (f36 (f65 f66 ?v0) ?v1) (f36 (f65 f66 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S17) (?v2 S3) (?v3 S17)) (= (= (f41 (f54 f55 ?v0) ?v1) (f41 (f54 f55 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S12) (?v1 S15) (?v2 S12) (?v3 S15)) (= (= (f44 (f52 f53 ?v0) ?v1) (f44 (f52 f53 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S8) (?v1 S11) (?v2 S8) (?v3 S11)) (= (= (f47 (f50 f51 ?v0) ?v1) (f47 (f50 f51 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S76) (?v1 S3)) (=> (= (f113 ?v0 f11) f1) (=> (forall ((?v2 S7) (?v3 S3)) (=> (= (f113 ?v0 ?v3) f1) (= (f113 ?v0 (f6 (f7 f8 ?v2) ?v3)) f1))) (= (f113 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S77) (?v1 S18)) (=> (= (f114 ?v0 f30) f1) (=> (forall ((?v2 S11) (?v3 S18)) (=> (= (f114 ?v0 ?v3) f1) (= (f114 ?v0 (f26 (f69 f70 ?v2) ?v3)) f1))) (= (f114 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S78) (?v1 S22)) (=> (= (f115 ?v0 f35) f1) (=> (forall ((?v2 S15) (?v3 S22)) (=> (= (f115 ?v0 ?v3) f1) (= (f115 ?v0 (f31 (f67 f68 ?v2) ?v3)) f1))) (= (f115 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S79) (?v1 S26)) (=> (= (f116 ?v0 f40) f1) (=> (forall ((?v2 S17) (?v3 S26)) (=> (= (f116 ?v0 ?v3) f1) (= (f116 ?v0 (f36 (f65 f66 ?v2) ?v3)) f1))) (= (f116 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S80) (?v1 S17)) (=> (= (f117 ?v0 f25) f1) (=> (forall ((?v2 S3) (?v3 S17)) (=> (= (f117 ?v0 ?v3) f1) (= (f117 ?v0 (f41 (f54 f55 ?v2) ?v3)) f1))) (= (f117 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S81) (?v1 S15)) (=> (= (f118 ?v0 f21) f1) (=> (forall ((?v2 S12) (?v3 S15)) (=> (= (f118 ?v0 ?v3) f1) (= (f118 ?v0 (f44 (f52 f53 ?v2) ?v3)) f1))) (= (f118 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S82) (?v1 S11)) (=> (= (f119 ?v0 f16) f1) (=> (forall ((?v2 S8) (?v3 S11)) (=> (= (f119 ?v0 ?v3) f1) (= (f119 ?v0 (f47 (f50 f51 ?v2) ?v3)) f1))) (= (f119 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S8)) (= (= f17 ?v0) (= ?v0 f17))))
(assert (forall ((?v0 S12)) (= (= f22 ?v0) (= ?v0 f22))))
(assert (forall ((?v0 S3)) (= (= f11 ?v0) (= ?v0 f11))))
(assert (forall ((?v0 S7)) (= (= f10 ?v0) (= ?v0 f10))))
(assert (forall ((?v0 S18)) (= (= f30 ?v0) (= ?v0 f30))))
(assert (forall ((?v0 S22)) (= (= f35 ?v0) (= ?v0 f35))))
(assert (forall ((?v0 S26)) (= (= f40 ?v0) (= ?v0 f40))))
(assert (forall ((?v0 S17)) (= (= f25 ?v0) (= ?v0 f25))))
(assert (forall ((?v0 S15)) (= (= f21 ?v0) (= ?v0 f21))))
(assert (forall ((?v0 S11)) (= (= f16 ?v0) (= ?v0 f16))))
(assert (forall ((?v0 S4)) (= (= (f12 ?v0) f1) (forall ((?v1 S7) (?v2 S7)) (= (f9 ?v0 ?v1) (f9 ?v0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S7)) (= (= (f71 (f72 f73 ?v0) ?v1) f11) (= ?v0 f11))))
(assert (forall ((?v0 S18) (?v1 S11)) (= (= (f74 (f75 f76 ?v0) ?v1) f30) (= ?v0 f30))))
(assert (forall ((?v0 S22) (?v1 S15)) (= (= (f77 (f78 f79 ?v0) ?v1) f35) (= ?v0 f35))))
(assert (forall ((?v0 S26) (?v1 S17)) (= (= (f80 (f81 f82 ?v0) ?v1) f40) (= ?v0 f40))))
(assert (forall ((?v0 S17) (?v1 S3)) (= (= (f83 (f84 f85 ?v0) ?v1) f25) (= ?v0 f25))))
(assert (forall ((?v0 S15) (?v1 S12)) (= (= (f86 (f87 f88 ?v0) ?v1) f21) (= ?v0 f21))))
(assert (forall ((?v0 S11) (?v1 S8)) (= (= (f89 (f90 f91 ?v0) ?v1) f16) (= ?v0 f16))))
(assert (forall ((?v0 S7)) (= (f71 (f72 f73 f11) ?v0) f11)))
(assert (forall ((?v0 S11)) (= (f74 (f75 f76 f30) ?v0) f30)))
(assert (forall ((?v0 S15)) (= (f77 (f78 f79 f35) ?v0) f35)))
(assert (forall ((?v0 S17)) (= (f80 (f81 f82 f40) ?v0) f40)))
(assert (forall ((?v0 S3)) (= (f83 (f84 f85 f25) ?v0) f25)))
(assert (forall ((?v0 S12)) (= (f86 (f87 f88 f21) ?v0) f21)))
(assert (forall ((?v0 S8)) (= (f89 (f90 f91 f16) ?v0) f16)))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S7) (?v2 S3)) (=> (= ?v0 (f6 (f7 f8 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S18)) (=> (forall ((?v1 S11) (?v2 S18)) (=> (= ?v0 (f26 (f69 f70 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S22)) (=> (forall ((?v1 S15) (?v2 S22)) (=> (= ?v0 (f31 (f67 f68 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S17) (?v2 S26)) (=> (= ?v0 (f36 (f65 f66 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S17)) (=> (forall ((?v1 S3) (?v2 S17)) (=> (= ?v0 (f41 (f54 f55 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S15)) (=> (forall ((?v1 S12) (?v2 S15)) (=> (= ?v0 (f44 (f52 f53 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S11)) (=> (forall ((?v1 S8) (?v2 S11)) (=> (= ?v0 (f47 (f50 f51 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S3)) (= (= (f92 f120 ?v0) f17) (= ?v0 f11))))
(assert (forall ((?v0 S18)) (= (= (f121 f122 ?v0) f17) (= ?v0 f30))))
(assert (forall ((?v0 S22)) (= (= (f110 f123 ?v0) f17) (= ?v0 f35))))
(assert (forall ((?v0 S26)) (= (= (f107 f124 ?v0) f17) (= ?v0 f40))))
(assert (forall ((?v0 S17)) (= (= (f98 f125 ?v0) f17) (= ?v0 f25))))
(assert (forall ((?v0 S15)) (= (= (f95 f126 ?v0) f17) (= ?v0 f21))))
(assert (forall ((?v0 S11)) (= (= (f127 f128 ?v0) f17) (= ?v0 f16))))
(assert (forall ((?v0 S7) (?v1 S3) (?v2 S7)) (= (f71 (f72 f129 (f6 (f7 f8 ?v0) ?v1)) ?v2) (f6 (f7 f8 (f9 (f3 f4 ?v1) ?v2)) (f71 (f72 f129 ?v1) ?v2)))))
(assert (forall ((?v0 S15) (?v1 S22) (?v2 S15)) (= (f77 (f78 f130 (f31 (f67 f68 ?v0) ?v1)) ?v2) (f31 (f67 f68 (f44 (f45 f46 ?v1) ?v2)) (f77 (f78 f130 ?v1) ?v2)))))
(assert (forall ((?v0 S17) (?v1 S26) (?v2 S17)) (= (f80 (f81 f131 (f36 (f65 f66 ?v0) ?v1)) ?v2) (f36 (f65 f66 (f41 (f42 f43 ?v1) ?v2)) (f80 (f81 f131 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S18) (?v2 S11)) (= (f74 (f75 f132 (f26 (f69 f70 ?v0) ?v1)) ?v2) (f26 (f69 f70 (f47 (f48 f49 ?v1) ?v2)) (f74 (f75 f132 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S11) (?v2 S8)) (= (f89 (f90 f133 (f47 (f50 f51 ?v0) ?v1)) ?v2) (f47 (f50 f51 (f13 (f14 f15 ?v1) ?v2)) (f89 (f90 f133 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S17) (?v2 S3)) (= (f83 (f84 f134 (f41 (f54 f55 ?v0) ?v1)) ?v2) (f41 (f54 f55 (f6 (f23 f24 ?v1) ?v2)) (f83 (f84 f134 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S15) (?v2 S12)) (= (f86 (f87 f135 (f44 (f52 f53 ?v0) ?v1)) ?v2) (f44 (f52 f53 (f18 (f19 f20 ?v1) ?v2)) (f86 (f87 f135 ?v1) ?v2)))))
(assert (forall ((?v0 S7)) (= (f138 (f136 f137 ?v0) f17) (f6 (f7 f8 ?v0) f11))))
(assert (forall ((?v0 S11)) (= (f141 (f139 f140 ?v0) f17) (f26 (f69 f70 ?v0) f30))))
(assert (forall ((?v0 S15)) (= (f144 (f142 f143 ?v0) f17) (f31 (f67 f68 ?v0) f35))))
(assert (forall ((?v0 S17)) (= (f147 (f145 f146 ?v0) f17) (f36 (f65 f66 ?v0) f40))))
(assert (forall ((?v0 S3)) (= (f150 (f148 f149 ?v0) f17) (f41 (f54 f55 ?v0) f25))))
(assert (forall ((?v0 S12)) (= (f153 (f151 f152 ?v0) f17) (f44 (f52 f53 ?v0) f21))))
(assert (forall ((?v0 S8)) (= (f89 (f154 f155 ?v0) f17) (f47 (f50 f51 ?v0) f16))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7)) (= (f9 (f3 f4 (f6 (f156 f157 ?v0) ?v1)) ?v2) (f9 (f3 f4 ?v0) (f9 (f3 f4 ?v1) ?v2)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S15)) (= (f44 (f45 f46 (f31 (f158 f159 ?v0) ?v1)) ?v2) (f44 (f45 f46 ?v0) (f44 (f45 f46 ?v1) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S17)) (= (f41 (f42 f43 (f36 (f160 f161 ?v0) ?v1)) ?v2) (f41 (f42 f43 ?v0) (f41 (f42 f43 ?v1) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S11)) (= (f47 (f48 f49 (f26 (f162 f163 ?v0) ?v1)) ?v2) (f47 (f48 f49 ?v0) (f47 (f48 f49 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S8)) (= (f13 (f14 f15 (f47 (f164 f165 ?v0) ?v1)) ?v2) (f13 (f14 f15 ?v0) (f13 (f14 f15 ?v1) ?v2)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S3)) (= (f6 (f23 f24 (f41 (f166 f167 ?v0) ?v1)) ?v2) (f6 (f23 f24 ?v0) (f6 (f23 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S12)) (= (f18 (f19 f20 (f44 (f168 f169 ?v0) ?v1)) ?v2) (f18 (f19 f20 ?v0) (f18 (f19 f20 ?v1) ?v2)))))
(assert (forall ((?v0 S7)) (= (f92 f170 (f6 (f7 f8 ?v0) f11)) f17)))
(assert (forall ((?v0 S11)) (= (f121 f171 (f26 (f69 f70 ?v0) f30)) f17)))
(assert (forall ((?v0 S15)) (= (f110 f172 (f31 (f67 f68 ?v0) f35)) f17)))
(assert (forall ((?v0 S17)) (= (f107 f173 (f36 (f65 f66 ?v0) f40)) f17)))
(assert (forall ((?v0 S3)) (= (f98 f174 (f41 (f54 f55 ?v0) f25)) f17)))
(assert (forall ((?v0 S12)) (= (f95 f175 (f44 (f52 f53 ?v0) f21)) f17)))
(assert (forall ((?v0 S8)) (= (f127 f176 (f47 (f50 f51 ?v0) f16)) f17)))
(assert (forall ((?v0 S3)) (= (f6 (f156 f157 f11) ?v0) f11)))
(assert (forall ((?v0 S18)) (= (f26 (f162 f163 f30) ?v0) f30)))
(assert (forall ((?v0 S22)) (= (f31 (f158 f159 f35) ?v0) f35)))
(assert (forall ((?v0 S26)) (= (f36 (f160 f161 f40) ?v0) f40)))
(assert (forall ((?v0 S17)) (= (f41 (f166 f167 f25) ?v0) f25)))
(assert (forall ((?v0 S15)) (= (f44 (f168 f169 f21) ?v0) f21)))
(assert (forall ((?v0 S11)) (= (f47 (f164 f165 f16) ?v0) f16)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f89 (f154 f155 ?v0) ?v1) f16) (= ?v0 f17))))
(assert (forall ((?v0 S12) (?v1 S8)) (= (= (f153 (f151 f152 ?v0) ?v1) f21) (= ?v0 f22))))
(assert (forall ((?v0 S3) (?v1 S8)) (= (= (f150 (f148 f149 ?v0) ?v1) f25) (= ?v0 f11))))
(assert (forall ((?v0 S7) (?v1 S8)) (= (= (f138 (f136 f137 ?v0) ?v1) f11) (= ?v0 f10))))
(assert (forall ((?v0 S18) (?v1 S8)) (= (= (f177 (f178 f179 ?v0) ?v1) f29) (= ?v0 f30))))
(assert (forall ((?v0 S22) (?v1 S8)) (= (= (f180 (f181 f182 ?v0) ?v1) f34) (= ?v0 f35))))
(assert (forall ((?v0 S26) (?v1 S8)) (= (= (f183 (f184 f185 ?v0) ?v1) f39) (= ?v0 f40))))
(assert (forall ((?v0 S17) (?v1 S8)) (= (= (f147 (f145 f146 ?v0) ?v1) f40) (= ?v0 f25))))
(assert (forall ((?v0 S15) (?v1 S8)) (= (= (f144 (f142 f143 ?v0) ?v1) f35) (= ?v0 f21))))
(assert (forall ((?v0 S11) (?v1 S8)) (= (= (f141 (f139 f140 ?v0) ?v1) f30) (= ?v0 f16))))
(assert (forall ((?v0 S8)) (= (f138 (f136 f137 f10) ?v0) f11)))
(assert (forall ((?v0 S8)) (= (f89 (f154 f155 f17) ?v0) f16)))
(assert (forall ((?v0 S8)) (= (f153 (f151 f152 f22) ?v0) f21)))
(assert (forall ((?v0 S8)) (= (f150 (f148 f149 f11) ?v0) f25)))
(assert (forall ((?v0 S8)) (= (f177 (f178 f179 f30) ?v0) f29)))
(assert (forall ((?v0 S8)) (= (f180 (f181 f182 f35) ?v0) f34)))
(assert (forall ((?v0 S8)) (= (f183 (f184 f185 f40) ?v0) f39)))
(assert (forall ((?v0 S8)) (= (f147 (f145 f146 f25) ?v0) f40)))
(assert (forall ((?v0 S8)) (= (f144 (f142 f143 f21) ?v0) f35)))
(assert (forall ((?v0 S8)) (= (f141 (f139 f140 f16) ?v0) f30)))
(assert (forall ((?v0 S8) (?v1 S11)) (= (= (f119 (f186 (f47 (f50 f51 ?v0) ?v1)) f16) f1) (and (= (f187 ?v0 f17) f1) (= (f119 (f186 ?v1) f16) f1)))))
(assert (forall ((?v0 S12) (?v1 S15)) (= (= (f118 (f188 (f44 (f52 f53 ?v0) ?v1)) f21) f1) (and (= (f189 ?v0 f22) f1) (= (f118 (f188 ?v1) f21) f1)))))
(assert (forall ((?v0 S18) (?v1 S21)) (= (= (f190 (f56 (f57 f58 ?v0) ?v1) f29) f1) (and (= (f114 (f191 ?v0) f30) f1) (= (f190 ?v1 f29) f1)))))
(assert (forall ((?v0 S22) (?v1 S25)) (= (= (f192 (f59 (f60 f61 ?v0) ?v1) f34) f1) (and (= (f115 (f193 ?v0) f35) f1) (= (f192 ?v1 f34) f1)))))
(assert (forall ((?v0 S15) (?v1 S22)) (= (= (f115 (f193 (f31 (f67 f68 ?v0) ?v1)) f35) f1) (and (= (f118 (f188 ?v0) f21) f1) (= (f115 (f193 ?v1) f35) f1)))))
(assert (forall ((?v0 S11) (?v1 S18)) (= (= (f114 (f191 (f26 (f69 f70 ?v0) ?v1)) f30) f1) (and (= (f119 (f186 ?v0) f16) f1) (= (f114 (f191 ?v1) f30) f1)))))
(assert (forall ((?v0 S8) (?v1 S11)) (let ((?v_0 (f186 f16))) (= (= (f119 ?v_0 (f47 (f50 f51 ?v0) ?v1)) f1) (and (= (f187 f17 ?v0) f1) (= (f119 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S15)) (let ((?v_0 (f188 f21))) (= (= (f118 ?v_0 (f44 (f52 f53 ?v0) ?v1)) f1) (and (= (f189 f22 ?v0) f1) (= (f118 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S18) (?v1 S21)) (= (= (f190 f29 (f56 (f57 f58 ?v0) ?v1)) f1) (and (= (f114 (f191 f30) ?v0) f1) (= (f190 f29 ?v1) f1)))))
(assert (forall ((?v0 S22) (?v1 S25)) (= (= (f192 f34 (f59 (f60 f61 ?v0) ?v1)) f1) (and (= (f115 (f193 f35) ?v0) f1) (= (f192 f34 ?v1) f1)))))
(assert (forall ((?v0 S15) (?v1 S22)) (let ((?v_0 (f193 f35))) (= (= (f115 ?v_0 (f31 (f67 f68 ?v0) ?v1)) f1) (and (= (f118 (f188 f21) ?v0) f1) (= (f115 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S11) (?v1 S18)) (let ((?v_0 (f191 f30))) (= (= (f114 ?v_0 (f26 (f69 f70 ?v0) ?v1)) f1) (and (= (f119 (f186 f16) ?v0) f1) (= (f114 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (= (f114 (f191 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S22) (?v1 S22)) (= (= (f115 (f193 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (= (f118 (f188 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f119 (f186 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S11) (?v1 S8) (?v2 S11)) (= (= (f141 (f139 f140 ?v0) ?v1) (f141 (f139 f140 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S15) (?v1 S8) (?v2 S15)) (= (= (f144 (f142 f143 ?v0) ?v1) (f144 (f142 f143 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S17) (?v1 S8) (?v2 S17)) (= (= (f147 (f145 f146 ?v0) ?v1) (f147 (f145 f146 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S7) (?v1 S8) (?v2 S7)) (= (= (f138 (f136 f137 ?v0) ?v1) (f138 (f136 f137 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S3)) (= (= (f150 (f148 f149 ?v0) ?v1) (f150 (f148 f149 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S12) (?v1 S8) (?v2 S12)) (= (= (f153 (f151 f152 ?v0) ?v1) (f153 (f151 f152 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (= (f89 (f154 f155 ?v0) ?v1) (f89 (f154 f155 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (not (= ?v0 f17)) (= (f127 f176 (f89 (f154 f155 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S12) (?v1 S8)) (=> (not (= ?v0 f22)) (= (f95 f175 (f153 (f151 f152 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S8)) (=> (not (= ?v0 f11)) (= (f98 f174 (f150 (f148 f149 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S7) (?v1 S8)) (=> (not (= ?v0 f10)) (= (f92 f170 (f138 (f136 f137 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S18) (?v1 S8)) (=> (not (= ?v0 f30)) (= (f194 f195 (f177 (f178 f179 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S22) (?v1 S8)) (=> (not (= ?v0 f35)) (= (f101 f196 (f180 (f181 f182 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S26) (?v1 S8)) (=> (not (= ?v0 f40)) (= (f104 f197 (f183 (f184 f185 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S17) (?v1 S8)) (=> (not (= ?v0 f25)) (= (f107 f173 (f147 (f145 f146 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S15) (?v1 S8)) (=> (not (= ?v0 f21)) (= (f110 f172 (f144 (f142 f143 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S11) (?v1 S8)) (=> (not (= ?v0 f16)) (= (f121 f171 (f141 (f139 f140 ?v0) ?v1)) ?v1))))
(check-sat)
(exit)