(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unsat)
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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () S1)
(declare-fun f4 () S3)
(declare-fun f5 (S4 S3) S3)
(declare-fun f6 (S5 S2) S4)
(declare-fun f7 () S5)
(declare-fun f8 () S3)
(declare-fun f9 () S2)
(declare-fun f10 (S6 S3) S7)
(declare-fun f11 () S6)
(declare-fun f12 () S7)
(declare-fun f13 (S8 S9) S9)
(declare-fun f14 (S10 S11) S8)
(declare-fun f15 () S10)
(declare-fun f16 () S11)
(declare-fun f17 () S9)
(declare-fun f18 (S12 S13) S13)
(declare-fun f19 (S14 S7) S12)
(declare-fun f20 () S14)
(declare-fun f21 () S13)
(declare-fun f22 (S15 S16) S16)
(declare-fun f23 (S17 S3) S15)
(declare-fun f24 () S17)
(declare-fun f25 () S16)
(declare-fun f26 (S18 S19) S19)
(declare-fun f27 (S20 S21) S18)
(declare-fun f28 () S20)
(declare-fun f29 () S21)
(declare-fun f30 () S19)
(declare-fun f31 (S22 S23) S23)
(declare-fun f32 (S24 S25) S22)
(declare-fun f33 () S24)
(declare-fun f34 () S25)
(declare-fun f35 () S23)
(declare-fun f36 (S26 S27) S27)
(declare-fun f37 (S28 S29) S26)
(declare-fun f38 () S28)
(declare-fun f39 () S29)
(declare-fun f40 () S27)
(declare-fun f41 (S30 S29) S29)
(declare-fun f42 (S31 S16) S30)
(declare-fun f43 () S31)
(declare-fun f44 (S32 S25) S25)
(declare-fun f45 (S33 S13) S32)
(declare-fun f46 () S33)
(declare-fun f47 (S34 S21) S21)
(declare-fun f48 (S35 S9) S34)
(declare-fun f49 () S35)
(declare-fun f50 (S36 S2) S3)
(declare-fun f51 (S37 S3) S36)
(declare-fun f52 () S37)
(declare-fun f53 (S38 S9) S21)
(declare-fun f54 (S39 S21) S38)
(declare-fun f55 () S39)
(declare-fun f56 (S40 S13) S25)
(declare-fun f57 (S41 S25) S40)
(declare-fun f58 () S41)
(declare-fun f59 (S42 S16) S29)
(declare-fun f60 (S43 S29) S42)
(declare-fun f61 () S43)
(declare-fun f62 (S44 S3) S16)
(declare-fun f63 (S45 S16) S44)
(declare-fun f64 () S45)
(declare-fun f65 (S46 S7) S13)
(declare-fun f66 (S47 S13) S46)
(declare-fun f67 () S47)
(declare-fun f68 (S48 S11) S9)
(declare-fun f69 (S49 S9) S48)
(declare-fun f70 () S49)
(declare-fun f71 (S50 S3) S1)
(declare-fun f72 (S51 S21) S1)
(declare-fun f73 (S52 S25) S1)
(declare-fun f74 (S53 S29) S1)
(declare-fun f75 (S54 S16) S1)
(declare-fun f76 (S55 S13) S1)
(declare-fun f77 (S56 S9) S1)
(declare-fun f78 (S57 S2) S2)
(declare-fun f79 (S58 S3) S57)
(declare-fun f80 () S58)
(declare-fun f81 (S59 S21) S7)
(declare-fun f82 () S59)
(declare-fun f83 (S60 S25) S7)
(declare-fun f84 () S60)
(declare-fun f85 (S61 S29) S7)
(declare-fun f86 () S61)
(declare-fun f87 (S62 S16) S7)
(declare-fun f88 () S62)
(declare-fun f89 (S63 S13) S7)
(declare-fun f90 () S63)
(declare-fun f91 (S64 S9) S7)
(declare-fun f92 () S64)
(declare-fun f93 (S65 S9) S66)
(declare-fun f94 () S65)
(declare-fun f95 (S67 S21) S8)
(declare-fun f96 () S67)
(declare-fun f97 (S68 S25) S12)
(declare-fun f98 () S68)
(declare-fun f99 (S69 S29) S15)
(declare-fun f100 () S69)
(declare-fun f101 (S70 S16) S4)
(declare-fun f102 () S70)
(declare-fun f103 (S71 S7) S7)
(declare-fun f104 (S72 S13) S71)
(declare-fun f105 () S72)
(declare-fun f106 (S66 S11) S11)
(declare-fun f107 (S73 S9) S59)
(declare-fun f108 () S73)
(declare-fun f109 (S74 S16) S61)
(declare-fun f110 () S74)
(declare-fun f111 (S75 S3) S62)
(declare-fun f112 () S75)
(declare-fun f113 (S76 S11) S64)
(declare-fun f114 () S76)
(declare-fun f115 (S77 S2) S6)
(declare-fun f116 () S77)
(declare-fun f117 () S49)
(declare-fun f118 () S47)
(declare-fun f119 () S45)
(declare-fun f120 () S37)
(declare-fun f121 () S64)
(declare-fun f122 () S63)
(declare-fun f123 () S62)
(declare-fun f124 () S6)
(declare-fun f125 () S71)
(declare-fun f126 (S57) S1)
(declare-fun f127 (S78 S11) S79)
(declare-fun f128 () S78)
(declare-fun f129 (S79 S7) S9)
(declare-fun f130 (S80 S7) S46)
(declare-fun f131 () S80)
(declare-fun f132 (S81 S3) S82)
(declare-fun f133 () S81)
(declare-fun f134 (S82 S7) S16)
(declare-fun f135 (S83 S2) S84)
(declare-fun f136 () S83)
(declare-fun f137 (S84 S7) S3)
(declare-fun f138 () S3)
(declare-fun f139 (S3) S50)
(declare-fun f140 (S85 S3) S84)
(declare-fun f141 () S85)
(declare-fun f142 (S86 S21) S79)
(declare-fun f143 () S86)
(declare-fun f144 (S87 S25) S46)
(declare-fun f145 () S87)
(declare-fun f146 (S88 S29) S82)
(declare-fun f147 () S88)
(declare-fun f148 (S89 S16) S84)
(declare-fun f149 () S89)
(declare-fun f150 () S72)
(declare-fun f151 (S90 S7) S11)
(declare-fun f152 (S91 S9) S90)
(declare-fun f153 () S91)
(declare-fun f154 (S92 S7) S2)
(declare-fun f155 (S93 S3) S92)
(declare-fun f156 () S93)
(declare-fun f157 (S9) S56)
(declare-fun f158 (S16) S54)
(declare-fun f159 (S94 S9) S79)
(declare-fun f160 () S94)
(declare-fun f161 (S95 S11) S90)
(declare-fun f162 () S95)
(declare-fun f163 (S96 S7) S25)
(declare-fun f164 (S97 S25) S96)
(declare-fun f165 () S97)
(declare-fun f166 () S47)
(declare-fun f167 (S98 S7) S29)
(declare-fun f168 (S99 S29) S98)
(declare-fun f169 () S99)
(declare-fun f170 (S100 S16) S82)
(declare-fun f171 () S100)
(declare-fun f172 (S101 S7) S71)
(declare-fun f173 () S101)
(declare-fun f174 (S102 S2) S92)
(declare-fun f175 () S102)
(declare-fun f176 (S103 S7) S21)
(declare-fun f177 (S104 S9) S103)
(declare-fun f178 () S104)
(declare-fun f179 (S105 S13) S96)
(declare-fun f180 () S105)
(declare-fun f181 (S106 S16) S98)
(declare-fun f182 () S106)
(declare-fun f183 (S13) S55)
(declare-fun f184 (S2 S2) S1)
(declare-fun f185 (S11 S11) S1)
(declare-fun f186 (S107 S7) S1)
(declare-fun f187 (S7) S107)
(assert (not (= f1 f2)))
(assert (not (= f3 f1)))
(assert (forall ((?v0 S2)) (=> (= f4 (f5 (f6 f7 ?v0) f8)) (=> (not (= ?v0 f9)) (= f3 f1)))))
(assert (= (f10 f11 f4) f12))
(assert (not (= f4 f8)))
(assert (= (f10 f11 f4) f12))
(assert (not (= f4 f8)))
(assert (= (f5 (f6 f7 f9) f8) f8))
(assert (= (f13 (f14 f15 f16) f17) f17))
(assert (= (f18 (f19 f20 f12) f21) f21))
(assert (= (f22 (f23 f24 f8) f25) f25))
(assert (= (f26 (f27 f28 f29) f30) f30))
(assert (= (f31 (f32 f33 f34) f35) f35))
(assert (= (f36 (f37 f38 f39) f40) f40))
(assert (= (f41 (f42 f43 f25) f39) f39))
(assert (= (f44 (f45 f46 f21) f34) f34))
(assert (= (f47 (f48 f49 f17) f29) f29))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f5 (f6 f7 ?v0) ?v1) f8) (and (= ?v0 f9) (= ?v1 f8)))))
(assert (forall ((?v0 S11) (?v1 S9)) (= (= (f13 (f14 f15 ?v0) ?v1) f17) (and (= ?v0 f16) (= ?v1 f17)))))
(assert (forall ((?v0 S7) (?v1 S13)) (= (= (f18 (f19 f20 ?v0) ?v1) f21) (and (= ?v0 f12) (= ?v1 f21)))))
(assert (forall ((?v0 S3) (?v1 S16)) (= (= (f22 (f23 f24 ?v0) ?v1) f25) (and (= ?v0 f8) (= ?v1 f25)))))
(assert (forall ((?v0 S21) (?v1 S19)) (= (= (f26 (f27 f28 ?v0) ?v1) f30) (and (= ?v0 f29) (= ?v1 f30)))))
(assert (forall ((?v0 S25) (?v1 S23)) (= (= (f31 (f32 f33 ?v0) ?v1) f35) (and (= ?v0 f34) (= ?v1 f35)))))
(assert (forall ((?v0 S29) (?v1 S27)) (= (= (f36 (f37 f38 ?v0) ?v1) f40) (and (= ?v0 f39) (= ?v1 f40)))))
(assert (forall ((?v0 S16) (?v1 S29)) (= (= (f41 (f42 f43 ?v0) ?v1) f39) (and (= ?v0 f25) (= ?v1 f39)))))
(assert (forall ((?v0 S13) (?v1 S25)) (= (= (f44 (f45 f46 ?v0) ?v1) f34) (and (= ?v0 f21) (= ?v1 f34)))))
(assert (forall ((?v0 S9) (?v1 S21)) (= (= (f47 (f48 f49 ?v0) ?v1) f29) (and (= ?v0 f17) (= ?v1 f29)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f5 (f6 f7 ?v0) f8))) (= (f50 (f51 f52 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_0 (f47 (f48 f49 ?v0) f29))) (= (f53 (f54 f55 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f44 (f45 f46 ?v0) f34))) (= (f56 (f57 f58 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S16) (?v1 S16)) (let ((?v_0 (f41 (f42 f43 ?v0) f39))) (= (f59 (f60 f61 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f22 (f23 f24 ?v0) f25))) (= (f62 (f63 f64 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f18 (f19 f20 ?v0) f21))) (= (f65 (f66 f67 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f13 (f14 f15 ?v0) f17))) (= (f68 (f69 f70 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S3)) (= (= (f5 (f6 f7 ?v0) ?v1) (f5 (f6 f7 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S9) (?v1 S21) (?v2 S9) (?v3 S21)) (= (= (f47 (f48 f49 ?v0) ?v1) (f47 (f48 f49 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S13) (?v1 S25) (?v2 S13) (?v3 S25)) (= (= (f44 (f45 f46 ?v0) ?v1) (f44 (f45 f46 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S16) (?v1 S29) (?v2 S16) (?v3 S29)) (= (= (f41 (f42 f43 ?v0) ?v1) (f41 (f42 f43 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S16) (?v2 S3) (?v3 S16)) (= (= (f22 (f23 f24 ?v0) ?v1) (f22 (f23 f24 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S7) (?v1 S13) (?v2 S7) (?v3 S13)) (= (= (f18 (f19 f20 ?v0) ?v1) (f18 (f19 f20 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S11) (?v1 S9) (?v2 S11) (?v3 S9)) (= (= (f13 (f14 f15 ?v0) ?v1) (f13 (f14 f15 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S50) (?v1 S3)) (=> (= (f71 ?v0 f8) f1) (=> (forall ((?v2 S2) (?v3 S3)) (=> (= (f71 ?v0 ?v3) f1) (= (f71 ?v0 (f5 (f6 f7 ?v2) ?v3)) f1))) (= (f71 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S51) (?v1 S21)) (=> (= (f72 ?v0 f29) f1) (=> (forall ((?v2 S9) (?v3 S21)) (=> (= (f72 ?v0 ?v3) f1) (= (f72 ?v0 (f47 (f48 f49 ?v2) ?v3)) f1))) (= (f72 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S52) (?v1 S25)) (=> (= (f73 ?v0 f34) f1) (=> (forall ((?v2 S13) (?v3 S25)) (=> (= (f73 ?v0 ?v3) f1) (= (f73 ?v0 (f44 (f45 f46 ?v2) ?v3)) f1))) (= (f73 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S53) (?v1 S29)) (=> (= (f74 ?v0 f39) f1) (=> (forall ((?v2 S16) (?v3 S29)) (=> (= (f74 ?v0 ?v3) f1) (= (f74 ?v0 (f41 (f42 f43 ?v2) ?v3)) f1))) (= (f74 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S54) (?v1 S16)) (=> (= (f75 ?v0 f25) f1) (=> (forall ((?v2 S3) (?v3 S16)) (=> (= (f75 ?v0 ?v3) f1) (= (f75 ?v0 (f22 (f23 f24 ?v2) ?v3)) f1))) (= (f75 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S55) (?v1 S13)) (=> (= (f76 ?v0 f21) f1) (=> (forall ((?v2 S7) (?v3 S13)) (=> (= (f76 ?v0 ?v3) f1) (= (f76 ?v0 (f18 (f19 f20 ?v2) ?v3)) f1))) (= (f76 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S56) (?v1 S9)) (=> (= (f77 ?v0 f17) f1) (=> (forall ((?v2 S11) (?v3 S9)) (=> (= (f77 ?v0 ?v3) f1) (= (f77 ?v0 (f13 (f14 f15 ?v2) ?v3)) f1))) (= (f77 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S11)) (= (= f16 ?v0) (= ?v0 f16))))
(assert (forall ((?v0 S7)) (= (= f12 ?v0) (= ?v0 f12))))
(assert (forall ((?v0 S2)) (= (= f9 ?v0) (= ?v0 f9))))
(assert (forall ((?v0 S3)) (= (= f8 ?v0) (= ?v0 f8))))
(assert (forall ((?v0 S21)) (= (= f29 ?v0) (= ?v0 f29))))
(assert (forall ((?v0 S25)) (= (= f34 ?v0) (= ?v0 f34))))
(assert (forall ((?v0 S29)) (= (= f39 ?v0) (= ?v0 f39))))
(assert (forall ((?v0 S16)) (= (= f25 ?v0) (= ?v0 f25))))
(assert (forall ((?v0 S13)) (= (= f21 ?v0) (= ?v0 f21))))
(assert (forall ((?v0 S9)) (= (= f17 ?v0) (= ?v0 f17))))
(assert (forall ((?v0 S3)) (=> (not (exists ((?v1 S2) (?v2 S3)) (and (not (= ?v1 f9)) (and (= ?v2 f8) (= ?v0 (f5 (f6 f7 ?v1) ?v2)))))) (exists ((?v1 S2)) (= (f78 (f79 f80 ?v0) ?v1) f9)))))
(assert (forall ((?v0 S2)) (= (f10 f11 (f5 (f6 f7 ?v0) f8)) f12)))
(assert (forall ((?v0 S9)) (= (f81 f82 (f47 (f48 f49 ?v0) f29)) f12)))
(assert (forall ((?v0 S13)) (= (f83 f84 (f44 (f45 f46 ?v0) f34)) f12)))
(assert (forall ((?v0 S16)) (= (f85 f86 (f41 (f42 f43 ?v0) f39)) f12)))
(assert (forall ((?v0 S3)) (= (f87 f88 (f22 (f23 f24 ?v0) f25)) f12)))
(assert (forall ((?v0 S7)) (= (f89 f90 (f18 (f19 f20 ?v0) f21)) f12)))
(assert (forall ((?v0 S11)) (= (f91 f92 (f13 (f14 f15 ?v0) f17)) f12)))
(assert (forall ((?v0 S2)) (= (f50 (f51 f52 f8) ?v0) f8)))
(assert (forall ((?v0 S9)) (= (f53 (f54 f55 f29) ?v0) f29)))
(assert (forall ((?v0 S13)) (= (f56 (f57 f58 f34) ?v0) f34)))
(assert (forall ((?v0 S16)) (= (f59 (f60 f61 f39) ?v0) f39)))
(assert (forall ((?v0 S3)) (= (f62 (f63 f64 f25) ?v0) f25)))
(assert (forall ((?v0 S7)) (= (f65 (f66 f67 f21) ?v0) f21)))
(assert (forall ((?v0 S11)) (= (f68 (f69 f70 f17) ?v0) f17)))
(assert (forall ((?v0 S9) (?v1 S11)) (= (= (f68 (f69 f70 ?v0) ?v1) f17) (= ?v0 f17))))
(assert (forall ((?v0 S13) (?v1 S7)) (= (= (f65 (f66 f67 ?v0) ?v1) f21) (= ?v0 f21))))
(assert (forall ((?v0 S16) (?v1 S3)) (= (= (f62 (f63 f64 ?v0) ?v1) f25) (= ?v0 f25))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (= (f50 (f51 f52 ?v0) ?v1) f8) (= ?v0 f8))))
(assert (forall ((?v0 S9) (?v1 S11)) (= (f91 f92 (f68 (f69 f70 ?v0) ?v1)) (f91 f92 ?v0))))
(assert (forall ((?v0 S13) (?v1 S7)) (= (f89 f90 (f65 (f66 f67 ?v0) ?v1)) (f89 f90 ?v0))))
(assert (forall ((?v0 S16) (?v1 S3)) (= (f87 f88 (f62 (f63 f64 ?v0) ?v1)) (f87 f88 ?v0))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f10 f11 (f50 (f51 f52 ?v0) ?v1)) (f10 f11 ?v0))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f93 f94 ?v0) (f93 f94 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f79 f80 ?v0) (f79 f80 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9)) (= (= (f93 f94 ?v0) (f93 f94 f17)) (= ?v0 f17))))
(assert (forall ((?v0 S3)) (= (= (f79 f80 ?v0) (f79 f80 f8)) (= ?v0 f8))))
(assert (= (f91 f92 f17) f12))
(assert (= (f89 f90 f21) f12))
(assert (= (f87 f88 f25) f12))
(assert (= (f10 f11 f8) f12))
(assert (forall ((?v0 S9)) (= (f13 (f95 f96 f29) ?v0) f17)))
(assert (forall ((?v0 S13)) (= (f18 (f97 f98 f34) ?v0) f21)))
(assert (forall ((?v0 S16)) (= (f22 (f99 f100 f39) ?v0) f25)))
(assert (forall ((?v0 S3)) (= (f5 (f101 f102 f25) ?v0) f8)))
(assert (forall ((?v0 S7)) (= (f103 (f104 f105 f21) ?v0) f12)))
(assert (forall ((?v0 S11)) (= (f106 (f93 f94 f17) ?v0) f16)))
(assert (forall ((?v0 S2)) (= (f78 (f79 f80 f8) ?v0) f9)))
(assert (forall ((?v0 S21) (?v1 S9)) (= (= (f13 (f95 f96 ?v0) ?v1) f17) (or (= ?v0 f29) (not (= (f81 (f107 f108 ?v1) ?v0) f12))))))
(assert (forall ((?v0 S29) (?v1 S16)) (= (= (f22 (f99 f100 ?v0) ?v1) f25) (or (= ?v0 f39) (not (= (f85 (f109 f110 ?v1) ?v0) f12))))))
(assert (forall ((?v0 S16) (?v1 S3)) (= (= (f5 (f101 f102 ?v0) ?v1) f8) (or (= ?v0 f25) (not (= (f87 (f111 f112 ?v1) ?v0) f12))))))
(assert (forall ((?v0 S9) (?v1 S11)) (= (= (f106 (f93 f94 ?v0) ?v1) f16) (or (= ?v0 f17) (not (= (f91 (f113 f114 ?v1) ?v0) f12))))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (= (f78 (f79 f80 ?v0) ?v1) f9) (or (= ?v0 f8) (not (= (f10 (f115 f116 ?v1) ?v0) f12))))))
(assert (forall ((?v0 S9) (?v1 S11)) (= (= (f68 (f69 f117 ?v0) ?v1) f17) (= (f91 f92 ?v0) f12))))
(assert (forall ((?v0 S13) (?v1 S7)) (= (= (f65 (f66 f118 ?v0) ?v1) f21) (= (f89 f90 ?v0) f12))))
(assert (forall ((?v0 S16) (?v1 S3)) (= (= (f62 (f63 f119 ?v0) ?v1) f25) (= (f87 f88 ?v0) f12))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (= (f50 (f51 f120 ?v0) ?v1) f8) (= (f10 f11 ?v0) f12))))
(assert (forall ((?v0 S9)) (=> (forall ((?v1 S11) (?v2 S9)) (=> (= ?v0 (f13 (f14 f15 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S13)) (=> (forall ((?v1 S7) (?v2 S13)) (=> (= ?v0 (f18 (f19 f20 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S16)) (=> (forall ((?v1 S3) (?v2 S16)) (=> (= ?v0 (f22 (f23 f24 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2) (?v2 S3)) (=> (= ?v0 (f5 (f6 f7 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S9)) (= (= (f91 f121 ?v0) f12) (= ?v0 f17))))
(assert (forall ((?v0 S13)) (= (= (f89 f122 ?v0) f12) (= ?v0 f21))))
(assert (forall ((?v0 S16)) (= (= (f87 f123 ?v0) f12) (= ?v0 f25))))
(assert (forall ((?v0 S3)) (= (= (f10 f124 ?v0) f12) (= ?v0 f8))))
(assert (forall ((?v0 S11) (?v1 S9)) (= (f91 f92 (f13 (f14 f15 ?v0) ?v1)) (ite (= ?v1 f17) f12 (f103 f125 (f91 f92 ?v1))))))
(assert (forall ((?v0 S7) (?v1 S13)) (= (f89 f90 (f18 (f19 f20 ?v0) ?v1)) (ite (= ?v1 f21) f12 (f103 f125 (f89 f90 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S16)) (= (f87 f88 (f22 (f23 f24 ?v0) ?v1)) (ite (= ?v1 f25) f12 (f103 f125 (f87 f88 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f10 f11 (f5 (f6 f7 ?v0) ?v1)) (ite (= ?v1 f8) f12 (f103 f125 (f10 f11 ?v1))))))
(assert (forall ((?v0 S7) (?v1 S13) (?v2 S7)) (= (f65 (f66 f118 (f18 (f19 f20 ?v0) ?v1)) ?v2) (f18 (f19 f20 (f103 (f104 f105 ?v1) ?v2)) (f65 (f66 f118 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S16) (?v2 S3)) (= (f62 (f63 f119 (f22 (f23 f24 ?v0) ?v1)) ?v2) (f22 (f23 f24 (f5 (f101 f102 ?v1) ?v2)) (f62 (f63 f119 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S9) (?v2 S11)) (= (f68 (f69 f117 (f13 (f14 f15 ?v0) ?v1)) ?v2) (f13 (f14 f15 (f106 (f93 f94 ?v1) ?v2)) (f68 (f69 f117 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (f50 (f51 f120 (f5 (f6 f7 ?v0) ?v1)) ?v2) (f5 (f6 f7 (f78 (f79 f80 ?v1) ?v2)) (f50 (f51 f120 ?v1) ?v2)))))
(assert (forall ((?v0 S3)) (=> (not (= (f126 (f79 f80 ?v0)) f1)) (exists ((?v1 S2)) (= (f78 (f79 f80 ?v0) ?v1) f9)))))
(assert (forall ((?v0 S11)) (= (f129 (f127 f128 ?v0) f12) (f13 (f14 f15 ?v0) f17))))
(assert (forall ((?v0 S7)) (= (f65 (f130 f131 ?v0) f12) (f18 (f19 f20 ?v0) f21))))
(assert (forall ((?v0 S3)) (= (f134 (f132 f133 ?v0) f12) (f22 (f23 f24 ?v0) f25))))
(assert (forall ((?v0 S2)) (= (f137 (f135 f136 ?v0) f12) (f5 (f6 f7 ?v0) f8))))
(assert (let ((?v_0 (= f4 f8))) (=> ?v_0 (= (forall ((?v0 S2)) (=> (= (f78 (f79 f80 f4) ?v0) f9) (= (f78 (f79 f80 f138) ?v0) f9))) (or (= (f71 (f139 f4) (f137 (f140 f141 f138) (f10 f11 f4))) f1) (and ?v_0 (= f138 f8)))))))
(assert (forall ((?v0 S9) (?v1 S11)) (=> (not (= ?v0 f17)) (= (f91 f92 (f13 (f14 f15 ?v1) ?v0)) (f103 f125 (f91 f92 ?v0))))))
(assert (forall ((?v0 S13) (?v1 S7)) (=> (not (= ?v0 f21)) (= (f89 f90 (f18 (f19 f20 ?v1) ?v0)) (f103 f125 (f89 f90 ?v0))))))
(assert (forall ((?v0 S16) (?v1 S3)) (=> (not (= ?v0 f25)) (= (f87 f88 (f22 (f23 f24 ?v1) ?v0)) (f103 f125 (f87 f88 ?v0))))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (not (= ?v0 f8)) (= (f10 f11 (f5 (f6 f7 ?v1) ?v0)) (f103 f125 (f10 f11 ?v0))))))
(assert (forall ((?v0 S21)) (=> (not (= ?v0 f29)) (not (= (f129 (f142 f143 ?v0) (f81 f82 ?v0)) f17)))))
(assert (forall ((?v0 S25)) (=> (not (= ?v0 f34)) (not (= (f65 (f144 f145 ?v0) (f83 f84 ?v0)) f21)))))
(assert (forall ((?v0 S29)) (=> (not (= ?v0 f39)) (not (= (f134 (f146 f147 ?v0) (f85 f86 ?v0)) f25)))))
(assert (forall ((?v0 S16)) (=> (not (= ?v0 f25)) (not (= (f137 (f148 f149 ?v0) (f87 f88 ?v0)) f8)))))
(assert (forall ((?v0 S13)) (=> (not (= ?v0 f21)) (not (= (f103 (f104 f150 ?v0) (f89 f90 ?v0)) f12)))))
(assert (forall ((?v0 S9)) (=> (not (= ?v0 f17)) (not (= (f151 (f152 f153 ?v0) (f91 f92 ?v0)) f16)))))
(assert (forall ((?v0 S3)) (=> (not (= ?v0 f8)) (not (= (f154 (f155 f156 ?v0) (f10 f11 ?v0)) f9)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (forall ((?v2 S7)) (= (f154 (f155 f156 ?v0) ?v2) (f154 (f155 f156 ?v1) ?v2))))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= ?v0 ?v1) (forall ((?v2 S7)) (= (f151 (f152 f153 ?v0) ?v2) (f151 (f152 f153 ?v1) ?v2))))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= ?v0 ?v1) (forall ((?v2 S7)) (= (f103 (f104 f150 ?v0) ?v2) (f103 (f104 f150 ?v1) ?v2))))))
(assert (forall ((?v0 S16) (?v1 S16)) (= (= ?v0 ?v1) (forall ((?v2 S7)) (= (f137 (f148 f149 ?v0) ?v2) (f137 (f148 f149 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f155 f156 ?v0) (f155 f156 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f152 f153 ?v0) (f152 f153 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f104 f150 ?v0) (f104 f150 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S16) (?v1 S16)) (= (= (f148 f149 ?v0) (f148 f149 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S7) (?v2 S2)) (= (= (f137 (f135 f136 ?v0) ?v1) (f137 (f135 f136 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S11) (?v1 S7) (?v2 S11)) (= (= (f129 (f127 f128 ?v0) ?v1) (f129 (f127 f128 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (= (f65 (f130 f131 ?v0) ?v1) (f65 (f130 f131 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S3)) (= (= (f134 (f132 f133 ?v0) ?v1) (f134 (f132 f133 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f151 (f152 f153 ?v0) (f91 f92 ?v0)) (f151 (f152 f153 ?v1) (f91 f92 ?v1))) (=> (= (f77 (f157 ?v0) ?v1) f1) (=> (= (f77 (f157 ?v1) ?v0) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S16) (?v1 S16)) (=> (= (f137 (f148 f149 ?v0) (f87 f88 ?v0)) (f137 (f148 f149 ?v1) (f87 f88 ?v1))) (=> (= (f75 (f158 ?v0) ?v1) f1) (=> (= (f75 (f158 ?v1) ?v0) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f154 (f155 f156 ?v0) (f10 f11 ?v0)) (f154 (f155 f156 ?v1) (f10 f11 ?v1))) (=> (= (f71 (f139 ?v0) ?v1) f1) (=> (= (f71 (f139 ?v1) ?v0) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S9) (?v1 S7) (?v2 S11)) (= (f106 (f93 f94 (f129 (f159 f160 ?v0) ?v1)) ?v2) (f151 (f161 f162 (f106 (f93 f94 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S25) (?v1 S7) (?v2 S13)) (= (f18 (f97 f98 (f163 (f164 f165 ?v0) ?v1)) ?v2) (f65 (f66 f166 (f18 (f97 f98 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S29) (?v1 S7) (?v2 S16)) (= (f22 (f99 f100 (f167 (f168 f169 ?v0) ?v1)) ?v2) (f134 (f170 f171 (f22 (f99 f100 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S16) (?v1 S7) (?v2 S3)) (= (f5 (f101 f102 (f134 (f170 f171 ?v0) ?v1)) ?v2) (f137 (f140 f141 (f5 (f101 f102 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S13) (?v1 S7) (?v2 S7)) (= (f103 (f104 f105 (f65 (f66 f166 ?v0) ?v1)) ?v2) (f103 (f172 f173 (f103 (f104 f105 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S2)) (= (f78 (f79 f80 (f137 (f140 f141 ?v0) ?v1)) ?v2) (f154 (f174 f175 (f78 (f79 f80 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S11) (?v1 S9) (?v2 S7)) (= (f151 (f152 f153 (f13 (f14 f15 ?v0) ?v1)) (f103 f125 ?v2)) (f151 (f152 f153 ?v1) ?v2))))
(assert (forall ((?v0 S7) (?v1 S13) (?v2 S7)) (= (f103 (f104 f150 (f18 (f19 f20 ?v0) ?v1)) (f103 f125 ?v2)) (f103 (f104 f150 ?v1) ?v2))))
(assert (forall ((?v0 S3) (?v1 S16) (?v2 S7)) (= (f137 (f148 f149 (f22 (f23 f24 ?v0) ?v1)) (f103 f125 ?v2)) (f137 (f148 f149 ?v1) ?v2))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S7)) (= (f154 (f155 f156 (f5 (f6 f7 ?v0) ?v1)) (f103 f125 ?v2)) (f154 (f155 f156 ?v1) ?v2))))
(assert (forall ((?v0 S9) (?v1 S7) (?v2 S7)) (= (f129 (f142 f143 (f176 (f177 f178 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f17))))
(assert (forall ((?v0 S13) (?v1 S7) (?v2 S7)) (= (f65 (f144 f145 (f163 (f179 f180 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f21))))
(assert (forall ((?v0 S16) (?v1 S7) (?v2 S7)) (= (f134 (f146 f147 (f167 (f181 f182 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f25))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S7)) (= (f137 (f148 f149 (f134 (f132 f133 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f8))))
(assert (forall ((?v0 S2) (?v1 S7) (?v2 S7)) (= (f154 (f155 f156 (f137 (f135 f136 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f9))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f103 (f104 f150 (f65 (f130 f131 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f12))))
(assert (forall ((?v0 S11) (?v1 S7) (?v2 S7)) (= (f151 (f152 f153 (f129 (f127 f128 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f16))))
(assert (forall ((?v0 S57)) (= (= (f126 ?v0) f1) (forall ((?v1 S2) (?v2 S2)) (= (f78 ?v0 ?v1) (f78 ?v0 ?v2))))))
(assert (forall ((?v0 S9) (?v1 S7)) (let ((?v_0 (f177 f178 ?v0))) (= (f176 ?v_0 (f103 f125 ?v1)) (f47 (f48 f49 f17) (f176 ?v_0 ?v1))))))
(assert (forall ((?v0 S13) (?v1 S7)) (let ((?v_0 (f179 f180 ?v0))) (= (f163 ?v_0 (f103 f125 ?v1)) (f44 (f45 f46 f21) (f163 ?v_0 ?v1))))))
(assert (forall ((?v0 S16) (?v1 S7)) (let ((?v_0 (f181 f182 ?v0))) (= (f167 ?v_0 (f103 f125 ?v1)) (f41 (f42 f43 f25) (f167 ?v_0 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S7)) (let ((?v_0 (f132 f133 ?v0))) (= (f134 ?v_0 (f103 f125 ?v1)) (f22 (f23 f24 f8) (f134 ?v_0 ?v1))))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f130 f131 ?v0))) (= (f65 ?v_0 (f103 f125 ?v1)) (f18 (f19 f20 f12) (f65 ?v_0 ?v1))))))
(assert (forall ((?v0 S11) (?v1 S7)) (let ((?v_0 (f127 f128 ?v0))) (= (f129 ?v_0 (f103 f125 ?v1)) (f13 (f14 f15 f16) (f129 ?v_0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S7)) (let ((?v_0 (f135 f136 ?v0))) (= (f137 ?v_0 (f103 f125 ?v1)) (f5 (f6 f7 f9) (f137 ?v_0 ?v1))))))
(assert (forall ((?v0 S9)) (= (f91 f121 ?v0) (ite (= ?v0 f17) f12 (f103 f125 (f91 f92 ?v0))))))
(assert (forall ((?v0 S13)) (= (f89 f122 ?v0) (ite (= ?v0 f21) f12 (f103 f125 (f89 f90 ?v0))))))
(assert (forall ((?v0 S16)) (= (f87 f123 ?v0) (ite (= ?v0 f25) f12 (f103 f125 (f87 f88 ?v0))))))
(assert (forall ((?v0 S3)) (= (f10 f124 ?v0) (ite (= ?v0 f8) f12 (f103 f125 (f10 f11 ?v0))))))
(assert (forall ((?v0 S7)) (= (f129 (f142 f143 f29) ?v0) f17)))
(assert (forall ((?v0 S7)) (= (f65 (f144 f145 f34) ?v0) f21)))
(assert (forall ((?v0 S7)) (= (f134 (f146 f147 f39) ?v0) f25)))
(assert (forall ((?v0 S7)) (= (f137 (f148 f149 f25) ?v0) f8)))
(assert (forall ((?v0 S7)) (= (f154 (f155 f156 f8) ?v0) f9)))
(assert (forall ((?v0 S7)) (= (f103 (f104 f150 f21) ?v0) f12)))
(assert (forall ((?v0 S7)) (= (f151 (f152 f153 f17) ?v0) f16)))
(assert (forall ((?v0 S11) (?v1 S9)) (= (f151 (f152 f153 (f13 (f14 f15 ?v0) ?v1)) f12) ?v0)))
(assert (forall ((?v0 S7) (?v1 S13)) (= (f103 (f104 f150 (f18 (f19 f20 ?v0) ?v1)) f12) ?v0)))
(assert (forall ((?v0 S3) (?v1 S16)) (= (f137 (f148 f149 (f22 (f23 f24 ?v0) ?v1)) f12) ?v0)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f154 (f155 f156 (f5 (f6 f7 ?v0) ?v1)) f12) ?v0)))
(assert (forall ((?v0 S11)) (= (f68 (f69 f117 f17) ?v0) f17)))
(assert (forall ((?v0 S7)) (= (f65 (f66 f118 f21) ?v0) f21)))
(assert (forall ((?v0 S3)) (= (f62 (f63 f119 f25) ?v0) f25)))
(assert (forall ((?v0 S2)) (= (f50 (f51 f120 f8) ?v0) f8)))
(assert (forall ((?v0 S7)) (= (f176 (f177 f178 f17) ?v0) f29)))
(assert (forall ((?v0 S7)) (= (f163 (f179 f180 f21) ?v0) f34)))
(assert (forall ((?v0 S7)) (= (f167 (f181 f182 f25) ?v0) f39)))
(assert (forall ((?v0 S7)) (= (f134 (f132 f133 f8) ?v0) f25)))
(assert (forall ((?v0 S7)) (= (f65 (f130 f131 f12) ?v0) f21)))
(assert (forall ((?v0 S7)) (= (f129 (f127 f128 f16) ?v0) f17)))
(assert (forall ((?v0 S7)) (= (f137 (f135 f136 f9) ?v0) f8)))
(assert (forall ((?v0 S9) (?v1 S7)) (= (= (f176 (f177 f178 ?v0) ?v1) f29) (= ?v0 f17))))
(assert (forall ((?v0 S13) (?v1 S7)) (= (= (f163 (f179 f180 ?v0) ?v1) f34) (= ?v0 f21))))
(assert (forall ((?v0 S16) (?v1 S7)) (= (= (f167 (f181 f182 ?v0) ?v1) f39) (= ?v0 f25))))
(assert (forall ((?v0 S3) (?v1 S7)) (= (= (f134 (f132 f133 ?v0) ?v1) f25) (= ?v0 f8))))
(assert (forall ((?v0 S2) (?v1 S7)) (= (= (f137 (f135 f136 ?v0) ?v1) f8) (= ?v0 f9))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f65 (f130 f131 ?v0) ?v1) f21) (= ?v0 f12))))
(assert (forall ((?v0 S11) (?v1 S7)) (= (= (f129 (f127 f128 ?v0) ?v1) f17) (= ?v0 f16))))
(assert (forall ((?v0 S9) (?v1 S7)) (=> (not (= ?v0 f17)) (= (f81 f82 (f176 (f177 f178 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S13) (?v1 S7)) (=> (not (= ?v0 f21)) (= (f83 f84 (f163 (f179 f180 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S16) (?v1 S7)) (=> (not (= ?v0 f25)) (= (f85 f86 (f167 (f181 f182 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S7)) (=> (not (= ?v0 f8)) (= (f87 f88 (f134 (f132 f133 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (not (= ?v0 f12)) (= (f89 f90 (f65 (f130 f131 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S11) (?v1 S7)) (=> (not (= ?v0 f16)) (= (f91 f92 (f129 (f127 f128 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S7)) (=> (not (= ?v0 f9)) (= (f10 f11 (f137 (f135 f136 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S21)) (= (= (f129 (f142 f143 ?v0) (f81 f82 ?v0)) f17) (= ?v0 f29))))
(assert (forall ((?v0 S25)) (= (= (f65 (f144 f145 ?v0) (f83 f84 ?v0)) f21) (= ?v0 f34))))
(assert (forall ((?v0 S29)) (= (= (f134 (f146 f147 ?v0) (f85 f86 ?v0)) f25) (= ?v0 f39))))
(assert (forall ((?v0 S16)) (= (= (f137 (f148 f149 ?v0) (f87 f88 ?v0)) f8) (= ?v0 f25))))
(assert (forall ((?v0 S13)) (= (= (f103 (f104 f150 ?v0) (f89 f90 ?v0)) f12) (= ?v0 f21))))
(assert (forall ((?v0 S9)) (= (= (f151 (f152 f153 ?v0) (f91 f92 ?v0)) f16) (= ?v0 f17))))
(assert (forall ((?v0 S3)) (= (= (f154 (f155 f156 ?v0) (f10 f11 ?v0)) f9) (= ?v0 f8))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7)) (=> (forall ((?v3 S2)) (=> (= (f78 (f79 f80 ?v0) ?v3) f9) (= (f78 (f79 f80 ?v1) ?v3) f9))) (=> (= (f10 f11 ?v0) ?v2) (=> (not (= ?v2 f12)) (= (f71 (f139 ?v0) (f137 (f140 f141 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S9)) (= (f77 (f157 ?v0) f17) f1)))
(assert (forall ((?v0 S13)) (= (f76 (f183 ?v0) f21) f1)))
(assert (forall ((?v0 S16)) (= (f75 (f158 ?v0) f25) f1)))
(assert (forall ((?v0 S2)) (= (f184 ?v0 f9) f1)))
(assert (forall ((?v0 S11)) (= (f185 ?v0 f16) f1)))
(assert (forall ((?v0 S3)) (= (f71 (f139 ?v0) f8) f1)))
(assert (forall ((?v0 S7)) (= (f186 (f187 ?v0) f12) f1)))
(assert (forall ((?v0 S7)) (= (f129 (f159 f160 f17) (f103 f125 ?v0)) f17)))
(assert (forall ((?v0 S7)) (= (f65 (f66 f166 f21) (f103 f125 ?v0)) f21)))
(assert (forall ((?v0 S7)) (= (f134 (f170 f171 f25) (f103 f125 ?v0)) f25)))
(assert (forall ((?v0 S7)) (= (f137 (f140 f141 f8) (f103 f125 ?v0)) f8)))
(assert (forall ((?v0 S7)) (= (f154 (f174 f175 f9) (f103 f125 ?v0)) f9)))
(assert (forall ((?v0 S7)) (= (f103 (f172 f173 f12) (f103 f125 ?v0)) f12)))
(assert (forall ((?v0 S7)) (= (f151 (f161 f162 f16) (f103 f125 ?v0)) f16)))
(assert (forall ((?v0 S9) (?v1 S7)) (= (= (f129 (f159 f160 ?v0) ?v1) f17) (and (= ?v0 f17) (not (= ?v1 f12))))))
(assert (forall ((?v0 S16) (?v1 S7)) (= (= (f134 (f170 f171 ?v0) ?v1) f25) (and (= ?v0 f25) (not (= ?v1 f12))))))
(assert (forall ((?v0 S3) (?v1 S7)) (= (= (f137 (f140 f141 ?v0) ?v1) f8) (and (= ?v0 f8) (not (= ?v1 f12))))))
(assert (forall ((?v0 S2) (?v1 S7)) (= (= (f154 (f174 f175 ?v0) ?v1) f9) (and (= ?v0 f9) (not (= ?v1 f12))))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f103 (f172 f173 ?v0) ?v1) f12) (and (= ?v0 f12) (not (= ?v1 f12))))))
(assert (forall ((?v0 S11) (?v1 S7)) (= (= (f151 (f161 f162 ?v0) ?v1) f16) (and (= ?v0 f16) (not (= ?v1 f12))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S7)) (=> (= (f185 ?v0 ?v1) f1) (= (f185 (f151 (f161 f162 ?v0) ?v2) (f151 (f161 f162 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S7)) (=> (= (f184 ?v0 ?v1) f1) (= (f184 (f154 (f174 f175 ?v0) ?v2) (f154 (f174 f175 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S7)) (=> (= (f76 (f183 ?v0) ?v1) f1) (= (f76 (f183 (f65 (f66 f166 ?v0) ?v2)) (f65 (f66 f166 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S7)) (=> (= (f75 (f158 ?v0) ?v1) f1) (= (f75 (f158 (f134 (f170 f171 ?v0) ?v2)) (f134 (f170 f171 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7)) (=> (= (f71 (f139 ?v0) ?v1) f1) (= (f71 (f139 (f137 (f140 f141 ?v0) ?v2)) (f137 (f140 f141 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= (f186 (f187 ?v0) ?v1) f1) (= (f186 (f187 (f103 (f172 f173 ?v0) ?v2)) (f103 (f172 f173 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S7)) (=> (= (f103 f125 ?v0) f12) false)))
(assert (forall ((?v0 S7)) (=> (= f12 (f103 f125 ?v0)) false)))
(assert (forall ((?v0 S7)) (not (= (f103 f125 ?v0) f12))))
(assert (forall ((?v0 S7)) (not (= (f103 f125 ?v0) f12))))
(assert (forall ((?v0 S7)) (= (f186 (f187 (f103 f125 f12)) ?v0) f1)))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f103 f125 f12))) (= (= (f103 (f172 f173 ?v0) ?v1) ?v_0) (or (= ?v1 f12) (= ?v0 ?v_0))))))
(assert (forall ((?v0 S7)) (let ((?v_0 (f103 f125 f12))) (= (f103 (f172 f173 ?v_0) ?v0) ?v_0))))
(assert (forall ((?v0 S7)) (let ((?v_0 (f103 f125 f12))) (= (= (f186 (f187 ?v0) ?v_0) f1) (= ?v0 ?v_0)))))
(assert (forall ((?v0 S11)) (= (f185 ?v0 ?v0) f1)))
(assert (forall ((?v0 S2)) (= (f184 ?v0 ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f71 (f139 ?v0) ?v0) f1)))
(assert (forall ((?v0 S7)) (= (f186 (f187 ?v0) ?v0) f1)))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f185 ?v0 ?v1) f1) (=> (= (f185 ?v1 ?v2) f1) (= (f185 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f184 ?v0 ?v1) f1) (=> (= (f184 ?v1 ?v2) f1) (= (f184 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f139 ?v0))) (=> (= (f71 ?v_0 ?v1) f1) (=> (= (f71 (f139 ?v1) ?v2) f1) (= (f71 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f187 ?v0))) (=> (= (f186 ?v_0 ?v1) f1) (=> (= (f186 (f187 ?v1) ?v2) f1) (= (f186 ?v_0 ?v2) f1))))))
(check-sat)
(exit)
