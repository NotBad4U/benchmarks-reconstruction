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
(declare-fun f3 () S2)
(declare-fun f4 (S3 S2) S2)
(declare-fun f5 (S4 S5) S3)
(declare-fun f6 () S4)
(declare-fun f7 () S5)
(declare-fun f8 (S6 S5) S5)
(declare-fun f9 (S7 S2) S6)
(declare-fun f10 () S7)
(declare-fun f11 () S2)
(declare-fun f12 (S3) S1)
(declare-fun f13 () S5)
(declare-fun f14 (S9 S8) S8)
(declare-fun f15 (S10 S11) S9)
(declare-fun f16 () S10)
(declare-fun f17 () S11)
(declare-fun f18 () S8)
(declare-fun f19 (S12 S13) S6)
(declare-fun f20 () S12)
(declare-fun f21 () S13)
(declare-fun f22 (S15 S14) S14)
(declare-fun f23 (S16 S17) S15)
(declare-fun f24 () S16)
(declare-fun f25 () S17)
(declare-fun f26 () S14)
(declare-fun f27 (S19 S18) S18)
(declare-fun f28 (S20 S21) S19)
(declare-fun f29 () S20)
(declare-fun f30 () S21)
(declare-fun f31 () S18)
(declare-fun f32 (S23 S22) S22)
(declare-fun f33 (S24 S25) S23)
(declare-fun f34 () S24)
(declare-fun f35 () S25)
(declare-fun f36 () S22)
(declare-fun f37 (S27 S26) S26)
(declare-fun f38 (S28 S29) S27)
(declare-fun f39 () S28)
(declare-fun f40 () S29)
(declare-fun f41 () S26)
(declare-fun f42 (S30 S17) S17)
(declare-fun f43 (S31 S26) S30)
(declare-fun f44 () S31)
(declare-fun f45 (S32 S13) S13)
(declare-fun f46 (S33 S22) S32)
(declare-fun f47 () S33)
(declare-fun f48 (S34 S11) S11)
(declare-fun f49 (S35 S18) S34)
(declare-fun f50 () S35)
(declare-fun f51 () S5)
(declare-fun f52 (S36 S5) S8)
(declare-fun f53 (S37 S2) S36)
(declare-fun f54 () S37)
(declare-fun f55 (S38 S13) S8)
(declare-fun f56 (S39 S5) S38)
(declare-fun f57 () S39)
(declare-fun f58 (S40 S17) S8)
(declare-fun f59 (S41 S14) S40)
(declare-fun f60 () S41)
(declare-fun f61 (S42 S25) S8)
(declare-fun f62 (S43 S22) S42)
(declare-fun f63 () S43)
(declare-fun f64 (S44 S29) S8)
(declare-fun f65 (S45 S26) S44)
(declare-fun f66 () S45)
(declare-fun f67 (S46 S26) S8)
(declare-fun f68 (S47 S17) S46)
(declare-fun f69 () S47)
(declare-fun f70 (S48 S22) S8)
(declare-fun f71 (S49 S13) S48)
(declare-fun f72 () S49)
(declare-fun f73 (S50 S8) S34)
(declare-fun f74 () S50)
(declare-fun f75 (S51 S5) S32)
(declare-fun f76 () S51)
(declare-fun f77 (S52 S14) S30)
(declare-fun f78 () S52)
(declare-fun f79 (S53 S21) S21)
(declare-fun f80 (S54 S18) S53)
(declare-fun f81 () S54)
(declare-fun f82 (S55 S25) S25)
(declare-fun f83 (S56 S22) S55)
(declare-fun f84 () S56)
(declare-fun f85 (S57 S29) S29)
(declare-fun f86 (S58 S26) S57)
(declare-fun f87 () S58)
(declare-fun f88 (S59 S17) S27)
(declare-fun f89 () S59)
(declare-fun f90 (S60 S13) S23)
(declare-fun f91 () S60)
(declare-fun f92 (S61 S11) S19)
(declare-fun f93 () S61)
(declare-fun f94 (S62 S5) S6)
(declare-fun f95 () S62)
(declare-fun f96 (S63 S22) S23)
(declare-fun f97 () S63)
(declare-fun f98 (S64 S26) S27)
(declare-fun f99 () S64)
(declare-fun f100 (S65 S18) S19)
(declare-fun f101 () S65)
(declare-fun f102 (S66 S11) S34)
(declare-fun f103 () S66)
(declare-fun f104 (S67 S17) S30)
(declare-fun f105 () S67)
(declare-fun f106 (S68 S13) S32)
(declare-fun f107 () S68)
(declare-fun f108 (S69 S5) S1)
(declare-fun f109 (S70 S18) S1)
(declare-fun f110 (S71 S22) S1)
(declare-fun f111 (S72 S26) S1)
(declare-fun f112 (S73 S17) S1)
(declare-fun f113 (S74 S13) S1)
(declare-fun f114 (S75 S11) S1)
(declare-fun f115 () S36)
(declare-fun f116 (S76 S18) S8)
(declare-fun f117 () S76)
(declare-fun f118 () S48)
(declare-fun f119 () S46)
(declare-fun f120 () S40)
(declare-fun f121 () S38)
(declare-fun f122 (S77 S11) S8)
(declare-fun f123 () S77)
(declare-fun f124 (S78 S2) S5)
(declare-fun f125 (S79 S5) S78)
(declare-fun f126 () S79)
(declare-fun f127 (S80 S11) S18)
(declare-fun f128 (S81 S18) S80)
(declare-fun f129 () S81)
(declare-fun f130 (S82 S13) S22)
(declare-fun f131 (S83 S22) S82)
(declare-fun f132 () S83)
(declare-fun f133 (S84 S17) S26)
(declare-fun f134 (S85 S26) S84)
(declare-fun f135 () S85)
(declare-fun f136 (S86 S14) S17)
(declare-fun f137 (S87 S17) S86)
(declare-fun f138 () S87)
(declare-fun f139 (S88 S5) S13)
(declare-fun f140 (S89 S13) S88)
(declare-fun f141 () S89)
(declare-fun f142 (S90 S8) S11)
(declare-fun f143 (S91 S11) S90)
(declare-fun f144 () S91)
(declare-fun f145 () S79)
(declare-fun f146 () S83)
(declare-fun f147 () S85)
(declare-fun f148 () S81)
(declare-fun f149 () S91)
(declare-fun f150 () S87)
(declare-fun f151 () S89)
(declare-fun f152 (S92 S2) S93)
(declare-fun f153 () S92)
(declare-fun f154 (S93 S8) S5)
(declare-fun f155 (S94 S11) S95)
(declare-fun f156 () S94)
(declare-fun f157 (S95 S8) S18)
(declare-fun f158 (S96 S13) S97)
(declare-fun f159 () S96)
(declare-fun f160 (S97 S8) S22)
(declare-fun f161 (S98 S17) S99)
(declare-fun f162 () S98)
(declare-fun f163 (S99 S8) S26)
(declare-fun f164 (S100 S14) S101)
(declare-fun f165 () S100)
(declare-fun f166 (S101 S8) S17)
(declare-fun f167 (S102 S5) S103)
(declare-fun f168 () S102)
(declare-fun f169 (S103 S8) S13)
(declare-fun f170 (S104 S8) S90)
(declare-fun f171 () S104)
(declare-fun f172 () S36)
(declare-fun f173 () S76)
(declare-fun f174 () S48)
(declare-fun f175 () S46)
(declare-fun f176 () S40)
(declare-fun f177 () S38)
(declare-fun f178 () S77)
(declare-fun f179 (S105 S21) S8)
(declare-fun f180 () S105)
(declare-fun f181 (S106 S8) S21)
(declare-fun f182 (S107 S18) S106)
(declare-fun f183 () S107)
(declare-fun f184 () S42)
(declare-fun f185 (S108 S8) S25)
(declare-fun f186 (S109 S22) S108)
(declare-fun f187 () S109)
(declare-fun f188 () S44)
(declare-fun f189 (S110 S8) S29)
(declare-fun f190 (S111 S26) S110)
(declare-fun f191 () S111)
(assert (not (= f1 f2)))
(assert (not (forall ((?v0 S2)) (=> (not (= ?v0 f3)) (= (f4 (f5 f6 f7) ?v0) f3)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f6 (f8 (f9 f10 f11) f7)))) (= (f4 ?v_0 f3) (f4 ?v_0 ?v0)))))
(assert (not (= f11 f3)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f6 (f8 (f9 f10 f11) f7)))) (= (f4 ?v_0 f3) (f4 ?v_0 ?v0)))))
(assert (= (f12 (f5 f6 (f8 (f9 f10 f11) f7))) f1))
(assert (=> (= f11 f3) (exists ((?v0 S2)) (= (f4 (f5 f6 (f8 (f9 f10 f11) f7)) ?v0) f3))))
(assert (not (exists ((?v0 S2) (?v1 S5)) (and (not (= ?v0 f3)) (and (= ?v1 f13) (= (f8 (f9 f10 f11) f7) (f8 (f9 f10 ?v0) ?v1)))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f13) ?v0) f3)))
(assert (forall ((?v0 S8)) (= (f14 (f15 f16 f17) ?v0) f18)))
(assert (forall ((?v0 S5)) (= (f8 (f19 f20 f21) ?v0) f13)))
(assert (forall ((?v0 S14)) (= (f22 (f23 f24 f25) ?v0) f26)))
(assert (forall ((?v0 S18)) (= (f27 (f28 f29 f30) ?v0) f31)))
(assert (forall ((?v0 S22)) (= (f32 (f33 f34 f35) ?v0) f36)))
(assert (forall ((?v0 S26)) (= (f37 (f38 f39 f40) ?v0) f41)))
(assert (forall ((?v0 S17)) (= (f42 (f43 f44 f41) ?v0) f25)))
(assert (forall ((?v0 S13)) (= (f45 (f46 f47 f36) ?v0) f21)))
(assert (forall ((?v0 S11)) (= (f48 (f49 f50 f31) ?v0) f17)))
(assert (=> (not (exists ((?v0 S2) (?v1 S5)) (and (not (= ?v0 f3)) (and (= ?v1 f13) (= f7 (f8 (f9 f10 ?v0) ?v1)))))) (exists ((?v0 S2)) (= (f4 (f5 f6 f7) ?v0) f3))))
(assert (forall ((?v0 S5)) (=> (not (= (f12 (f5 f6 ?v0)) f1)) (exists ((?v1 S2)) (= (f4 (f5 f6 ?v0) ?v1) f3)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f5 f6 ?v0) (f5 f6 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S26) (?v1 S26)) (= (= (f43 f44 ?v0) (f43 f44 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S17) (?v1 S17)) (= (= (f23 f24 ?v0) (f23 f24 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8)) (= (= f18 ?v0) (= ?v0 f18))))
(assert (forall ((?v0 S5)) (= (= f13 ?v0) (= ?v0 f13))))
(assert (forall ((?v0 S14)) (= (= f26 ?v0) (= ?v0 f26))))
(assert (forall ((?v0 S2)) (= (= f3 ?v0) (= ?v0 f3))))
(assert (forall ((?v0 S18)) (= (= f31 ?v0) (= ?v0 f31))))
(assert (forall ((?v0 S22)) (= (= f36 ?v0) (= ?v0 f36))))
(assert (forall ((?v0 S26)) (= (= f41 ?v0) (= ?v0 f41))))
(assert (forall ((?v0 S17)) (= (= f25 ?v0) (= ?v0 f25))))
(assert (forall ((?v0 S13)) (= (= f21 ?v0) (= ?v0 f21))))
(assert (forall ((?v0 S11)) (= (= f17 ?v0) (= ?v0 f17))))
(assert (not (exists ((?v0 S2) (?v1 S5)) (and (not (= ?v0 f3)) (and (= ?v1 f13) (= f51 (f8 (f9 f10 ?v0) ?v1)))))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (= (f4 (f5 f6 ?v0) ?v1) f3) (or (= ?v0 f13) (not (= (f52 (f53 f54 ?v1) ?v0) f18))))))
(assert (forall ((?v0 S13) (?v1 S5)) (= (= (f8 (f19 f20 ?v0) ?v1) f13) (or (= ?v0 f21) (not (= (f55 (f56 f57 ?v1) ?v0) f18))))))
(assert (forall ((?v0 S17) (?v1 S14)) (= (= (f22 (f23 f24 ?v0) ?v1) f26) (or (= ?v0 f25) (not (= (f58 (f59 f60 ?v1) ?v0) f18))))))
(assert (forall ((?v0 S25) (?v1 S22)) (= (= (f32 (f33 f34 ?v0) ?v1) f36) (or (= ?v0 f35) (not (= (f61 (f62 f63 ?v1) ?v0) f18))))))
(assert (forall ((?v0 S29) (?v1 S26)) (= (= (f37 (f38 f39 ?v0) ?v1) f41) (or (= ?v0 f40) (not (= (f64 (f65 f66 ?v1) ?v0) f18))))))
(assert (forall ((?v0 S26) (?v1 S17)) (= (= (f42 (f43 f44 ?v0) ?v1) f25) (or (= ?v0 f41) (not (= (f67 (f68 f69 ?v1) ?v0) f18))))))
(assert (forall ((?v0 S22) (?v1 S13)) (= (= (f45 (f46 f47 ?v0) ?v1) f21) (or (= ?v0 f36) (not (= (f70 (f71 f72 ?v1) ?v0) f18))))))
(assert (= (f8 (f9 f10 f3) f13) f13))
(assert (= (f48 (f73 f74 f18) f17) f17))
(assert (= (f45 (f75 f76 f13) f21) f21))
(assert (= (f42 (f77 f78 f26) f25) f25))
(assert (= (f79 (f80 f81 f31) f30) f30))
(assert (= (f82 (f83 f84 f36) f35) f35))
(assert (= (f85 (f86 f87 f41) f40) f40))
(assert (= (f37 (f88 f89 f25) f41) f41))
(assert (= (f32 (f90 f91 f21) f36) f36))
(assert (= (f27 (f92 f93 f17) f31) f31))
(assert (forall ((?v0 S2) (?v1 S5)) (= (= (f8 (f9 f10 ?v0) ?v1) f13) (and (= ?v0 f3) (= ?v1 f13)))))
(assert (forall ((?v0 S8) (?v1 S11)) (= (= (f48 (f73 f74 ?v0) ?v1) f17) (and (= ?v0 f18) (= ?v1 f17)))))
(assert (forall ((?v0 S5) (?v1 S13)) (= (= (f45 (f75 f76 ?v0) ?v1) f21) (and (= ?v0 f13) (= ?v1 f21)))))
(assert (forall ((?v0 S14) (?v1 S17)) (= (= (f42 (f77 f78 ?v0) ?v1) f25) (and (= ?v0 f26) (= ?v1 f25)))))
(assert (forall ((?v0 S18) (?v1 S21)) (= (= (f79 (f80 f81 ?v0) ?v1) f30) (and (= ?v0 f31) (= ?v1 f30)))))
(assert (forall ((?v0 S22) (?v1 S25)) (= (= (f82 (f83 f84 ?v0) ?v1) f35) (and (= ?v0 f36) (= ?v1 f35)))))
(assert (forall ((?v0 S26) (?v1 S29)) (= (= (f85 (f86 f87 ?v0) ?v1) f40) (and (= ?v0 f41) (= ?v1 f40)))))
(assert (forall ((?v0 S17) (?v1 S26)) (= (= (f37 (f88 f89 ?v0) ?v1) f41) (and (= ?v0 f25) (= ?v1 f41)))))
(assert (forall ((?v0 S13) (?v1 S22)) (= (= (f32 (f90 f91 ?v0) ?v1) f36) (and (= ?v0 f21) (= ?v1 f36)))))
(assert (forall ((?v0 S11) (?v1 S18)) (= (= (f27 (f92 f93 ?v0) ?v1) f31) (and (= ?v0 f17) (= ?v1 f31)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S2)) (= (f4 (f5 f6 (f8 (f94 f95 ?v0) ?v1)) ?v2) (f4 (f5 f6 ?v0) (f4 (f5 f6 ?v1) ?v2)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S13)) (= (f45 (f46 f47 (f32 (f96 f97 ?v0) ?v1)) ?v2) (f45 (f46 f47 ?v0) (f45 (f46 f47 ?v1) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S17)) (= (f42 (f43 f44 (f37 (f98 f99 ?v0) ?v1)) ?v2) (f42 (f43 f44 ?v0) (f42 (f43 f44 ?v1) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S11)) (= (f48 (f49 f50 (f27 (f100 f101 ?v0) ?v1)) ?v2) (f48 (f49 f50 ?v0) (f48 (f49 f50 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S8)) (= (f14 (f15 f16 (f48 (f102 f103 ?v0) ?v1)) ?v2) (f14 (f15 f16 ?v0) (f14 (f15 f16 ?v1) ?v2)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S14)) (= (f22 (f23 f24 (f42 (f104 f105 ?v0) ?v1)) ?v2) (f22 (f23 f24 ?v0) (f22 (f23 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S5)) (= (f8 (f19 f20 (f45 (f106 f107 ?v0) ?v1)) ?v2) (f8 (f19 f20 ?v0) (f8 (f19 f20 ?v1) ?v2)))))
(assert (forall ((?v0 S5)) (= (f8 (f94 f95 f13) ?v0) f13)))
(assert (forall ((?v0 S18)) (= (f27 (f100 f101 f31) ?v0) f31)))
(assert (forall ((?v0 S22)) (= (f32 (f96 f97 f36) ?v0) f36)))
(assert (forall ((?v0 S26)) (= (f37 (f98 f99 f41) ?v0) f41)))
(assert (forall ((?v0 S17)) (= (f42 (f104 f105 f25) ?v0) f25)))
(assert (forall ((?v0 S13)) (= (f45 (f106 f107 f21) ?v0) f21)))
(assert (forall ((?v0 S11)) (= (f48 (f102 f103 f17) ?v0) f17)))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2) (?v3 S5)) (= (= (f8 (f9 f10 ?v0) ?v1) (f8 (f9 f10 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S11) (?v1 S18) (?v2 S11) (?v3 S18)) (= (= (f27 (f92 f93 ?v0) ?v1) (f27 (f92 f93 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S13) (?v1 S22) (?v2 S13) (?v3 S22)) (= (= (f32 (f90 f91 ?v0) ?v1) (f32 (f90 f91 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S17) (?v1 S26) (?v2 S17) (?v3 S26)) (= (= (f37 (f88 f89 ?v0) ?v1) (f37 (f88 f89 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S14) (?v1 S17) (?v2 S14) (?v3 S17)) (= (= (f42 (f77 f78 ?v0) ?v1) (f42 (f77 f78 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5) (?v1 S13) (?v2 S5) (?v3 S13)) (= (= (f45 (f75 f76 ?v0) ?v1) (f45 (f75 f76 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S8) (?v1 S11) (?v2 S8) (?v3 S11)) (= (= (f48 (f73 f74 ?v0) ?v1) (f48 (f73 f74 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5)) (= (= (f5 f6 ?v0) (f5 f6 f13)) (= ?v0 f13))))
(assert (forall ((?v0 S26)) (= (= (f43 f44 ?v0) (f43 f44 f41)) (= ?v0 f41))))
(assert (forall ((?v0 S17)) (= (= (f23 f24 ?v0) (f23 f24 f25)) (= ?v0 f25))))
(assert (forall ((?v0 S3)) (= (= (f12 ?v0) f1) (forall ((?v1 S2) (?v2 S2)) (= (f4 ?v0 ?v1) (f4 ?v0 ?v2))))))
(assert (forall ((?v0 S69) (?v1 S5)) (=> (= (f108 ?v0 f13) f1) (=> (forall ((?v2 S2) (?v3 S5)) (=> (= (f108 ?v0 ?v3) f1) (= (f108 ?v0 (f8 (f9 f10 ?v2) ?v3)) f1))) (= (f108 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S70) (?v1 S18)) (=> (= (f109 ?v0 f31) f1) (=> (forall ((?v2 S11) (?v3 S18)) (=> (= (f109 ?v0 ?v3) f1) (= (f109 ?v0 (f27 (f92 f93 ?v2) ?v3)) f1))) (= (f109 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S71) (?v1 S22)) (=> (= (f110 ?v0 f36) f1) (=> (forall ((?v2 S13) (?v3 S22)) (=> (= (f110 ?v0 ?v3) f1) (= (f110 ?v0 (f32 (f90 f91 ?v2) ?v3)) f1))) (= (f110 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S72) (?v1 S26)) (=> (= (f111 ?v0 f41) f1) (=> (forall ((?v2 S17) (?v3 S26)) (=> (= (f111 ?v0 ?v3) f1) (= (f111 ?v0 (f37 (f88 f89 ?v2) ?v3)) f1))) (= (f111 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S73) (?v1 S17)) (=> (= (f112 ?v0 f25) f1) (=> (forall ((?v2 S14) (?v3 S17)) (=> (= (f112 ?v0 ?v3) f1) (= (f112 ?v0 (f42 (f77 f78 ?v2) ?v3)) f1))) (= (f112 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S74) (?v1 S13)) (=> (= (f113 ?v0 f21) f1) (=> (forall ((?v2 S5) (?v3 S13)) (=> (= (f113 ?v0 ?v3) f1) (= (f113 ?v0 (f45 (f75 f76 ?v2) ?v3)) f1))) (= (f113 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S75) (?v1 S11)) (=> (= (f114 ?v0 f17) f1) (=> (forall ((?v2 S8) (?v3 S11)) (=> (= (f114 ?v0 ?v3) f1) (= (f114 ?v0 (f48 (f73 f74 ?v2) ?v3)) f1))) (= (f114 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S5)) (=> (forall ((?v1 S2) (?v2 S5)) (=> (= ?v0 (f8 (f9 f10 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S18)) (=> (forall ((?v1 S11) (?v2 S18)) (=> (= ?v0 (f27 (f92 f93 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S22)) (=> (forall ((?v1 S13) (?v2 S22)) (=> (= ?v0 (f32 (f90 f91 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S17) (?v2 S26)) (=> (= ?v0 (f37 (f88 f89 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S17)) (=> (forall ((?v1 S14) (?v2 S17)) (=> (= ?v0 (f42 (f77 f78 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S13)) (=> (forall ((?v1 S5) (?v2 S13)) (=> (= ?v0 (f45 (f75 f76 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S11)) (=> (forall ((?v1 S8) (?v2 S11)) (=> (= ?v0 (f48 (f73 f74 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S5)) (= (= (f52 f115 ?v0) f18) (= ?v0 f13))))
(assert (forall ((?v0 S18)) (= (= (f116 f117 ?v0) f18) (= ?v0 f31))))
(assert (forall ((?v0 S22)) (= (= (f70 f118 ?v0) f18) (= ?v0 f36))))
(assert (forall ((?v0 S26)) (= (= (f67 f119 ?v0) f18) (= ?v0 f41))))
(assert (forall ((?v0 S17)) (= (= (f58 f120 ?v0) f18) (= ?v0 f25))))
(assert (forall ((?v0 S13)) (= (= (f55 f121 ?v0) f18) (= ?v0 f21))))
(assert (forall ((?v0 S11)) (= (= (f122 f123 ?v0) f18) (= ?v0 f17))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f8 (f9 f10 ?v0) f13))) (= (f124 (f125 f126 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f27 (f92 f93 ?v0) f31))) (= (f127 (f128 f129 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f32 (f90 f91 ?v0) f36))) (= (f130 (f131 f132 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S17) (?v1 S17)) (let ((?v_0 (f37 (f88 f89 ?v0) f41))) (= (f133 (f134 f135 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S14) (?v1 S14)) (let ((?v_0 (f42 (f77 f78 ?v0) f25))) (= (f136 (f137 f138 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S5) (?v1 S5)) (let ((?v_0 (f45 (f75 f76 ?v0) f21))) (= (f139 (f140 f141 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f48 (f73 f74 ?v0) f17))) (= (f142 (f143 f144 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2)) (= (f124 (f125 f145 (f8 (f9 f10 ?v0) ?v1)) ?v2) (f8 (f9 f10 (f4 (f5 f6 ?v1) ?v2)) (f124 (f125 f145 ?v1) ?v2)))))
(assert (forall ((?v0 S13) (?v1 S22) (?v2 S13)) (= (f130 (f131 f146 (f32 (f90 f91 ?v0) ?v1)) ?v2) (f32 (f90 f91 (f45 (f46 f47 ?v1) ?v2)) (f130 (f131 f146 ?v1) ?v2)))))
(assert (forall ((?v0 S17) (?v1 S26) (?v2 S17)) (= (f133 (f134 f147 (f37 (f88 f89 ?v0) ?v1)) ?v2) (f37 (f88 f89 (f42 (f43 f44 ?v1) ?v2)) (f133 (f134 f147 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S18) (?v2 S11)) (= (f127 (f128 f148 (f27 (f92 f93 ?v0) ?v1)) ?v2) (f27 (f92 f93 (f48 (f49 f50 ?v1) ?v2)) (f127 (f128 f148 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S11) (?v2 S8)) (= (f142 (f143 f149 (f48 (f73 f74 ?v0) ?v1)) ?v2) (f48 (f73 f74 (f14 (f15 f16 ?v1) ?v2)) (f142 (f143 f149 ?v1) ?v2)))))
(assert (forall ((?v0 S14) (?v1 S17) (?v2 S14)) (= (f136 (f137 f150 (f42 (f77 f78 ?v0) ?v1)) ?v2) (f42 (f77 f78 (f22 (f23 f24 ?v1) ?v2)) (f136 (f137 f150 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S13) (?v2 S5)) (= (f139 (f140 f151 (f45 (f75 f76 ?v0) ?v1)) ?v2) (f45 (f75 f76 (f8 (f19 f20 ?v1) ?v2)) (f139 (f140 f151 ?v1) ?v2)))))
(assert (forall ((?v0 S2)) (= (f154 (f152 f153 ?v0) f18) (f8 (f9 f10 ?v0) f13))))
(assert (forall ((?v0 S11)) (= (f157 (f155 f156 ?v0) f18) (f27 (f92 f93 ?v0) f31))))
(assert (forall ((?v0 S13)) (= (f160 (f158 f159 ?v0) f18) (f32 (f90 f91 ?v0) f36))))
(assert (forall ((?v0 S17)) (= (f163 (f161 f162 ?v0) f18) (f37 (f88 f89 ?v0) f41))))
(assert (forall ((?v0 S14)) (= (f166 (f164 f165 ?v0) f18) (f42 (f77 f78 ?v0) f25))))
(assert (forall ((?v0 S5)) (= (f169 (f167 f168 ?v0) f18) (f45 (f75 f76 ?v0) f21))))
(assert (forall ((?v0 S8)) (= (f142 (f170 f171 ?v0) f18) (f48 (f73 f74 ?v0) f17))))
(assert (forall ((?v0 S2)) (= (f52 f172 (f8 (f9 f10 ?v0) f13)) f18)))
(assert (forall ((?v0 S11)) (= (f116 f173 (f27 (f92 f93 ?v0) f31)) f18)))
(assert (forall ((?v0 S13)) (= (f70 f174 (f32 (f90 f91 ?v0) f36)) f18)))
(assert (forall ((?v0 S17)) (= (f67 f175 (f37 (f88 f89 ?v0) f41)) f18)))
(assert (forall ((?v0 S14)) (= (f58 f176 (f42 (f77 f78 ?v0) f25)) f18)))
(assert (forall ((?v0 S5)) (= (f55 f177 (f45 (f75 f76 ?v0) f21)) f18)))
(assert (forall ((?v0 S8)) (= (f122 f178 (f48 (f73 f74 ?v0) f17)) f18)))
(assert (forall ((?v0 S11) (?v1 S8) (?v2 S11)) (= (= (f157 (f155 f156 ?v0) ?v1) (f157 (f155 f156 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S13) (?v1 S8) (?v2 S13)) (= (= (f160 (f158 f159 ?v0) ?v1) (f160 (f158 f159 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S17) (?v1 S8) (?v2 S17)) (= (= (f163 (f161 f162 ?v0) ?v1) (f163 (f161 f162 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S8) (?v2 S2)) (= (= (f154 (f152 f153 ?v0) ?v1) (f154 (f152 f153 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S14) (?v1 S8) (?v2 S14)) (= (= (f166 (f164 f165 ?v0) ?v1) (f166 (f164 f165 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S5) (?v1 S8) (?v2 S5)) (= (= (f169 (f167 f168 ?v0) ?v1) (f169 (f167 f168 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (= (f142 (f170 f171 ?v0) ?v1) (f142 (f170 f171 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S18) (?v1 S11)) (= (f116 f173 (f127 (f128 f129 ?v0) ?v1)) (f116 f173 ?v0))))
(assert (forall ((?v0 S22) (?v1 S13)) (= (f70 f174 (f130 (f131 f132 ?v0) ?v1)) (f70 f174 ?v0))))
(assert (forall ((?v0 S26) (?v1 S17)) (= (f67 f175 (f133 (f134 f135 ?v0) ?v1)) (f67 f175 ?v0))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (f52 f172 (f124 (f125 f126 ?v0) ?v1)) (f52 f172 ?v0))))
(assert (forall ((?v0 S17) (?v1 S14)) (= (f58 f176 (f136 (f137 f138 ?v0) ?v1)) (f58 f176 ?v0))))
(assert (forall ((?v0 S13) (?v1 S5)) (= (f55 f177 (f139 (f140 f141 ?v0) ?v1)) (f55 f177 ?v0))))
(assert (forall ((?v0 S11) (?v1 S8)) (= (f122 f178 (f142 (f143 f144 ?v0) ?v1)) (f122 f178 ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (not (= ?v0 f18)) (= (f122 f178 (f142 (f170 f171 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S5) (?v1 S8)) (=> (not (= ?v0 f13)) (= (f55 f177 (f169 (f167 f168 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S14) (?v1 S8)) (=> (not (= ?v0 f26)) (= (f58 f176 (f166 (f164 f165 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S8)) (=> (not (= ?v0 f3)) (= (f52 f172 (f154 (f152 f153 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S18) (?v1 S8)) (=> (not (= ?v0 f31)) (= (f179 f180 (f181 (f182 f183 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S22) (?v1 S8)) (=> (not (= ?v0 f36)) (= (f61 f184 (f185 (f186 f187 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S26) (?v1 S8)) (=> (not (= ?v0 f41)) (= (f64 f188 (f189 (f190 f191 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S17) (?v1 S8)) (=> (not (= ?v0 f25)) (= (f67 f175 (f163 (f161 f162 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S13) (?v1 S8)) (=> (not (= ?v0 f21)) (= (f70 f174 (f160 (f158 f159 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S11) (?v1 S8)) (=> (not (= ?v0 f17)) (= (f116 f173 (f157 (f155 f156 ?v0) ?v1)) ?v1))))
(check-sat)
(exit)