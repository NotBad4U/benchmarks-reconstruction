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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S2)
(declare-fun f4 (S4 S5) S3)
(declare-fun f5 () S4)
(declare-fun f6 () S5)
(declare-fun f7 () S2)
(declare-fun f8 () S5)
(declare-fun f9 () S5)
(declare-fun f10 (S7 S6) S6)
(declare-fun f11 (S8 S9) S7)
(declare-fun f12 () S8)
(declare-fun f13 () S9)
(declare-fun f14 () S6)
(declare-fun f15 (S11 S10) S10)
(declare-fun f16 (S12 S13) S11)
(declare-fun f17 () S12)
(declare-fun f18 () S13)
(declare-fun f19 () S10)
(declare-fun f20 (S14 S5) S5)
(declare-fun f21 (S15 S16) S14)
(declare-fun f22 () S15)
(declare-fun f23 () S16)
(declare-fun f24 (S18 S17) S17)
(declare-fun f25 (S19 S20) S18)
(declare-fun f26 () S19)
(declare-fun f27 () S20)
(declare-fun f28 () S17)
(declare-fun f29 (S22 S21) S21)
(declare-fun f30 (S23 S24) S22)
(declare-fun f31 () S23)
(declare-fun f32 () S24)
(declare-fun f33 () S21)
(declare-fun f34 (S26 S25) S25)
(declare-fun f35 (S27 S28) S26)
(declare-fun f36 () S27)
(declare-fun f37 () S28)
(declare-fun f38 () S25)
(declare-fun f39 (S29 S16) S16)
(declare-fun f40 (S30 S25) S29)
(declare-fun f41 () S30)
(declare-fun f42 (S31 S13) S13)
(declare-fun f43 (S32 S21) S31)
(declare-fun f44 () S32)
(declare-fun f45 (S33 S9) S9)
(declare-fun f46 (S34 S17) S33)
(declare-fun f47 () S34)
(declare-fun f48 (S3) S1)
(declare-fun f49 (S35 S5) S6)
(declare-fun f50 (S36 S2) S35)
(declare-fun f51 () S36)
(declare-fun f52 (S37 S13) S6)
(declare-fun f53 (S38 S10) S37)
(declare-fun f54 () S38)
(declare-fun f55 (S39 S16) S6)
(declare-fun f56 (S40 S5) S39)
(declare-fun f57 () S40)
(declare-fun f58 (S41 S24) S6)
(declare-fun f59 (S42 S21) S41)
(declare-fun f60 () S42)
(declare-fun f61 (S43 S28) S6)
(declare-fun f62 (S44 S25) S43)
(declare-fun f63 () S44)
(declare-fun f64 (S45 S25) S6)
(declare-fun f65 (S46 S16) S45)
(declare-fun f66 () S46)
(declare-fun f67 (S47 S21) S6)
(declare-fun f68 (S48 S13) S47)
(declare-fun f69 () S48)
(declare-fun f70 (S49 S2) S5)
(declare-fun f71 (S50 S5) S49)
(declare-fun f72 () S50)
(declare-fun f73 (S51 S9) S17)
(declare-fun f74 (S52 S17) S51)
(declare-fun f75 () S52)
(declare-fun f76 (S53 S13) S21)
(declare-fun f77 (S54 S21) S53)
(declare-fun f78 () S54)
(declare-fun f79 (S55 S16) S25)
(declare-fun f80 (S56 S25) S55)
(declare-fun f81 () S56)
(declare-fun f82 (S57 S5) S16)
(declare-fun f83 (S58 S16) S57)
(declare-fun f84 () S58)
(declare-fun f85 (S59 S10) S13)
(declare-fun f86 (S60 S13) S59)
(declare-fun f87 () S60)
(declare-fun f88 (S61 S6) S9)
(declare-fun f89 (S62 S9) S61)
(declare-fun f90 () S62)
(declare-fun f91 (S63 S2) S14)
(declare-fun f92 () S63)
(declare-fun f93 (S64 S6) S5)
(declare-fun f94 (S65 S2) S64)
(declare-fun f95 () S65)
(declare-fun f96 (S66 S6) S61)
(declare-fun f97 () S66)
(declare-fun f98 (S67 S6) S13)
(declare-fun f99 (S68 S10) S67)
(declare-fun f100 () S68)
(declare-fun f101 (S69 S6) S16)
(declare-fun f102 (S70 S5) S69)
(declare-fun f103 () S70)
(declare-fun f104 (S71 S6) S20)
(declare-fun f105 (S72 S17) S71)
(declare-fun f106 () S72)
(declare-fun f107 (S73 S6) S24)
(declare-fun f108 (S74 S21) S73)
(declare-fun f109 () S74)
(declare-fun f110 (S75 S6) S28)
(declare-fun f111 (S76 S25) S75)
(declare-fun f112 () S76)
(declare-fun f113 (S77 S6) S25)
(declare-fun f114 (S78 S16) S77)
(declare-fun f115 () S78)
(declare-fun f116 (S79 S6) S21)
(declare-fun f117 (S80 S13) S79)
(declare-fun f118 () S80)
(declare-fun f119 (S81 S6) S17)
(declare-fun f120 (S82 S9) S81)
(declare-fun f121 () S82)
(declare-fun f122 (S83 S9) S18)
(declare-fun f123 () S83)
(declare-fun f124 (S84 S13) S22)
(declare-fun f125 () S84)
(declare-fun f126 (S85 S16) S26)
(declare-fun f127 () S85)
(declare-fun f128 (S86 S5) S29)
(declare-fun f129 () S86)
(declare-fun f130 (S87 S10) S31)
(declare-fun f131 () S87)
(declare-fun f132 (S88 S6) S33)
(declare-fun f133 () S88)
(declare-fun f134 (S89 S20) S20)
(declare-fun f135 (S90 S17) S89)
(declare-fun f136 () S90)
(declare-fun f137 (S91 S24) S24)
(declare-fun f138 (S92 S21) S91)
(declare-fun f139 () S92)
(declare-fun f140 (S93 S28) S28)
(declare-fun f141 (S94 S25) S93)
(declare-fun f142 () S94)
(declare-fun f143 (S95 S5) S1)
(declare-fun f144 (S96 S17) S1)
(declare-fun f145 (S97 S21) S1)
(declare-fun f146 (S98 S25) S1)
(declare-fun f147 (S99 S16) S1)
(declare-fun f148 (S100 S13) S1)
(declare-fun f149 (S101 S9) S1)
(declare-fun f150 () S35)
(declare-fun f151 (S102 S17) S6)
(declare-fun f152 () S102)
(declare-fun f153 () S47)
(declare-fun f154 () S45)
(declare-fun f155 () S39)
(declare-fun f156 () S37)
(declare-fun f157 (S103 S9) S6)
(declare-fun f158 () S103)
(declare-fun f159 () S50)
(declare-fun f160 () S54)
(declare-fun f161 () S56)
(declare-fun f162 () S52)
(declare-fun f163 () S62)
(declare-fun f164 () S58)
(declare-fun f165 () S60)
(declare-fun f166 () S7)
(declare-fun f167 (S104 S5) S14)
(declare-fun f168 () S104)
(declare-fun f169 (S105 S21) S22)
(declare-fun f170 () S105)
(declare-fun f171 (S106 S25) S26)
(declare-fun f172 () S106)
(declare-fun f173 (S107 S17) S18)
(declare-fun f174 () S107)
(declare-fun f175 (S108 S9) S33)
(declare-fun f176 () S108)
(declare-fun f177 (S109 S16) S29)
(declare-fun f178 () S109)
(declare-fun f179 (S110 S13) S31)
(declare-fun f180 () S110)
(declare-fun f181 () S35)
(declare-fun f182 () S102)
(declare-fun f183 () S47)
(declare-fun f184 () S45)
(declare-fun f185 () S39)
(declare-fun f186 () S37)
(declare-fun f187 () S103)
(declare-fun f188 (S5) S95)
(declare-fun f189 (S2 S2) S1)
(declare-fun f190 (S9) S101)
(declare-fun f191 (S6 S6) S1)
(declare-fun f192 (S13) S100)
(declare-fun f193 (S10 S10) S1)
(declare-fun f194 (S16) S99)
(declare-fun f195 (S20 S20) S1)
(declare-fun f196 (S17) S96)
(declare-fun f197 (S24 S24) S1)
(declare-fun f198 (S21) S97)
(declare-fun f199 (S28 S28) S1)
(declare-fun f200 (S25) S98)
(assert (not (= f1 f2)))
(assert (not (= (forall ((?v0 S2)) (=> (= (f3 (f4 f5 f6) ?v0) f7) (= (f3 (f4 f5 f8) ?v0) f7))) (= f8 f9))))
(assert (= f6 f9))
(assert (= f6 f9))
(assert (forall ((?v0 S2)) (= (f3 (f4 f5 f9) ?v0) f7)))
(assert (forall ((?v0 S6)) (= (f10 (f11 f12 f13) ?v0) f14)))
(assert (forall ((?v0 S10)) (= (f15 (f16 f17 f18) ?v0) f19)))
(assert (forall ((?v0 S5)) (= (f20 (f21 f22 f23) ?v0) f9)))
(assert (forall ((?v0 S17)) (= (f24 (f25 f26 f27) ?v0) f28)))
(assert (forall ((?v0 S21)) (= (f29 (f30 f31 f32) ?v0) f33)))
(assert (forall ((?v0 S25)) (= (f34 (f35 f36 f37) ?v0) f38)))
(assert (forall ((?v0 S16)) (= (f39 (f40 f41 f38) ?v0) f23)))
(assert (forall ((?v0 S13)) (= (f42 (f43 f44 f33) ?v0) f18)))
(assert (forall ((?v0 S9)) (= (f45 (f46 f47 f28) ?v0) f13)))
(assert (forall ((?v0 S5)) (= (= (f4 f5 ?v0) (f4 f5 f9)) (= ?v0 f9))))
(assert (forall ((?v0 S21)) (= (= (f43 f44 ?v0) (f43 f44 f33)) (= ?v0 f33))))
(assert (forall ((?v0 S13)) (= (= (f16 f17 ?v0) (f16 f17 f18)) (= ?v0 f18))))
(assert (forall ((?v0 S5)) (=> (not (= (f48 (f4 f5 ?v0)) f1)) (exists ((?v1 S2)) (= (f3 (f4 f5 ?v0) ?v1) f7)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f4 f5 ?v0) (f4 f5 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S21) (?v1 S21)) (= (= (f43 f44 ?v0) (f43 f44 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f16 f17 ?v0) (f16 f17 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (= (f3 (f4 f5 ?v0) ?v1) f7) (or (= ?v0 f9) (not (= (f49 (f50 f51 ?v1) ?v0) f14))))))
(assert (forall ((?v0 S13) (?v1 S10)) (= (= (f15 (f16 f17 ?v0) ?v1) f19) (or (= ?v0 f18) (not (= (f52 (f53 f54 ?v1) ?v0) f14))))))
(assert (forall ((?v0 S16) (?v1 S5)) (= (= (f20 (f21 f22 ?v0) ?v1) f9) (or (= ?v0 f23) (not (= (f55 (f56 f57 ?v1) ?v0) f14))))))
(assert (forall ((?v0 S24) (?v1 S21)) (= (= (f29 (f30 f31 ?v0) ?v1) f33) (or (= ?v0 f32) (not (= (f58 (f59 f60 ?v1) ?v0) f14))))))
(assert (forall ((?v0 S28) (?v1 S25)) (= (= (f34 (f35 f36 ?v0) ?v1) f38) (or (= ?v0 f37) (not (= (f61 (f62 f63 ?v1) ?v0) f14))))))
(assert (forall ((?v0 S25) (?v1 S16)) (= (= (f39 (f40 f41 ?v0) ?v1) f23) (or (= ?v0 f38) (not (= (f64 (f65 f66 ?v1) ?v0) f14))))))
(assert (forall ((?v0 S21) (?v1 S13)) (= (= (f42 (f43 f44 ?v0) ?v1) f18) (or (= ?v0 f33) (not (= (f67 (f68 f69 ?v1) ?v0) f14))))))
(assert (forall ((?v0 S6)) (= (= f14 ?v0) (= ?v0 f14))))
(assert (forall ((?v0 S10)) (= (= f19 ?v0) (= ?v0 f19))))
(assert (forall ((?v0 S5)) (= (= f9 ?v0) (= ?v0 f9))))
(assert (forall ((?v0 S2)) (= (= f7 ?v0) (= ?v0 f7))))
(assert (forall ((?v0 S17)) (= (= f28 ?v0) (= ?v0 f28))))
(assert (forall ((?v0 S21)) (= (= f33 ?v0) (= ?v0 f33))))
(assert (forall ((?v0 S25)) (= (= f38 ?v0) (= ?v0 f38))))
(assert (forall ((?v0 S16)) (= (= f23 ?v0) (= ?v0 f23))))
(assert (forall ((?v0 S13)) (= (= f18 ?v0) (= ?v0 f18))))
(assert (forall ((?v0 S9)) (= (= f13 ?v0) (= ?v0 f13))))
(assert (forall ((?v0 S2)) (= (f70 (f71 f72 f9) ?v0) f9)))
(assert (forall ((?v0 S9)) (= (f73 (f74 f75 f28) ?v0) f28)))
(assert (forall ((?v0 S13)) (= (f76 (f77 f78 f33) ?v0) f33)))
(assert (forall ((?v0 S16)) (= (f79 (f80 f81 f38) ?v0) f38)))
(assert (forall ((?v0 S5)) (= (f82 (f83 f84 f23) ?v0) f23)))
(assert (forall ((?v0 S10)) (= (f85 (f86 f87 f18) ?v0) f18)))
(assert (forall ((?v0 S6)) (= (f88 (f89 f90 f13) ?v0) f13)))
(assert (forall ((?v0 S5) (?v1 S2)) (= (= (f70 (f71 f72 ?v0) ?v1) f9) (= ?v0 f9))))
(assert (forall ((?v0 S17) (?v1 S9)) (= (= (f73 (f74 f75 ?v0) ?v1) f28) (= ?v0 f28))))
(assert (forall ((?v0 S21) (?v1 S13)) (= (= (f76 (f77 f78 ?v0) ?v1) f33) (= ?v0 f33))))
(assert (forall ((?v0 S25) (?v1 S16)) (= (= (f79 (f80 f81 ?v0) ?v1) f38) (= ?v0 f38))))
(assert (forall ((?v0 S16) (?v1 S5)) (= (= (f82 (f83 f84 ?v0) ?v1) f23) (= ?v0 f23))))
(assert (forall ((?v0 S13) (?v1 S10)) (= (= (f85 (f86 f87 ?v0) ?v1) f18) (= ?v0 f18))))
(assert (forall ((?v0 S9) (?v1 S6)) (= (= (f88 (f89 f90 ?v0) ?v1) f13) (= ?v0 f13))))
(assert (forall ((?v0 S5)) (=> (not (exists ((?v1 S2) (?v2 S5)) (and (not (= ?v1 f7)) (and (= ?v2 f9) (= ?v0 (f20 (f91 f92 ?v1) ?v2)))))) (exists ((?v1 S2)) (= (f3 (f4 f5 ?v0) ?v1) f7)))))
(assert (forall ((?v0 S6)) (= (f93 (f94 f95 f7) ?v0) f9)))
(assert (forall ((?v0 S6)) (= (f88 (f96 f97 f14) ?v0) f13)))
(assert (forall ((?v0 S6)) (= (f98 (f99 f100 f19) ?v0) f18)))
(assert (forall ((?v0 S6)) (= (f101 (f102 f103 f9) ?v0) f23)))
(assert (forall ((?v0 S6)) (= (f104 (f105 f106 f28) ?v0) f27)))
(assert (forall ((?v0 S6)) (= (f107 (f108 f109 f33) ?v0) f32)))
(assert (forall ((?v0 S6)) (= (f110 (f111 f112 f38) ?v0) f37)))
(assert (forall ((?v0 S6)) (= (f113 (f114 f115 f23) ?v0) f38)))
(assert (forall ((?v0 S6)) (= (f116 (f117 f118 f18) ?v0) f33)))
(assert (forall ((?v0 S6)) (= (f119 (f120 f121 f13) ?v0) f28)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f88 (f96 f97 ?v0) ?v1) f13) (= ?v0 f14))))
(assert (forall ((?v0 S10) (?v1 S6)) (= (= (f98 (f99 f100 ?v0) ?v1) f18) (= ?v0 f19))))
(assert (forall ((?v0 S5) (?v1 S6)) (= (= (f101 (f102 f103 ?v0) ?v1) f23) (= ?v0 f9))))
(assert (forall ((?v0 S2) (?v1 S6)) (= (= (f93 (f94 f95 ?v0) ?v1) f9) (= ?v0 f7))))
(assert (forall ((?v0 S17) (?v1 S6)) (= (= (f104 (f105 f106 ?v0) ?v1) f27) (= ?v0 f28))))
(assert (forall ((?v0 S21) (?v1 S6)) (= (= (f107 (f108 f109 ?v0) ?v1) f32) (= ?v0 f33))))
(assert (forall ((?v0 S25) (?v1 S6)) (= (= (f110 (f111 f112 ?v0) ?v1) f37) (= ?v0 f38))))
(assert (forall ((?v0 S16) (?v1 S6)) (= (= (f113 (f114 f115 ?v0) ?v1) f38) (= ?v0 f23))))
(assert (forall ((?v0 S13) (?v1 S6)) (= (= (f116 (f117 f118 ?v0) ?v1) f33) (= ?v0 f18))))
(assert (forall ((?v0 S9) (?v1 S6)) (= (= (f119 (f120 f121 ?v0) ?v1) f28) (= ?v0 f13))))
(assert (forall ((?v0 S2)) (= (f93 (f94 f95 ?v0) f14) (f20 (f91 f92 ?v0) f9))))
(assert (forall ((?v0 S9)) (= (f119 (f120 f121 ?v0) f14) (f24 (f122 f123 ?v0) f28))))
(assert (forall ((?v0 S13)) (= (f116 (f117 f118 ?v0) f14) (f29 (f124 f125 ?v0) f33))))
(assert (forall ((?v0 S16)) (= (f113 (f114 f115 ?v0) f14) (f34 (f126 f127 ?v0) f38))))
(assert (forall ((?v0 S5)) (= (f101 (f102 f103 ?v0) f14) (f39 (f128 f129 ?v0) f23))))
(assert (forall ((?v0 S10)) (= (f98 (f99 f100 ?v0) f14) (f42 (f130 f131 ?v0) f18))))
(assert (forall ((?v0 S6)) (= (f88 (f96 f97 ?v0) f14) (f45 (f132 f133 ?v0) f13))))
(assert (forall ((?v0 S9) (?v1 S6) (?v2 S9)) (= (= (f119 (f120 f121 ?v0) ?v1) (f119 (f120 f121 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S13) (?v1 S6) (?v2 S13)) (= (= (f116 (f117 f118 ?v0) ?v1) (f116 (f117 f118 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S16) (?v1 S6) (?v2 S16)) (= (= (f113 (f114 f115 ?v0) ?v1) (f113 (f114 f115 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f101 (f102 f103 ?v0) ?v1) (f101 (f102 f103 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S10) (?v1 S6) (?v2 S10)) (= (= (f98 (f99 f100 ?v0) ?v1) (f98 (f99 f100 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f88 (f96 f97 ?v0) ?v1) (f88 (f96 f97 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S2)) (= (= (f93 (f94 f95 ?v0) ?v1) (f93 (f94 f95 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2) (?v3 S5)) (= (= (f20 (f91 f92 ?v0) ?v1) (f20 (f91 f92 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S9) (?v1 S17) (?v2 S9) (?v3 S17)) (= (= (f24 (f122 f123 ?v0) ?v1) (f24 (f122 f123 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S13) (?v1 S21) (?v2 S13) (?v3 S21)) (= (= (f29 (f124 f125 ?v0) ?v1) (f29 (f124 f125 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S16) (?v1 S25) (?v2 S16) (?v3 S25)) (= (= (f34 (f126 f127 ?v0) ?v1) (f34 (f126 f127 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5) (?v1 S16) (?v2 S5) (?v3 S16)) (= (= (f39 (f128 f129 ?v0) ?v1) (f39 (f128 f129 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S10) (?v1 S13) (?v2 S10) (?v3 S13)) (= (= (f42 (f130 f131 ?v0) ?v1) (f42 (f130 f131 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S6) (?v3 S9)) (= (= (f45 (f132 f133 ?v0) ?v1) (f45 (f132 f133 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f20 (f91 f92 ?v0) f9))) (= (f70 (f71 f72 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_0 (f24 (f122 f123 ?v0) f28))) (= (f73 (f74 f75 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f29 (f124 f125 ?v0) f33))) (= (f76 (f77 f78 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S16) (?v1 S16)) (let ((?v_0 (f34 (f126 f127 ?v0) f38))) (= (f79 (f80 f81 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S5) (?v1 S5)) (let ((?v_0 (f39 (f128 f129 ?v0) f23))) (= (f82 (f83 f84 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f42 (f130 f131 ?v0) f18))) (= (f85 (f86 f87 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f45 (f132 f133 ?v0) f13))) (= (f88 (f89 f90 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S3)) (= (= (f48 ?v0) f1) (forall ((?v1 S2) (?v2 S2)) (= (f3 ?v0 ?v1) (f3 ?v0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S5)) (= (= (f20 (f91 f92 ?v0) ?v1) f9) (and (= ?v0 f7) (= ?v1 f9)))))
(assert (forall ((?v0 S6) (?v1 S9)) (= (= (f45 (f132 f133 ?v0) ?v1) f13) (and (= ?v0 f14) (= ?v1 f13)))))
(assert (forall ((?v0 S10) (?v1 S13)) (= (= (f42 (f130 f131 ?v0) ?v1) f18) (and (= ?v0 f19) (= ?v1 f18)))))
(assert (forall ((?v0 S5) (?v1 S16)) (= (= (f39 (f128 f129 ?v0) ?v1) f23) (and (= ?v0 f9) (= ?v1 f23)))))
(assert (forall ((?v0 S17) (?v1 S20)) (= (= (f134 (f135 f136 ?v0) ?v1) f27) (and (= ?v0 f28) (= ?v1 f27)))))
(assert (forall ((?v0 S21) (?v1 S24)) (= (= (f137 (f138 f139 ?v0) ?v1) f32) (and (= ?v0 f33) (= ?v1 f32)))))
(assert (forall ((?v0 S25) (?v1 S28)) (= (= (f140 (f141 f142 ?v0) ?v1) f37) (and (= ?v0 f38) (= ?v1 f37)))))
(assert (forall ((?v0 S16) (?v1 S25)) (= (= (f34 (f126 f127 ?v0) ?v1) f38) (and (= ?v0 f23) (= ?v1 f38)))))
(assert (forall ((?v0 S13) (?v1 S21)) (= (= (f29 (f124 f125 ?v0) ?v1) f33) (and (= ?v0 f18) (= ?v1 f33)))))
(assert (forall ((?v0 S9) (?v1 S17)) (= (= (f24 (f122 f123 ?v0) ?v1) f28) (and (= ?v0 f13) (= ?v1 f28)))))
(assert (= (f20 (f91 f92 f7) f9) f9))
(assert (= (f45 (f132 f133 f14) f13) f13))
(assert (= (f42 (f130 f131 f19) f18) f18))
(assert (= (f39 (f128 f129 f9) f23) f23))
(assert (= (f134 (f135 f136 f28) f27) f27))
(assert (= (f137 (f138 f139 f33) f32) f32))
(assert (= (f140 (f141 f142 f38) f37) f37))
(assert (= (f34 (f126 f127 f23) f38) f38))
(assert (= (f29 (f124 f125 f18) f33) f33))
(assert (= (f24 (f122 f123 f13) f28) f28))
(assert (forall ((?v0 S95) (?v1 S5)) (=> (= (f143 ?v0 f9) f1) (=> (forall ((?v2 S2) (?v3 S5)) (=> (= (f143 ?v0 ?v3) f1) (= (f143 ?v0 (f20 (f91 f92 ?v2) ?v3)) f1))) (= (f143 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S96) (?v1 S17)) (=> (= (f144 ?v0 f28) f1) (=> (forall ((?v2 S9) (?v3 S17)) (=> (= (f144 ?v0 ?v3) f1) (= (f144 ?v0 (f24 (f122 f123 ?v2) ?v3)) f1))) (= (f144 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S97) (?v1 S21)) (=> (= (f145 ?v0 f33) f1) (=> (forall ((?v2 S13) (?v3 S21)) (=> (= (f145 ?v0 ?v3) f1) (= (f145 ?v0 (f29 (f124 f125 ?v2) ?v3)) f1))) (= (f145 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S98) (?v1 S25)) (=> (= (f146 ?v0 f38) f1) (=> (forall ((?v2 S16) (?v3 S25)) (=> (= (f146 ?v0 ?v3) f1) (= (f146 ?v0 (f34 (f126 f127 ?v2) ?v3)) f1))) (= (f146 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S99) (?v1 S16)) (=> (= (f147 ?v0 f23) f1) (=> (forall ((?v2 S5) (?v3 S16)) (=> (= (f147 ?v0 ?v3) f1) (= (f147 ?v0 (f39 (f128 f129 ?v2) ?v3)) f1))) (= (f147 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S100) (?v1 S13)) (=> (= (f148 ?v0 f18) f1) (=> (forall ((?v2 S10) (?v3 S13)) (=> (= (f148 ?v0 ?v3) f1) (= (f148 ?v0 (f42 (f130 f131 ?v2) ?v3)) f1))) (= (f148 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S101) (?v1 S9)) (=> (= (f149 ?v0 f13) f1) (=> (forall ((?v2 S6) (?v3 S9)) (=> (= (f149 ?v0 ?v3) f1) (= (f149 ?v0 (f45 (f132 f133 ?v2) ?v3)) f1))) (= (f149 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S5)) (=> (forall ((?v1 S2) (?v2 S5)) (=> (= ?v0 (f20 (f91 f92 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S17)) (=> (forall ((?v1 S9) (?v2 S17)) (=> (= ?v0 (f24 (f122 f123 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S21)) (=> (forall ((?v1 S13) (?v2 S21)) (=> (= ?v0 (f29 (f124 f125 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S16) (?v2 S25)) (=> (= ?v0 (f34 (f126 f127 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S16)) (=> (forall ((?v1 S5) (?v2 S16)) (=> (= ?v0 (f39 (f128 f129 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S13)) (=> (forall ((?v1 S10) (?v2 S13)) (=> (= ?v0 (f42 (f130 f131 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S9)) (=> (forall ((?v1 S6) (?v2 S9)) (=> (= ?v0 (f45 (f132 f133 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S5)) (= (= (f49 f150 ?v0) f14) (= ?v0 f9))))
(assert (forall ((?v0 S17)) (= (= (f151 f152 ?v0) f14) (= ?v0 f28))))
(assert (forall ((?v0 S21)) (= (= (f67 f153 ?v0) f14) (= ?v0 f33))))
(assert (forall ((?v0 S25)) (= (= (f64 f154 ?v0) f14) (= ?v0 f38))))
(assert (forall ((?v0 S16)) (= (= (f55 f155 ?v0) f14) (= ?v0 f23))))
(assert (forall ((?v0 S13)) (= (= (f52 f156 ?v0) f14) (= ?v0 f18))))
(assert (forall ((?v0 S9)) (= (= (f157 f158 ?v0) f14) (= ?v0 f13))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2)) (= (f70 (f71 f159 (f20 (f91 f92 ?v0) ?v1)) ?v2) (f20 (f91 f92 (f3 (f4 f5 ?v1) ?v2)) (f70 (f71 f159 ?v1) ?v2)))))
(assert (forall ((?v0 S13) (?v1 S21) (?v2 S13)) (= (f76 (f77 f160 (f29 (f124 f125 ?v0) ?v1)) ?v2) (f29 (f124 f125 (f42 (f43 f44 ?v1) ?v2)) (f76 (f77 f160 ?v1) ?v2)))))
(assert (forall ((?v0 S16) (?v1 S25) (?v2 S16)) (= (f79 (f80 f161 (f34 (f126 f127 ?v0) ?v1)) ?v2) (f34 (f126 f127 (f39 (f40 f41 ?v1) ?v2)) (f79 (f80 f161 ?v1) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S17) (?v2 S9)) (= (f73 (f74 f162 (f24 (f122 f123 ?v0) ?v1)) ?v2) (f24 (f122 f123 (f45 (f46 f47 ?v1) ?v2)) (f73 (f74 f162 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S6)) (= (f88 (f89 f163 (f45 (f132 f133 ?v0) ?v1)) ?v2) (f45 (f132 f133 (f10 (f11 f12 ?v1) ?v2)) (f88 (f89 f163 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S16) (?v2 S5)) (= (f82 (f83 f164 (f39 (f128 f129 ?v0) ?v1)) ?v2) (f39 (f128 f129 (f20 (f21 f22 ?v1) ?v2)) (f82 (f83 f164 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S13) (?v2 S10)) (= (f85 (f86 f165 (f42 (f130 f131 ?v0) ?v1)) ?v2) (f42 (f130 f131 (f15 (f16 f17 ?v1) ?v2)) (f85 (f86 f165 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S6)) (let ((?v_0 (f94 f95 ?v0))) (= (f93 ?v_0 (f10 f166 ?v1)) (f20 (f91 f92 f7) (f93 ?v_0 ?v1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f96 f97 ?v0))) (= (f88 ?v_0 (f10 f166 ?v1)) (f45 (f132 f133 f14) (f88 ?v_0 ?v1))))))
(assert (forall ((?v0 S10) (?v1 S6)) (let ((?v_0 (f99 f100 ?v0))) (= (f98 ?v_0 (f10 f166 ?v1)) (f42 (f130 f131 f19) (f98 ?v_0 ?v1))))))
(assert (forall ((?v0 S5) (?v1 S6)) (let ((?v_0 (f102 f103 ?v0))) (= (f101 ?v_0 (f10 f166 ?v1)) (f39 (f128 f129 f9) (f101 ?v_0 ?v1))))))
(assert (forall ((?v0 S17) (?v1 S6)) (let ((?v_0 (f105 f106 ?v0))) (= (f104 ?v_0 (f10 f166 ?v1)) (f134 (f135 f136 f28) (f104 ?v_0 ?v1))))))
(assert (forall ((?v0 S21) (?v1 S6)) (let ((?v_0 (f108 f109 ?v0))) (= (f107 ?v_0 (f10 f166 ?v1)) (f137 (f138 f139 f33) (f107 ?v_0 ?v1))))))
(assert (forall ((?v0 S25) (?v1 S6)) (let ((?v_0 (f111 f112 ?v0))) (= (f110 ?v_0 (f10 f166 ?v1)) (f140 (f141 f142 f38) (f110 ?v_0 ?v1))))))
(assert (forall ((?v0 S16) (?v1 S6)) (let ((?v_0 (f114 f115 ?v0))) (= (f113 ?v_0 (f10 f166 ?v1)) (f34 (f126 f127 f23) (f113 ?v_0 ?v1))))))
(assert (forall ((?v0 S13) (?v1 S6)) (let ((?v_0 (f117 f118 ?v0))) (= (f116 ?v_0 (f10 f166 ?v1)) (f29 (f124 f125 f18) (f116 ?v_0 ?v1))))))
(assert (forall ((?v0 S9) (?v1 S6)) (let ((?v_0 (f120 f121 ?v0))) (= (f119 ?v_0 (f10 f166 ?v1)) (f24 (f122 f123 f13) (f119 ?v_0 ?v1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S2)) (= (f3 (f4 f5 (f20 (f167 f168 ?v0) ?v1)) ?v2) (f3 (f4 f5 ?v0) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S13)) (= (f42 (f43 f44 (f29 (f169 f170 ?v0) ?v1)) ?v2) (f42 (f43 f44 ?v0) (f42 (f43 f44 ?v1) ?v2)))))
(assert (forall ((?v0 S25) (?v1 S25) (?v2 S16)) (= (f39 (f40 f41 (f34 (f171 f172 ?v0) ?v1)) ?v2) (f39 (f40 f41 ?v0) (f39 (f40 f41 ?v1) ?v2)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S9)) (= (f45 (f46 f47 (f24 (f173 f174 ?v0) ?v1)) ?v2) (f45 (f46 f47 ?v0) (f45 (f46 f47 ?v1) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S6)) (= (f10 (f11 f12 (f45 (f175 f176 ?v0) ?v1)) ?v2) (f10 (f11 f12 ?v0) (f10 (f11 f12 ?v1) ?v2)))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S5)) (= (f20 (f21 f22 (f39 (f177 f178 ?v0) ?v1)) ?v2) (f20 (f21 f22 ?v0) (f20 (f21 f22 ?v1) ?v2)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S10)) (= (f15 (f16 f17 (f42 (f179 f180 ?v0) ?v1)) ?v2) (f15 (f16 f17 ?v0) (f15 (f16 f17 ?v1) ?v2)))))
(assert (forall ((?v0 S2)) (= (f49 f181 (f20 (f91 f92 ?v0) f9)) f14)))
(assert (forall ((?v0 S9)) (= (f151 f182 (f24 (f122 f123 ?v0) f28)) f14)))
(assert (forall ((?v0 S13)) (= (f67 f183 (f29 (f124 f125 ?v0) f33)) f14)))
(assert (forall ((?v0 S16)) (= (f64 f184 (f34 (f126 f127 ?v0) f38)) f14)))
(assert (forall ((?v0 S5)) (= (f55 f185 (f39 (f128 f129 ?v0) f23)) f14)))
(assert (forall ((?v0 S10)) (= (f52 f186 (f42 (f130 f131 ?v0) f18)) f14)))
(assert (forall ((?v0 S6)) (= (f157 f187 (f45 (f132 f133 ?v0) f13)) f14)))
(assert (forall ((?v0 S5)) (= (f20 (f167 f168 f9) ?v0) f9)))
(assert (forall ((?v0 S17)) (= (f24 (f173 f174 f28) ?v0) f28)))
(assert (forall ((?v0 S21)) (= (f29 (f169 f170 f33) ?v0) f33)))
(assert (forall ((?v0 S25)) (= (f34 (f171 f172 f38) ?v0) f38)))
(assert (forall ((?v0 S16)) (= (f39 (f177 f178 f23) ?v0) f23)))
(assert (forall ((?v0 S13)) (= (f42 (f179 f180 f18) ?v0) f18)))
(assert (forall ((?v0 S9)) (= (f45 (f175 f176 f13) ?v0) f13)))
(assert (forall ((?v0 S2) (?v1 S5)) (= (= (f143 (f188 (f20 (f91 f92 ?v0) ?v1)) f9) f1) (and (= (f189 ?v0 f7) f1) (= (f143 (f188 ?v1) f9) f1)))))
(assert (forall ((?v0 S6) (?v1 S9)) (= (= (f149 (f190 (f45 (f132 f133 ?v0) ?v1)) f13) f1) (and (= (f191 ?v0 f14) f1) (= (f149 (f190 ?v1) f13) f1)))))
(assert (forall ((?v0 S10) (?v1 S13)) (= (= (f148 (f192 (f42 (f130 f131 ?v0) ?v1)) f18) f1) (and (= (f193 ?v0 f19) f1) (= (f148 (f192 ?v1) f18) f1)))))
(assert (forall ((?v0 S5) (?v1 S16)) (= (= (f147 (f194 (f39 (f128 f129 ?v0) ?v1)) f23) f1) (and (= (f143 (f188 ?v0) f9) f1) (= (f147 (f194 ?v1) f23) f1)))))
(assert (forall ((?v0 S17) (?v1 S20)) (= (= (f195 (f134 (f135 f136 ?v0) ?v1) f27) f1) (and (= (f144 (f196 ?v0) f28) f1) (= (f195 ?v1 f27) f1)))))
(assert (forall ((?v0 S21) (?v1 S24)) (= (= (f197 (f137 (f138 f139 ?v0) ?v1) f32) f1) (and (= (f145 (f198 ?v0) f33) f1) (= (f197 ?v1 f32) f1)))))
(assert (forall ((?v0 S25) (?v1 S28)) (= (= (f199 (f140 (f141 f142 ?v0) ?v1) f37) f1) (and (= (f146 (f200 ?v0) f38) f1) (= (f199 ?v1 f37) f1)))))
(assert (forall ((?v0 S16) (?v1 S25)) (= (= (f146 (f200 (f34 (f126 f127 ?v0) ?v1)) f38) f1) (and (= (f147 (f194 ?v0) f23) f1) (= (f146 (f200 ?v1) f38) f1)))))
(assert (forall ((?v0 S13) (?v1 S21)) (= (= (f145 (f198 (f29 (f124 f125 ?v0) ?v1)) f33) f1) (and (= (f148 (f192 ?v0) f18) f1) (= (f145 (f198 ?v1) f33) f1)))))
(assert (forall ((?v0 S9) (?v1 S17)) (= (= (f144 (f196 (f24 (f122 f123 ?v0) ?v1)) f28) f1) (and (= (f149 (f190 ?v0) f13) f1) (= (f144 (f196 ?v1) f28) f1)))))
(assert (forall ((?v0 S2) (?v1 S5)) (let ((?v_0 (f188 f9))) (= (= (f143 ?v_0 (f20 (f91 f92 ?v0) ?v1)) f1) (and (= (f189 f7 ?v0) f1) (= (f143 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S6) (?v1 S9)) (let ((?v_0 (f190 f13))) (= (= (f149 ?v_0 (f45 (f132 f133 ?v0) ?v1)) f1) (and (= (f191 f14 ?v0) f1) (= (f149 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S10) (?v1 S13)) (let ((?v_0 (f192 f18))) (= (= (f148 ?v_0 (f42 (f130 f131 ?v0) ?v1)) f1) (and (= (f193 f19 ?v0) f1) (= (f148 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S5) (?v1 S16)) (let ((?v_0 (f194 f23))) (= (= (f147 ?v_0 (f39 (f128 f129 ?v0) ?v1)) f1) (and (= (f143 (f188 f9) ?v0) f1) (= (f147 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S17) (?v1 S20)) (= (= (f195 f27 (f134 (f135 f136 ?v0) ?v1)) f1) (and (= (f144 (f196 f28) ?v0) f1) (= (f195 f27 ?v1) f1)))))
(assert (forall ((?v0 S21) (?v1 S24)) (= (= (f197 f32 (f137 (f138 f139 ?v0) ?v1)) f1) (and (= (f145 (f198 f33) ?v0) f1) (= (f197 f32 ?v1) f1)))))
(assert (forall ((?v0 S25) (?v1 S28)) (= (= (f199 f37 (f140 (f141 f142 ?v0) ?v1)) f1) (and (= (f146 (f200 f38) ?v0) f1) (= (f199 f37 ?v1) f1)))))
(assert (forall ((?v0 S16) (?v1 S25)) (let ((?v_0 (f200 f38))) (= (= (f146 ?v_0 (f34 (f126 f127 ?v0) ?v1)) f1) (and (= (f147 (f194 f23) ?v0) f1) (= (f146 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S21)) (let ((?v_0 (f198 f33))) (= (= (f145 ?v_0 (f29 (f124 f125 ?v0) ?v1)) f1) (and (= (f148 (f192 f18) ?v0) f1) (= (f145 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S9) (?v1 S17)) (let ((?v_0 (f196 f28))) (= (= (f144 ?v_0 (f24 (f122 f123 ?v0) ?v1)) f1) (and (= (f149 (f190 f13) ?v0) f1) (= (f144 ?v_0 ?v1) f1))))))
(check-sat)
(exit)