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
(declare-sort S112 0)
(declare-sort S113 0)
(declare-sort S114 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S2) S3)
(declare-fun f5 (S2) S3)
(declare-fun f6 (S5 S4) S1)
(declare-fun f7 (S4) S5)
(declare-fun f8 (S4) S5)
(declare-fun f9 (S6 S3) S1)
(declare-fun f10 (S3) S6)
(declare-fun f11 (S3) S6)
(declare-fun f12 (S7 S5) S1)
(declare-fun f13 (S5) S7)
(declare-fun f14 (S5) S7)
(declare-fun f15 (S8 S6) S1)
(declare-fun f16 (S6) S8)
(declare-fun f17 (S6) S8)
(declare-fun f18 (S9 S7) S1)
(declare-fun f19 (S7) S9)
(declare-fun f20 (S7 S7) S1)
(declare-fun f21 (S10 S8) S1)
(declare-fun f22 (S8) S10)
(declare-fun f23 (S8 S8) S1)
(declare-fun f24 (S12 S11) S1)
(declare-fun f25 (S11) S12)
(declare-fun f26 (S11 S11) S1)
(declare-fun f27 (S11 S13) S1)
(declare-fun f28 (S13) S11)
(declare-fun f29 (S13) S11)
(declare-fun f30 (S13 S14) S1)
(declare-fun f31 (S14) S13)
(declare-fun f32 (S14) S13)
(declare-fun f33 (S4 S15) S1)
(declare-fun f34 (S16 S4) S4)
(declare-fun f35 (S4) S16)
(declare-fun f36 (S17 S3) S3)
(declare-fun f37 (S3) S17)
(declare-fun f38 (S18 S5) S5)
(declare-fun f39 (S5) S18)
(declare-fun f40 (S19 S6) S6)
(declare-fun f41 (S6) S19)
(declare-fun f42 (S20 S13) S13)
(declare-fun f43 (S13) S20)
(declare-fun f44 (S14 S21) S1)
(declare-fun f45 (S22 S14) S14)
(declare-fun f46 (S14) S22)
(declare-fun f47 (S14) S13)
(declare-fun f48 () S14)
(declare-fun f49 (S21) S22)
(declare-fun f50 (S23 S24) S21)
(declare-fun f51 () S23)
(declare-fun f52 () S24)
(declare-fun f53 () S14)
(declare-fun f54 (S4) S1)
(declare-fun f55 () S4)
(declare-fun f56 (S25 S4) S14)
(declare-fun f57 (S26) S25)
(declare-fun f58 () S26)
(declare-fun f59 (S27 S14) S2)
(declare-fun f60 () S27)
(declare-fun f61 (S28 S2) S2)
(declare-fun f62 (S29 S2) S28)
(declare-fun f63 () S29)
(declare-fun f64 () S2)
(declare-fun f65 (S24) S1)
(declare-fun f66 () S28)
(declare-fun f67 (S15) S5)
(declare-fun f68 (S26 S15) S21)
(declare-fun f69 (S3) S1)
(declare-fun f70 (S6) S1)
(declare-fun f71 (S6) S6)
(declare-fun f72 (S5) S1)
(declare-fun f73 (S5) S5)
(declare-fun f74 (S14) S1)
(declare-fun f75 (S13) S1)
(declare-fun f76 (S13) S13)
(declare-fun f77 (S8) S1)
(declare-fun f78 (S10) S1)
(declare-fun f79 (S10) S10)
(declare-fun f80 (S7) S1)
(declare-fun f81 (S9) S1)
(declare-fun f82 (S9) S9)
(declare-fun f83 (S11) S1)
(declare-fun f84 (S12) S1)
(declare-fun f85 (S12) S12)
(declare-fun f86 (S11) S11)
(declare-fun f87 (S7) S7)
(declare-fun f88 (S8) S8)
(declare-fun f89 (S31 S8) S3)
(declare-fun f90 (S30) S31)
(declare-fun f91 (S33 S7) S3)
(declare-fun f92 (S32) S33)
(declare-fun f93 (S35 S11) S3)
(declare-fun f94 (S34) S35)
(declare-fun f95 (S36 S13) S3)
(declare-fun f96 (S27) S36)
(declare-fun f97 (S38 S5) S3)
(declare-fun f98 (S37) S38)
(declare-fun f99 (S40 S6) S3)
(declare-fun f100 (S39) S40)
(declare-fun f101 (S42 S14) S3)
(declare-fun f102 (S41) S42)
(declare-fun f103 (S44 S8) S4)
(declare-fun f104 (S43) S44)
(declare-fun f105 (S46 S7) S4)
(declare-fun f106 (S45) S46)
(declare-fun f107 (S48 S11) S4)
(declare-fun f108 (S47) S48)
(declare-fun f109 (S50 S13) S4)
(declare-fun f110 (S49) S50)
(declare-fun f111 (S52 S5) S4)
(declare-fun f112 (S51) S52)
(declare-fun f113 (S54 S6) S4)
(declare-fun f114 (S53) S54)
(declare-fun f115 (S56 S14) S4)
(declare-fun f116 (S55) S56)
(declare-fun f117 (S58 S3) S8)
(declare-fun f118 (S57) S58)
(declare-fun f119 (S60 S3) S7)
(declare-fun f120 (S59) S60)
(declare-fun f121 (S62 S3) S11)
(declare-fun f122 (S61) S62)
(declare-fun f123 (S64 S3) S13)
(declare-fun f124 (S63) S64)
(declare-fun f125 (S66 S3) S5)
(declare-fun f126 (S65) S66)
(declare-fun f127 (S68 S3) S6)
(declare-fun f128 (S67) S68)
(declare-fun f129 (S70 S3) S14)
(declare-fun f130 (S69) S70)
(declare-fun f131 (S72 S4) S8)
(declare-fun f132 (S71) S72)
(declare-fun f133 (S74 S4) S7)
(declare-fun f134 (S73) S74)
(declare-fun f135 (S76 S4) S11)
(declare-fun f136 (S75) S76)
(declare-fun f137 (S78 S4) S13)
(declare-fun f138 (S77) S78)
(declare-fun f139 (S80 S4) S5)
(declare-fun f140 (S79) S80)
(declare-fun f141 (S82 S4) S6)
(declare-fun f142 (S81) S82)
(declare-fun f143 (S84 S4) S3)
(declare-fun f144 (S83) S84)
(declare-fun f145 (S86 S3) S4)
(declare-fun f146 (S85) S86)
(declare-fun f147 (S87) S16)
(declare-fun f148 (S88) S22)
(declare-fun f149 (S90 S6) S14)
(declare-fun f150 (S89) S90)
(declare-fun f151 (S92 S5) S14)
(declare-fun f152 (S91) S92)
(declare-fun f153 (S94 S13) S14)
(declare-fun f154 (S93) S94)
(declare-fun f155 () S6)
(declare-fun f156 () S5)
(declare-fun f157 () S13)
(declare-fun f158 () S3)
(declare-fun f159 () S4)
(declare-fun f160 (S2) S17)
(declare-fun f161 (S15) S16)
(declare-fun f162 (S95 S8) S8)
(declare-fun f163 (S6) S95)
(declare-fun f164 (S96 S7) S7)
(declare-fun f165 (S5) S96)
(declare-fun f166 (S97 S11) S11)
(declare-fun f167 (S13) S97)
(declare-fun f168 (S14) S20)
(declare-fun f169 (S4) S18)
(declare-fun f170 (S3) S19)
(declare-fun f171 () S8)
(declare-fun f172 () S7)
(declare-fun f173 () S11)
(declare-fun f174 (S37 S4) S2)
(declare-fun f175 () S37)
(declare-fun f176 (S39 S3) S2)
(declare-fun f177 () S39)
(declare-fun f178 (S30 S6) S2)
(declare-fun f179 () S30)
(declare-fun f180 (S99 S14) S6)
(declare-fun f181 (S98) S99)
(declare-fun f182 (S32 S5) S2)
(declare-fun f183 () S32)
(declare-fun f184 (S101 S14) S5)
(declare-fun f185 (S100) S101)
(declare-fun f186 (S34 S13) S2)
(declare-fun f187 () S34)
(declare-fun f188 (S103 S14) S13)
(declare-fun f189 (S102) S103)
(declare-fun f190 (S104 S8) S2)
(declare-fun f191 () S104)
(declare-fun f192 (S105 S7) S2)
(declare-fun f193 () S105)
(declare-fun f194 (S106 S11) S2)
(declare-fun f195 () S106)
(declare-fun f196 (S108 S8) S14)
(declare-fun f197 (S107) S108)
(declare-fun f198 (S110 S7) S14)
(declare-fun f199 (S109) S110)
(declare-fun f200 (S112 S11) S14)
(declare-fun f201 (S111) S112)
(declare-fun f202 (S21) S13)
(declare-fun f203 (S2) S6)
(declare-fun f204 (S6 S8) S1)
(declare-fun f205 (S5 S7) S1)
(declare-fun f206 (S13 S11) S1)
(declare-fun f207 (S14) S11)
(declare-fun f208 (S4) S7)
(declare-fun f209 (S3) S8)
(declare-fun f210 (S113 S114) S24)
(declare-fun f211 () S113)
(declare-fun f212 (S15) S114)
(declare-fun f213 (S83 S15) S2)
(declare-fun f214 (S55 S21) S15)
(declare-fun f215 (S85 S2) S15)
(declare-fun f216 (S81 S15) S3)
(declare-fun f217 (S79 S15) S4)
(declare-fun f218 (S77 S15) S14)
(declare-fun f219 (S69 S2) S21)
(declare-fun f220 (S67 S2) S3)
(declare-fun f221 (S65 S2) S4)
(declare-fun f222 (S63 S2) S14)
(declare-fun f223 (S53 S3) S15)
(declare-fun f224 (S51 S4) S15)
(declare-fun f225 (S49 S14) S15)
(declare-fun f226 (S14) S14)
(declare-fun f227 (S4) S4)
(declare-fun f228 (S3) S3)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 ?v0) ?v1) f1) (= (f3 (f5 ?v1) ?v0) f1))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f6 (f7 ?v0) ?v1) f1) (= (f6 (f8 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f9 (f10 ?v0) ?v1) f1) (= (f9 (f11 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f12 (f13 ?v0) ?v1) f1) (= (f12 (f14 ?v1) ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f15 (f16 ?v0) ?v1) f1) (= (f15 (f17 ?v1) ?v0) f1))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f18 (f19 ?v0) ?v1) f1) (= (f20 ?v1 ?v0) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f21 (f22 ?v0) ?v1) f1) (= (f23 ?v1 ?v0) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f24 (f25 ?v0) ?v1) f1) (= (f26 ?v1 ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f27 (f28 ?v0) ?v1) f1) (= (f27 (f29 ?v1) ?v0) f1))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f30 (f31 ?v0) ?v1) f1) (= (f30 (f32 ?v1) ?v0) f1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S15)) (= (= (f33 (f34 (f35 ?v0) ?v1) ?v2) f1) (and (= (f33 ?v0 ?v2) f1) (= (f33 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (= (= (f3 (f36 (f37 ?v0) ?v1) ?v2) f1) (and (= (f3 ?v0 ?v2) f1) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S4)) (= (= (f6 (f38 (f39 ?v0) ?v1) ?v2) f1) (and (= (f6 ?v0 ?v2) f1) (= (f6 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (= (= (f9 (f40 (f41 ?v0) ?v1) ?v2) f1) (and (= (f9 ?v0 ?v2) f1) (= (f9 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S14)) (= (= (f30 (f42 (f43 ?v0) ?v1) ?v2) f1) (and (= (f30 ?v0 ?v2) f1) (= (f30 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S21)) (= (= (f44 (f45 (f46 ?v0) ?v1) ?v2) f1) (and (= (f44 ?v0 ?v2) f1) (= (f44 ?v1 ?v2) f1)))))
(assert (not (= (f30 (f47 f48) (f45 (f49 (f50 f51 f52)) f53)) f1)))
(assert (= (f54 f55) f1))
(assert (forall ((?v0 S14)) (let ((?v_0 (f56 (f57 f58) f55))) (=> (= (f30 (f32 ?v0) ?v_0) f1) (=> (= (f59 f60 ?v0) (f61 (f62 f63 (f59 f60 ?v_0)) f64)) (forall ((?v1 S24)) (=> (= (f65 ?v1) f1) (= (f30 (f47 ?v0) (f45 (f49 (f50 f51 ?v1)) f53)) f1))))))))
(assert (= (f30 (f32 f48) (f56 (f57 f58) f55)) f1))
(assert (= (f3 (f5 (f61 f66 f64)) (f59 f60 (f56 (f57 f58) f55))) f1))
(assert (= (f59 f60 f48) (f61 (f62 f63 (f59 f60 (f56 (f57 f58) f55))) (f61 f66 f64))))
(assert (= (f65 f52) f1))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f30 (f32 ?v0) ?v1) f1) (= (f30 (f47 ?v1) ?v0) f1))))
(assert (forall ((?v0 S24) (?v1 S14)) (=> (= (f65 ?v0) f1) (=> (forall ((?v2 S15)) (=> (= (f6 (f67 ?v2) f55) f1) (= (f30 (f47 ?v1) (f45 (f49 (f68 f58 ?v2)) f53)) f1))) (= (f30 (f47 ?v1) (f45 (f49 (f50 f51 ?v0)) f53)) f1)))))
(assert (forall ((?v0 S3)) (=> (= (f69 ?v0) f1) (= (f70 (f71 (f10 ?v0))) f1))))
(assert (forall ((?v0 S4)) (=> (= (f54 ?v0) f1) (= (f72 (f73 (f7 ?v0))) f1))))
(assert (forall ((?v0 S14)) (=> (= (f74 ?v0) f1) (= (f75 (f76 (f31 ?v0))) f1))))
(assert (forall ((?v0 S8)) (=> (= (f77 ?v0) f1) (= (f78 (f79 (f22 ?v0))) f1))))
(assert (forall ((?v0 S7)) (=> (= (f80 ?v0) f1) (= (f81 (f82 (f19 ?v0))) f1))))
(assert (forall ((?v0 S11)) (=> (= (f83 ?v0) f1) (= (f84 (f85 (f25 ?v0))) f1))))
(assert (forall ((?v0 S13)) (=> (= (f75 ?v0) f1) (= (f83 (f86 (f28 ?v0))) f1))))
(assert (forall ((?v0 S5)) (=> (= (f72 ?v0) f1) (= (f80 (f87 (f13 ?v0))) f1))))
(assert (forall ((?v0 S6)) (=> (= (f70 ?v0) f1) (= (f77 (f88 (f16 ?v0))) f1))))
(assert (forall ((?v0 S4) (?v1 S26)) (=> (= (f54 ?v0) f1) (= (f74 (f56 (f57 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S8) (?v1 S30)) (=> (= (f77 ?v0) f1) (= (f69 (f89 (f90 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S7) (?v1 S32)) (=> (= (f80 ?v0) f1) (= (f69 (f91 (f92 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S11) (?v1 S34)) (=> (= (f83 ?v0) f1) (= (f69 (f93 (f94 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S13) (?v1 S27)) (=> (= (f75 ?v0) f1) (= (f69 (f95 (f96 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S5) (?v1 S37)) (=> (= (f72 ?v0) f1) (= (f69 (f97 (f98 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S6) (?v1 S39)) (=> (= (f70 ?v0) f1) (= (f69 (f99 (f100 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S41)) (=> (= (f74 ?v0) f1) (= (f69 (f101 (f102 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S8) (?v1 S43)) (=> (= (f77 ?v0) f1) (= (f54 (f103 (f104 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S7) (?v1 S45)) (=> (= (f80 ?v0) f1) (= (f54 (f105 (f106 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S11) (?v1 S47)) (=> (= (f83 ?v0) f1) (= (f54 (f107 (f108 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S13) (?v1 S49)) (=> (= (f75 ?v0) f1) (= (f54 (f109 (f110 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S5) (?v1 S51)) (=> (= (f72 ?v0) f1) (= (f54 (f111 (f112 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S6) (?v1 S53)) (=> (= (f70 ?v0) f1) (= (f54 (f113 (f114 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S55)) (=> (= (f74 ?v0) f1) (= (f54 (f115 (f116 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S57)) (=> (= (f69 ?v0) f1) (= (f77 (f117 (f118 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S59)) (=> (= (f69 ?v0) f1) (= (f80 (f119 (f120 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S61)) (=> (= (f69 ?v0) f1) (= (f83 (f121 (f122 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S63)) (=> (= (f69 ?v0) f1) (= (f75 (f123 (f124 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S65)) (=> (= (f69 ?v0) f1) (= (f72 (f125 (f126 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S67)) (=> (= (f69 ?v0) f1) (= (f70 (f127 (f128 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S69)) (=> (= (f69 ?v0) f1) (= (f74 (f129 (f130 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S71)) (=> (= (f54 ?v0) f1) (= (f77 (f131 (f132 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S73)) (=> (= (f54 ?v0) f1) (= (f80 (f133 (f134 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S75)) (=> (= (f54 ?v0) f1) (= (f83 (f135 (f136 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S77)) (=> (= (f54 ?v0) f1) (= (f75 (f137 (f138 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S79)) (=> (= (f54 ?v0) f1) (= (f72 (f139 (f140 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S81)) (=> (= (f54 ?v0) f1) (= (f70 (f141 (f142 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S83)) (=> (= (f54 ?v0) f1) (= (f69 (f143 (f144 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S85)) (=> (= (f69 ?v0) f1) (= (f54 (f145 (f146 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S87)) (=> (= (f54 ?v0) f1) (= (f54 (f34 (f147 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S88)) (=> (= (f74 ?v0) f1) (= (f74 (f45 (f148 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S6) (?v1 S89)) (=> (= (f70 ?v0) f1) (= (f74 (f149 (f150 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S5) (?v1 S91)) (=> (= (f72 ?v0) f1) (= (f74 (f151 (f152 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S13) (?v1 S93)) (=> (= (f75 ?v0) f1) (= (f74 (f153 (f154 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S14)) (= (f30 (f32 f53) ?v0) f1)))
(assert (forall ((?v0 S6)) (= (f15 (f17 f155) ?v0) f1)))
(assert (forall ((?v0 S5)) (= (f12 (f14 f156) ?v0) f1)))
(assert (forall ((?v0 S13)) (= (f27 (f29 f157) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f9 (f11 f158) ?v0) f1)))
(assert (forall ((?v0 S4)) (= (f6 (f8 f159) ?v0) f1)))
(assert (forall ((?v0 S14) (?v1 S21)) (=> (= (f74 ?v0) f1) (= (f74 (f45 (f49 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f69 ?v0) f1) (= (f69 (f36 (f160 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S15)) (=> (= (f54 ?v0) f1) (= (f54 (f34 (f161 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S8) (?v1 S6)) (=> (= (f77 ?v0) f1) (= (f77 (f162 (f163 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S7) (?v1 S5)) (=> (= (f80 ?v0) f1) (= (f80 (f164 (f165 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S11) (?v1 S13)) (=> (= (f83 ?v0) f1) (= (f83 (f166 (f167 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S13) (?v1 S14)) (=> (= (f75 ?v0) f1) (= (f75 (f42 (f168 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S5) (?v1 S4)) (=> (= (f72 ?v0) f1) (= (f72 (f38 (f169 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S6) (?v1 S3)) (=> (= (f70 ?v0) f1) (= (f70 (f40 (f170 ?v1) ?v0)) f1))))
(assert (= (f69 f158) f1))
(assert (= (f54 f159) f1))
(assert (= (f74 f53) f1))
(assert (= (f77 f171) f1))
(assert (= (f80 f172) f1))
(assert (= (f83 f173) f1))
(assert (= (f75 f157) f1))
(assert (= (f72 f156) f1))
(assert (= (f70 f155) f1))
(assert (forall ((?v0 S4) (?v1 S26)) (=> (= (f54 ?v0) f1) (= (f3 (f5 (f59 f60 (f56 (f57 ?v1) ?v0))) (f174 f175 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S85)) (=> (= (f69 ?v0) f1) (= (f3 (f5 (f174 f175 (f145 (f146 ?v1) ?v0))) (f176 f177 ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S98)) (=> (= (f74 ?v0) f1) (= (f3 (f5 (f178 f179 (f180 (f181 ?v1) ?v0))) (f59 f60 ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S100)) (=> (= (f74 ?v0) f1) (= (f3 (f5 (f182 f183 (f184 (f185 ?v1) ?v0))) (f59 f60 ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S102)) (=> (= (f74 ?v0) f1) (= (f3 (f5 (f186 f187 (f188 (f189 ?v1) ?v0))) (f59 f60 ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S55)) (=> (= (f74 ?v0) f1) (= (f3 (f5 (f174 f175 (f115 (f116 ?v1) ?v0))) (f59 f60 ?v0)) f1))))
(assert (forall ((?v0 S8) (?v1 S30)) (=> (= (f77 ?v0) f1) (= (f3 (f5 (f176 f177 (f89 (f90 ?v1) ?v0))) (f190 f191 ?v0)) f1))))
(assert (forall ((?v0 S7) (?v1 S32)) (=> (= (f80 ?v0) f1) (= (f3 (f5 (f176 f177 (f91 (f92 ?v1) ?v0))) (f192 f193 ?v0)) f1))))
(assert (forall ((?v0 S11) (?v1 S34)) (=> (= (f83 ?v0) f1) (= (f3 (f5 (f176 f177 (f93 (f94 ?v1) ?v0))) (f194 f195 ?v0)) f1))))
(assert (forall ((?v0 S13) (?v1 S27)) (=> (= (f75 ?v0) f1) (= (f3 (f5 (f176 f177 (f95 (f96 ?v1) ?v0))) (f186 f187 ?v0)) f1))))
(assert (forall ((?v0 S5) (?v1 S37)) (=> (= (f72 ?v0) f1) (= (f3 (f5 (f176 f177 (f97 (f98 ?v1) ?v0))) (f182 f183 ?v0)) f1))))
(assert (forall ((?v0 S6) (?v1 S39)) (=> (= (f70 ?v0) f1) (= (f3 (f5 (f176 f177 (f99 (f100 ?v1) ?v0))) (f178 f179 ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S41)) (=> (= (f74 ?v0) f1) (= (f3 (f5 (f176 f177 (f101 (f102 ?v1) ?v0))) (f59 f60 ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S83)) (=> (= (f54 ?v0) f1) (= (f3 (f5 (f176 f177 (f143 (f144 ?v1) ?v0))) (f174 f175 ?v0)) f1))))
(assert (forall ((?v0 S8) (?v1 S107)) (=> (= (f77 ?v0) f1) (= (f3 (f5 (f59 f60 (f196 (f197 ?v1) ?v0))) (f190 f191 ?v0)) f1))))
(assert (forall ((?v0 S7) (?v1 S109)) (=> (= (f80 ?v0) f1) (= (f3 (f5 (f59 f60 (f198 (f199 ?v1) ?v0))) (f192 f193 ?v0)) f1))))
(assert (forall ((?v0 S11) (?v1 S111)) (=> (= (f83 ?v0) f1) (= (f3 (f5 (f59 f60 (f200 (f201 ?v1) ?v0))) (f194 f195 ?v0)) f1))))
(assert (forall ((?v0 S13) (?v1 S93)) (=> (= (f75 ?v0) f1) (= (f3 (f5 (f59 f60 (f153 (f154 ?v1) ?v0))) (f186 f187 ?v0)) f1))))
(assert (forall ((?v0 S5) (?v1 S91)) (=> (= (f72 ?v0) f1) (= (f3 (f5 (f59 f60 (f151 (f152 ?v1) ?v0))) (f182 f183 ?v0)) f1))))
(assert (forall ((?v0 S6) (?v1 S89)) (=> (= (f70 ?v0) f1) (= (f3 (f5 (f59 f60 (f149 (f150 ?v1) ?v0))) (f178 f179 ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S88)) (=> (= (f74 ?v0) f1) (= (f3 (f5 (f59 f60 (f45 (f148 ?v1) ?v0))) (f59 f60 ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S87)) (=> (= (f54 ?v0) f1) (= (f3 (f5 (f174 f175 (f34 (f147 ?v1) ?v0))) (f174 f175 ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S81)) (=> (= (f54 ?v0) f1) (= (f3 (f5 (f178 f179 (f141 (f142 ?v1) ?v0))) (f174 f175 ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S79)) (=> (= (f54 ?v0) f1) (= (f3 (f5 (f182 f183 (f139 (f140 ?v1) ?v0))) (f174 f175 ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S77)) (=> (= (f54 ?v0) f1) (= (f3 (f5 (f186 f187 (f137 (f138 ?v1) ?v0))) (f174 f175 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S69)) (=> (= (f69 ?v0) f1) (= (f3 (f5 (f59 f60 (f129 (f130 ?v1) ?v0))) (f176 f177 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S67)) (=> (= (f69 ?v0) f1) (= (f3 (f5 (f178 f179 (f127 (f128 ?v1) ?v0))) (f176 f177 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S65)) (=> (= (f69 ?v0) f1) (= (f3 (f5 (f182 f183 (f125 (f126 ?v1) ?v0))) (f176 f177 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S63)) (=> (= (f69 ?v0) f1) (= (f3 (f5 (f186 f187 (f123 (f124 ?v1) ?v0))) (f176 f177 ?v0)) f1))))
(assert (forall ((?v0 S6) (?v1 S53)) (=> (= (f70 ?v0) f1) (= (f3 (f5 (f174 f175 (f113 (f114 ?v1) ?v0))) (f178 f179 ?v0)) f1))))
(assert (forall ((?v0 S5) (?v1 S51)) (=> (= (f72 ?v0) f1) (= (f3 (f5 (f174 f175 (f111 (f112 ?v1) ?v0))) (f182 f183 ?v0)) f1))))
(assert (forall ((?v0 S13) (?v1 S49)) (=> (= (f75 ?v0) f1) (= (f3 (f5 (f174 f175 (f109 (f110 ?v1) ?v0))) (f186 f187 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f69 ?v0) f1) (=> (= (f9 (f11 ?v1) ?v0) f1) (= (f3 (f5 (f176 f177 ?v1)) (f176 f177 ?v0)) f1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f74 ?v0) f1) (=> (= (f30 (f32 ?v1) ?v0) f1) (= (f3 (f5 (f59 f60 ?v1)) (f59 f60 ?v0)) f1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (= (f54 ?v0) f1) (=> (= (f6 (f8 ?v1) ?v0) f1) (= (f3 (f5 (f174 f175 ?v1)) (f174 f175 ?v0)) f1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f77 ?v0) f1) (=> (= (f23 ?v1 ?v0) f1) (= (f3 (f5 (f190 f191 ?v1)) (f190 f191 ?v0)) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f80 ?v0) f1) (=> (= (f20 ?v1 ?v0) f1) (= (f3 (f5 (f192 f193 ?v1)) (f192 f193 ?v0)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f83 ?v0) f1) (=> (= (f26 ?v1 ?v0) f1) (= (f3 (f5 (f194 f195 ?v1)) (f194 f195 ?v0)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f75 ?v0) f1) (=> (= (f27 (f29 ?v1) ?v0) f1) (= (f3 (f5 (f186 f187 ?v1)) (f186 f187 ?v0)) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f72 ?v0) f1) (=> (= (f12 (f14 ?v1) ?v0) f1) (= (f3 (f5 (f182 f183 ?v1)) (f182 f183 ?v0)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f70 ?v0) f1) (=> (= (f15 (f17 ?v1) ?v0) f1) (= (f3 (f5 (f178 f179 ?v1)) (f178 f179 ?v0)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f69 ?v0) f1) (=> (= (f9 (f11 ?v1) ?v0) f1) (=> (= (f3 (f5 (f176 f177 ?v0)) (f176 f177 ?v1)) f1) (= ?v1 ?v0))))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f74 ?v0) f1) (=> (= (f30 (f32 ?v1) ?v0) f1) (=> (= (f3 (f5 (f59 f60 ?v0)) (f59 f60 ?v1)) f1) (= ?v1 ?v0))))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (= (f54 ?v0) f1) (=> (= (f6 (f8 ?v1) ?v0) f1) (=> (= (f3 (f5 (f174 f175 ?v0)) (f174 f175 ?v1)) f1) (= ?v1 ?v0))))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f77 ?v0) f1) (=> (= (f23 ?v1 ?v0) f1) (=> (= (f3 (f5 (f190 f191 ?v0)) (f190 f191 ?v1)) f1) (= ?v1 ?v0))))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f80 ?v0) f1) (=> (= (f20 ?v1 ?v0) f1) (=> (= (f3 (f5 (f192 f193 ?v0)) (f192 f193 ?v1)) f1) (= ?v1 ?v0))))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f83 ?v0) f1) (=> (= (f26 ?v1 ?v0) f1) (=> (= (f3 (f5 (f194 f195 ?v0)) (f194 f195 ?v1)) f1) (= ?v1 ?v0))))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f75 ?v0) f1) (=> (= (f27 (f29 ?v1) ?v0) f1) (=> (= (f3 (f5 (f186 f187 ?v0)) (f186 f187 ?v1)) f1) (= ?v1 ?v0))))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f72 ?v0) f1) (=> (= (f12 (f14 ?v1) ?v0) f1) (=> (= (f3 (f5 (f182 f183 ?v0)) (f182 f183 ?v1)) f1) (= ?v1 ?v0))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f70 ?v0) f1) (=> (= (f15 (f17 ?v1) ?v0) f1) (=> (= (f3 (f5 (f178 f179 ?v0)) (f178 f179 ?v1)) f1) (= ?v1 ?v0))))))
(assert (forall ((?v0 S14) (?v1 S21)) (=> (= (f74 ?v0) f1) (= (f3 (f5 (f59 f60 ?v0)) (f59 f60 (f45 (f49 ?v1) ?v0))) f1))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f69 ?v0) f1) (= (f3 (f5 (f176 f177 ?v0)) (f176 f177 (f36 (f160 ?v1) ?v0))) f1))))
(assert (forall ((?v0 S4) (?v1 S15)) (=> (= (f54 ?v0) f1) (= (f3 (f5 (f174 f175 ?v0)) (f174 f175 (f34 (f161 ?v1) ?v0))) f1))))
(assert (forall ((?v0 S8) (?v1 S6)) (=> (= (f77 ?v0) f1) (= (f3 (f5 (f190 f191 ?v0)) (f190 f191 (f162 (f163 ?v1) ?v0))) f1))))
(assert (forall ((?v0 S7) (?v1 S5)) (=> (= (f80 ?v0) f1) (= (f3 (f5 (f192 f193 ?v0)) (f192 f193 (f164 (f165 ?v1) ?v0))) f1))))
(assert (forall ((?v0 S11) (?v1 S13)) (=> (= (f83 ?v0) f1) (= (f3 (f5 (f194 f195 ?v0)) (f194 f195 (f166 (f167 ?v1) ?v0))) f1))))
(assert (forall ((?v0 S13) (?v1 S14)) (=> (= (f75 ?v0) f1) (= (f3 (f5 (f186 f187 ?v0)) (f186 f187 (f42 (f168 ?v1) ?v0))) f1))))
(assert (forall ((?v0 S5) (?v1 S4)) (=> (= (f72 ?v0) f1) (= (f3 (f5 (f182 f183 ?v0)) (f182 f183 (f38 (f169 ?v1) ?v0))) f1))))
(assert (forall ((?v0 S6) (?v1 S3)) (=> (= (f70 ?v0) f1) (= (f3 (f5 (f178 f179 ?v0)) (f178 f179 (f40 (f170 ?v1) ?v0))) f1))))
(assert (forall ((?v0 S14) (?v1 S21)) (let ((?v_0 (f59 f60 ?v0))) (=> (= (f74 ?v0) f1) (= (f59 f60 (f45 (f49 ?v1) ?v0)) (ite (= (f30 (f202 ?v1) ?v0) f1) ?v_0 (f61 f66 ?v_0)))))))
(assert (forall ((?v0 S4) (?v1 S15)) (let ((?v_0 (f174 f175 ?v0))) (=> (= (f54 ?v0) f1) (= (f174 f175 (f34 (f161 ?v1) ?v0)) (ite (= (f6 (f67 ?v1) ?v0) f1) ?v_0 (f61 f66 ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S2)) (let ((?v_0 (f176 f177 ?v0))) (=> (= (f69 ?v0) f1) (= (f176 f177 (f36 (f160 ?v1) ?v0)) (ite (= (f9 (f203 ?v1) ?v0) f1) ?v_0 (f61 f66 ?v_0)))))))
(assert (forall ((?v0 S8) (?v1 S6)) (let ((?v_0 (f190 f191 ?v0))) (=> (= (f77 ?v0) f1) (= (f190 f191 (f162 (f163 ?v1) ?v0)) (ite (= (f204 ?v1 ?v0) f1) ?v_0 (f61 f66 ?v_0)))))))
(assert (forall ((?v0 S7) (?v1 S5)) (let ((?v_0 (f192 f193 ?v0))) (=> (= (f80 ?v0) f1) (= (f192 f193 (f164 (f165 ?v1) ?v0)) (ite (= (f205 ?v1 ?v0) f1) ?v_0 (f61 f66 ?v_0)))))))
(assert (forall ((?v0 S11) (?v1 S13)) (let ((?v_0 (f194 f195 ?v0))) (=> (= (f83 ?v0) f1) (= (f194 f195 (f166 (f167 ?v1) ?v0)) (ite (= (f206 ?v1 ?v0) f1) ?v_0 (f61 f66 ?v_0)))))))
(assert (forall ((?v0 S13) (?v1 S14)) (let ((?v_0 (f186 f187 ?v0))) (=> (= (f75 ?v0) f1) (= (f186 f187 (f42 (f168 ?v1) ?v0)) (ite (= (f27 (f207 ?v1) ?v0) f1) ?v_0 (f61 f66 ?v_0)))))))
(assert (forall ((?v0 S5) (?v1 S4)) (let ((?v_0 (f182 f183 ?v0))) (=> (= (f72 ?v0) f1) (= (f182 f183 (f38 (f169 ?v1) ?v0)) (ite (= (f12 (f208 ?v1) ?v0) f1) ?v_0 (f61 f66 ?v_0)))))))
(assert (forall ((?v0 S6) (?v1 S3)) (let ((?v_0 (f178 f179 ?v0))) (=> (= (f70 ?v0) f1) (= (f178 f179 (f40 (f170 ?v1) ?v0)) (ite (= (f15 (f209 ?v1) ?v0) f1) ?v_0 (f61 f66 ?v_0)))))))
(assert (forall ((?v0 S14) (?v1 S21)) (=> (= (f74 ?v0) f1) (=> (not (= (f30 (f202 ?v1) ?v0) f1)) (= (f59 f60 (f45 (f49 ?v1) ?v0)) (f61 f66 (f59 f60 ?v0)))))))
(assert (forall ((?v0 S4) (?v1 S15)) (=> (= (f54 ?v0) f1) (=> (not (= (f6 (f67 ?v1) ?v0) f1)) (= (f174 f175 (f34 (f161 ?v1) ?v0)) (f61 f66 (f174 f175 ?v0)))))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f69 ?v0) f1) (=> (not (= (f9 (f203 ?v1) ?v0) f1)) (= (f176 f177 (f36 (f160 ?v1) ?v0)) (f61 f66 (f176 f177 ?v0)))))))
(assert (forall ((?v0 S8) (?v1 S6)) (=> (= (f77 ?v0) f1) (=> (not (= (f204 ?v1 ?v0) f1)) (= (f190 f191 (f162 (f163 ?v1) ?v0)) (f61 f66 (f190 f191 ?v0)))))))
(assert (forall ((?v0 S7) (?v1 S5)) (=> (= (f80 ?v0) f1) (=> (not (= (f205 ?v1 ?v0) f1)) (= (f192 f193 (f164 (f165 ?v1) ?v0)) (f61 f66 (f192 f193 ?v0)))))))
(assert (forall ((?v0 S11) (?v1 S13)) (=> (= (f83 ?v0) f1) (=> (not (= (f206 ?v1 ?v0) f1)) (= (f194 f195 (f166 (f167 ?v1) ?v0)) (f61 f66 (f194 f195 ?v0)))))))
(assert (forall ((?v0 S13) (?v1 S14)) (=> (= (f75 ?v0) f1) (=> (not (= (f27 (f207 ?v1) ?v0) f1)) (= (f186 f187 (f42 (f168 ?v1) ?v0)) (f61 f66 (f186 f187 ?v0)))))))
(assert (forall ((?v0 S5) (?v1 S4)) (=> (= (f72 ?v0) f1) (=> (not (= (f12 (f208 ?v1) ?v0) f1)) (= (f182 f183 (f38 (f169 ?v1) ?v0)) (f61 f66 (f182 f183 ?v0)))))))
(assert (forall ((?v0 S6) (?v1 S3)) (=> (= (f70 ?v0) f1) (=> (not (= (f15 (f209 ?v1) ?v0) f1)) (= (f178 f179 (f40 (f170 ?v1) ?v0)) (f61 f66 (f178 f179 ?v0)))))))
(assert (forall ((?v0 S15) (?v1 S14)) (let ((?v_0 (f49 (f68 f58 ?v0)))) (=> (= (f30 (f47 (f45 ?v_0 ?v1)) (f45 (f49 (f50 f51 (f210 f211 (f212 ?v0)))) f53)) f1) (= (f30 (f47 ?v1) (f45 ?v_0 f53)) f1)))))
(assert (forall ((?v0 S15)) (=> (= (f6 (f67 ?v0) f159) f1) false)))
(assert (forall ((?v0 S21)) (=> (= (f30 (f202 ?v0) f53) f1) false)))
(assert (forall ((?v0 S3)) (=> (= (f15 (f209 ?v0) f155) f1) false)))
(assert (forall ((?v0 S4)) (=> (= (f12 (f208 ?v0) f156) f1) false)))
(assert (forall ((?v0 S14)) (=> (= (f27 (f207 ?v0) f157) f1) false)))
(assert (forall ((?v0 S2)) (=> (= (f9 (f203 ?v0) f158) f1) false)))
(assert (forall ((?v0 S21) (?v1 S14) (?v2 S21)) (let ((?v_0 (f202 ?v0))) (=> (=> (not (= (f30 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f30 ?v_0 (f45 (f49 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S15) (?v1 S4) (?v2 S15)) (let ((?v_0 (f67 ?v0))) (=> (=> (not (= (f6 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f6 ?v_0 (f34 (f161 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S3)) (let ((?v_0 (f209 ?v0))) (=> (=> (not (= (f15 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f15 ?v_0 (f40 (f170 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S5) (?v2 S4)) (let ((?v_0 (f208 ?v0))) (=> (=> (not (= (f12 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f12 ?v_0 (f38 (f169 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S14) (?v1 S13) (?v2 S14)) (let ((?v_0 (f207 ?v0))) (=> (=> (not (= (f27 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f27 ?v_0 (f42 (f168 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f203 ?v0))) (=> (=> (not (= (f9 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f9 ?v_0 (f36 (f160 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S14)) (let ((?v_0 (f202 ?v0))) (=> (= (f30 ?v_0 (f45 (f49 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f30 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S4)) (let ((?v_0 (f67 ?v0))) (=> (= (f6 ?v_0 (f34 (f161 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f6 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6)) (let ((?v_0 (f209 ?v0))) (=> (= (f15 ?v_0 (f40 (f170 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f15 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S5)) (let ((?v_0 (f208 ?v0))) (=> (= (f12 ?v_0 (f38 (f169 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f12 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S13)) (let ((?v_0 (f207 ?v0))) (=> (= (f27 ?v_0 (f42 (f168 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f27 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f203 ?v0))) (=> (= (f9 ?v_0 (f36 (f160 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f9 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f30 (f32 ?v0) ?v1) f1) (=> (= (f30 (f32 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f15 (f17 ?v0) ?v1) f1) (=> (= (f15 (f17 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f12 (f14 ?v0) ?v1) f1) (=> (= (f12 (f14 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f27 (f29 ?v0) ?v1) f1) (=> (= (f27 (f29 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f9 (f11 ?v0) ?v1) f1) (=> (= (f9 (f11 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (= (f6 (f8 ?v0) ?v1) f1) (=> (= (f6 (f8 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S15)) (let ((?v_0 (f67 ?v2))) (=> (= (f6 (f8 ?v0) ?v1) f1) (=> (= (f6 ?v_0 ?v0) f1) (= (f6 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S21)) (let ((?v_0 (f202 ?v2))) (=> (= (f30 (f32 ?v0) ?v1) f1) (=> (= (f30 ?v_0 ?v0) f1) (= (f30 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (let ((?v_0 (f209 ?v2))) (=> (= (f15 (f17 ?v0) ?v1) f1) (=> (= (f15 ?v_0 ?v0) f1) (= (f15 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S4)) (let ((?v_0 (f208 ?v2))) (=> (= (f12 (f14 ?v0) ?v1) f1) (=> (= (f12 ?v_0 ?v0) f1) (= (f12 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S14)) (let ((?v_0 (f207 ?v2))) (=> (= (f27 (f29 ?v0) ?v1) f1) (=> (= (f27 ?v_0 ?v0) f1) (= (f27 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f203 ?v2))) (=> (= (f9 (f11 ?v0) ?v1) f1) (=> (= (f9 ?v_0 ?v0) f1) (= (f9 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S83) (?v2 S15) (?v3 S4)) (=> (= ?v0 (f213 ?v1 ?v2)) (=> (= (f6 (f67 ?v2) ?v3) f1) (= (f9 (f203 ?v0) (f143 (f144 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S15) (?v1 S55) (?v2 S21) (?v3 S14)) (=> (= ?v0 (f214 ?v1 ?v2)) (=> (= (f30 (f202 ?v2) ?v3) f1) (= (f6 (f67 ?v0) (f115 (f116 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S15) (?v1 S85) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f215 ?v1 ?v2)) (=> (= (f9 (f203 ?v2) ?v3) f1) (= (f6 (f67 ?v0) (f145 (f146 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S21) (?v1 S26) (?v2 S15) (?v3 S4)) (=> (= ?v0 (f68 ?v1 ?v2)) (=> (= (f6 (f67 ?v2) ?v3) f1) (= (f30 (f202 ?v0) (f56 (f57 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S27) (?v2 S14) (?v3 S13)) (=> (= ?v0 (f59 ?v1 ?v2)) (=> (= (f27 (f207 ?v2) ?v3) f1) (= (f9 (f203 ?v0) (f95 (f96 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S81) (?v2 S15) (?v3 S4)) (=> (= ?v0 (f216 ?v1 ?v2)) (=> (= (f6 (f67 ?v2) ?v3) f1) (= (f15 (f209 ?v0) (f141 (f142 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S4) (?v1 S79) (?v2 S15) (?v3 S4)) (=> (= ?v0 (f217 ?v1 ?v2)) (=> (= (f6 (f67 ?v2) ?v3) f1) (= (f12 (f208 ?v0) (f139 (f140 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S14) (?v1 S77) (?v2 S15) (?v3 S4)) (=> (= ?v0 (f218 ?v1 ?v2)) (=> (= (f6 (f67 ?v2) ?v3) f1) (= (f27 (f207 ?v0) (f137 (f138 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S21) (?v1 S69) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f219 ?v1 ?v2)) (=> (= (f9 (f203 ?v2) ?v3) f1) (= (f30 (f202 ?v0) (f129 (f130 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S67) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f220 ?v1 ?v2)) (=> (= (f9 (f203 ?v2) ?v3) f1) (= (f15 (f209 ?v0) (f127 (f128 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S4) (?v1 S65) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f221 ?v1 ?v2)) (=> (= (f9 (f203 ?v2) ?v3) f1) (= (f12 (f208 ?v0) (f125 (f126 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S14) (?v1 S63) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f222 ?v1 ?v2)) (=> (= (f9 (f203 ?v2) ?v3) f1) (= (f27 (f207 ?v0) (f123 (f124 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S15) (?v1 S53) (?v2 S3) (?v3 S6)) (=> (= ?v0 (f223 ?v1 ?v2)) (=> (= (f15 (f209 ?v2) ?v3) f1) (= (f6 (f67 ?v0) (f113 (f114 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S15) (?v1 S51) (?v2 S4) (?v3 S5)) (=> (= ?v0 (f224 ?v1 ?v2)) (=> (= (f12 (f208 ?v2) ?v3) f1) (= (f6 (f67 ?v0) (f111 (f112 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S15) (?v1 S49) (?v2 S14) (?v3 S13)) (=> (= ?v0 (f225 ?v1 ?v2)) (=> (= (f27 (f207 ?v2) ?v3) f1) (= (f6 (f67 ?v0) (f109 (f110 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (or (= (f74 (f226 ?v0)) f1) (= (f74 (f226 ?v1)) f1)) (= (f74 (f226 (f45 (f46 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (or (= (f70 (f71 ?v0)) f1) (= (f70 (f71 ?v1)) f1)) (= (f70 (f71 (f40 (f41 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (or (= (f72 (f73 ?v0)) f1) (= (f72 (f73 ?v1)) f1)) (= (f72 (f73 (f38 (f39 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (or (= (f75 (f76 ?v0)) f1) (= (f75 (f76 ?v1)) f1)) (= (f75 (f76 (f42 (f43 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (or (= (f54 (f227 ?v0)) f1) (= (f54 (f227 ?v1)) f1)) (= (f54 (f227 (f34 (f35 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (or (= (f69 (f228 ?v0)) f1) (= (f69 (f228 ?v1)) f1)) (= (f69 (f228 (f36 (f37 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S2)) (= (f69 (f228 (f4 ?v0))) f1)))
(assert (forall ((?v0 S15)) (=> (= (f6 (f67 ?v0) f55) f1) (= (f65 (f210 f211 (f212 ?v0))) f1))))
(assert (forall ((?v0 S2)) (= (f176 f177 (f228 (f4 ?v0))) (f61 f66 ?v0))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f158) (not (= (f9 (f203 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S14) (?v1 S21)) (=> (= ?v0 f53) (not (= (f30 (f202 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S4) (?v1 S15)) (=> (= ?v0 f159) (not (= (f6 (f67 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S4)) (= (= (f227 ?v0) f159) (forall ((?v1 S15)) (not (= (f33 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S6)) (= (= (f71 ?v0) f155) (forall ((?v1 S3)) (not (= (f9 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S5)) (= (= (f73 ?v0) f156) (forall ((?v1 S4)) (not (= (f6 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S13)) (= (= (f76 ?v0) f157) (forall ((?v1 S14)) (not (= (f30 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S14)) (= (= (f226 ?v0) f53) (forall ((?v1 S21)) (not (= (f44 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (= (f228 ?v0) f158) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f9 (f203 ?v0) f158) f1) false)))
(assert (forall ((?v0 S21)) (= (= (f30 (f202 ?v0) f53) f1) false)))
(assert (forall ((?v0 S15)) (= (= (f6 (f67 ?v0) f159) f1) false)))
(assert (forall ((?v0 S4)) (= (= f159 (f227 ?v0)) (forall ((?v1 S15)) (not (= (f33 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S6)) (= (= f155 (f71 ?v0)) (forall ((?v1 S3)) (not (= (f9 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S5)) (= (= f156 (f73 ?v0)) (forall ((?v1 S4)) (not (= (f6 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S13)) (= (= f157 (f76 ?v0)) (forall ((?v1 S14)) (not (= (f30 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S14)) (= (= f53 (f226 ?v0)) (forall ((?v1 S21)) (not (= (f44 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (= f158 (f228 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f9 (f203 ?v1) f158) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S14)) (= (forall ((?v1 S21)) (=> (= (f30 (f202 ?v1) f53) f1) (= (f44 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S4)) (= (forall ((?v1 S15)) (=> (= (f6 (f67 ?v1) f159) f1) (= (f33 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f9 (f203 ?v1) f158) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S14)) (= (exists ((?v1 S21)) (and (= (f30 (f202 ?v1) f53) f1) (= (f44 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S4)) (= (exists ((?v1 S15)) (and (= (f6 (f67 ?v1) f159) f1) (= (f33 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f9 (f203 ?v1) ?v0) f1)) (not (= ?v0 f158)))))
(assert (forall ((?v0 S14)) (= (exists ((?v1 S21)) (= (f30 (f202 ?v1) ?v0) f1)) (not (= ?v0 f53)))))
(assert (forall ((?v0 S4)) (= (exists ((?v1 S15)) (= (f6 (f67 ?v1) ?v0) f1)) (not (= ?v0 f159)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f9 (f203 ?v1) ?v0) f1))) (= ?v0 f158))))
(assert (forall ((?v0 S14)) (= (forall ((?v1 S21)) (not (= (f30 (f202 ?v1) ?v0) f1))) (= ?v0 f53))))
(assert (forall ((?v0 S4)) (= (forall ((?v1 S15)) (not (= (f6 (f67 ?v1) ?v0) f1))) (= ?v0 f159))))
(check-sat)
(exit)