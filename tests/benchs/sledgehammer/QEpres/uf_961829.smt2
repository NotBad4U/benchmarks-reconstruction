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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S4) S1)
(declare-fun f4 (S5 S3) S2)
(declare-fun f5 (S2) S5)
(declare-fun f6 (S4 S2) S1)
(declare-fun f7 (S3) S2)
(declare-fun f8 (S6 S8) S1)
(declare-fun f9 (S9 S7) S6)
(declare-fun f10 (S6) S9)
(declare-fun f11 (S8 S6) S1)
(declare-fun f12 (S7) S6)
(declare-fun f13 (S10 S12) S1)
(declare-fun f14 (S13 S11) S10)
(declare-fun f15 (S10) S13)
(declare-fun f16 (S12 S10) S1)
(declare-fun f17 (S11) S10)
(declare-fun f18 (S14 S11) S1)
(declare-fun f19 (S16 S15) S14)
(declare-fun f20 (S14) S16)
(declare-fun f21 (S11 S14) S1)
(declare-fun f22 (S15) S14)
(declare-fun f23 (S17 S19) S1)
(declare-fun f24 (S20 S18) S17)
(declare-fun f25 (S17) S20)
(declare-fun f26 (S19 S17) S1)
(declare-fun f27 (S18) S17)
(declare-fun f28 (S21 S2) S2)
(declare-fun f29 (S2) S21)
(declare-fun f30 (S22 S6) S6)
(declare-fun f31 (S6) S22)
(declare-fun f32 (S23 S10) S10)
(declare-fun f33 (S10) S23)
(declare-fun f34 (S24 S14) S14)
(declare-fun f35 (S14) S24)
(declare-fun f36 (S25 S17) S17)
(declare-fun f37 (S17) S25)
(declare-fun f38 (S26 S18) S1)
(declare-fun f39 (S27 S19) S26)
(declare-fun f40 (S28 S19) S27)
(declare-fun f41 () S28)
(declare-fun f42 (S29 S18) S19)
(declare-fun f43 (S30 S19) S29)
(declare-fun f44 () S30)
(declare-fun f45 () S27)
(declare-fun f46 (S31 S8) S8)
(declare-fun f47 () S31)
(declare-fun f48 () S7)
(declare-fun f49 (S32 S8) S19)
(declare-fun f50 () S32)
(declare-fun f51 () S19)
(declare-fun f52 () S32)
(declare-fun f53 (S33 S7) S3)
(declare-fun f54 () S33)
(declare-fun f55 (S34 S7) S7)
(declare-fun f56 (S35 S8) S34)
(declare-fun f57 () S35)
(declare-fun f58 (S36 S18) S8)
(declare-fun f59 (S37 S19) S36)
(declare-fun f60 (S38 S19) S37)
(declare-fun f61 () S38)
(declare-fun f62 () S29)
(declare-fun f63 (S39 S7) S18)
(declare-fun f64 (S40 S32) S39)
(declare-fun f65 () S40)
(declare-fun f66 (S41 S18) S18)
(declare-fun f67 (S42 S19) S41)
(declare-fun f68 () S42)
(declare-fun f69 () S19)
(declare-fun f70 () S18)
(declare-fun f71 (S43 S31) S34)
(declare-fun f72 () S43)
(declare-fun f73 (S44 S19) S31)
(declare-fun f74 () S44)
(declare-fun f75 () S3)
(declare-fun f76 () S8)
(declare-fun f77 (S19) S17)
(declare-fun f78 () S19)
(declare-fun f79 (S19) S17)
(declare-fun f80 (S45 S19) S19)
(declare-fun f81 (S46 S19) S45)
(declare-fun f82 () S46)
(declare-fun f83 (S47 S6) S34)
(declare-fun f84 () S47)
(declare-fun f85 (S48 S28) S6)
(declare-fun f86 (S49 S28) S48)
(declare-fun f87 (S27) S49)
(declare-fun f88 () S37)
(declare-fun f89 () S19)
(declare-fun f90 () S18)
(declare-fun f91 () S34)
(declare-fun f92 (S50 S17) S41)
(declare-fun f93 () S50)
(declare-fun f94 () S7)
(declare-fun f95 (S51 S15) S15)
(declare-fun f96 (S52 S14) S51)
(declare-fun f97 () S52)
(declare-fun f98 () S15)
(declare-fun f99 (S53 S11) S11)
(declare-fun f100 (S54 S10) S53)
(declare-fun f101 () S54)
(declare-fun f102 () S11)
(declare-fun f103 (S55 S3) S3)
(declare-fun f104 (S56 S2) S55)
(declare-fun f105 () S56)
(declare-fun f106 (S57 S12) S53)
(declare-fun f107 () S57)
(declare-fun f108 (S58 S11) S51)
(declare-fun f109 () S58)
(declare-fun f110 (S59 S4) S55)
(declare-fun f111 () S59)
(declare-fun f112 (S61 S3) S11)
(declare-fun f113 (S62 S60) S61)
(declare-fun f114 () S62)
(declare-fun f115 (S60 S4) S12)
(declare-fun f116 (S64 S3) S15)
(declare-fun f117 (S65 S63) S64)
(declare-fun f118 () S65)
(declare-fun f119 (S63 S4) S11)
(declare-fun f120 (S67 S3) S18)
(declare-fun f121 (S68 S66) S67)
(declare-fun f122 () S68)
(declare-fun f123 (S66 S4) S19)
(declare-fun f124 (S70 S3) S7)
(declare-fun f125 (S71 S69) S70)
(declare-fun f126 () S71)
(declare-fun f127 (S69 S4) S8)
(declare-fun f128 (S73 S11) S3)
(declare-fun f129 (S74 S72) S73)
(declare-fun f130 () S74)
(declare-fun f131 (S72 S12) S4)
(declare-fun f132 (S76 S15) S3)
(declare-fun f133 (S77 S75) S76)
(declare-fun f134 () S77)
(declare-fun f135 (S75 S11) S4)
(declare-fun f136 (S79 S18) S3)
(declare-fun f137 (S80 S78) S79)
(declare-fun f138 () S80)
(declare-fun f139 (S78 S19) S4)
(declare-fun f140 (S82 S81) S33)
(declare-fun f141 () S82)
(declare-fun f142 (S81 S8) S4)
(declare-fun f143 (S84 S7) S11)
(declare-fun f144 (S85 S83) S84)
(declare-fun f145 () S85)
(declare-fun f146 (S83 S8) S12)
(declare-fun f147 (S87 S7) S15)
(declare-fun f148 (S88 S86) S87)
(declare-fun f149 () S88)
(declare-fun f150 (S86 S8) S11)
(declare-fun f151 (S90 S18) S7)
(declare-fun f152 (S91 S89) S90)
(declare-fun f153 () S91)
(declare-fun f154 (S89 S19) S8)
(declare-fun f155 (S93 S11) S7)
(declare-fun f156 (S94 S92) S93)
(declare-fun f157 () S94)
(declare-fun f158 (S92 S12) S8)
(declare-fun f159 (S96 S15) S7)
(declare-fun f160 (S97 S95) S96)
(declare-fun f161 () S97)
(declare-fun f162 (S95 S11) S8)
(declare-fun f163 (S17) S17)
(declare-fun f164 (S6) S6)
(declare-fun f165 (S2) S2)
(declare-fun f166 (S14) S14)
(declare-fun f167 (S10) S10)
(declare-fun f168 (S98 S30) S29)
(declare-fun f169 (S99 S19) S98)
(declare-fun f170 () S99)
(declare-fun f171 (S17 S17) S1)
(declare-fun f172 (S6 S6) S1)
(declare-fun f173 (S10 S10) S1)
(declare-fun f174 (S14 S14) S1)
(declare-fun f175 (S2 S2) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S4)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (and (= (f6 ?v2 (f7 ?v1)) f1) (= (f3 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S8)) (= (= (f8 (f9 (f10 ?v0) ?v1) ?v2) f1) (and (= (f11 ?v2 (f12 ?v1)) f1) (= (f8 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S11) (?v2 S12)) (= (= (f13 (f14 (f15 ?v0) ?v1) ?v2) f1) (and (= (f16 ?v2 (f17 ?v1)) f1) (= (f13 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S15) (?v2 S11)) (= (= (f18 (f19 (f20 ?v0) ?v1) ?v2) f1) (and (= (f21 ?v2 (f22 ?v1)) f1) (= (f18 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S17) (?v1 S18) (?v2 S19)) (= (= (f23 (f24 (f25 ?v0) ?v1) ?v2) f1) (and (= (f26 ?v2 (f27 ?v1)) f1) (= (f23 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S4)) (= (= (f3 (f28 (f29 ?v0) ?v1) ?v2) f1) (and (= (f3 ?v1 ?v2) f1) (= (f3 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S8)) (= (= (f8 (f30 (f31 ?v0) ?v1) ?v2) f1) (and (= (f8 ?v1 ?v2) f1) (= (f8 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S12)) (= (= (f13 (f32 (f33 ?v0) ?v1) ?v2) f1) (and (= (f13 ?v1 ?v2) f1) (= (f13 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S11)) (= (= (f18 (f34 (f35 ?v0) ?v1) ?v2) f1) (and (= (f18 ?v1 ?v2) f1) (= (f18 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S19)) (= (= (f23 (f36 (f37 ?v0) ?v1) ?v2) f1) (and (= (f23 ?v1 ?v2) f1) (= (f23 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S18)) (= (= (f38 (f39 (f40 f41 ?v0) ?v1) ?v2) f1) true)))
(assert (forall ((?v0 S19) (?v1 S18)) (= (f42 (f43 f44 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S19) (?v1 S18)) (= (= (f38 (f39 f45 ?v0) ?v1) f1) false)))
(assert (forall ((?v0 S8)) (= (f46 f47 ?v0) ?v0)))
(assert (not false))
(assert (forall ((?v0 S8)) (=> (= (f11 ?v0 (f12 f48)) f1) (and (not (= (f49 f50 ?v0) f51)) (not (= (f49 f52 ?v0) f51))))))
(assert (let ((?v_0 (f42 f62 (f63 (f64 f65 f50) f48)))) (= (f53 f54 (f55 (f56 f57 (f58 (f59 (f60 f61 ?v_0) f51) (f66 (f67 f68 f69) f70))) (f55 (f71 f72 (f73 f74 ?v_0)) f48))) f75)))
(assert (= (f49 f52 (f46 (f73 f74 (f42 f62 (f63 (f64 f65 f50) f48))) f76)) f51))
(assert (= (f23 (f77 f51) f78) f1))
(assert (let ((?v_0 (f42 f62 (f63 (f64 f65 f50) f48)))) (= (f23 (f79 f78) (f80 (f81 f82 ?v_0) (f42 f62 (f63 (f64 f65 f52) (f55 (f83 f84 (f85 (f86 (f87 f45) f41) f41)) (f55 (f71 f72 (f73 f74 ?v_0)) f48)))))) f1)))
(assert (= (f8 (f85 (f86 (f87 f45) f41) f41) (f46 (f73 f74 (f42 f62 (f63 (f64 f65 f50) f48))) f76)) f1))
(assert (= (f11 f76 (f12 f48)) f1))
(assert (= f76 (f58 (f59 f88 f89) f90)))
(assert (forall ((?v0 S19)) (= (= (f23 (f77 f69) ?v0) f1) (= (f23 (f79 f51) ?v0) f1))))
(assert (forall ((?v0 S19) (?v1 S19)) (let ((?v_0 (f58 (f59 f88 ?v1) f70))) (= (f46 (f73 f74 ?v0) ?v_0) ?v_0))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f58 (f59 (f60 f61 ?v1) ?v2) f70))) (= (f46 (f73 f74 ?v0) ?v_0) ?v_0))))
(assert (forall ((?v0 S19) (?v1 S18)) (= (f42 f62 (f66 (f67 f68 ?v0) ?v1)) (f80 (f81 f82 ?v0) (f42 f62 ?v1)))))
(assert (= (f42 f62 f70) f69))
(assert (forall ((?v0 S7)) (let ((?v_0 (f42 f62 (f63 (f64 f65 f50) ?v0)))) (= (f55 f91 ?v0) (f55 (f56 f57 (f58 (f59 (f60 f61 ?v_0) f51) (f66 (f67 f68 f69) f70))) (f55 (f71 f72 (f73 f74 ?v_0)) ?v0))))))
(assert (forall ((?v0 S19) (?v1 S18)) (= (f49 f52 (f58 (f59 f88 ?v0) ?v1)) f69)))
(assert (forall ((?v0 S19) (?v1 S19)) (=> (not (= ?v0 f51)) (=> (not (= ?v1 f51)) (= (f23 (f79 f51) (f80 (f81 f82 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S19) (?v1 S19)) (= (f23 (f77 f51) (f80 (f81 f82 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S19) (?v1 S19)) (let ((?v_0 (f77 f51))) (=> (= (f23 ?v_0 ?v0) f1) (=> (= (f23 ?v_0 ?v1) f1) (= (f23 ?v_0 (f80 (f81 f82 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S17) (?v1 S18)) (= (= (f66 (f92 f93 ?v0) ?v1) f70) (forall ((?v2 S19)) (=> (= (f26 ?v2 (f27 ?v1)) f1) (not (= (f23 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (= (f55 (f83 f84 ?v0) ?v1) f94) (forall ((?v2 S8)) (=> (= (f11 ?v2 (f12 ?v1)) f1) (not (= (f8 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S14) (?v1 S15)) (= (= (f95 (f96 f97 ?v0) ?v1) f98) (forall ((?v2 S11)) (=> (= (f21 ?v2 (f22 ?v1)) f1) (not (= (f18 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S10) (?v1 S11)) (= (= (f99 (f100 f101 ?v0) ?v1) f102) (forall ((?v2 S12)) (=> (= (f16 ?v2 (f17 ?v1)) f1) (not (= (f13 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f103 (f104 f105 ?v0) ?v1) f75) (forall ((?v2 S4)) (=> (= (f6 ?v2 (f7 ?v1)) f1) (not (= (f3 ?v0 ?v2) f1)))))))
(assert (= (f23 (f79 f51) f69) f1))
(assert (forall ((?v0 S18)) (= (= (f42 f62 ?v0) f51) (= (f26 f51 (f27 ?v0)) f1))))
(assert (forall ((?v0 S12) (?v1 S11) (?v2 S12) (?v3 S11)) (= (= (f99 (f106 f107 ?v0) ?v1) (f99 (f106 f107 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S11) (?v1 S15) (?v2 S11) (?v3 S15)) (= (= (f95 (f108 f109 ?v0) ?v1) (f95 (f108 f109 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S19) (?v1 S18) (?v2 S19) (?v3 S18)) (= (= (f66 (f67 f68 ?v0) ?v1) (f66 (f67 f68 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S8) (?v1 S7) (?v2 S8) (?v3 S7)) (= (= (f55 (f56 f57 ?v0) ?v1) (f55 (f56 f57 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S4) (?v3 S3)) (= (= (f103 (f110 f111 ?v0) ?v1) (f103 (f110 f111 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S12) (?v1 S11)) (not (= (f99 (f106 f107 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S11) (?v1 S15)) (not (= (f95 (f108 f109 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S19) (?v1 S18)) (not (= (f66 (f67 f68 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S8) (?v1 S7)) (not (= (f55 (f56 f57 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S4) (?v1 S3)) (not (= (f103 (f110 f111 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S11) (?v1 S12)) (not (= ?v0 (f99 (f106 f107 ?v1) ?v0)))))
(assert (forall ((?v0 S15) (?v1 S11)) (not (= ?v0 (f95 (f108 f109 ?v1) ?v0)))))
(assert (forall ((?v0 S18) (?v1 S19)) (not (= ?v0 (f66 (f67 f68 ?v1) ?v0)))))
(assert (forall ((?v0 S7) (?v1 S8)) (not (= ?v0 (f55 (f56 f57 ?v1) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S4)) (not (= ?v0 (f103 (f110 f111 ?v1) ?v0)))))
(assert (forall ((?v0 S19) (?v1 S19)) (=> (= (f23 (f77 ?v0) ?v1) f1) (=> (= (f23 (f77 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f77 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (=> (= (f23 (f77 ?v1) ?v2) f1) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S19) (?v1 S19)) (or (= (f23 (f77 ?v0) ?v1) f1) (= (f23 (f77 ?v1) ?v0) f1))))
(assert (forall ((?v0 S19)) (= (f23 (f77 ?v0) ?v0) f1)))
(assert (forall ((?v0 S19) (?v1 S19)) (or (= (f23 (f79 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f23 (f79 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_0 (f81 f82 ?v0))) (= (f80 (f81 f82 (f80 ?v_0 ?v1)) ?v2) (f80 ?v_0 (f80 (f81 f82 ?v1) ?v2))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (let ((?v_1 (f81 f82 ?v0)) (?v_0 (f81 f82 ?v1))) (= (f80 ?v_1 (f80 ?v_0 ?v2)) (f80 ?v_0 (f80 ?v_1 ?v2))))))
(assert (forall ((?v0 S19) (?v1 S19)) (= (f80 (f81 f82 ?v0) ?v1) (f80 (f81 f82 ?v1) ?v0))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S18) (?v3 S19) (?v4 S19) (?v5 S18)) (= (= (f58 (f59 (f60 f61 ?v0) ?v1) ?v2) (f58 (f59 (f60 f61 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S19) (?v1 S18) (?v2 S19) (?v3 S18)) (= (= (f58 (f59 f88 ?v0) ?v1) (f58 (f59 f88 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S7)) (= (f55 (f71 f72 f47) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S7)) (= (f55 (f83 f84 ?v0) (f55 (f83 f84 ?v1) ?v2)) (f55 (f83 f84 (f30 (f31 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (f103 (f104 f105 ?v0) (f103 (f104 f105 ?v1) ?v2)) (f103 (f104 f105 (f28 (f29 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S11)) (= (f99 (f100 f101 ?v0) (f99 (f100 f101 ?v1) ?v2)) (f99 (f100 f101 (f32 (f33 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S15)) (= (f95 (f96 f97 ?v0) (f95 (f96 f97 ?v1) ?v2)) (f95 (f96 f97 (f34 (f35 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S18)) (= (f66 (f92 f93 ?v0) (f66 (f92 f93 ?v1) ?v2)) (f66 (f92 f93 (f36 (f37 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S18)) (=> (= (f26 ?v0 (f27 (f66 (f67 f68 ?v1) ?v2))) f1) (or (= ?v0 ?v1) (= (f26 ?v0 (f27 ?v2)) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S7)) (=> (= (f11 ?v0 (f12 (f55 (f56 f57 ?v1) ?v2))) f1) (or (= ?v0 ?v1) (= (f11 ?v0 (f12 ?v2)) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S11)) (=> (= (f16 ?v0 (f17 (f99 (f106 f107 ?v1) ?v2))) f1) (or (= ?v0 ?v1) (= (f16 ?v0 (f17 ?v2)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S15)) (=> (= (f21 ?v0 (f22 (f95 (f108 f109 ?v1) ?v2))) f1) (or (= ?v0 ?v1) (= (f21 ?v0 (f22 ?v2)) f1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (=> (= (f6 ?v0 (f7 (f103 (f110 f111 ?v1) ?v2))) f1) (or (= ?v0 ?v1) (= (f6 ?v0 (f7 ?v2)) f1)))))
(assert (forall ((?v0 S11) (?v1 S15)) (not (= (f95 (f108 f109 ?v0) ?v1) f98))))
(assert (forall ((?v0 S12) (?v1 S11)) (not (= (f99 (f106 f107 ?v0) ?v1) f102))))
(assert (forall ((?v0 S4) (?v1 S3)) (not (= (f103 (f110 f111 ?v0) ?v1) f75))))
(assert (forall ((?v0 S19) (?v1 S18)) (not (= (f66 (f67 f68 ?v0) ?v1) f70))))
(assert (forall ((?v0 S8) (?v1 S7)) (not (= (f55 (f56 f57 ?v0) ?v1) f94))))
(assert (forall ((?v0 S11) (?v1 S15)) (not (= f98 (f95 (f108 f109 ?v0) ?v1)))))
(assert (forall ((?v0 S12) (?v1 S11)) (not (= f102 (f99 (f106 f107 ?v0) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S3)) (not (= f75 (f103 (f110 f111 ?v0) ?v1)))))
(assert (forall ((?v0 S19) (?v1 S18)) (not (= f70 (f66 (f67 f68 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S7)) (not (= f94 (f55 (f56 f57 ?v0) ?v1)))))
(assert (not (= f51 f69)))
(assert (forall ((?v0 S19) (?v1 S19)) (= (= (f23 (f79 ?v0) ?v1) f1) (and (= (f23 (f77 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S31) (?v1 S8) (?v2 S7)) (let ((?v_0 (f71 f72 ?v0))) (= (f55 ?v_0 (f55 (f56 f57 ?v1) ?v2)) (f55 (f56 f57 (f46 ?v0 ?v1)) (f55 ?v_0 ?v2))))))
(assert (forall ((?v0 S32) (?v1 S8) (?v2 S7)) (let ((?v_0 (f64 f65 ?v0))) (= (f63 ?v_0 (f55 (f56 f57 ?v1) ?v2)) (f66 (f67 f68 (f49 ?v0 ?v1)) (f63 ?v_0 ?v2))))))
(assert (forall ((?v0 S60) (?v1 S4) (?v2 S3)) (let ((?v_0 (f113 f114 ?v0))) (= (f112 ?v_0 (f103 (f110 f111 ?v1) ?v2)) (f99 (f106 f107 (f115 ?v0 ?v1)) (f112 ?v_0 ?v2))))))
(assert (forall ((?v0 S63) (?v1 S4) (?v2 S3)) (let ((?v_0 (f117 f118 ?v0))) (= (f116 ?v_0 (f103 (f110 f111 ?v1) ?v2)) (f95 (f108 f109 (f119 ?v0 ?v1)) (f116 ?v_0 ?v2))))))
(assert (forall ((?v0 S66) (?v1 S4) (?v2 S3)) (let ((?v_0 (f121 f122 ?v0))) (= (f120 ?v_0 (f103 (f110 f111 ?v1) ?v2)) (f66 (f67 f68 (f123 ?v0 ?v1)) (f120 ?v_0 ?v2))))))
(assert (forall ((?v0 S69) (?v1 S4) (?v2 S3)) (let ((?v_0 (f125 f126 ?v0))) (= (f124 ?v_0 (f103 (f110 f111 ?v1) ?v2)) (f55 (f56 f57 (f127 ?v0 ?v1)) (f124 ?v_0 ?v2))))))
(assert (forall ((?v0 S72) (?v1 S12) (?v2 S11)) (let ((?v_0 (f129 f130 ?v0))) (= (f128 ?v_0 (f99 (f106 f107 ?v1) ?v2)) (f103 (f110 f111 (f131 ?v0 ?v1)) (f128 ?v_0 ?v2))))))
(assert (forall ((?v0 S75) (?v1 S11) (?v2 S15)) (let ((?v_0 (f133 f134 ?v0))) (= (f132 ?v_0 (f95 (f108 f109 ?v1) ?v2)) (f103 (f110 f111 (f135 ?v0 ?v1)) (f132 ?v_0 ?v2))))))
(assert (forall ((?v0 S78) (?v1 S19) (?v2 S18)) (let ((?v_0 (f137 f138 ?v0))) (= (f136 ?v_0 (f66 (f67 f68 ?v1) ?v2)) (f103 (f110 f111 (f139 ?v0 ?v1)) (f136 ?v_0 ?v2))))))
(assert (forall ((?v0 S81) (?v1 S8) (?v2 S7)) (let ((?v_0 (f140 f141 ?v0))) (= (f53 ?v_0 (f55 (f56 f57 ?v1) ?v2)) (f103 (f110 f111 (f142 ?v0 ?v1)) (f53 ?v_0 ?v2))))))
(assert (forall ((?v0 S83) (?v1 S8) (?v2 S7)) (let ((?v_0 (f144 f145 ?v0))) (= (f143 ?v_0 (f55 (f56 f57 ?v1) ?v2)) (f99 (f106 f107 (f146 ?v0 ?v1)) (f143 ?v_0 ?v2))))))
(assert (forall ((?v0 S86) (?v1 S8) (?v2 S7)) (let ((?v_0 (f148 f149 ?v0))) (= (f147 ?v_0 (f55 (f56 f57 ?v1) ?v2)) (f95 (f108 f109 (f150 ?v0 ?v1)) (f147 ?v_0 ?v2))))))
(assert (forall ((?v0 S89) (?v1 S19) (?v2 S18)) (let ((?v_0 (f152 f153 ?v0))) (= (f151 ?v_0 (f66 (f67 f68 ?v1) ?v2)) (f55 (f56 f57 (f154 ?v0 ?v1)) (f151 ?v_0 ?v2))))))
(assert (forall ((?v0 S92) (?v1 S12) (?v2 S11)) (let ((?v_0 (f156 f157 ?v0))) (= (f155 ?v_0 (f99 (f106 f107 ?v1) ?v2)) (f55 (f56 f57 (f158 ?v0 ?v1)) (f155 ?v_0 ?v2))))))
(assert (forall ((?v0 S95) (?v1 S11) (?v2 S15)) (let ((?v_0 (f160 f161 ?v0))) (= (f159 ?v_0 (f95 (f108 f109 ?v1) ?v2)) (f55 (f56 f57 (f162 ?v0 ?v1)) (f159 ?v_0 ?v2))))))
(assert (forall ((?v0 S31) (?v1 S7) (?v2 S31)) (= (= (f55 (f71 f72 ?v0) ?v1) (f55 (f71 f72 ?v2) ?v1)) (forall ((?v3 S8)) (=> (= (f11 ?v3 (f12 ?v1)) f1) (= (f46 ?v0 ?v3) (f46 ?v2 ?v3)))))))
(assert (forall ((?v0 S32) (?v1 S7) (?v2 S32)) (= (= (f63 (f64 f65 ?v0) ?v1) (f63 (f64 f65 ?v2) ?v1)) (forall ((?v3 S8)) (=> (= (f11 ?v3 (f12 ?v1)) f1) (= (f49 ?v0 ?v3) (f49 ?v2 ?v3)))))))
(assert (forall ((?v0 S81) (?v1 S7) (?v2 S81)) (= (= (f53 (f140 f141 ?v0) ?v1) (f53 (f140 f141 ?v2) ?v1)) (forall ((?v3 S8)) (=> (= (f11 ?v3 (f12 ?v1)) f1) (= (f142 ?v0 ?v3) (f142 ?v2 ?v3)))))))
(assert (forall ((?v0 S83) (?v1 S7) (?v2 S83)) (= (= (f143 (f144 f145 ?v0) ?v1) (f143 (f144 f145 ?v2) ?v1)) (forall ((?v3 S8)) (=> (= (f11 ?v3 (f12 ?v1)) f1) (= (f146 ?v0 ?v3) (f146 ?v2 ?v3)))))))
(assert (forall ((?v0 S86) (?v1 S7) (?v2 S86)) (= (= (f147 (f148 f149 ?v0) ?v1) (f147 (f148 f149 ?v2) ?v1)) (forall ((?v3 S8)) (=> (= (f11 ?v3 (f12 ?v1)) f1) (= (f150 ?v0 ?v3) (f150 ?v2 ?v3)))))))
(assert (forall ((?v0 S89) (?v1 S18) (?v2 S89)) (= (= (f151 (f152 f153 ?v0) ?v1) (f151 (f152 f153 ?v2) ?v1)) (forall ((?v3 S19)) (=> (= (f26 ?v3 (f27 ?v1)) f1) (= (f154 ?v0 ?v3) (f154 ?v2 ?v3)))))))
(assert (forall ((?v0 S78) (?v1 S18) (?v2 S78)) (= (= (f136 (f137 f138 ?v0) ?v1) (f136 (f137 f138 ?v2) ?v1)) (forall ((?v3 S19)) (=> (= (f26 ?v3 (f27 ?v1)) f1) (= (f139 ?v0 ?v3) (f139 ?v2 ?v3)))))))
(assert (forall ((?v0 S69) (?v1 S3) (?v2 S69)) (= (= (f124 (f125 f126 ?v0) ?v1) (f124 (f125 f126 ?v2) ?v1)) (forall ((?v3 S4)) (=> (= (f6 ?v3 (f7 ?v1)) f1) (= (f127 ?v0 ?v3) (f127 ?v2 ?v3)))))))
(assert (forall ((?v0 S66) (?v1 S3) (?v2 S66)) (= (= (f120 (f121 f122 ?v0) ?v1) (f120 (f121 f122 ?v2) ?v1)) (forall ((?v3 S4)) (=> (= (f6 ?v3 (f7 ?v1)) f1) (= (f123 ?v0 ?v3) (f123 ?v2 ?v3)))))))
(assert (forall ((?v0 S63) (?v1 S3) (?v2 S63)) (= (= (f116 (f117 f118 ?v0) ?v1) (f116 (f117 f118 ?v2) ?v1)) (forall ((?v3 S4)) (=> (= (f6 ?v3 (f7 ?v1)) f1) (= (f119 ?v0 ?v3) (f119 ?v2 ?v3)))))))
(assert (forall ((?v0 S60) (?v1 S3) (?v2 S60)) (= (= (f112 (f113 f114 ?v0) ?v1) (f112 (f113 f114 ?v2) ?v1)) (forall ((?v3 S4)) (=> (= (f6 ?v3 (f7 ?v1)) f1) (= (f115 ?v0 ?v3) (f115 ?v2 ?v3)))))))
(assert (forall ((?v0 S95) (?v1 S15) (?v2 S95)) (= (= (f159 (f160 f161 ?v0) ?v1) (f159 (f160 f161 ?v2) ?v1)) (forall ((?v3 S11)) (=> (= (f21 ?v3 (f22 ?v1)) f1) (= (f162 ?v0 ?v3) (f162 ?v2 ?v3)))))))
(assert (forall ((?v0 S75) (?v1 S15) (?v2 S75)) (= (= (f132 (f133 f134 ?v0) ?v1) (f132 (f133 f134 ?v2) ?v1)) (forall ((?v3 S11)) (=> (= (f21 ?v3 (f22 ?v1)) f1) (= (f135 ?v0 ?v3) (f135 ?v2 ?v3)))))))
(assert (forall ((?v0 S92) (?v1 S11) (?v2 S92)) (= (= (f155 (f156 f157 ?v0) ?v1) (f155 (f156 f157 ?v2) ?v1)) (forall ((?v3 S12)) (=> (= (f16 ?v3 (f17 ?v1)) f1) (= (f158 ?v0 ?v3) (f158 ?v2 ?v3)))))))
(assert (forall ((?v0 S72) (?v1 S11) (?v2 S72)) (= (= (f128 (f129 f130 ?v0) ?v1) (f128 (f129 f130 ?v2) ?v1)) (forall ((?v3 S12)) (=> (= (f16 ?v3 (f17 ?v1)) f1) (= (f131 ?v0 ?v3) (f131 ?v2 ?v3)))))))
(assert (forall ((?v0 S31) (?v1 S7)) (= (= (f55 (f71 f72 ?v0) ?v1) f94) (= ?v1 f94))))
(assert (forall ((?v0 S32) (?v1 S7)) (= (= (f63 (f64 f65 ?v0) ?v1) f70) (= ?v1 f94))))
(assert (forall ((?v0 S95) (?v1 S15)) (= (= (f159 (f160 f161 ?v0) ?v1) f94) (= ?v1 f98))))
(assert (forall ((?v0 S92) (?v1 S11)) (= (= (f155 (f156 f157 ?v0) ?v1) f94) (= ?v1 f102))))
(assert (forall ((?v0 S69) (?v1 S3)) (= (= (f124 (f125 f126 ?v0) ?v1) f94) (= ?v1 f75))))
(assert (forall ((?v0 S89) (?v1 S18)) (= (= (f151 (f152 f153 ?v0) ?v1) f94) (= ?v1 f70))))
(assert (forall ((?v0 S86) (?v1 S7)) (= (= (f147 (f148 f149 ?v0) ?v1) f98) (= ?v1 f94))))
(assert (forall ((?v0 S83) (?v1 S7)) (= (= (f143 (f144 f145 ?v0) ?v1) f102) (= ?v1 f94))))
(assert (forall ((?v0 S81) (?v1 S7)) (= (= (f53 (f140 f141 ?v0) ?v1) f75) (= ?v1 f94))))
(assert (forall ((?v0 S78) (?v1 S18)) (= (= (f136 (f137 f138 ?v0) ?v1) f75) (= ?v1 f70))))
(assert (forall ((?v0 S75) (?v1 S15)) (= (= (f132 (f133 f134 ?v0) ?v1) f75) (= ?v1 f98))))
(assert (forall ((?v0 S72) (?v1 S11)) (= (= (f128 (f129 f130 ?v0) ?v1) f75) (= ?v1 f102))))
(assert (forall ((?v0 S66) (?v1 S3)) (= (= (f120 (f121 f122 ?v0) ?v1) f70) (= ?v1 f75))))
(assert (forall ((?v0 S63) (?v1 S3)) (= (= (f116 (f117 f118 ?v0) ?v1) f98) (= ?v1 f75))))
(assert (forall ((?v0 S60) (?v1 S3)) (= (= (f112 (f113 f114 ?v0) ?v1) f102) (= ?v1 f75))))
(assert (forall ((?v0 S31)) (= (f55 (f71 f72 ?v0) f94) f94)))
(assert (forall ((?v0 S32)) (= (f63 (f64 f65 ?v0) f94) f70)))
(assert (forall ((?v0 S86)) (= (f147 (f148 f149 ?v0) f94) f98)))
(assert (forall ((?v0 S83)) (= (f143 (f144 f145 ?v0) f94) f102)))
(assert (forall ((?v0 S81)) (= (f53 (f140 f141 ?v0) f94) f75)))
(assert (forall ((?v0 S95)) (= (f159 (f160 f161 ?v0) f98) f94)))
(assert (forall ((?v0 S92)) (= (f155 (f156 f157 ?v0) f102) f94)))
(assert (forall ((?v0 S69)) (= (f124 (f125 f126 ?v0) f75) f94)))
(assert (forall ((?v0 S89)) (= (f151 (f152 f153 ?v0) f70) f94)))
(assert (forall ((?v0 S78)) (= (f136 (f137 f138 ?v0) f70) f75)))
(assert (forall ((?v0 S75)) (= (f132 (f133 f134 ?v0) f98) f75)))
(assert (forall ((?v0 S72)) (= (f128 (f129 f130 ?v0) f102) f75)))
(assert (forall ((?v0 S66)) (= (f120 (f121 f122 ?v0) f75) f70)))
(assert (forall ((?v0 S63)) (= (f116 (f117 f118 ?v0) f75) f98)))
(assert (forall ((?v0 S60)) (= (f112 (f113 f114 ?v0) f75) f102)))
(assert (forall ((?v0 S31) (?v1 S7)) (= (= f94 (f55 (f71 f72 ?v0) ?v1)) (= ?v1 f94))))
(assert (forall ((?v0 S32) (?v1 S7)) (= (= f70 (f63 (f64 f65 ?v0) ?v1)) (= ?v1 f94))))
(assert (forall ((?v0 S95) (?v1 S15)) (= (= f94 (f159 (f160 f161 ?v0) ?v1)) (= ?v1 f98))))
(assert (forall ((?v0 S92) (?v1 S11)) (= (= f94 (f155 (f156 f157 ?v0) ?v1)) (= ?v1 f102))))
(assert (forall ((?v0 S69) (?v1 S3)) (= (= f94 (f124 (f125 f126 ?v0) ?v1)) (= ?v1 f75))))
(assert (forall ((?v0 S89) (?v1 S18)) (= (= f94 (f151 (f152 f153 ?v0) ?v1)) (= ?v1 f70))))
(assert (forall ((?v0 S86) (?v1 S7)) (= (= f98 (f147 (f148 f149 ?v0) ?v1)) (= ?v1 f94))))
(assert (forall ((?v0 S83) (?v1 S7)) (= (= f102 (f143 (f144 f145 ?v0) ?v1)) (= ?v1 f94))))
(assert (forall ((?v0 S81) (?v1 S7)) (= (= f75 (f53 (f140 f141 ?v0) ?v1)) (= ?v1 f94))))
(assert (forall ((?v0 S78) (?v1 S18)) (= (= f75 (f136 (f137 f138 ?v0) ?v1)) (= ?v1 f70))))
(assert (forall ((?v0 S75) (?v1 S15)) (= (= f75 (f132 (f133 f134 ?v0) ?v1)) (= ?v1 f98))))
(assert (forall ((?v0 S72) (?v1 S11)) (= (= f75 (f128 (f129 f130 ?v0) ?v1)) (= ?v1 f102))))
(assert (forall ((?v0 S66) (?v1 S3)) (= (= f70 (f120 (f121 f122 ?v0) ?v1)) (= ?v1 f75))))
(assert (forall ((?v0 S63) (?v1 S3)) (= (= f98 (f116 (f117 f118 ?v0) ?v1)) (= ?v1 f75))))
(assert (forall ((?v0 S60) (?v1 S3)) (= (= f102 (f112 (f113 f114 ?v0) ?v1)) (= ?v1 f75))))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S7)) (let ((?v_1 (f83 f84 ?v0)) (?v_0 (f56 f57 ?v1))) (let ((?v_2 (f55 ?v_1 ?v2))) (= (f55 ?v_1 (f55 ?v_0 ?v2)) (ite (= (f8 ?v0 ?v1) f1) (f55 ?v_0 ?v_2) ?v_2))))))
(assert (forall ((?v0 S10) (?v1 S12) (?v2 S11)) (let ((?v_1 (f100 f101 ?v0)) (?v_0 (f106 f107 ?v1))) (let ((?v_2 (f99 ?v_1 ?v2))) (= (f99 ?v_1 (f99 ?v_0 ?v2)) (ite (= (f13 ?v0 ?v1) f1) (f99 ?v_0 ?v_2) ?v_2))))))
(assert (forall ((?v0 S14) (?v1 S11) (?v2 S15)) (let ((?v_1 (f96 f97 ?v0)) (?v_0 (f108 f109 ?v1))) (let ((?v_2 (f95 ?v_1 ?v2))) (= (f95 ?v_1 (f95 ?v_0 ?v2)) (ite (= (f18 ?v0 ?v1) f1) (f95 ?v_0 ?v_2) ?v_2))))))
(assert (forall ((?v0 S17) (?v1 S19) (?v2 S18)) (let ((?v_1 (f92 f93 ?v0)) (?v_0 (f67 f68 ?v1))) (let ((?v_2 (f66 ?v_1 ?v2))) (= (f66 ?v_1 (f66 ?v_0 ?v2)) (ite (= (f23 ?v0 ?v1) f1) (f66 ?v_0 ?v_2) ?v_2))))))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S3)) (let ((?v_1 (f104 f105 ?v0)) (?v_0 (f110 f111 ?v1))) (let ((?v_2 (f103 ?v_1 ?v2))) (= (f103 ?v_1 (f103 ?v_0 ?v2)) (ite (= (f3 ?v0 ?v1) f1) (f103 ?v_0 ?v_2) ?v_2))))))
(assert (forall ((?v0 S17) (?v1 S18)) (= (= (f66 (f92 f93 ?v0) ?v1) ?v1) (forall ((?v2 S19)) (=> (= (f26 ?v2 (f27 ?v1)) f1) (= (f23 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (= (f55 (f83 f84 ?v0) ?v1) ?v1) (forall ((?v2 S8)) (=> (= (f11 ?v2 (f12 ?v1)) f1) (= (f8 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f103 (f104 f105 ?v0) ?v1) ?v1) (forall ((?v2 S4)) (=> (= (f6 ?v2 (f7 ?v1)) f1) (= (f3 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S14) (?v1 S15)) (= (= (f95 (f96 f97 ?v0) ?v1) ?v1) (forall ((?v2 S11)) (=> (= (f21 ?v2 (f22 ?v1)) f1) (= (f18 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S11)) (= (= (f99 (f100 f101 ?v0) ?v1) ?v1) (forall ((?v2 S12)) (=> (= (f16 ?v2 (f17 ?v1)) f1) (= (f13 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S17) (?v1 S18)) (= (f27 (f66 (f92 f93 ?v0) ?v1)) (f163 (f24 (f25 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (f12 (f55 (f83 f84 ?v0) ?v1)) (f164 (f9 (f10 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f7 (f103 (f104 f105 ?v0) ?v1)) (f165 (f4 (f5 ?v0) ?v1)))))
(assert (forall ((?v0 S14) (?v1 S15)) (= (f22 (f95 (f96 f97 ?v0) ?v1)) (f166 (f19 (f20 ?v0) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S11)) (= (f17 (f99 (f100 f101 ?v0) ?v1)) (f167 (f14 (f15 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (f55 (f83 f84 ?v0) f94) f94)))
(assert (forall ((?v0 S14)) (= (f95 (f96 f97 ?v0) f98) f98)))
(assert (forall ((?v0 S10)) (= (f99 (f100 f101 ?v0) f102) f102)))
(assert (forall ((?v0 S2)) (= (f103 (f104 f105 ?v0) f75) f75)))
(assert (forall ((?v0 S17)) (= (f66 (f92 f93 ?v0) f70) f70)))
(assert (forall ((?v0 S19) (?v1 S19)) (= (= (f80 (f81 f82 ?v0) ?v1) f51) (or (= ?v0 f51) (= ?v1 f51)))))
(assert (forall ((?v0 S19)) (= (f80 (f81 f82 ?v0) f51) f51)))
(assert (forall ((?v0 S19)) (= (f80 (f81 f82 f51) ?v0) f51)))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S18)) (= (f49 f52 (f58 (f59 (f60 f61 ?v0) ?v1) ?v2)) ?v0)))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S18) (?v3 S19) (?v4 S18)) (not (= (f58 (f59 (f60 f61 ?v0) ?v1) ?v2) (f58 (f59 f88 ?v3) ?v4)))))
(assert (forall ((?v0 S19) (?v1 S18) (?v2 S19) (?v3 S19) (?v4 S18)) (not (= (f58 (f59 f88 ?v0) ?v1) (f58 (f59 (f60 f61 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S28) (?v3 S19) (?v4 S19) (?v5 S18)) (= (= (f8 (f85 (f86 (f87 ?v0) ?v1) ?v2) (f58 (f59 (f60 f61 ?v3) ?v4) ?v5)) f1) (= (f38 (f39 (f40 ?v1 ?v3) ?v4) ?v5) f1))))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S28) (?v3 S19) (?v4 S18)) (= (= (f8 (f85 (f86 (f87 ?v0) ?v1) ?v2) (f58 (f59 f88 ?v3) ?v4)) f1) (= (f38 (f39 ?v0 ?v3) ?v4) f1))))
(assert (forall ((?v0 S18)) (=> (forall ((?v1 S19)) (=> (= (f26 ?v1 (f27 ?v0)) f1) (not (= ?v1 f51)))) (= (f23 (f79 f51) (f42 f62 ?v0)) f1))))
(assert (forall ((?v0 S18) (?v1 S19)) (=> (forall ((?v2 S19)) (=> (= (f26 ?v2 (f27 ?v0)) f1) (not (= ?v2 f51)))) (=> (= (f26 ?v1 (f27 ?v0)) f1) (= (f23 (f77 ?v1) (f42 f62 ?v0)) f1)))))
(assert (forall ((?v0 S18) (?v1 S17)) (=> (forall ((?v2 S19)) (=> (= (f26 ?v2 (f27 ?v0)) f1) (not (= (f23 ?v1 ?v2) f1)))) (= (f66 (f92 f93 ?v1) ?v0) f70))))
(assert (forall ((?v0 S7) (?v1 S6)) (=> (forall ((?v2 S8)) (=> (= (f11 ?v2 (f12 ?v0)) f1) (not (= (f8 ?v1 ?v2) f1)))) (= (f55 (f83 f84 ?v1) ?v0) f94))))
(assert (forall ((?v0 S15) (?v1 S14)) (=> (forall ((?v2 S11)) (=> (= (f21 ?v2 (f22 ?v0)) f1) (not (= (f18 ?v1 ?v2) f1)))) (= (f95 (f96 f97 ?v1) ?v0) f98))))
(assert (forall ((?v0 S11) (?v1 S10)) (=> (forall ((?v2 S12)) (=> (= (f16 ?v2 (f17 ?v0)) f1) (not (= (f13 ?v1 ?v2) f1)))) (= (f99 (f100 f101 ?v1) ?v0) f102))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (forall ((?v2 S4)) (=> (= (f6 ?v2 (f7 ?v0)) f1) (not (= (f3 ?v1 ?v2) f1)))) (= (f103 (f104 f105 ?v1) ?v0) f75))))
(assert (forall ((?v0 S7) (?v1 S8)) (=> (forall ((?v2 S8)) (=> (= (f11 ?v2 (f12 ?v0)) f1) (not (= (f49 f52 ?v2) f51)))) (=> (forall ((?v2 S8)) (=> (= (f11 ?v2 (f12 ?v0)) f1) (not (= (f49 f50 ?v2) f51)))) (=> (= (f11 ?v1 (f12 (f55 f91 ?v0))) f1) (not (= (f49 f52 ?v1) f51)))))))
(assert (= (f23 (f77 f51) f69) f1))
(assert (= (f23 (f79 f51) f69) f1))
(assert (not (= (f23 (f79 f69) f51) f1)))
(assert (= (f23 (f77 f51) f69) f1))
(assert (not (= (f23 (f77 f69) f51) f1)))
(assert (forall ((?v0 S19) (?v1 S18)) (= (f49 f50 (f58 (f59 f88 ?v0) ?v1)) (f42 (f168 (f169 f170 f51) f44) ?v1))))
(assert (forall ((?v0 S18) (?v1 S19)) (= (f171 (f27 ?v0) (f27 (f66 (f67 f68 ?v1) ?v0))) f1)))
(assert (forall ((?v0 S7) (?v1 S8)) (= (f172 (f12 ?v0) (f12 (f55 (f56 f57 ?v1) ?v0))) f1)))
(assert (forall ((?v0 S11) (?v1 S12)) (= (f173 (f17 ?v0) (f17 (f99 (f106 f107 ?v1) ?v0))) f1)))
(assert (forall ((?v0 S15) (?v1 S11)) (= (f174 (f22 ?v0) (f22 (f95 (f108 f109 ?v1) ?v0))) f1)))
(assert (forall ((?v0 S3) (?v1 S4)) (= (f175 (f7 ?v0) (f7 (f103 (f110 f111 ?v1) ?v0))) f1)))
(assert (forall ((?v0 S17) (?v1 S18)) (= (f171 (f27 (f66 (f92 f93 ?v0) ?v1)) (f27 ?v1)) f1)))
(assert (forall ((?v0 S6) (?v1 S7)) (= (f172 (f12 (f55 (f83 f84 ?v0) ?v1)) (f12 ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f175 (f7 (f103 (f104 f105 ?v0) ?v1)) (f7 ?v1)) f1)))
(assert (forall ((?v0 S14) (?v1 S15)) (= (f174 (f22 (f95 (f96 f97 ?v0) ?v1)) (f22 ?v1)) f1)))
(assert (forall ((?v0 S10) (?v1 S11)) (= (f173 (f17 (f99 (f100 f101 ?v0) ?v1)) (f17 ?v1)) f1)))
(check-sat)
(exit)