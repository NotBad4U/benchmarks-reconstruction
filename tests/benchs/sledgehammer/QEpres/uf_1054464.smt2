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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S4 S2) S2)
(declare-fun f5 (S2) S4)
(declare-fun f6 (S5 S6) S1)
(declare-fun f7 (S7 S5) S5)
(declare-fun f8 (S5) S7)
(declare-fun f9 (S8 S9) S1)
(declare-fun f10 (S10 S8) S8)
(declare-fun f11 (S8) S10)
(declare-fun f12 (S11 S12) S1)
(declare-fun f13 (S13 S11) S11)
(declare-fun f14 (S11) S13)
(declare-fun f15 (S14 S15) S1)
(declare-fun f16 (S16 S14) S14)
(declare-fun f17 (S14) S16)
(declare-fun f18 (S18 S17) S1)
(declare-fun f19 (S19 S15) S18)
(declare-fun f20 (S20 S15) S19)
(declare-fun f21 () S20)
(declare-fun f22 () S19)
(declare-fun f23 (S21 S6) S6)
(declare-fun f24 () S21)
(declare-fun f25 (S6 S5) S1)
(declare-fun f26 (S22) S5)
(declare-fun f27 () S22)
(declare-fun f28 (S23 S6) S15)
(declare-fun f29 () S23)
(declare-fun f30 () S15)
(declare-fun f31 () S23)
(declare-fun f32 (S24 S22) S25)
(declare-fun f33 () S24)
(declare-fun f34 (S26 S22) S22)
(declare-fun f35 (S27 S6) S26)
(declare-fun f36 () S27)
(declare-fun f37 (S28 S17) S6)
(declare-fun f38 (S29 S15) S28)
(declare-fun f39 (S30 S15) S29)
(declare-fun f40 () S30)
(declare-fun f41 (S31 S17) S15)
(declare-fun f42 () S31)
(declare-fun f43 (S32 S22) S17)
(declare-fun f44 (S33 S23) S32)
(declare-fun f45 () S33)
(declare-fun f46 (S34 S17) S17)
(declare-fun f47 (S35 S15) S34)
(declare-fun f48 () S35)
(declare-fun f49 () S15)
(declare-fun f50 () S17)
(declare-fun f51 (S36 S21) S26)
(declare-fun f52 () S36)
(declare-fun f53 (S37 S15) S21)
(declare-fun f54 () S37)
(declare-fun f55 () S25)
(declare-fun f56 () S6)
(declare-fun f57 (S3 S2) S1)
(declare-fun f58 (S38 S17) S3)
(declare-fun f59 (S39 S15) S38)
(declare-fun f60 () S39)
(declare-fun f61 () S15)
(declare-fun f62 () S17)
(declare-fun f63 (S25) S2)
(declare-fun f64 (S21) S7)
(declare-fun f65 (S15) S14)
(declare-fun f66 () S15)
(declare-fun f67 (S15) S14)
(declare-fun f68 (S40 S15) S15)
(declare-fun f69 (S41 S15) S40)
(declare-fun f70 () S41)
(declare-fun f71 (S42 S5) S26)
(declare-fun f72 () S42)
(declare-fun f73 (S43 S20) S5)
(declare-fun f74 (S44 S20) S43)
(declare-fun f75 (S19) S44)
(declare-fun f76 () S26)
(declare-fun f77 (S45 S14) S34)
(declare-fun f78 () S45)
(declare-fun f79 (S15 S14) S1)
(declare-fun f80 (S17) S14)
(declare-fun f81 (S46 S25) S25)
(declare-fun f82 (S47 S2) S46)
(declare-fun f83 () S47)
(declare-fun f84 () S22)
(declare-fun f85 (S49 S48) S48)
(declare-fun f86 (S50 S11) S49)
(declare-fun f87 () S50)
(declare-fun f88 () S48)
(declare-fun f89 (S12 S11) S1)
(declare-fun f90 (S48) S11)
(declare-fun f91 (S51 S12) S12)
(declare-fun f92 (S52 S8) S51)
(declare-fun f93 () S52)
(declare-fun f94 () S12)
(declare-fun f95 (S9 S8) S1)
(declare-fun f96 (S12) S8)
(declare-fun f97 (S53 S5) S14)
(declare-fun f98 (S23) S53)
(declare-fun f99 (S55 S17) S48)
(declare-fun f100 (S56 S54) S55)
(declare-fun f101 () S56)
(declare-fun f102 (S57 S14) S11)
(declare-fun f103 (S54) S57)
(declare-fun f104 (S59 S17) S12)
(declare-fun f105 (S60 S58) S59)
(declare-fun f106 () S60)
(declare-fun f107 (S61 S14) S8)
(declare-fun f108 (S58) S61)
(declare-fun f109 (S63 S25) S48)
(declare-fun f110 (S64 S62) S63)
(declare-fun f111 () S64)
(declare-fun f112 (S65 S2) S11)
(declare-fun f113 (S62) S65)
(declare-fun f114 (S67 S25) S12)
(declare-fun f115 (S68 S66) S67)
(declare-fun f116 () S68)
(declare-fun f117 (S69 S2) S8)
(declare-fun f118 (S66) S69)
(declare-fun f119 (S71 S22) S48)
(declare-fun f120 (S72 S70) S71)
(declare-fun f121 () S72)
(declare-fun f122 (S73 S5) S11)
(declare-fun f123 (S70) S73)
(declare-fun f124 (S75 S22) S12)
(declare-fun f125 (S76 S74) S75)
(declare-fun f126 () S76)
(declare-fun f127 (S77 S5) S8)
(declare-fun f128 (S74) S77)
(declare-fun f129 (S79 S48) S17)
(declare-fun f130 (S80 S78) S79)
(declare-fun f131 () S80)
(declare-fun f132 (S81 S11) S14)
(declare-fun f133 (S78) S81)
(declare-fun f134 (S83 S12) S17)
(declare-fun f135 (S84 S82) S83)
(declare-fun f136 () S84)
(declare-fun f137 (S85 S8) S14)
(declare-fun f138 (S82) S85)
(declare-fun f139 (S87 S48) S25)
(declare-fun f140 (S88 S86) S87)
(declare-fun f141 () S88)
(declare-fun f142 (S89 S11) S2)
(declare-fun f143 (S86) S89)
(declare-fun f144 (S91 S12) S25)
(declare-fun f145 (S92 S90) S91)
(declare-fun f146 () S92)
(declare-fun f147 (S93 S8) S2)
(declare-fun f148 (S90) S93)
(declare-fun f149 (S95 S48) S22)
(declare-fun f150 (S96 S94) S95)
(declare-fun f151 () S96)
(declare-fun f152 (S97 S11) S5)
(declare-fun f153 (S94) S97)
(declare-fun f154 (S99 S12) S22)
(declare-fun f155 (S100 S98) S99)
(declare-fun f156 () S100)
(declare-fun f157 (S101 S8) S5)
(declare-fun f158 (S98) S101)
(declare-fun f159 (S102 S9) S51)
(declare-fun f160 () S102)
(declare-fun f161 (S103 S12) S49)
(declare-fun f162 () S103)
(declare-fun f163 (S104 S3) S46)
(declare-fun f164 () S104)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (and (= (f3 ?v1 ?v2) f1) (= (f3 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S6)) (= (= (f6 (f7 (f8 ?v0) ?v1) ?v2) f1) (and (= (f6 ?v1 ?v2) f1) (= (f6 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S9)) (= (= (f9 (f10 (f11 ?v0) ?v1) ?v2) f1) (and (= (f9 ?v1 ?v2) f1) (= (f9 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (= (= (f12 (f13 (f14 ?v0) ?v1) ?v2) f1) (and (= (f12 ?v1 ?v2) f1) (= (f12 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S15)) (= (= (f15 (f16 (f17 ?v0) ?v1) ?v2) f1) (and (= (f15 ?v1 ?v2) f1) (= (f15 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S17)) (= (= (f18 (f19 (f20 f21 ?v0) ?v1) ?v2) f1) true)))
(assert (forall ((?v0 S15) (?v1 S17)) (= (= (f18 (f19 f22 ?v0) ?v1) f1) false)))
(assert (forall ((?v0 S6)) (= (f23 f24 ?v0) ?v0)))
(assert (not false))
(assert (forall ((?v0 S6)) (=> (= (f25 ?v0 (f26 f27)) f1) (and (not (= (f28 f29 ?v0) f30)) (not (= (f28 f31 ?v0) f30))))))
(assert (let ((?v_0 (f41 f42 (f43 (f44 f45 f29) f27)))) (not (= (f32 f33 (f34 (f35 f36 (f37 (f38 (f39 f40 ?v_0) f30) (f46 (f47 f48 f49) f50))) (f34 (f51 f52 (f53 f54 ?v_0)) f27))) f55))))
(assert (= (f28 f31 f56) f30))
(assert (let ((?v_0 (f41 f42 (f43 (f44 f45 f29) f27)))) (= (f57 (f58 (f59 f60 f61) f62) (f63 (f32 f33 (f34 (f35 f36 (f37 (f38 (f39 f40 ?v_0) f30) (f46 (f47 f48 f49) f50))) (f34 (f51 f52 (f53 f54 ?v_0)) f27))))) f1)))
(assert (let ((?v_0 (f41 f42 (f43 (f44 f45 f29) f27)))) (or (= f56 (f37 (f38 (f39 f40 ?v_0) f30) (f46 (f47 f48 f49) f50))) (= (f25 f56 (f7 (f64 (f53 f54 ?v_0)) (f26 f27))) f1))))
(assert (= (f15 (f65 f30) f66) f1))
(assert (let ((?v_0 (f41 f42 (f43 (f44 f45 f29) f27)))) (= (f15 (f67 f66) (f68 (f69 f70 ?v_0) (f41 f42 (f43 (f44 f45 f31) (f34 (f71 f72 (f73 (f74 (f75 f22) f21) f21)) (f34 (f51 f52 (f53 f54 ?v_0)) f27)))))) f1)))
(assert (forall ((?v0 S15)) (= (= (f15 (f65 f49) ?v0) f1) (= (f15 (f67 f30) ?v0) f1))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f37 (f38 (f39 f40 ?v1) ?v2) f50))) (= (f23 (f53 f54 ?v0) ?v_0) ?v_0))))
(assert (forall ((?v0 S15) (?v1 S17)) (= (f41 f42 (f46 (f47 f48 ?v0) ?v1)) (f68 (f69 f70 ?v0) (f41 f42 ?v1)))))
(assert (= (f41 f42 f50) f49))
(assert (forall ((?v0 S22)) (let ((?v_0 (f41 f42 (f43 (f44 f45 f29) ?v0)))) (= (f34 f76 ?v0) (f34 (f35 f36 (f37 (f38 (f39 f40 ?v_0) f30) (f46 (f47 f48 f49) f50))) (f34 (f51 f52 (f53 f54 ?v_0)) ?v0))))))
(assert (forall ((?v0 S15) (?v1 S15)) (=> (not (= ?v0 f30)) (=> (not (= ?v1 f30)) (= (f15 (f67 f30) (f68 (f69 f70 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (f15 (f65 f30) (f68 (f69 f70 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S15) (?v1 S15)) (let ((?v_0 (f65 f30))) (=> (= (f15 ?v_0 ?v0) f1) (=> (= (f15 ?v_0 ?v1) f1) (= (f15 ?v_0 (f68 (f69 f70 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S14) (?v1 S17)) (= (= (f46 (f77 f78 ?v0) ?v1) f50) (forall ((?v2 S15)) (=> (= (f79 ?v2 (f80 ?v1)) f1) (not (= (f15 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S2) (?v1 S25)) (= (= (f81 (f82 f83 ?v0) ?v1) f55) (forall ((?v2 S3)) (=> (= (f57 ?v2 (f63 ?v1)) f1) (not (= (f3 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S5) (?v1 S22)) (= (= (f34 (f71 f72 ?v0) ?v1) f84) (forall ((?v2 S6)) (=> (= (f25 ?v2 (f26 ?v1)) f1) (not (= (f6 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S11) (?v1 S48)) (= (= (f85 (f86 f87 ?v0) ?v1) f88) (forall ((?v2 S12)) (=> (= (f89 ?v2 (f90 ?v1)) f1) (not (= (f12 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S8) (?v1 S12)) (= (= (f91 (f92 f93 ?v0) ?v1) f94) (forall ((?v2 S9)) (=> (= (f95 ?v2 (f96 ?v1)) f1) (not (= (f9 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S21) (?v1 S22)) (= (f26 (f34 (f51 f52 ?v0) ?v1)) (f7 (f64 ?v0) (f26 ?v1)))))
(assert (forall ((?v0 S23) (?v1 S22)) (= (f80 (f43 (f44 f45 ?v0) ?v1)) (f97 (f98 ?v0) (f26 ?v1)))))
(assert (forall ((?v0 S54) (?v1 S17)) (= (f90 (f99 (f100 f101 ?v0) ?v1)) (f102 (f103 ?v0) (f80 ?v1)))))
(assert (forall ((?v0 S58) (?v1 S17)) (= (f96 (f104 (f105 f106 ?v0) ?v1)) (f107 (f108 ?v0) (f80 ?v1)))))
(assert (forall ((?v0 S62) (?v1 S25)) (= (f90 (f109 (f110 f111 ?v0) ?v1)) (f112 (f113 ?v0) (f63 ?v1)))))
(assert (forall ((?v0 S66) (?v1 S25)) (= (f96 (f114 (f115 f116 ?v0) ?v1)) (f117 (f118 ?v0) (f63 ?v1)))))
(assert (forall ((?v0 S70) (?v1 S22)) (= (f90 (f119 (f120 f121 ?v0) ?v1)) (f122 (f123 ?v0) (f26 ?v1)))))
(assert (forall ((?v0 S74) (?v1 S22)) (= (f96 (f124 (f125 f126 ?v0) ?v1)) (f127 (f128 ?v0) (f26 ?v1)))))
(assert (forall ((?v0 S78) (?v1 S48)) (= (f80 (f129 (f130 f131 ?v0) ?v1)) (f132 (f133 ?v0) (f90 ?v1)))))
(assert (forall ((?v0 S82) (?v1 S12)) (= (f80 (f134 (f135 f136 ?v0) ?v1)) (f137 (f138 ?v0) (f96 ?v1)))))
(assert (forall ((?v0 S86) (?v1 S48)) (= (f63 (f139 (f140 f141 ?v0) ?v1)) (f142 (f143 ?v0) (f90 ?v1)))))
(assert (forall ((?v0 S90) (?v1 S12)) (= (f63 (f144 (f145 f146 ?v0) ?v1)) (f147 (f148 ?v0) (f96 ?v1)))))
(assert (forall ((?v0 S94) (?v1 S48)) (= (f26 (f149 (f150 f151 ?v0) ?v1)) (f152 (f153 ?v0) (f90 ?v1)))))
(assert (forall ((?v0 S98) (?v1 S12)) (= (f26 (f154 (f155 f156 ?v0) ?v1)) (f157 (f158 ?v0) (f96 ?v1)))))
(assert (= (f15 (f67 f30) f49) f1))
(assert (= (f15 (f65 f30) f49) f1))
(assert (forall ((?v0 S17)) (= (= (f41 f42 ?v0) f30) (= (f79 f30 (f80 ?v0)) f1))))
(assert (forall ((?v0 S9) (?v1 S12) (?v2 S9) (?v3 S12)) (= (= (f91 (f159 f160 ?v0) ?v1) (f91 (f159 f160 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S12) (?v1 S48) (?v2 S12) (?v3 S48)) (= (= (f85 (f161 f162 ?v0) ?v1) (f85 (f161 f162 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S15) (?v1 S17) (?v2 S15) (?v3 S17)) (= (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 f48 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S6) (?v1 S22) (?v2 S6) (?v3 S22)) (= (= (f34 (f35 f36 ?v0) ?v1) (f34 (f35 f36 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S25) (?v2 S3) (?v3 S25)) (= (= (f81 (f163 f164 ?v0) ?v1) (f81 (f163 f164 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S9) (?v1 S12)) (not (= (f91 (f159 f160 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S12) (?v1 S48)) (not (= (f85 (f161 f162 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S15) (?v1 S17)) (not (= (f46 (f47 f48 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S6) (?v1 S22)) (not (= (f34 (f35 f36 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S3) (?v1 S25)) (not (= (f81 (f163 f164 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S12) (?v1 S9)) (not (= ?v0 (f91 (f159 f160 ?v1) ?v0)))))
(assert (forall ((?v0 S48) (?v1 S12)) (not (= ?v0 (f85 (f161 f162 ?v1) ?v0)))))
(assert (forall ((?v0 S17) (?v1 S15)) (not (= ?v0 (f46 (f47 f48 ?v1) ?v0)))))
(assert (forall ((?v0 S22) (?v1 S6)) (not (= ?v0 (f34 (f35 f36 ?v1) ?v0)))))
(assert (forall ((?v0 S25) (?v1 S3)) (not (= ?v0 (f81 (f163 f164 ?v1) ?v0)))))
(assert (forall ((?v0 S15) (?v1 S15)) (=> (= (f15 (f65 ?v0) ?v1) f1) (=> (= (f15 (f65 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f65 ?v0))) (=> (= (f15 ?v_0 ?v1) f1) (=> (= (f15 (f65 ?v1) ?v2) f1) (= (f15 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S15) (?v1 S15)) (or (= (f15 (f65 ?v0) ?v1) f1) (= (f15 (f65 ?v1) ?v0) f1))))
(assert (forall ((?v0 S15)) (= (f15 (f65 ?v0) ?v0) f1)))
(assert (forall ((?v0 S15) (?v1 S15)) (or (= (f15 (f67 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f15 (f67 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f69 f70 ?v0))) (= (f68 (f69 f70 (f68 ?v_0 ?v1)) ?v2) (f68 ?v_0 (f68 (f69 f70 ?v1) ?v2))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_1 (f69 f70 ?v0)) (?v_0 (f69 f70 ?v1))) (= (f68 ?v_1 (f68 ?v_0 ?v2)) (f68 ?v_0 (f68 ?v_1 ?v2))))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (f68 (f69 f70 ?v0) ?v1) (f68 (f69 f70 ?v1) ?v0))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S17) (?v3 S15) (?v4 S15) (?v5 S17)) (= (= (f37 (f38 (f39 f40 ?v0) ?v1) ?v2) (f37 (f38 (f39 f40 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S22)) (= (f34 (f51 f52 f24) ?v0) ?v0)))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S22)) (= (f34 (f71 f72 ?v0) (f34 (f71 f72 ?v1) ?v2)) (f34 (f71 f72 (f7 (f8 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S12)) (= (f91 (f92 f93 ?v0) (f91 (f92 f93 ?v1) ?v2)) (f91 (f92 f93 (f10 (f11 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S48)) (= (f85 (f86 f87 ?v0) (f85 (f86 f87 ?v1) ?v2)) (f85 (f86 f87 (f13 (f14 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S25)) (= (f81 (f82 f83 ?v0) (f81 (f82 f83 ?v1) ?v2)) (f81 (f82 f83 (f4 (f5 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S17)) (= (f46 (f77 f78 ?v0) (f46 (f77 f78 ?v1) ?v2)) (f46 (f77 f78 (f16 (f17 ?v0) ?v1)) ?v2))))
(assert (= (f15 (f65 f30) f30) f1))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S17)) (=> (= (f79 ?v0 (f80 (f46 (f47 f48 ?v1) ?v2))) f1) (or (= ?v0 ?v1) (= (f79 ?v0 (f80 ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S25)) (=> (= (f57 ?v0 (f63 (f81 (f163 f164 ?v1) ?v2))) f1) (or (= ?v0 ?v1) (= (f57 ?v0 (f63 ?v2)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S22)) (=> (= (f25 ?v0 (f26 (f34 (f35 f36 ?v1) ?v2))) f1) (or (= ?v0 ?v1) (= (f25 ?v0 (f26 ?v2)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S12)) (=> (= (f95 ?v0 (f96 (f91 (f159 f160 ?v1) ?v2))) f1) (or (= ?v0 ?v1) (= (f95 ?v0 (f96 ?v2)) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S48)) (=> (= (f89 ?v0 (f90 (f85 (f161 f162 ?v1) ?v2))) f1) (or (= ?v0 ?v1) (= (f89 ?v0 (f90 ?v2)) f1)))))
(assert (forall ((?v0 S12) (?v1 S48)) (not (= (f85 (f161 f162 ?v0) ?v1) f88))))
(assert (forall ((?v0 S9) (?v1 S12)) (not (= (f91 (f159 f160 ?v0) ?v1) f94))))
(assert (forall ((?v0 S3) (?v1 S25)) (not (= (f81 (f163 f164 ?v0) ?v1) f55))))
(assert (forall ((?v0 S15) (?v1 S17)) (not (= (f46 (f47 f48 ?v0) ?v1) f50))))
(assert (forall ((?v0 S6) (?v1 S22)) (not (= (f34 (f35 f36 ?v0) ?v1) f84))))
(assert (forall ((?v0 S12) (?v1 S48)) (not (= f88 (f85 (f161 f162 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S12)) (not (= f94 (f91 (f159 f160 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S25)) (not (= f55 (f81 (f163 f164 ?v0) ?v1)))))
(assert (forall ((?v0 S15) (?v1 S17)) (not (= f50 (f46 (f47 f48 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S22)) (not (= f84 (f34 (f35 f36 ?v0) ?v1)))))
(assert (not (= f30 f49)))
(check-sat)
(exit)