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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 () S2)
(declare-fun f5 (S4 S5) S3)
(declare-fun f6 (S6 S3) S4)
(declare-fun f7 () S6)
(declare-fun f8 () S3)
(declare-fun f9 () S5)
(declare-fun f10 (S7 S3) S3)
(declare-fun f11 () S7)
(declare-fun f12 (S8 S3) S6)
(declare-fun f13 () S8)
(declare-fun f14 (S9 S3) S2)
(declare-fun f15 () S9)
(declare-fun f16 (S10 S3) S7)
(declare-fun f17 () S10)
(declare-fun f18 (S11 S3 S12) S1)
(declare-fun f19 (S13 S12) S11)
(declare-fun f20 (S14 S5) S13)
(declare-fun f21 (S15 S11) S14)
(declare-fun f22 () S15)
(declare-fun f23 (S16 S5) S6)
(declare-fun f24 () S16)
(declare-fun f25 (S17 S5) S5)
(declare-fun f26 () S17)
(declare-fun f27 (S11 S5) S12)
(declare-fun f28 () S5)
(declare-fun f29 (S18 S12) S12)
(declare-fun f30 (S19 S12) S18)
(declare-fun f31 () S19)
(declare-fun f32 (S20 S5) S1)
(declare-fun f33 () S8)
(declare-fun f34 (S22 S21) S3)
(declare-fun f35 (S23 S3) S22)
(declare-fun f36 (S24 S10) S23)
(declare-fun f37 () S24)
(declare-fun f38 (S9) S2)
(declare-fun f39 (S9) S9)
(declare-fun f40 () S4)
(declare-fun f41 (S2 S21) S1)
(declare-fun f42 (S25 S3) S5)
(declare-fun f43 () S25)
(declare-fun f44 (S26 S21) S1)
(declare-fun f45 (S27 S21) S26)
(declare-fun f46 (S9) S27)
(declare-fun f47 () S11)
(declare-fun f48 (S27) S26)
(declare-fun f49 (S30 S29) S1)
(declare-fun f50 (S28) S30)
(declare-fun f51 (S31 S29) S1)
(declare-fun f52 (S28) S31)
(declare-fun f53 (S34 S33) S1)
(declare-fun f54 (S32) S34)
(declare-fun f55 (S35 S33) S1)
(declare-fun f56 (S32) S35)
(declare-fun f57 (S35 S37) S1)
(declare-fun f58 (S36) S32)
(declare-fun f59 (S38 S37) S1)
(declare-fun f60 (S36) S38)
(declare-fun f61 (S31 S39) S1)
(declare-fun f62 (S27) S28)
(declare-fun f63 (S26 S39) S1)
(declare-fun f64 (S38 S41) S1)
(declare-fun f65 (S40) S36)
(declare-fun f66 (S42 S41) S1)
(declare-fun f67 (S40) S42)
(declare-fun f68 (S42 S44) S1)
(declare-fun f69 (S43) S40)
(declare-fun f70 (S45 S44) S1)
(declare-fun f71 (S43) S45)
(declare-fun f72 (S27) S27)
(declare-fun f73 (S36) S36)
(declare-fun f74 (S32) S32)
(declare-fun f75 (S28) S28)
(declare-fun f76 (S30) S30)
(declare-fun f77 (S40) S40)
(declare-fun f78 (S43) S43)
(declare-fun f79 (S32 S37) S35)
(declare-fun f80 (S46 S29) S1)
(declare-fun f81 (S30 S29) S46)
(declare-fun f82 (S28 S39) S31)
(declare-fun f83 (S36 S41) S38)
(declare-fun f84 (S40 S44) S42)
(declare-fun f85 (S47 S12) S5)
(declare-fun f86 () S47)
(declare-fun f87 () S47)
(declare-fun f88 (S48 S5) S17)
(declare-fun f89 () S48)
(declare-fun f90 (S49 S21) S21)
(declare-fun f91 (S50 S3) S49)
(declare-fun f92 () S50)
(declare-fun f93 (S45 S51) S1)
(declare-fun f94 (S52 S44) S44)
(declare-fun f95 (S53 S51) S52)
(declare-fun f96 () S53)
(declare-fun f97 (S54 S41) S41)
(declare-fun f98 (S55 S44) S54)
(declare-fun f99 () S55)
(declare-fun f100 (S56) S20)
(declare-fun f101 (S58 S57) S1)
(declare-fun f102 (S56) S58)
(declare-fun f103 (S59 S57) S57)
(declare-fun f104 (S60 S5) S59)
(declare-fun f105 () S60)
(declare-fun f106 (S61 S62) S1)
(declare-fun f107 (S64 S63) S1)
(declare-fun f108 (S61) S64)
(declare-fun f109 (S65 S63) S63)
(declare-fun f110 (S66 S62) S65)
(declare-fun f111 () S66)
(declare-fun f112 (S67 S29) S29)
(declare-fun f113 (S68 S39) S67)
(declare-fun f114 () S68)
(declare-fun f115 (S69 S33) S33)
(declare-fun f116 (S70 S37) S69)
(declare-fun f117 () S70)
(declare-fun f118 (S71 S37) S37)
(declare-fun f119 (S72 S41) S71)
(declare-fun f120 () S72)
(declare-fun f121 (S73 S39) S39)
(declare-fun f122 (S74 S21) S73)
(declare-fun f123 () S74)
(declare-fun f124 (S43 S51) S45)
(declare-fun f125 (S75 S57) S1)
(declare-fun f126 (S58 S57) S75)
(declare-fun f127 (S56 S5) S20)
(declare-fun f128 (S76 S63) S1)
(declare-fun f129 (S64 S63) S76)
(declare-fun f130 (S77 S62) S1)
(declare-fun f131 (S61 S62) S77)
(declare-fun f132 (S78 S57) S5)
(declare-fun f133 (S79 S5) S78)
(declare-fun f134 (S80 S48) S79)
(declare-fun f135 () S80)
(declare-fun f136 (S81 S62) S62)
(declare-fun f137 (S82 S62) S81)
(declare-fun f138 () S82)
(declare-fun f139 (S83 S63) S62)
(declare-fun f140 (S84 S62) S83)
(declare-fun f141 (S85 S82) S84)
(declare-fun f142 () S85)
(declare-fun f143 () S62)
(declare-fun f144 () S25)
(assert (not (= f1 f2)))
(assert (not (= (f3 f4 (f5 (f6 f7 f8) f9)) f1)))
(assert (= (f3 f4 f8) f1))
(assert (forall ((?v0 S3)) (=> (= (f3 f4 ?v0) f1) (= (f3 f4 (f10 f11 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S5) (?v2 S3)) (= (f5 (f6 (f12 f13 (f5 (f6 f7 ?v0) ?v1)) ?v2) ?v1) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S5)) (=> (= (f3 (f14 f15 ?v0) ?v1) f1) (= (f3 (f14 f15 (f5 (f6 f7 ?v0) ?v2)) (f5 (f6 f7 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S5)) (= (f5 (f6 f7 (f10 (f16 f17 ?v0) ?v1)) ?v2) (f10 (f16 f17 (f5 (f6 f7 ?v0) ?v2)) (f5 (f6 f7 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S12) (?v3 S5) (?v4 S12)) (=> (= (f18 ?v0 ?v1 ?v2) f1) (= (f18 (f19 (f20 (f21 f22 ?v0) ?v3) ?v4) (f5 (f6 f7 ?v1) ?v3) ?v2) f1))))
(assert (forall ((?v0 S5) (?v1 S3) (?v2 S5)) (= (f5 (f6 (f23 f24 (f25 f26 ?v0)) ?v1) ?v2) (f5 (f6 f7 (f5 (f6 (f23 f24 ?v0) ?v1) ?v2)) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f14 f15 ?v0) ?v1) f1) (= (f3 (f14 f15 (f10 (f16 f17 ?v0) ?v2)) (f10 (f16 f17 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 f17 ?v2))) (=> (= (f3 (f14 f15 ?v0) ?v1) f1) (= (f3 (f14 f15 (f10 ?v_0 ?v0)) (f10 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f14 f15 ?v0) ?v1) f1) (= (f3 (f14 f15 (f10 f11 ?v0)) (f10 f11 ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (not (= (f10 f11 ?v0) (f10 (f16 f17 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (not (= (f10 (f16 f17 ?v0) ?v1) (f10 f11 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f10 f11 ?v0) (f10 f11 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (= (f10 (f16 f17 ?v0) ?v1) (f10 (f16 f17 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5) (?v1 S3) (?v2 S3) (?v3 S5)) (let ((?v_0 (f23 f24 ?v0))) (= (f5 (f6 ?v_0 (f10 (f16 f17 ?v1) ?v2)) ?v3) (f10 (f16 f17 (f5 (f6 ?v_0 ?v1) ?v3)) (f5 (f6 ?v_0 ?v2) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S5)) (= (f5 (f6 (f12 f13 (f10 (f16 f17 ?v0) ?v1)) ?v2) ?v3) (f10 (f16 f17 (f5 (f6 (f12 f13 ?v0) ?v2) ?v3)) (f5 (f6 (f12 f13 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S5)) (=> (= (f3 (f14 f15 ?v0) ?v1) f1) (= (f3 (f14 f15 (f5 (f6 (f12 f13 ?v0) ?v2) ?v3)) (f5 (f6 (f12 f13 ?v1) ?v2) ?v3)) f1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S11) (?v3 S12)) (=> (= ?v0 ?v1) (= (f27 (f19 (f20 (f21 f22 ?v2) ?v0) ?v3) ?v1) ?v3))))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S12) (?v3 S3)) (=> (= (f18 ?v0 ?v1 ?v2) f1) (=> (= (f3 (f14 f15 ?v1) ?v3) f1) (= (f18 ?v0 ?v3 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S12) (?v3 S11) (?v4 S3) (?v5 S12) (?v6 S5)) (=> (= (f18 ?v0 ?v1 ?v2) f1) (=> (= (f18 ?v3 ?v4 ?v5) f1) (=> (= ?v0 (f19 (f20 (f21 f22 ?v3) ?v6) ?v5)) (= (f18 ?v3 (f5 (f6 (f12 f13 ?v1) ?v4) ?v6) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f14 f15 (f10 f11 ?v0)) ?v1) f1) (=> (forall ((?v2 S3)) (=> (= ?v1 (f10 f11 ?v2)) (=> (= (f3 (f14 f15 ?v0) ?v2) f1) false))) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f14 f15 (f10 (f16 f17 (f10 f11 ?v0)) ?v1)) (f5 (f6 (f12 f13 ?v0) ?v1) f28)) f1)))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S12) (?v3 S12) (?v4 S3)) (=> (= (f18 ?v0 ?v1 (f29 (f30 f31 ?v2) ?v3)) f1) (=> (= (f18 ?v0 ?v4 ?v2) f1) (= (f18 ?v0 (f10 (f16 f17 ?v1) ?v4) ?v3) f1)))))
(assert (forall ((?v0 S5)) (not (= ?v0 (f25 f26 ?v0)))))
(assert (forall ((?v0 S5)) (not (= (f25 f26 ?v0) ?v0))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f25 f26 ?v0) (f25 f26 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f25 f26 ?v0) (f25 f26 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S12)) (=> (= (f18 ?v0 (f10 f11 ?v1) ?v2) f1) (=> (forall ((?v3 S12) (?v4 S12)) (=> (= (f18 (f19 (f20 (f21 f22 ?v0) f28) ?v3) ?v1 ?v4) f1) false)) false))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S3) (?v3 S12)) (=> (= (f18 (f19 (f20 (f21 f22 ?v0) f28) ?v1) ?v2 ?v3) f1) (= (f18 ?v0 (f10 f11 ?v2) (f29 (f30 f31 ?v1) ?v3)) f1))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (= (= (f29 (f30 f31 ?v0) ?v1) (f29 (f30 f31 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5)) (=> (= (f25 f26 ?v0) f28) false)))
(assert (forall ((?v0 S5)) (=> (= f28 (f25 f26 ?v0)) false)))
(assert (forall ((?v0 S5)) (not (= (f25 f26 ?v0) f28))))
(assert (forall ((?v0 S5)) (not (= (f25 f26 ?v0) f28))))
(assert (forall ((?v0 S5)) (not (= f28 (f25 f26 ?v0)))))
(assert (forall ((?v0 S5)) (not (= f28 (f25 f26 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (f5 (f6 (f23 f24 f28) ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S12) (?v3 S12)) (let ((?v_0 (f21 f22 ?v0))) (= (f19 (f20 (f21 f22 (f19 (f20 ?v_0 ?v1) ?v2)) f28) ?v3) (f19 (f20 (f21 f22 (f19 (f20 ?v_0 f28) ?v3)) (f25 f26 ?v1)) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S12)) (=> (= (f18 ?v0 (f10 f11 ?v1) ?v2) f1) (=> (forall ((?v3 S12) (?v4 S12)) (=> (= ?v2 (f29 (f30 f31 ?v3) ?v4)) (=> (= (f18 (f19 (f20 (f21 f22 ?v0) f28) ?v3) ?v1 ?v4) f1) false))) false))))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S3) (?v3 S12)) (=> (= (f18 ?v0 (f10 (f16 f17 ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S12)) (=> (= (f18 ?v0 ?v1 (f29 (f30 f31 ?v4) ?v3)) f1) (=> (= (f18 ?v0 ?v2 ?v4) f1) false))) false))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f14 f15 (f10 (f16 f17 ?v0) ?v1)) ?v2) f1) (=> (forall ((?v3 S3)) (=> (= ?v2 (f5 (f6 (f12 f13 ?v3) ?v1) f28)) (=> (= ?v0 (f10 f11 ?v3)) false))) (=> (forall ((?v3 S3)) (=> (= ?v2 (f10 (f16 f17 ?v3) ?v1)) (=> (= (f3 (f14 f15 ?v0) ?v3) f1) false))) (=> (forall ((?v3 S3)) (=> (= ?v2 (f10 (f16 f17 ?v0) ?v3)) (=> (= (f3 (f14 f15 ?v1) ?v3) f1) false))) false))))))
(assert (forall ((?v0 S5)) (=> (=> (= ?v0 f28) false) (=> (forall ((?v1 S5)) (=> (= ?v0 (f25 f26 ?v1)) false)) false))))
(assert (forall ((?v0 S20) (?v1 S5)) (=> (= (f32 ?v0 ?v1) f1) (=> (forall ((?v2 S5)) (=> (= (f32 ?v0 (f25 f26 ?v2)) f1) (= (f32 ?v0 ?v2) f1))) (= (f32 ?v0 f28) f1)))))
(assert (forall ((?v0 S20) (?v1 S5)) (=> (= (f32 ?v0 f28) f1) (=> (forall ((?v2 S5)) (=> (= (f32 ?v0 ?v2) f1) (= (f32 ?v0 (f25 f26 ?v2)) f1))) (= (f32 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S5)) (=> (not (= ?v0 f28)) (exists ((?v1 S5)) (= ?v0 (f25 f26 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S5)) (= (f5 (f6 (f12 f33 ?v0) ?v1) ?v2) (f5 (f6 (f12 f13 ?v0) (f5 (f6 (f23 f24 ?v2) ?v1) f28)) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S21)) (let ((?v_0 (f36 f37 f17))) (=> (= (f3 f4 (f34 (f35 ?v_0 (f5 (f6 (f12 f13 ?v0) ?v1) f28)) ?v2)) f1) (=> (= (f3 f4 ?v1) f1) (= (f3 f4 (f34 (f35 ?v_0 (f10 (f16 f17 (f10 f11 ?v0)) ?v1)) ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S5)) (= (f5 (f6 (f12 f33 (f10 (f16 f17 ?v0) ?v1)) ?v2) ?v3) (f10 (f16 f17 (f5 (f6 (f12 f33 ?v0) ?v2) ?v3)) (f5 (f6 (f12 f33 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 (f12 f33 ?v0) ?v1) f28) (f5 (f6 (f12 f13 ?v0) ?v1) f28))))
(assert (forall ((?v0 S3) (?v1 S21) (?v2 S3) (?v3 S21)) (let ((?v_0 (f36 f37 f17))) (= (= (f34 (f35 ?v_0 (f10 f11 ?v0)) ?v1) (f34 (f35 ?v_0 (f10 f11 ?v2)) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S21)) (let ((?v_0 (f36 f37 f17))) (=> (= (f3 (f14 f15 ?v0) ?v1) f1) (= (f3 (f14 f15 (f34 (f35 ?v_0 ?v0) ?v2)) (f34 (f35 ?v_0 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S21) (?v2 S3)) (let ((?v_0 (f36 f37 f17))) (= (= (f34 (f35 ?v_0 ?v0) ?v1) (f34 (f35 ?v_0 ?v2) ?v1)) (= ?v0 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S21)) (let ((?v_1 (f36 f37 f17)) (?v_0 (f38 (f39 f15)))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (=> (= ?v1 (f34 (f35 ?v_1 (f5 (f6 (f12 f13 ?v2) ?v0) f28)) ?v3)) (= (f3 ?v_0 (f34 (f35 ?v_1 (f10 (f16 f17 (f10 f11 ?v2)) ?v0)) ?v3)) f1)))))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S21) (?v3 S12) (?v4 S12)) (let ((?v_0 (f34 (f35 (f36 f37 f17) (f5 f40 ?v1)) ?v2))) (=> (= (f18 ?v0 ?v_0 ?v3) f1) (=> (= (f18 ?v0 ?v_0 ?v4) f1) (= ?v3 ?v4))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f14 f15 ?v0) ?v1) f1) (or (exists ((?v2 S3) (?v3 S3)) (and (= ?v0 (f10 (f16 f17 (f10 f11 ?v2)) ?v3)) (= ?v1 (f5 (f6 (f12 f13 ?v2) ?v3) f28)))) (or (exists ((?v2 S3) (?v3 S3) (?v4 S3)) (and (= ?v0 (f10 (f16 f17 ?v2) ?v4)) (and (= ?v1 (f10 (f16 f17 ?v3) ?v4)) (= (f3 (f14 f15 ?v2) ?v3) f1)))) (or (exists ((?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f16 f17 ?v4))) (and (= ?v0 (f10 ?v_0 ?v2)) (and (= ?v1 (f10 ?v_0 ?v3)) (= (f3 (f14 f15 ?v2) ?v3) f1))))) (exists ((?v2 S3) (?v3 S3)) (and (= ?v0 (f10 f11 ?v2)) (and (= ?v1 (f10 f11 ?v3)) (= (f3 (f14 f15 ?v2) ?v3) f1))))))))))
(assert (forall ((?v0 S5) (?v1 S3)) (=> (= (f3 (f14 f15 (f5 f40 ?v0)) ?v1) f1) false)))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S12)) (=> (= (f18 ?v0 (f5 f40 ?v1) ?v2) f1) (=> (=> (= (f27 ?v0 ?v1) ?v2) false) false))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S12)) (=> (= (f27 ?v0 ?v1) ?v2) (= (f18 ?v0 (f5 f40 ?v1) ?v2) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f5 f40 ?v0) (f5 f40 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S5)) (not (= (f10 (f16 f17 ?v0) ?v1) (f5 f40 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S3) (?v2 S3)) (not (= (f5 f40 ?v0) (f10 (f16 f17 ?v1) ?v2)))))
(assert (forall ((?v0 S3)) (=> (= (f3 (f38 (f39 f15)) ?v0) f1) (= (f3 f4 ?v0) f1))))
(assert (forall ((?v0 S3)) (=> (= (f3 f4 ?v0) f1) (= (f3 (f38 (f39 f15)) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S3)) (not (= (f5 f40 ?v0) (f10 f11 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S5)) (not (= (f10 f11 ?v0) (f5 f40 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S3)) (= (f5 (f6 (f12 f13 (f5 f40 ?v0)) ?v1) ?v0) ?v1)))
(assert (forall ((?v0 S5) (?v1 S21) (?v2 S5) (?v3 S21)) (let ((?v_0 (f36 f37 f17))) (= (= (f34 (f35 ?v_0 (f5 f40 ?v0)) ?v1) (f34 (f35 ?v_0 (f5 f40 ?v2)) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S5) (?v1 S21) (?v2 S3) (?v3 S21)) (let ((?v_0 (f36 f37 f17))) (not (= (f34 (f35 ?v_0 (f5 f40 ?v0)) ?v1) (f34 (f35 ?v_0 (f10 f11 ?v2)) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S5) (?v3 S21)) (not (= (f10 (f16 f17 (f10 f11 ?v0)) ?v1) (f34 (f35 (f36 f37 f17) (f5 f40 ?v2)) ?v3)))))
(assert (forall ((?v0 S21) (?v1 S5)) (=> (= (f41 f4 ?v0) f1) (= (f3 f4 (f34 (f35 (f36 f37 f17) (f5 f40 ?v1)) ?v0)) f1))))
(assert (forall ((?v0 S5)) (= (f42 f43 (f5 f40 ?v0)) f28)))
(assert (forall ((?v0 S3)) (= (= (f3 f4 ?v0) f1) (or (exists ((?v1 S21) (?v2 S5)) (and (= ?v0 (f34 (f35 (f36 f37 f17) (f5 f40 ?v2)) ?v1)) (= (f41 f4 ?v1) f1))) (or (exists ((?v1 S3)) (and (= ?v0 (f10 f11 ?v1)) (= (f3 f4 ?v1) f1))) (exists ((?v1 S3) (?v2 S3) (?v3 S21)) (let ((?v_0 (f36 f37 f17))) (and (= ?v0 (f34 (f35 ?v_0 (f10 (f16 f17 (f10 f11 ?v1)) ?v2)) ?v3)) (and (= (f3 f4 (f34 (f35 ?v_0 (f5 (f6 (f12 f13 ?v1) ?v2) f28)) ?v3)) f1) (= (f3 f4 ?v2) f1))))))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S3)) (let ((?v_0 (f35 (f36 f37 f17) ?v2))) (=> (= (f44 (f45 (f46 f15) ?v0) ?v1) f1) (= (f3 (f14 f15 (f34 ?v_0 ?v0)) (f34 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S5)) (=> (= ?v0 (f5 f40 ?v1)) false)) (=> (forall ((?v1 S3) (?v2 S3)) (=> (= ?v0 (f10 (f16 f17 ?v1) ?v2)) false)) (=> (forall ((?v1 S3)) (=> (= ?v0 (f10 f11 ?v1)) false)) false)))))
(assert (forall ((?v0 S5) (?v1 S21) (?v2 S3)) (=> (= (f3 (f14 f15 (f34 (f35 (f36 f37 f17) (f5 f40 ?v0)) ?v1)) ?v2) f1) (exists ((?v3 S21)) (and (= (f44 (f45 (f46 f15) ?v1) ?v3) f1) (= ?v2 (f34 (f35 (f36 f37 f17) (f5 f40 ?v0)) ?v3)))))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f27 f47 ?v0) (f27 f47 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S5)) (not (= (f29 (f30 f31 ?v0) ?v1) (f27 f47 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S12) (?v2 S12)) (not (= (f27 f47 ?v0) (f29 (f30 f31 ?v1) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S21)) (=> (= (f44 (f48 (f46 ?v0)) ?v1) f1) (= (f41 (f38 ?v0) ?v1) f1))))
(assert (forall ((?v0 S28) (?v1 S29)) (=> (= (f49 (f50 ?v0) ?v1) f1) (= (f51 (f52 ?v0) ?v1) f1))))
(assert (forall ((?v0 S32) (?v1 S33)) (=> (= (f53 (f54 ?v0) ?v1) f1) (= (f55 (f56 ?v0) ?v1) f1))))
(assert (forall ((?v0 S36) (?v1 S37)) (=> (= (f57 (f56 (f58 ?v0)) ?v1) f1) (= (f59 (f60 ?v0) ?v1) f1))))
(assert (forall ((?v0 S27) (?v1 S39)) (=> (= (f61 (f52 (f62 ?v0)) ?v1) f1) (= (f63 (f48 ?v0) ?v1) f1))))
(assert (forall ((?v0 S40) (?v1 S41)) (=> (= (f64 (f60 (f65 ?v0)) ?v1) f1) (= (f66 (f67 ?v0) ?v1) f1))))
(assert (forall ((?v0 S43) (?v1 S44)) (=> (= (f68 (f67 (f69 ?v0)) ?v1) f1) (= (f70 (f71 ?v0) ?v1) f1))))
(assert (forall ((?v0 S9) (?v1 S21)) (=> (= (f41 (f38 ?v0) ?v1) f1) (= (f44 (f48 (f46 ?v0)) ?v1) f1))))
(assert (forall ((?v0 S28) (?v1 S29)) (=> (= (f51 (f52 ?v0) ?v1) f1) (= (f49 (f50 ?v0) ?v1) f1))))
(assert (forall ((?v0 S32) (?v1 S33)) (=> (= (f55 (f56 ?v0) ?v1) f1) (= (f53 (f54 ?v0) ?v1) f1))))
(assert (forall ((?v0 S36) (?v1 S37)) (=> (= (f59 (f60 ?v0) ?v1) f1) (= (f57 (f56 (f58 ?v0)) ?v1) f1))))
(assert (forall ((?v0 S27) (?v1 S39)) (=> (= (f63 (f48 ?v0) ?v1) f1) (= (f61 (f52 (f62 ?v0)) ?v1) f1))))
(assert (forall ((?v0 S40) (?v1 S41)) (=> (= (f66 (f67 ?v0) ?v1) f1) (= (f64 (f60 (f65 ?v0)) ?v1) f1))))
(assert (forall ((?v0 S43) (?v1 S44)) (=> (= (f70 (f71 ?v0) ?v1) f1) (= (f68 (f67 (f69 ?v0)) ?v1) f1))))
(assert (forall ((?v0 S9)) (= (f46 (f39 ?v0)) (f72 (f46 ?v0)))))
(assert (forall ((?v0 S36)) (= (f58 (f73 ?v0)) (f74 (f58 ?v0)))))
(assert (forall ((?v0 S28)) (= (f50 (f75 ?v0)) (f76 (f50 ?v0)))))
(assert (forall ((?v0 S27)) (= (f62 (f72 ?v0)) (f75 (f62 ?v0)))))
(assert (forall ((?v0 S40)) (= (f65 (f77 ?v0)) (f73 (f65 ?v0)))))
(assert (forall ((?v0 S43)) (= (f69 (f78 ?v0)) (f77 (f69 ?v0)))))
(assert (forall ((?v0 S9) (?v1 S21) (?v2 S21)) (= (= (f44 (f45 (f46 (f39 ?v0)) ?v1) ?v2) f1) (= (f44 (f45 (f72 (f46 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S36) (?v1 S37) (?v2 S37)) (= (= (f57 (f79 (f58 (f73 ?v0)) ?v1) ?v2) f1) (= (f57 (f79 (f74 (f58 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S28) (?v1 S29) (?v2 S29)) (= (= (f80 (f81 (f50 (f75 ?v0)) ?v1) ?v2) f1) (= (f80 (f81 (f76 (f50 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S27) (?v1 S39) (?v2 S39)) (= (= (f61 (f82 (f62 (f72 ?v0)) ?v1) ?v2) f1) (= (f61 (f82 (f75 (f62 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S40) (?v1 S41) (?v2 S41)) (= (= (f64 (f83 (f65 (f77 ?v0)) ?v1) ?v2) f1) (= (f64 (f83 (f73 (f65 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S43) (?v1 S44) (?v2 S44)) (= (= (f68 (f84 (f69 (f78 ?v0)) ?v1) ?v2) f1) (= (f68 (f84 (f77 (f69 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S5)) (= (f85 f86 (f27 f47 ?v0)) f28)))
(assert (forall ((?v0 S5)) (= (f85 f87 (f27 f47 ?v0)) f28)))
(assert (forall ((?v0 S12)) (=> (forall ((?v1 S5)) (=> (= ?v0 (f27 f47 ?v1)) false)) (=> (forall ((?v1 S12) (?v2 S12)) (=> (= ?v0 (f29 (f30 f31 ?v1) ?v2)) false)) false))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (f85 f87 (f29 (f30 f31 ?v0) ?v1)) (f25 (f88 f89 (f25 (f88 f89 (f85 f87 ?v0)) (f85 f87 ?v1))) (f25 f26 f28)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (f85 f86 (f29 (f30 f31 ?v0) ?v1)) (f25 (f88 f89 (f25 (f88 f89 (f85 f86 ?v0)) (f85 f86 ?v1))) (f25 f26 f28)))))
(assert (forall ((?v0 S3) (?v1 S21) (?v2 S3)) (=> (= (f3 (f14 f15 (f34 (f35 (f36 f37 f17) ?v0) ?v1)) ?v2) f1) (=> (forall ((?v3 S3)) (=> (= (f3 (f14 f15 ?v0) ?v3) f1) (=> (= ?v2 (f34 (f35 (f36 f37 f17) ?v3) ?v1)) false))) (=> (forall ((?v3 S21)) (=> (= (f44 (f45 (f46 f15) ?v1) ?v3) f1) (=> (= ?v2 (f34 (f35 (f36 f37 f17) ?v0) ?v3)) false))) (=> (forall ((?v3 S3) (?v4 S3) (?v5 S21)) (=> (= ?v0 (f10 f11 ?v3)) (=> (= ?v1 (f90 (f91 f92 ?v4) ?v5)) (=> (= ?v2 (f34 (f35 (f36 f37 f17) (f5 (f6 (f12 f13 ?v3) ?v4) f28)) ?v5)) false)))) false))))))
(assert (forall ((?v0 S3)) (= (f42 f43 (f10 f11 ?v0)) (f25 (f88 f89 (f42 f43 ?v0)) (f25 f26 f28)))))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S21)) (let ((?v_0 (f48 (f46 ?v0)))) (=> (= (f3 (f38 ?v0) ?v1) f1) (=> (= (f44 ?v_0 ?v2) f1) (= (f44 ?v_0 (f90 (f91 f92 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S43) (?v1 S51) (?v2 S44)) (let ((?v_0 (f67 (f69 ?v0)))) (=> (= (f93 (f71 ?v0) ?v1) f1) (=> (= (f68 ?v_0 ?v2) f1) (= (f68 ?v_0 (f94 (f95 f96 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S40) (?v1 S44) (?v2 S41)) (let ((?v_0 (f60 (f65 ?v0)))) (=> (= (f68 (f67 ?v0) ?v1) f1) (=> (= (f64 ?v_0 ?v2) f1) (= (f64 ?v_0 (f97 (f98 f99 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S56) (?v1 S5) (?v2 S57)) (let ((?v_0 (f102 ?v0))) (=> (= (f32 (f100 ?v0) ?v1) f1) (=> (= (f101 ?v_0 ?v2) f1) (= (f101 ?v_0 (f103 (f104 f105 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S61) (?v1 S62) (?v2 S63)) (let ((?v_0 (f108 ?v0))) (=> (= (f106 ?v0 ?v1) f1) (=> (= (f107 ?v_0 ?v2) f1) (= (f107 ?v_0 (f109 (f110 f111 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S28) (?v1 S39) (?v2 S29)) (let ((?v_0 (f50 ?v0))) (=> (= (f61 (f52 ?v0) ?v1) f1) (=> (= (f49 ?v_0 ?v2) f1) (= (f49 ?v_0 (f112 (f113 f114 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S32) (?v1 S37) (?v2 S33)) (let ((?v_0 (f54 ?v0))) (=> (= (f57 (f56 ?v0) ?v1) f1) (=> (= (f53 ?v_0 ?v2) f1) (= (f53 ?v_0 (f115 (f116 f117 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S36) (?v1 S41) (?v2 S37)) (let ((?v_0 (f56 (f58 ?v0)))) (=> (= (f64 (f60 ?v0) ?v1) f1) (=> (= (f57 ?v_0 ?v2) f1) (= (f57 ?v_0 (f118 (f119 f120 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S27) (?v1 S21) (?v2 S39)) (let ((?v_0 (f52 (f62 ?v0)))) (=> (= (f44 (f48 ?v0) ?v1) f1) (=> (= (f61 ?v_0 ?v2) f1) (= (f61 ?v_0 (f121 (f122 f123 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (= (= (f25 (f88 f89 ?v0) ?v1) (f25 (f88 f89 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f88 f89 ?v0))) (= (= (f25 ?v_0 ?v1) (f25 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f88 f89 ?v0))) (= (f25 (f88 f89 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f88 f89 ?v1) ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_1 (f88 f89 ?v0)) (?v_0 (f88 f89 ?v1))) (= (f25 ?v_1 (f25 ?v_0 ?v2)) (f25 ?v_0 (f25 ?v_1 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f25 (f88 f89 ?v0) ?v1) (f25 (f88 f89 ?v1) ?v0))))
(assert (forall ((?v0 S5)) (= (f25 (f88 f89 f28) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (f25 (f88 f89 ?v0) f28) ?v0)))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f25 (f88 f89 ?v0) ?v1) f28) (and (= ?v0 f28) (= ?v1 f28)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f25 (f88 f89 ?v0) ?v1) ?v0) (= ?v1 f28))))
(assert (forall ((?v0 S5) (?v1 S5)) (let ((?v_0 (f88 f89 ?v0))) (= (f25 ?v_0 (f25 f26 ?v1)) (f25 f26 (f25 ?v_0 ?v1))))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f25 (f88 f89 (f25 f26 ?v0)) ?v1) (f25 f26 (f25 (f88 f89 ?v0) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f25 (f88 f89 (f25 f26 ?v0)) ?v1) (f25 (f88 f89 ?v0) (f25 f26 ?v1)))))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S21) (?v3 S3) (?v4 S21)) (let ((?v_0 (f46 ?v0))) (= (= (f44 (f45 ?v_0 (f90 (f91 f92 ?v1) ?v2)) (f90 (f91 f92 ?v3) ?v4)) f1) (or (and (= (f3 (f14 ?v0 ?v1) ?v3) f1) (= ?v4 ?v2)) (and (= ?v3 ?v1) (= (f44 (f45 ?v_0 ?v2) ?v4) f1)))))))
(assert (forall ((?v0 S43) (?v1 S51) (?v2 S44) (?v3 S51) (?v4 S44)) (let ((?v_0 (f69 ?v0))) (= (= (f68 (f84 ?v_0 (f94 (f95 f96 ?v1) ?v2)) (f94 (f95 f96 ?v3) ?v4)) f1) (or (and (= (f93 (f124 ?v0 ?v1) ?v3) f1) (= ?v4 ?v2)) (and (= ?v3 ?v1) (= (f68 (f84 ?v_0 ?v2) ?v4) f1)))))))
(assert (forall ((?v0 S40) (?v1 S44) (?v2 S41) (?v3 S44) (?v4 S41)) (let ((?v_0 (f65 ?v0))) (= (= (f64 (f83 ?v_0 (f97 (f98 f99 ?v1) ?v2)) (f97 (f98 f99 ?v3) ?v4)) f1) (or (and (= (f68 (f84 ?v0 ?v1) ?v3) f1) (= ?v4 ?v2)) (and (= ?v3 ?v1) (= (f64 (f83 ?v_0 ?v2) ?v4) f1)))))))
(assert (forall ((?v0 S56) (?v1 S5) (?v2 S57) (?v3 S5) (?v4 S57)) (let ((?v_0 (f102 ?v0))) (= (= (f125 (f126 ?v_0 (f103 (f104 f105 ?v1) ?v2)) (f103 (f104 f105 ?v3) ?v4)) f1) (or (and (= (f32 (f127 ?v0 ?v1) ?v3) f1) (= ?v4 ?v2)) (and (= ?v3 ?v1) (= (f125 (f126 ?v_0 ?v2) ?v4) f1)))))))
(assert (forall ((?v0 S61) (?v1 S62) (?v2 S63) (?v3 S62) (?v4 S63)) (let ((?v_0 (f108 ?v0))) (= (= (f128 (f129 ?v_0 (f109 (f110 f111 ?v1) ?v2)) (f109 (f110 f111 ?v3) ?v4)) f1) (or (and (= (f130 (f131 ?v0 ?v1) ?v3) f1) (= ?v4 ?v2)) (and (= ?v3 ?v1) (= (f128 (f129 ?v_0 ?v2) ?v4) f1)))))))
(assert (forall ((?v0 S27) (?v1 S21) (?v2 S39) (?v3 S21) (?v4 S39)) (let ((?v_0 (f62 ?v0))) (= (= (f61 (f82 ?v_0 (f121 (f122 f123 ?v1) ?v2)) (f121 (f122 f123 ?v3) ?v4)) f1) (or (and (= (f44 (f45 ?v0 ?v1) ?v3) f1) (= ?v4 ?v2)) (and (= ?v3 ?v1) (= (f61 (f82 ?v_0 ?v2) ?v4) f1)))))))
(assert (forall ((?v0 S36) (?v1 S41) (?v2 S37) (?v3 S41) (?v4 S37)) (let ((?v_0 (f58 ?v0))) (= (= (f57 (f79 ?v_0 (f118 (f119 f120 ?v1) ?v2)) (f118 (f119 f120 ?v3) ?v4)) f1) (or (and (= (f64 (f83 ?v0 ?v1) ?v3) f1) (= ?v4 ?v2)) (and (= ?v3 ?v1) (= (f57 (f79 ?v_0 ?v2) ?v4) f1)))))))
(assert (forall ((?v0 S5) (?v1 S5)) (let ((?v_0 (f25 f26 f28))) (= (= (f25 (f88 f89 ?v0) ?v1) ?v_0) (or (and (= ?v0 ?v_0) (= ?v1 f28)) (and (= ?v0 f28) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S5) (?v1 S5)) (let ((?v_0 (f25 f26 f28))) (= (= ?v_0 (f25 (f88 f89 ?v0) ?v1)) (or (and (= ?v0 ?v_0) (= ?v1 f28)) (and (= ?v0 f28) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f42 f43 (f10 (f16 f17 ?v0) ?v1)) (f25 (f88 f89 (f25 (f88 f89 (f42 f43 ?v0)) (f42 f43 ?v1))) (f25 f26 f28)))))
(assert (forall ((?v0 S5) (?v1 S57)) (let ((?v_0 (f134 f135 f89))) (= (f25 (f88 f89 ?v0) (f132 (f133 ?v_0 f28) ?v1)) (f132 (f133 ?v_0 ?v0) ?v1)))))
(assert (forall ((?v0 S62) (?v1 S63)) (let ((?v_0 (f141 f142 f138))) (= (f136 (f137 f138 ?v0) (f139 (f140 ?v_0 f143) ?v1)) (f139 (f140 ?v_0 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f42 f144 (f10 f11 ?v0)) (f25 (f88 f89 (f42 f144 ?v0)) (f25 f26 f28)))))
(assert (forall ((?v0 S10) (?v1 S3) (?v2 S3) (?v3 S21)) (let ((?v_0 (f36 f37 ?v0))) (= (f34 (f35 ?v_0 ?v1) (f90 (f91 f92 ?v2) ?v3)) (f34 (f35 ?v_0 (f10 (f16 ?v0 ?v1) ?v2)) ?v3)))))
(assert (forall ((?v0 S82) (?v1 S62) (?v2 S62) (?v3 S63)) (let ((?v_0 (f141 f142 ?v0))) (= (f139 (f140 ?v_0 ?v1) (f109 (f110 f111 ?v2) ?v3)) (f139 (f140 ?v_0 (f136 (f137 ?v0 ?v1) ?v2)) ?v3)))))
(assert (forall ((?v0 S48) (?v1 S5) (?v2 S5) (?v3 S57)) (let ((?v_0 (f134 f135 ?v0))) (= (f132 (f133 ?v_0 ?v1) (f103 (f104 f105 ?v2) ?v3)) (f132 (f133 ?v_0 (f25 (f88 ?v0 ?v1) ?v2)) ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f42 f144 (f10 (f16 f17 ?v0) ?v1)) (f25 (f88 f89 (f25 (f88 f89 (f42 f144 ?v0)) (f42 f144 ?v1))) (f25 f26 f28)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S57)) (let ((?v_1 (f134 f135 f89)) (?v_0 (f88 f89 ?v0))) (= (f132 (f133 ?v_1 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f132 (f133 ?v_1 ?v1) ?v2))))))
(assert (forall ((?v0 S62) (?v1 S62) (?v2 S63)) (let ((?v_1 (f141 f142 f138)) (?v_0 (f137 f138 ?v0))) (= (f139 (f140 ?v_1 (f136 ?v_0 ?v1)) ?v2) (f136 ?v_0 (f139 (f140 ?v_1 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S21) (?v2 S3) (?v3 S21)) (= (= (f90 (f91 f92 ?v0) ?v1) (f90 (f91 f92 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S51) (?v1 S44) (?v2 S51) (?v3 S44)) (= (= (f94 (f95 f96 ?v0) ?v1) (f94 (f95 f96 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S44) (?v1 S41) (?v2 S44) (?v3 S41)) (= (= (f97 (f98 f99 ?v0) ?v1) (f97 (f98 f99 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5) (?v1 S57) (?v2 S5) (?v3 S57)) (= (= (f103 (f104 f105 ?v0) ?v1) (f103 (f104 f105 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S62) (?v1 S63) (?v2 S62) (?v3 S63)) (= (= (f109 (f110 f111 ?v0) ?v1) (f109 (f110 f111 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S21) (?v1 S39) (?v2 S21) (?v3 S39)) (= (= (f121 (f122 f123 ?v0) ?v1) (f121 (f122 f123 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S41) (?v1 S37) (?v2 S41) (?v3 S37)) (= (= (f118 (f119 f120 ?v0) ?v1) (f118 (f119 f120 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S21)) (not (= (f90 (f91 f92 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S51) (?v1 S44)) (not (= (f94 (f95 f96 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S44) (?v1 S41)) (not (= (f97 (f98 f99 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S5) (?v1 S57)) (not (= (f103 (f104 f105 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S62) (?v1 S63)) (not (= (f109 (f110 f111 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S21) (?v1 S39)) (not (= (f121 (f122 f123 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S41) (?v1 S37)) (not (= (f118 (f119 f120 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S21) (?v1 S3)) (not (= ?v0 (f90 (f91 f92 ?v1) ?v0)))))
(assert (forall ((?v0 S44) (?v1 S51)) (not (= ?v0 (f94 (f95 f96 ?v1) ?v0)))))
(assert (forall ((?v0 S41) (?v1 S44)) (not (= ?v0 (f97 (f98 f99 ?v1) ?v0)))))
(assert (forall ((?v0 S57) (?v1 S5)) (not (= ?v0 (f103 (f104 f105 ?v1) ?v0)))))
(assert (forall ((?v0 S63) (?v1 S62)) (not (= ?v0 (f109 (f110 f111 ?v1) ?v0)))))
(assert (forall ((?v0 S39) (?v1 S21)) (not (= ?v0 (f121 (f122 f123 ?v1) ?v0)))))
(assert (forall ((?v0 S37) (?v1 S41)) (not (= ?v0 (f118 (f119 f120 ?v1) ?v0)))))
(check-sat)
(exit)