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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S2)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S4) S4)
(declare-fun f6 (S6 S4) S5)
(declare-fun f7 () S6)
(declare-fun f8 (S7 S2) S3)
(declare-fun f9 () S7)
(declare-fun f10 (S9 S8) S8)
(declare-fun f11 (S10 S8) S9)
(declare-fun f12 () S10)
(declare-fun f13 (S12 S11) S11)
(declare-fun f14 (S13 S11) S12)
(declare-fun f15 () S13)
(declare-fun f16 (S15 S14) S14)
(declare-fun f17 (S16 S14) S15)
(declare-fun f18 () S16)
(declare-fun f19 (S18 S17) S17)
(declare-fun f20 (S19 S17) S18)
(declare-fun f21 () S19)
(declare-fun f22 (S21 S20) S20)
(declare-fun f23 (S22 S20) S21)
(declare-fun f24 () S22)
(declare-fun f25 (S24 S23) S23)
(declare-fun f26 (S25 S23) S24)
(declare-fun f27 () S25)
(declare-fun f28 (S27 S26) S26)
(declare-fun f29 (S28 S26) S27)
(declare-fun f30 () S28)
(declare-fun f31 (S29 S4) S27)
(declare-fun f32 () S29)
(declare-fun f33 () S4)
(declare-fun f34 () S26)
(declare-fun f35 (S30 S26) S9)
(declare-fun f36 () S30)
(declare-fun f37 () S8)
(declare-fun f38 (S31 S2) S12)
(declare-fun f39 () S31)
(declare-fun f40 () S2)
(declare-fun f41 () S11)
(declare-fun f42 (S32 S23) S15)
(declare-fun f43 () S32)
(declare-fun f44 () S23)
(declare-fun f45 () S14)
(declare-fun f46 (S33 S20) S18)
(declare-fun f47 () S33)
(declare-fun f48 () S20)
(declare-fun f49 () S17)
(declare-fun f50 (S34 S35) S35)
(declare-fun f51 () S34)
(declare-fun f52 () S35)
(declare-fun f53 (S36 S37) S37)
(declare-fun f54 () S36)
(declare-fun f55 () S37)
(declare-fun f56 (S38 S36) S36)
(declare-fun f57 (S39 S17) S38)
(declare-fun f58 () S39)
(declare-fun f59 (S40 S34) S34)
(declare-fun f60 (S41 S14) S40)
(declare-fun f61 () S41)
(declare-fun f62 (S42 S11) S21)
(declare-fun f63 () S42)
(declare-fun f64 (S43 S8) S24)
(declare-fun f65 () S43)
(declare-fun f66 () S2)
(declare-fun f67 () S6)
(declare-fun f68 (S44 S2) S4)
(declare-fun f69 (S45 S4) S44)
(declare-fun f70 () S45)
(declare-fun f71 () S10)
(declare-fun f72 (S46 S2) S8)
(declare-fun f73 (S47 S8) S46)
(declare-fun f74 () S47)
(declare-fun f75 () S16)
(declare-fun f76 (S48 S2) S14)
(declare-fun f77 (S49 S14) S48)
(declare-fun f78 () S49)
(declare-fun f79 () S25)
(declare-fun f80 (S50 S2) S23)
(declare-fun f81 (S51 S23) S50)
(declare-fun f82 () S51)
(declare-fun f83 () S28)
(declare-fun f84 (S52 S2) S26)
(declare-fun f85 (S53 S26) S52)
(declare-fun f86 () S53)
(declare-fun f87 (S54 S26) S5)
(declare-fun f88 () S54)
(declare-fun f89 (S55 S8) S27)
(declare-fun f90 () S55)
(declare-fun f91 (S56 S11) S3)
(declare-fun f92 () S56)
(declare-fun f93 (S57 S14) S24)
(declare-fun f94 () S57)
(declare-fun f95 (S58 S17) S21)
(declare-fun f96 () S58)
(declare-fun f97 (S59 S35) S40)
(declare-fun f98 () S59)
(declare-fun f99 (S60 S37) S38)
(declare-fun f100 () S60)
(declare-fun f101 (S61 S36) S18)
(declare-fun f102 () S61)
(declare-fun f103 (S62 S34) S15)
(declare-fun f104 () S62)
(declare-fun f105 (S63 S20) S12)
(declare-fun f106 () S63)
(declare-fun f107 (S64 S23) S9)
(declare-fun f108 () S64)
(declare-fun f109 (S65 S34) S40)
(declare-fun f110 () S65)
(declare-fun f111 (S66 S26) S2)
(declare-fun f112 () S66)
(declare-fun f113 (S67 S23) S2)
(declare-fun f114 () S67)
(declare-fun f115 (S68 S20) S2)
(declare-fun f116 () S68)
(declare-fun f117 (S69 S34) S2)
(declare-fun f118 () S69)
(declare-fun f119 (S70 S36) S2)
(declare-fun f120 () S70)
(declare-fun f121 (S71 S17) S2)
(declare-fun f122 () S71)
(declare-fun f123 (S72 S14) S2)
(declare-fun f124 () S72)
(declare-fun f125 (S73 S11) S2)
(declare-fun f126 () S73)
(declare-fun f127 (S74 S8) S2)
(declare-fun f128 () S74)
(declare-fun f129 () S65)
(declare-fun f130 (S75 S36) S38)
(declare-fun f131 () S75)
(declare-fun f132 () S26)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f4 ?v0) (f3 f4 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (= (f5 ?v_0 ?v1) (f5 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (= (f3 ?v_0 ?v1) (f3 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f11 f12 ?v0))) (= (= (f10 ?v_0 ?v1) (f10 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f14 f15 ?v0))) (= (= (f13 ?v_0 ?v1) (f13 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f17 f18 ?v0))) (= (= (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17)) (let ((?v_0 (f20 f21 ?v0))) (= (= (f19 ?v_0 ?v1) (f19 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S20)) (let ((?v_0 (f23 f24 ?v0))) (= (= (f22 ?v_0 ?v1) (f22 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f26 f27 ?v0))) (= (= (f25 ?v_0 ?v1) (f25 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f29 f30 ?v0))) (= (= (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (= (f28 (f31 f32 f33) f34) f34))
(assert (= (f10 (f35 f36 f34) f37) f37))
(assert (= (f13 (f38 f39 f40) f41) f41))
(assert (= (f16 (f42 f43 f44) f45) f45))
(assert (= (f19 (f46 f47 f48) f49) f49))
(assert (= (f50 f51 f52) f52))
(assert (= (f53 f54 f55) f55))
(assert (= (f56 (f57 f58 f49) f54) f54))
(assert (= (f59 (f60 f61 f45) f51) f51))
(assert (= (f22 (f62 f63 f41) f48) f48))
(assert (= (f25 (f64 f65 f37) f44) f44))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f11 f12 ?v0))) (= (f10 (f11 f12 (f10 ?v_0 ?v1)) ?v2) (f10 ?v_0 (f10 (f11 f12 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f14 f15 ?v0))) (= (f13 (f14 f15 (f13 ?v_0 ?v1)) ?v2) (f13 ?v_0 (f13 (f14 f15 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f17 f18 ?v0))) (= (f16 (f17 f18 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f17 f18 ?v1) ?v2))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f20 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S20)) (let ((?v_0 (f23 f24 ?v0))) (= (f22 (f23 f24 (f22 ?v_0 ?v1)) ?v2) (f22 ?v_0 (f22 (f23 f24 ?v1) ?v2))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f26 f27 ?v0))) (= (f25 (f26 f27 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f26 f27 ?v1) ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f29 f30 ?v0))) (= (f28 (f29 f30 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f29 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f3 (f8 f9 ?v0) f66))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f3 (f8 f9 ?v0) ?v1) (f3 (f8 f9 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f68 (f69 f70 ?v0) ?v1))) (= (f5 (f6 f67 ?v_0) ?v0) (f5 (f6 f67 ?v0) ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S2)) (let ((?v_0 (f72 (f73 f74 ?v0) ?v1))) (= (f10 (f11 f71 ?v_0) ?v0) (f10 (f11 f71 ?v0) ?v_0)))))
(assert (forall ((?v0 S14) (?v1 S2)) (let ((?v_0 (f76 (f77 f78 ?v0) ?v1))) (= (f16 (f17 f75 ?v_0) ?v0) (f16 (f17 f75 ?v0) ?v_0)))))
(assert (forall ((?v0 S23) (?v1 S2)) (let ((?v_0 (f80 (f81 f82 ?v0) ?v1))) (= (f25 (f26 f79 ?v_0) ?v0) (f25 (f26 f79 ?v0) ?v_0)))))
(assert (forall ((?v0 S26) (?v1 S2)) (let ((?v_0 (f84 (f85 f86 ?v0) ?v1))) (= (f28 (f29 f83 ?v_0) ?v0) (f28 (f29 f83 ?v0) ?v_0)))))
(assert (forall ((?v0 S4)) (= (f5 (f87 f88 f34) ?v0) f33)))
(assert (forall ((?v0 S26)) (= (f28 (f89 f90 f37) ?v0) f34)))
(assert (forall ((?v0 S2)) (= (f3 (f91 f92 f41) ?v0) f40)))
(assert (forall ((?v0 S23)) (= (f25 (f93 f94 f45) ?v0) f44)))
(assert (forall ((?v0 S20)) (= (f22 (f95 f96 f49) ?v0) f48)))
(assert (forall ((?v0 S34)) (= (f59 (f97 f98 f52) ?v0) f51)))
(assert (forall ((?v0 S36)) (= (f56 (f99 f100 f55) ?v0) f54)))
(assert (forall ((?v0 S17)) (= (f19 (f101 f102 f54) ?v0) f49)))
(assert (forall ((?v0 S14)) (= (f16 (f103 f104 f51) ?v0) f45)))
(assert (forall ((?v0 S11)) (= (f13 (f105 f106 f48) ?v0) f41)))
(assert (forall ((?v0 S8)) (= (f10 (f107 f108 f44) ?v0) f37)))
(assert (forall ((?v0 S26) (?v1 S26)) (= (= (f28 (f29 f83 ?v0) ?v1) f34) (or (= ?v0 f34) (= ?v1 f34)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f5 (f6 f67 ?v0) ?v1) f33) (or (= ?v0 f33) (= ?v1 f33)))))
(assert (forall ((?v0 S23) (?v1 S23)) (= (= (f25 (f26 f79 ?v0) ?v1) f44) (or (= ?v0 f44) (= ?v1 f44)))))
(assert (forall ((?v0 S34) (?v1 S34)) (= (= (f59 (f109 f110 ?v0) ?v1) f51) (or (= ?v0 f51) (= ?v1 f51)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f16 (f17 f75 ?v0) ?v1) f45) (or (= ?v0 f45) (= ?v1 f45)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f10 (f11 f71 ?v0) ?v1) f37) (or (= ?v0 f37) (= ?v1 f37)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f69 f70 ?v0))) (= (f68 ?v_0 (f3 (f8 f9 ?v1) ?v2)) (f5 (f6 f67 (f68 ?v_0 ?v1)) (f68 ?v_0 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (let ((?v_0 (f73 f74 ?v0))) (= (f72 ?v_0 (f3 (f8 f9 ?v1) ?v2)) (f10 (f11 f71 (f72 ?v_0 ?v1)) (f72 ?v_0 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S2) (?v2 S2)) (let ((?v_0 (f77 f78 ?v0))) (= (f76 ?v_0 (f3 (f8 f9 ?v1) ?v2)) (f16 (f17 f75 (f76 ?v_0 ?v1)) (f76 ?v_0 ?v2))))))
(assert (forall ((?v0 S23) (?v1 S2) (?v2 S2)) (let ((?v_0 (f81 f82 ?v0))) (= (f80 ?v_0 (f3 (f8 f9 ?v1) ?v2)) (f25 (f26 f79 (f80 ?v_0 ?v1)) (f80 ?v_0 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S2) (?v2 S2)) (let ((?v_0 (f85 f86 ?v0))) (= (f84 ?v_0 (f3 (f8 f9 ?v1) ?v2)) (f28 (f29 f83 (f84 ?v_0 ?v1)) (f84 ?v_0 ?v2))))))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f3 (f8 f9 f66) ?v0))))
(assert (= (f111 f112 f34) f40))
(assert (= (f113 f114 f44) f40))
(assert (= (f115 f116 f48) f40))
(assert (= (f117 f118 f51) f40))
(assert (= (f119 f120 f54) f40))
(assert (= (f121 f122 f49) f40))
(assert (= (f123 f124 f45) f40))
(assert (= (f125 f126 f41) f40))
(assert (= (f127 f128 f37) f40))
(assert (= f66 (f3 f4 f40)))
(assert (forall ((?v0 S4)) (= (f68 (f69 f70 ?v0) f66) ?v0)))
(assert (forall ((?v0 S26)) (= (f84 (f85 f86 ?v0) f66) ?v0)))
(assert (forall ((?v0 S23)) (= (f80 (f81 f82 ?v0) f66) ?v0)))
(assert (forall ((?v0 S8)) (= (f72 (f73 f74 ?v0) f66) ?v0)))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f5 (f6 f67 ?v0) ?v1) (f5 (f6 f67 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f10 (f11 f71 ?v0) ?v1) (f10 (f11 f71 ?v1) ?v0))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f16 (f17 f75 ?v0) ?v1) (f16 (f17 f75 ?v1) ?v0))))
(assert (forall ((?v0 S23) (?v1 S23)) (= (f25 (f26 f79 ?v0) ?v1) (f25 (f26 f79 ?v1) ?v0))))
(assert (forall ((?v0 S26) (?v1 S26)) (= (f28 (f29 f83 ?v0) ?v1) (f28 (f29 f83 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f5 (f6 f7 ?v0) ?v1) (f5 (f6 f7 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f3 (f8 f9 ?v0) ?v1) (f3 (f8 f9 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f10 (f11 f12 ?v0) ?v1) (f10 (f11 f12 ?v1) ?v0))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f13 (f14 f15 ?v0) ?v1) (f13 (f14 f15 ?v1) ?v0))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f16 (f17 f18 ?v0) ?v1) (f16 (f17 f18 ?v1) ?v0))))
(assert (forall ((?v0 S17) (?v1 S17)) (= (f19 (f20 f21 ?v0) ?v1) (f19 (f20 f21 ?v1) ?v0))))
(assert (forall ((?v0 S20) (?v1 S20)) (= (f22 (f23 f24 ?v0) ?v1) (f22 (f23 f24 ?v1) ?v0))))
(assert (forall ((?v0 S23) (?v1 S23)) (= (f25 (f26 f27 ?v0) ?v1) (f25 (f26 f27 ?v1) ?v0))))
(assert (forall ((?v0 S26) (?v1 S26)) (= (f28 (f29 f30 ?v0) ?v1) (f28 (f29 f30 ?v1) ?v0))))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 ?v0) f33) ?v0)))
(assert (forall ((?v0 S2)) (= (f3 (f8 f9 ?v0) f40) ?v0)))
(assert (forall ((?v0 S26)) (= (f28 (f29 f30 ?v0) f34) ?v0)))
(assert (forall ((?v0 S23)) (= (f25 (f26 f27 ?v0) f44) ?v0)))
(assert (forall ((?v0 S20)) (= (f22 (f23 f24 ?v0) f48) ?v0)))
(assert (forall ((?v0 S34)) (= (f59 (f109 f129 ?v0) f51) ?v0)))
(assert (forall ((?v0 S36)) (= (f56 (f130 f131 ?v0) f54) ?v0)))
(assert (forall ((?v0 S17)) (= (f19 (f20 f21 ?v0) f49) ?v0)))
(assert (forall ((?v0 S14)) (= (f16 (f17 f18 ?v0) f45) ?v0)))
(assert (forall ((?v0 S11)) (= (f13 (f14 f15 ?v0) f41) ?v0)))
(assert (forall ((?v0 S8)) (= (f10 (f11 f12 ?v0) f37) ?v0)))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f67 ?v0))) (= (f5 (f6 f67 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f67 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f11 f71 ?v0))) (= (f10 (f11 f71 (f10 ?v_0 ?v1)) ?v2) (f10 ?v_0 (f10 (f11 f71 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f17 f75 ?v0))) (= (f16 (f17 f75 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f17 f75 ?v1) ?v2))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f26 f79 ?v0))) (= (f25 (f26 f79 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f26 f79 ?v1) ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f29 f83 ?v0))) (= (f28 (f29 f83 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f29 f83 ?v1) ?v2))))))
(assert (not (forall ((?v0 S2) (?v1 S4) (?v2 S4) (?v3 S26)) (=> (not (= ?v1 f33)) (=> (not (= (f5 (f6 f7 ?v2) (f5 (f6 f67 ?v1) (f5 (f87 f88 ?v3) ?v1))) f33)) (=> (not (= ?v2 f33)) (=> (= (f3 (f8 f9 (ite (= ?v3 f34) f40 (f3 f4 (f111 f112 ?v3)))) ?v0) (f111 f112 f132)) (=> (forall ((?v4 S4)) (= (f5 (f87 f88 f132) ?v4) (f5 (f6 f67 (f68 (f69 f70 ?v4) ?v0)) (f5 (f6 f7 ?v2) (f5 (f6 f67 ?v4) (f5 (f87 f88 ?v3) ?v4)))))) (=> (not (= f132 f34)) (exists ((?v4 S4)) (and (not (= ?v4 f33)) (exists ((?v5 S26)) (let ((?v_2 (f111 f112 f132)) (?v_0 (= ?v5 f34)) (?v_1 (f3 (f8 f9 ?v0) f66))) (and (=> ?v_0 (and (= ?v_1 (f3 f4 ?v_2)) (forall ((?v6 S4)) (let ((?v_3 (f6 f67 ?v6)) (?v_4 (f69 f70 ?v6))) (= (f5 ?v_3 (f5 (f6 f67 (f68 ?v_4 ?v0)) (f5 (f6 f7 ?v2) (f5 ?v_3 (f5 (f87 f88 ?v3) ?v6))))) (f5 (f6 f67 (f68 ?v_4 ?v_1)) ?v4)))))) (=> (not ?v_0) (and (= (f3 (f8 f9 (f111 f112 ?v5)) ?v_1) ?v_2) (forall ((?v6 S4)) (let ((?v_5 (f6 f67 ?v6)) (?v_6 (f69 f70 ?v6))) (= (f5 ?v_5 (f5 (f6 f67 (f68 ?v_6 ?v0)) (f5 (f6 f7 ?v2) (f5 ?v_5 (f5 (f87 f88 ?v3) ?v6))))) (f5 (f6 f67 (f68 ?v_6 ?v_1)) (f5 (f6 f7 ?v4) (f5 ?v_5 (f5 (f87 f88 ?v5) ?v6)))))))))))))))))))))))
(check-sat)
(exit)
