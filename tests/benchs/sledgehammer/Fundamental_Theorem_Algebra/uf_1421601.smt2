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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S5) S2)
(declare-fun f5 () S4)
(declare-fun f6 () S5)
(declare-fun f7 () S3)
(declare-fun f8 (S6 S3) S2)
(declare-fun f9 () S6)
(declare-fun f10 () S5)
(declare-fun f11 () S3)
(declare-fun f12 (S7 S3) S1)
(declare-fun f13 (S3) S7)
(declare-fun f14 () S3)
(declare-fun f15 () S8)
(declare-fun f16 (S9 S8) S8)
(declare-fun f17 (S10 S3) S9)
(declare-fun f18 () S10)
(declare-fun f19 () S3)
(declare-fun f20 () S8)
(declare-fun f21 () S11)
(declare-fun f22 (S12 S11) S11)
(declare-fun f23 (S13 S14) S12)
(declare-fun f24 () S13)
(declare-fun f25 () S14)
(declare-fun f26 () S11)
(declare-fun f27 () S15)
(declare-fun f28 (S16 S15) S15)
(declare-fun f29 (S17 S18) S16)
(declare-fun f30 () S17)
(declare-fun f31 () S18)
(declare-fun f32 () S15)
(declare-fun f33 () S19)
(declare-fun f34 (S20 S19) S19)
(declare-fun f35 (S21 S11) S20)
(declare-fun f36 () S21)
(declare-fun f37 () S19)
(declare-fun f38 () S22)
(declare-fun f39 (S23 S22) S22)
(declare-fun f40 (S24 S8) S23)
(declare-fun f41 () S24)
(declare-fun f42 () S22)
(declare-fun f43 (S25 S18) S18)
(declare-fun f44 (S26 S27) S25)
(declare-fun f45 () S26)
(declare-fun f46 () S27)
(declare-fun f47 () S18)
(declare-fun f48 () S27)
(declare-fun f49 () S14)
(declare-fun f50 (S28 S11) S12)
(declare-fun f51 () S28)
(declare-fun f52 (S29 S18) S25)
(declare-fun f53 () S29)
(declare-fun f54 (S30 S8) S9)
(declare-fun f55 () S30)
(declare-fun f56 (S31 S14) S14)
(declare-fun f57 (S32 S14) S31)
(declare-fun f58 () S32)
(declare-fun f59 (S33 S5) S5)
(declare-fun f60 (S34 S5) S33)
(declare-fun f61 () S34)
(declare-fun f62 (S35 S27) S27)
(declare-fun f63 (S36 S27) S35)
(declare-fun f64 () S36)
(declare-fun f65 (S37 S18) S1)
(declare-fun f66 (S18) S37)
(declare-fun f67 (S38 S8) S1)
(declare-fun f68 (S8) S38)
(declare-fun f69 (S39 S11) S1)
(declare-fun f70 (S11) S39)
(declare-fun f71 (S5 S5) S1)
(declare-fun f72 (S27 S27) S1)
(declare-fun f73 (S14 S14) S1)
(declare-fun f74 (S40 S3) S33)
(declare-fun f75 () S40)
(declare-fun f76 (S41 S11) S31)
(declare-fun f77 () S41)
(declare-fun f78 (S42 S18) S35)
(declare-fun f79 () S42)
(declare-fun f80 (S43 S8) S2)
(declare-fun f81 () S43)
(declare-fun f82 (S44 S3) S14)
(declare-fun f83 (S45 S5) S44)
(declare-fun f84 () S45)
(declare-fun f85 (S46 S18) S14)
(declare-fun f86 (S47 S27) S46)
(declare-fun f87 () S47)
(declare-fun f88 (S48 S8) S14)
(declare-fun f89 (S49 S3) S48)
(declare-fun f90 () S49)
(declare-fun f91 () S33)
(declare-fun f92 () S35)
(declare-fun f93 () S2)
(declare-fun f94 (S50 S5) S3)
(declare-fun f95 (S51 S3) S50)
(declare-fun f96 () S51)
(declare-fun f97 () S51)
(declare-fun f98 (S33) S1)
(declare-fun f99 () S6)
(declare-fun f100 () S29)
(declare-fun f101 (S52 S27) S18)
(declare-fun f102 (S53 S18) S52)
(declare-fun f103 () S53)
(declare-fun f104 (S54 S14) S3)
(declare-fun f105 (S55 S3) S54)
(declare-fun f106 () S55)
(declare-fun f107 (S56 S14) S18)
(declare-fun f108 (S57 S18) S56)
(declare-fun f109 () S57)
(declare-fun f110 () S44)
(declare-fun f111 (S58 S14) S27)
(declare-fun f112 (S59 S18) S58)
(declare-fun f113 () S59)
(declare-fun f114 (S60 S14) S5)
(declare-fun f115 (S61 S3) S60)
(declare-fun f116 () S61)
(declare-fun f117 () S41)
(declare-fun f118 (S62 S8) S54)
(declare-fun f119 () S62)
(declare-fun f120 (S63 S5) S54)
(declare-fun f121 () S63)
(declare-fun f122 () S44)
(declare-fun f123 () S34)
(declare-fun f124 (S64 S5) S60)
(declare-fun f125 () S64)
(declare-fun f126 (S65 S14) S11)
(declare-fun f127 (S66 S14) S65)
(declare-fun f128 () S66)
(declare-fun f129 (S67 S27) S56)
(declare-fun f130 () S67)
(declare-fun f131 (S68 S14) S8)
(declare-fun f132 (S69 S3) S68)
(declare-fun f133 () S69)
(declare-fun f134 (S70 S11) S14)
(declare-fun f135 () S70)
(declare-fun f136 () S46)
(declare-fun f137 () S48)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f4 f5 f6))) (not (= (f3 ?v_0 f7) (f3 (f8 f9 f7) (f3 ?v_0 (f3 (f4 f5 f10) f11)))))))
(assert (= (f12 (f13 f14) f7) f1))
(assert (= f15 (f16 (f17 f18 f19) f20)))
(assert (= f21 (f22 (f23 f24 f25) f26)))
(assert (= f27 (f28 (f29 f30 f31) f32)))
(assert (= f33 (f34 (f35 f36 f21) f37)))
(assert (= f38 (f39 (f40 f41 f15) f42)))
(assert (= f31 (f43 (f44 f45 f46) f47)))
(assert (= f19 (f3 (f4 f5 f10) f11)))
(assert (= (f34 (f35 f36 f26) f37) f37))
(assert (= (f28 (f29 f30 f47) f32) f32))
(assert (= (f39 (f40 f41 f20) f42) f42))
(assert (= (f16 (f17 f18 f11) f20) f20))
(assert (= (f43 (f44 f45 f48) f47) f47))
(assert (= (f22 (f23 f24 f49) f26) f26))
(assert (= (f3 (f4 f5 f6) f11) f11))
(assert (forall ((?v0 S11) (?v1 S19)) (= (= (f34 (f35 f36 ?v0) ?v1) f37) (and (= ?v0 f26) (= ?v1 f37)))))
(assert (forall ((?v0 S18) (?v1 S15)) (= (= (f28 (f29 f30 ?v0) ?v1) f32) (and (= ?v0 f47) (= ?v1 f32)))))
(assert (forall ((?v0 S8) (?v1 S22)) (= (= (f39 (f40 f41 ?v0) ?v1) f42) (and (= ?v0 f20) (= ?v1 f42)))))
(assert (forall ((?v0 S3) (?v1 S8)) (= (= (f16 (f17 f18 ?v0) ?v1) f20) (and (= ?v0 f11) (= ?v1 f20)))))
(assert (forall ((?v0 S27) (?v1 S18)) (= (= (f43 (f44 f45 ?v0) ?v1) f47) (and (= ?v0 f48) (= ?v1 f47)))))
(assert (forall ((?v0 S14) (?v1 S11)) (= (= (f22 (f23 f24 ?v0) ?v1) f26) (and (= ?v0 f49) (= ?v1 f26)))))
(assert (forall ((?v0 S5) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f11) (and (= ?v0 f6) (= ?v1 f11)))))
(assert (forall ((?v0 S11)) (= (f22 (f50 f51 f26) ?v0) f26)))
(assert (forall ((?v0 S18)) (= (f43 (f52 f53 f47) ?v0) f47)))
(assert (forall ((?v0 S8)) (= (f16 (f54 f55 f20) ?v0) f20)))
(assert (forall ((?v0 S3)) (= (f3 (f8 f9 f11) ?v0) f11)))
(assert (forall ((?v0 S11)) (= (f22 (f50 f51 ?v0) f26) f26)))
(assert (forall ((?v0 S18)) (= (f43 (f52 f53 ?v0) f47) f47)))
(assert (forall ((?v0 S8)) (= (f16 (f54 f55 ?v0) f20) f20)))
(assert (forall ((?v0 S3)) (= (f3 (f8 f9 ?v0) f11) f11)))
(assert (forall ((?v0 S18)) (= (f43 (f52 f53 f31) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f22 (f50 f51 f21) ?v0) ?v0)))
(assert (forall ((?v0 S14)) (= (f56 (f57 f58 f25) ?v0) ?v0)))
(assert (forall ((?v0 S8)) (= (f16 (f54 f55 f15) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f8 f9 f19) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 f10) ?v0) ?v0)))
(assert (forall ((?v0 S27)) (= (f62 (f63 f64 f46) ?v0) ?v0)))
(assert (forall ((?v0 S18)) (= (f43 (f52 f53 f31) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f22 (f50 f51 f21) ?v0) ?v0)))
(assert (forall ((?v0 S14)) (= (f56 (f57 f58 f25) ?v0) ?v0)))
(assert (forall ((?v0 S8)) (= (f16 (f54 f55 f15) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f8 f9 f19) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 f10) ?v0) ?v0)))
(assert (forall ((?v0 S27)) (= (f62 (f63 f64 f46) ?v0) ?v0)))
(assert (forall ((?v0 S18)) (= (f43 (f52 f53 f31) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f22 (f50 f51 f21) ?v0) ?v0)))
(assert (forall ((?v0 S14)) (= (f56 (f57 f58 f25) ?v0) ?v0)))
(assert (forall ((?v0 S8)) (= (f16 (f54 f55 f15) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f8 f9 f19) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 f10) ?v0) ?v0)))
(assert (forall ((?v0 S27)) (= (f62 (f63 f64 f46) ?v0) ?v0)))
(assert (forall ((?v0 S18)) (= (f43 (f52 f53 ?v0) f31) ?v0)))
(assert (forall ((?v0 S11)) (= (f22 (f50 f51 ?v0) f21) ?v0)))
(assert (forall ((?v0 S14)) (= (f56 (f57 f58 ?v0) f25) ?v0)))
(assert (forall ((?v0 S8)) (= (f16 (f54 f55 ?v0) f15) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f8 f9 ?v0) f19) ?v0)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 ?v0) f10) ?v0)))
(assert (forall ((?v0 S27)) (= (f62 (f63 f64 ?v0) f46) ?v0)))
(assert (forall ((?v0 S18)) (= (f43 (f52 f53 ?v0) f31) ?v0)))
(assert (forall ((?v0 S11)) (= (f22 (f50 f51 ?v0) f21) ?v0)))
(assert (forall ((?v0 S14)) (= (f56 (f57 f58 ?v0) f25) ?v0)))
(assert (forall ((?v0 S8)) (= (f16 (f54 f55 ?v0) f15) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f8 f9 ?v0) f19) ?v0)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 ?v0) f10) ?v0)))
(assert (forall ((?v0 S27)) (= (f62 (f63 f64 ?v0) f46) ?v0)))
(assert (forall ((?v0 S18)) (= (f43 (f52 f53 ?v0) f31) ?v0)))
(assert (forall ((?v0 S11)) (= (f22 (f50 f51 ?v0) f21) ?v0)))
(assert (forall ((?v0 S14)) (= (f56 (f57 f58 ?v0) f25) ?v0)))
(assert (forall ((?v0 S8)) (= (f16 (f54 f55 ?v0) f15) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f8 f9 ?v0) f19) ?v0)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 ?v0) f10) ?v0)))
(assert (forall ((?v0 S27)) (= (f62 (f63 f64 ?v0) f46) ?v0)))
(assert (forall ((?v0 S11)) (= (= f26 ?v0) (= ?v0 f26))))
(assert (forall ((?v0 S18)) (= (= f47 ?v0) (= ?v0 f47))))
(assert (forall ((?v0 S8)) (= (= f20 ?v0) (= ?v0 f20))))
(assert (forall ((?v0 S5)) (= (= f6 ?v0) (= ?v0 f6))))
(assert (forall ((?v0 S3)) (= (= f11 ?v0) (= ?v0 f11))))
(assert (forall ((?v0 S27)) (= (= f48 ?v0) (= ?v0 f48))))
(assert (forall ((?v0 S14)) (= (= f49 ?v0) (= ?v0 f49))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18) (?v3 S18)) (let ((?v_0 (f52 f53 ?v0))) (= (f43 (f52 f53 (f43 ?v_0 ?v1)) (f43 (f52 f53 ?v2) ?v3)) (f43 (f52 f53 (f43 ?v_0 ?v2)) (f43 (f52 f53 ?v1) ?v3))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S27) (?v3 S27)) (let ((?v_0 (f63 f64 ?v0))) (= (f62 (f63 f64 (f62 ?v_0 ?v1)) (f62 (f63 f64 ?v2) ?v3)) (f62 (f63 f64 (f62 ?v_0 ?v2)) (f62 (f63 f64 ?v1) ?v3))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (let ((?v_0 (f60 f61 ?v0))) (= (f59 (f60 f61 (f59 ?v_0 ?v1)) (f59 (f60 f61 ?v2) ?v3)) (f59 (f60 f61 (f59 ?v_0 ?v2)) (f59 (f60 f61 ?v1) ?v3))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f54 f55 ?v0))) (= (f16 (f54 f55 (f16 ?v_0 ?v1)) (f16 (f54 f55 ?v2) ?v3)) (f16 (f54 f55 (f16 ?v_0 ?v2)) (f16 (f54 f55 ?v1) ?v3))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (let ((?v_0 (f57 f58 ?v0))) (= (f56 (f57 f58 (f56 ?v_0 ?v1)) (f56 (f57 f58 ?v2) ?v3)) (f56 (f57 f58 (f56 ?v_0 ?v2)) (f56 (f57 f58 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f3 (f8 f9 (f3 ?v_0 ?v1)) (f3 (f8 f9 ?v2) ?v3)) (f3 (f8 f9 (f3 ?v_0 ?v2)) (f3 (f8 f9 ?v1) ?v3))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18) (?v3 S18)) (let ((?v_1 (f52 f53 (f43 (f52 f53 ?v0) ?v1))) (?v_0 (f52 f53 ?v2))) (= (f43 ?v_1 (f43 ?v_0 ?v3)) (f43 ?v_0 (f43 ?v_1 ?v3))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S27) (?v3 S27)) (let ((?v_1 (f63 f64 (f62 (f63 f64 ?v0) ?v1))) (?v_0 (f63 f64 ?v2))) (= (f62 ?v_1 (f62 ?v_0 ?v3)) (f62 ?v_0 (f62 ?v_1 ?v3))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (let ((?v_1 (f60 f61 (f59 (f60 f61 ?v0) ?v1))) (?v_0 (f60 f61 ?v2))) (= (f59 ?v_1 (f59 ?v_0 ?v3)) (f59 ?v_0 (f59 ?v_1 ?v3))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_1 (f54 f55 (f16 (f54 f55 ?v0) ?v1))) (?v_0 (f54 f55 ?v2))) (= (f16 ?v_1 (f16 ?v_0 ?v3)) (f16 ?v_0 (f16 ?v_1 ?v3))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (let ((?v_1 (f57 f58 (f56 (f57 f58 ?v0) ?v1))) (?v_0 (f57 f58 ?v2))) (= (f56 ?v_1 (f56 ?v_0 ?v3)) (f56 ?v_0 (f56 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f8 f9 (f3 (f8 f9 ?v0) ?v1))) (?v_0 (f8 f9 ?v2))) (= (f3 ?v_1 (f3 ?v_0 ?v3)) (f3 ?v_0 (f3 ?v_1 ?v3))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18) (?v3 S18)) (let ((?v_0 (f52 f53 ?v0)) (?v_1 (f43 (f52 f53 ?v2) ?v3))) (= (f43 (f52 f53 (f43 ?v_0 ?v1)) ?v_1) (f43 ?v_0 (f43 (f52 f53 ?v1) ?v_1))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S27) (?v3 S27)) (let ((?v_0 (f63 f64 ?v0)) (?v_1 (f62 (f63 f64 ?v2) ?v3))) (= (f62 (f63 f64 (f62 ?v_0 ?v1)) ?v_1) (f62 ?v_0 (f62 (f63 f64 ?v1) ?v_1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (let ((?v_0 (f60 f61 ?v0)) (?v_1 (f59 (f60 f61 ?v2) ?v3))) (= (f59 (f60 f61 (f59 ?v_0 ?v1)) ?v_1) (f59 ?v_0 (f59 (f60 f61 ?v1) ?v_1))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f54 f55 ?v0)) (?v_1 (f16 (f54 f55 ?v2) ?v3))) (= (f16 (f54 f55 (f16 ?v_0 ?v1)) ?v_1) (f16 ?v_0 (f16 (f54 f55 ?v1) ?v_1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (let ((?v_0 (f57 f58 ?v0)) (?v_1 (f56 (f57 f58 ?v2) ?v3))) (= (f56 (f57 f58 (f56 ?v_0 ?v1)) ?v_1) (f56 ?v_0 (f56 (f57 f58 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f8 f9 ?v0)) (?v_1 (f3 (f8 f9 ?v2) ?v3))) (= (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v_1) (f3 ?v_0 (f3 (f8 f9 ?v1) ?v_1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f52 f53 ?v0))) (= (f43 (f52 f53 (f43 ?v_0 ?v1)) ?v2) (f43 (f52 f53 (f43 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S27)) (let ((?v_0 (f63 f64 ?v0))) (= (f62 (f63 f64 (f62 ?v_0 ?v1)) ?v2) (f62 (f63 f64 (f62 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f60 f61 ?v0))) (= (f59 (f60 f61 (f59 ?v_0 ?v1)) ?v2) (f59 (f60 f61 (f59 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f54 f55 ?v0))) (= (f16 (f54 f55 (f16 ?v_0 ?v1)) ?v2) (f16 (f54 f55 (f16 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f57 f58 ?v0))) (= (f56 (f57 f58 (f56 ?v_0 ?v1)) ?v2) (f56 (f57 f58 (f56 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v2) (f3 (f8 f9 (f3 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f52 f53 ?v0))) (= (f43 (f52 f53 (f43 ?v_0 ?v1)) ?v2) (f43 ?v_0 (f43 (f52 f53 ?v1) ?v2))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S27)) (let ((?v_0 (f63 f64 ?v0))) (= (f62 (f63 f64 (f62 ?v_0 ?v1)) ?v2) (f62 ?v_0 (f62 (f63 f64 ?v1) ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f60 f61 ?v0))) (= (f59 (f60 f61 (f59 ?v_0 ?v1)) ?v2) (f59 ?v_0 (f59 (f60 f61 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f54 f55 ?v0))) (= (f16 (f54 f55 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f54 f55 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f57 f58 ?v0))) (= (f56 (f57 f58 (f56 ?v_0 ?v1)) ?v2) (f56 ?v_0 (f56 (f57 f58 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f52 f53 ?v0))) (= (f43 (f52 f53 (f43 ?v_0 ?v1)) ?v2) (f43 ?v_0 (f43 (f52 f53 ?v1) ?v2))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S27)) (let ((?v_0 (f63 f64 ?v0))) (= (f62 (f63 f64 (f62 ?v_0 ?v1)) ?v2) (f62 ?v_0 (f62 (f63 f64 ?v1) ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f60 f61 ?v0))) (= (f59 (f60 f61 (f59 ?v_0 ?v1)) ?v2) (f59 ?v_0 (f59 (f60 f61 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f54 f55 ?v0))) (= (f16 (f54 f55 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f54 f55 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f57 f58 ?v0))) (= (f56 (f57 f58 (f56 ?v_0 ?v1)) ?v2) (f56 ?v_0 (f56 (f57 f58 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f52 f53 ?v0))) (= (f43 ?v_0 (f43 (f52 f53 ?v1) ?v2)) (f43 (f52 f53 (f43 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S27)) (let ((?v_0 (f63 f64 ?v0))) (= (f62 ?v_0 (f62 (f63 f64 ?v1) ?v2)) (f62 (f63 f64 (f62 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f60 f61 ?v0))) (= (f59 ?v_0 (f59 (f60 f61 ?v1) ?v2)) (f59 (f60 f61 (f59 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f54 f55 ?v0))) (= (f16 ?v_0 (f16 (f54 f55 ?v1) ?v2)) (f16 (f54 f55 (f16 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f57 f58 ?v0))) (= (f56 ?v_0 (f56 (f57 f58 ?v1) ?v2)) (f56 (f57 f58 (f56 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f3 ?v_0 (f3 (f8 f9 ?v1) ?v2)) (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_1 (f52 f53 ?v0)) (?v_0 (f52 f53 ?v1))) (= (f43 ?v_1 (f43 ?v_0 ?v2)) (f43 ?v_0 (f43 ?v_1 ?v2))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S27)) (let ((?v_1 (f63 f64 ?v0)) (?v_0 (f63 f64 ?v1))) (= (f62 ?v_1 (f62 ?v_0 ?v2)) (f62 ?v_0 (f62 ?v_1 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_1 (f60 f61 ?v0)) (?v_0 (f60 f61 ?v1))) (= (f59 ?v_1 (f59 ?v_0 ?v2)) (f59 ?v_0 (f59 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f54 f55 ?v0)) (?v_0 (f54 f55 ?v1))) (= (f16 ?v_1 (f16 ?v_0 ?v2)) (f16 ?v_0 (f16 ?v_1 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_1 (f57 f58 ?v0)) (?v_0 (f57 f58 ?v1))) (= (f56 ?v_1 (f56 ?v_0 ?v2)) (f56 ?v_0 (f56 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f8 f9 ?v0)) (?v_0 (f8 f9 ?v1))) (= (f3 ?v_1 (f3 ?v_0 ?v2)) (f3 ?v_0 (f3 ?v_1 ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f43 (f52 f53 ?v0) ?v1) (f43 (f52 f53 ?v1) ?v0))))
(assert (forall ((?v0 S27) (?v1 S27)) (= (f62 (f63 f64 ?v0) ?v1) (f62 (f63 f64 ?v1) ?v0))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f59 (f60 f61 ?v0) ?v1) (f59 (f60 f61 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f16 (f54 f55 ?v0) ?v1) (f16 (f54 f55 ?v1) ?v0))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f56 (f57 f58 ?v0) ?v1) (f56 (f57 f58 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f8 f9 ?v0) ?v1) (f3 (f8 f9 ?v1) ?v0))))
(assert (forall ((?v0 S18)) (= (= f31 ?v0) (= ?v0 f31))))
(assert (forall ((?v0 S3)) (= (= f19 ?v0) (= ?v0 f19))))
(assert (forall ((?v0 S11)) (= (= f21 ?v0) (= ?v0 f21))))
(assert (forall ((?v0 S14)) (= (= f25 ?v0) (= ?v0 f25))))
(assert (forall ((?v0 S8)) (= (= f15 ?v0) (= ?v0 f15))))
(assert (forall ((?v0 S5)) (= (= f10 ?v0) (= ?v0 f10))))
(assert (forall ((?v0 S27)) (= (= f46 ?v0) (= ?v0 f46))))
(assert (forall ((?v0 S27) (?v1 S18) (?v2 S27) (?v3 S18)) (= (= (f43 (f44 f45 ?v0) ?v1) (f43 (f44 f45 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S3) (?v3 S8)) (= (= (f16 (f17 f18 ?v0) ?v1) (f16 (f17 f18 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S14) (?v1 S11) (?v2 S14) (?v3 S11)) (= (= (f22 (f23 f24 ?v0) ?v1) (f22 (f23 f24 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5) (?v1 S3) (?v2 S5) (?v3 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) (f3 (f4 f5 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S11)) (= (f22 (f50 f51 ?v0) f26) f26)))
(assert (forall ((?v0 S18)) (= (f43 (f52 f53 ?v0) f47) f47)))
(assert (forall ((?v0 S8)) (= (f16 (f54 f55 ?v0) f20) f20)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 ?v0) f6) f6)))
(assert (forall ((?v0 S3)) (= (f3 (f8 f9 ?v0) f11) f11)))
(assert (forall ((?v0 S27)) (= (f62 (f63 f64 ?v0) f48) f48)))
(assert (forall ((?v0 S14)) (= (f56 (f57 f58 ?v0) f49) f49)))
(assert (forall ((?v0 S11)) (= (f22 (f50 f51 f26) ?v0) f26)))
(assert (forall ((?v0 S18)) (= (f43 (f52 f53 f47) ?v0) f47)))
(assert (forall ((?v0 S8)) (= (f16 (f54 f55 f20) ?v0) f20)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 f6) ?v0) f6)))
(assert (forall ((?v0 S3)) (= (f3 (f8 f9 f11) ?v0) f11)))
(assert (forall ((?v0 S27)) (= (f62 (f63 f64 f48) ?v0) f48)))
(assert (forall ((?v0 S14)) (= (f56 (f57 f58 f49) ?v0) f49)))
(assert (forall ((?v0 S18)) (= (f65 (f66 ?v0) f47) f1)))
(assert (forall ((?v0 S8)) (= (f67 (f68 ?v0) f20) f1)))
(assert (forall ((?v0 S11)) (= (f69 (f70 ?v0) f26) f1)))
(assert (forall ((?v0 S5)) (= (f71 ?v0 f6) f1)))
(assert (forall ((?v0 S27)) (= (f72 ?v0 f48) f1)))
(assert (forall ((?v0 S14)) (= (f73 ?v0 f49) f1)))
(assert (forall ((?v0 S3)) (= (f12 (f13 ?v0) f11) f1)))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f52 f53 ?v0))) (= (= (f65 (f66 (f43 ?v_0 ?v1)) (f43 ?v_0 ?v2)) f1) (or (= ?v0 f47) (= (f65 (f66 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f54 f55 ?v0))) (= (= (f67 (f68 (f16 ?v_0 ?v1)) (f16 ?v_0 ?v2)) f1) (or (= ?v0 f20) (= (f67 (f68 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f60 f61 ?v0))) (= (= (f71 (f59 ?v_0 ?v1) (f59 ?v_0 ?v2)) f1) (or (= ?v0 f6) (= (f71 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S27)) (let ((?v_0 (f63 f64 ?v0))) (= (= (f72 (f62 ?v_0 ?v1) (f62 ?v_0 ?v2)) f1) (or (= ?v0 f48) (= (f72 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (= (f12 (f13 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2)) f1) (or (= ?v0 f11) (= (f12 (f13 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (= (= (f65 (f66 (f43 (f52 f53 ?v0) ?v1)) (f43 (f52 f53 ?v2) ?v1)) f1) (or (= ?v1 f47) (= (f65 (f66 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (= (f67 (f68 (f16 (f54 f55 ?v0) ?v1)) (f16 (f54 f55 ?v2) ?v1)) f1) (or (= ?v1 f20) (= (f67 (f68 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (= (= (f71 (f59 (f60 f61 ?v0) ?v1) (f59 (f60 f61 ?v2) ?v1)) f1) (or (= ?v1 f6) (= (f71 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S27)) (= (= (f72 (f62 (f63 f64 ?v0) ?v1) (f62 (f63 f64 ?v2) ?v1)) f1) (or (= ?v1 f48) (= (f72 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f12 (f13 (f3 (f8 f9 ?v0) ?v1)) (f3 (f8 f9 ?v2) ?v1)) f1) (or (= ?v1 f11) (= (f12 (f13 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S37) (?v1 S18)) (=> (= (f65 ?v0 f47) f1) (=> (forall ((?v2 S27) (?v3 S18)) (=> (= (f65 ?v0 ?v3) f1) (= (f65 ?v0 (f43 (f44 f45 ?v2) ?v3)) f1))) (= (f65 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S38) (?v1 S8)) (=> (= (f67 ?v0 f20) f1) (=> (forall ((?v2 S3) (?v3 S8)) (=> (= (f67 ?v0 ?v3) f1) (= (f67 ?v0 (f16 (f17 f18 ?v2) ?v3)) f1))) (= (f67 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S39) (?v1 S11)) (=> (= (f69 ?v0 f26) f1) (=> (forall ((?v2 S14) (?v3 S11)) (=> (= (f69 ?v0 ?v3) f1) (= (f69 ?v0 (f22 (f23 f24 ?v2) ?v3)) f1))) (= (f69 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S7) (?v1 S3)) (=> (= (f12 ?v0 f11) f1) (=> (forall ((?v2 S5) (?v3 S3)) (=> (= (f12 ?v0 ?v3) f1) (= (f12 ?v0 (f3 (f4 f5 ?v2) ?v3)) f1))) (= (f12 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S14)) (= (f73 f25 ?v0) f1)))
(assert (forall ((?v0 S11)) (= (f69 (f70 f21) ?v0) f1)))
(assert (forall ((?v0 S5)) (= (f71 f10 ?v0) f1)))
(assert (forall ((?v0 S27)) (= (f72 f46 ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f12 (f13 f19) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f12 (f13 (f3 (f8 f9 ?v0) ?v1)) ?v2) f1) (= (f12 (f13 ?v1) ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f12 (f13 (f3 (f8 f9 ?v0) ?v1)) ?v2) f1) (= (f12 (f13 ?v0) ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= ?v0 (f3 (f8 f9 ?v1) ?v2)) (= (f12 (f13 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (= (f12 (f13 ?v2) ?v3) f1) (= (f12 (f13 (f3 (f8 f9 ?v0) ?v2)) (f3 (f8 f9 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f13 ?v0))) (=> (= (f12 ?v_0 ?v1) f1) (= (f12 ?v_0 (f3 (f8 f9 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f13 ?v0))) (=> (= (f12 ?v_0 ?v1) f1) (= (f12 ?v_0 (f3 (f8 f9 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f13 ?v0))) (=> (= (f12 ?v_0 ?v1) f1) (=> (= (f12 (f13 ?v1) ?v2) f1) (= (f12 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3)) (= (f12 (f13 ?v0) ?v0) f1)))
(assert (forall ((?v0 S14)) (= (f56 (f57 f58 f49) ?v0) f49)))
(assert (forall ((?v0 S27)) (= (f62 (f63 f64 f48) ?v0) f48)))
(assert (forall ((?v0 S3)) (= (f3 (f8 f9 f11) ?v0) f11)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 f6) ?v0) f6)))
(assert (forall ((?v0 S14)) (= (f56 (f57 f58 ?v0) f49) f49)))
(assert (forall ((?v0 S27)) (= (f62 (f63 f64 ?v0) f48) f48)))
(assert (forall ((?v0 S3)) (= (f3 (f8 f9 ?v0) f11) f11)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 ?v0) f6) f6)))
(assert (forall ((?v0 S27) (?v1 S27)) (= (= (f62 (f63 f64 ?v0) ?v1) f48) (or (= ?v0 f48) (= ?v1 f48)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f8 f9 ?v0) ?v1) f11) (or (= ?v0 f11) (= ?v1 f11)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f59 (f60 f61 ?v0) ?v1) f6) (or (= ?v0 f6) (= ?v1 f6)))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (not (= ?v0 f49)) (=> (not (= ?v1 f49)) (not (= (f56 (f57 f58 ?v0) ?v1) f49))))))
(assert (forall ((?v0 S27) (?v1 S27)) (=> (not (= ?v0 f48)) (=> (not (= ?v1 f48)) (not (= (f62 (f63 f64 ?v0) ?v1) f48))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 f11)) (=> (not (= ?v1 f11)) (not (= (f3 (f8 f9 ?v0) ?v1) f11))))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= ?v0 f6)) (=> (not (= ?v1 f6)) (not (= (f59 (f60 f61 ?v0) ?v1) f6))))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f56 (f57 f58 ?v0) ?v1) f49) (or (= ?v0 f49) (= ?v1 f49)))))
(assert (forall ((?v0 S27) (?v1 S27)) (=> (= (f62 (f63 f64 ?v0) ?v1) f48) (or (= ?v0 f48) (= ?v1 f48)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f8 f9 ?v0) ?v1) f11) (or (= ?v0 f11) (= ?v1 f11)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f59 (f60 f61 ?v0) ?v1) f6) (or (= ?v0 f6) (= ?v1 f6)))))
(assert (not (= f46 f48)))
(assert (not (= f10 f6)))
(assert (not (= f25 f49)))
(assert (not (= f19 f11)))
(assert (not (= f48 f46)))
(assert (not (= f6 f10)))
(assert (not (= f49 f25)))
(assert (not (= f11 f19)))
(assert (forall ((?v0 S3)) (=> (= (f12 (f13 f11) ?v0) f1) (= ?v0 f11))))
(assert (forall ((?v0 S14)) (=> (= (f73 f49 ?v0) f1) (= ?v0 f49))))
(assert (forall ((?v0 S27)) (=> (= (f72 f48 ?v0) f1) (= ?v0 f48))))
(assert (forall ((?v0 S5)) (=> (= (f71 f6 ?v0) f1) (= ?v0 f6))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f12 (f13 ?v0) (f3 (f8 f9 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f12 (f13 ?v0) (f3 (f8 f9 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (forall ((?v2 S3)) (=> (= ?v1 (f3 (f8 f9 ?v0) ?v2)) false)) false))))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 f6) ?v0) f6)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 f6) ?v0) f6)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 ?v0) f6) f6)))
(assert (forall ((?v0 S5)) (= (f59 (f60 f61 ?v0) f6) f6)))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S5) (?v2 S3)) (=> (= ?v0 (f3 (f4 f5 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S5)) (= ?v0 (f59 (f74 f75 (f3 (f4 f5 f6) (f3 (f4 f5 f10) f11))) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f74 f75 ?v0) (f74 f75 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3)) (= (= (f74 f75 ?v0) (f74 f75 f11)) (= ?v0 f11))))
(assert (forall ((?v0 S5)) (= (f59 (f74 f75 f11) ?v0) f6)))
(assert (forall ((?v0 S14)) (= (f56 (f76 f77 f26) ?v0) f49)))
(assert (forall ((?v0 S27)) (= (f62 (f78 f79 f47) ?v0) f48)))
(assert (forall ((?v0 S3)) (= (f3 (f80 f81 f20) ?v0) f11)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S5)) (= (f59 (f74 f75 (f3 (f8 f9 ?v0) ?v1)) ?v2) (f59 (f60 f61 (f59 (f74 f75 ?v0) ?v2)) (f59 (f74 f75 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S3)) (= (f3 (f80 f81 (f16 (f54 f55 ?v0) ?v1)) ?v2) (f3 (f8 f9 (f3 (f80 f81 ?v0) ?v2)) (f3 (f80 f81 ?v1) ?v2)))))
(assert (forall ((?v0 S5)) (= f6 (f59 (f74 f75 f11) ?v0))))
(assert (forall ((?v0 S5)) (= (f59 (f74 f75 f11) ?v0) f6)))
(assert (forall ((?v0 S3) (?v1 S5)) (=> (= (f59 (f74 f75 ?v0) ?v1) f6) (= (f59 (f74 f75 (f3 (f4 f5 f6) ?v0)) ?v1) f6))))
(assert (forall ((?v0 S5)) (= (f59 (f74 f75 f19) ?v0) f10)))
(assert (forall ((?v0 S27)) (= (f62 (f78 f79 f31) ?v0) f46)))
(assert (forall ((?v0 S5) (?v1 S5)) (let ((?v_0 (f74 f75 f11))) (= (f59 (f74 f75 (f3 (f4 f5 (f59 ?v_0 ?v0)) f11)) ?v1) (f59 ?v_0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f59 (f74 f75 (f3 (f4 f5 ?v0) f11)) ?v1) ?v0)))
(assert (forall ((?v0 S5) (?v1 S5)) (= ?v0 (f59 (f74 f75 (f3 (f4 f5 ?v0) f11)) ?v1))))
(assert (forall ((?v0 S5)) (= (f59 (f74 f75 (f3 (f4 f5 f6) f11)) ?v0) (f59 (f74 f75 f11) ?v0))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f59 (f74 f75 ?v0) ?v1) f6) (or (= ?v0 f11) (not (= (f82 (f83 f84 ?v1) ?v0) f49))))))
(assert (forall ((?v0 S18) (?v1 S27)) (= (= (f62 (f78 f79 ?v0) ?v1) f48) (or (= ?v0 f47) (not (= (f85 (f86 f87 ?v1) ?v0) f49))))))
(assert (forall ((?v0 S8) (?v1 S3)) (= (= (f3 (f80 f81 ?v0) ?v1) f11) (or (= ?v0 f20) (not (= (f88 (f89 f90 ?v1) ?v0) f49))))))
(assert (forall ((?v0 S3)) (=> (not (exists ((?v1 S5) (?v2 S3)) (and (not (= ?v1 f6)) (and (= ?v2 f11) (= ?v0 (f3 (f4 f5 ?v1) ?v2)))))) (exists ((?v1 S5)) (= (f59 (f74 f75 ?v0) ?v1) f6)))))
(assert (forall ((?v0 S5) (?v1 S3)) (= (= (f12 (f13 (f3 (f4 f5 ?v0) (f3 (f4 f5 f10) f11))) ?v1) f1) (= (f59 (f74 f75 ?v1) (f59 f91 ?v0)) f6))))
(assert (forall ((?v0 S27) (?v1 S18)) (= (= (f65 (f66 (f43 (f44 f45 ?v0) (f43 (f44 f45 f46) f47))) ?v1) f1) (= (f62 (f78 f79 ?v1) (f62 f92 ?v0)) f48))))
(assert (forall ((?v0 S3) (?v1 S8)) (= (= (f67 (f68 (f16 (f17 f18 ?v0) (f16 (f17 f18 f19) f20))) ?v1) f1) (= (f3 (f80 f81 ?v1) (f3 f93 ?v0)) f11))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f59 (f74 f75 ?v0) ?v1) f6) (= (f12 (f13 (f3 (f4 f5 (f59 f91 ?v1)) (f3 (f4 f5 f10) f11))) ?v0) f1))))
(assert (forall ((?v0 S18) (?v1 S27)) (= (= (f62 (f78 f79 ?v0) ?v1) f48) (= (f65 (f66 (f43 (f44 f45 (f62 f92 ?v1)) (f43 (f44 f45 f46) f47))) ?v0) f1))))
(assert (forall ((?v0 S8) (?v1 S3)) (= (= (f3 (f80 f81 ?v0) ?v1) f11) (= (f67 (f68 (f16 (f17 f18 (f3 f93 ?v1)) (f16 (f17 f18 f19) f20))) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (let ((?v_0 (f3 (f4 f5 ?v0) f11))) (= (f94 (f95 f96 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S5) (?v1 S3) (?v2 S5)) (= (f94 (f95 f97 (f3 (f4 f5 ?v0) ?v1)) ?v2) (f3 (f4 f5 (f59 (f74 f75 ?v1) ?v2)) (f94 (f95 f97 ?v1) ?v2)))))
(assert (forall ((?v0 S3)) (=> (not (= (f98 (f74 f75 ?v0)) f1)) (exists ((?v1 S5)) (= (f59 (f74 f75 ?v0) ?v1) f6)))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (f59 (f74 f75 (f3 f93 ?v0)) ?v1) (f59 f91 (f59 (f74 f75 ?v0) ?v1)))))
(assert (forall ((?v0 S33)) (= (= (f98 ?v0) f1) (forall ((?v1 S5) (?v2 S5)) (= (f59 ?v0 ?v1) (f59 ?v0 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S3)) (= (f3 f93 (f3 (f4 f5 ?v0) ?v1)) (f3 (f4 f5 (f59 f91 ?v0)) (f3 f93 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S3)) (= (f3 f93 (f3 (f4 f5 ?v0) ?v1)) (f3 (f4 f5 (f59 f91 ?v0)) (f3 f93 ?v1)))))
(assert (= (f62 f92 f48) f48))
(assert (= (f3 f93 f11) f11))
(assert (= (f59 f91 f6) f6))
(assert (forall ((?v0 S27)) (= (= f48 (f62 f92 ?v0)) (= f48 ?v0))))
(assert (forall ((?v0 S3)) (= (= f11 (f3 f93 ?v0)) (= f11 ?v0))))
(assert (forall ((?v0 S5)) (= (= f6 (f59 f91 ?v0)) (= f6 ?v0))))
(assert (forall ((?v0 S27)) (= (= ?v0 (f62 f92 ?v0)) (= ?v0 f48))))
(assert (forall ((?v0 S27)) (= (= (f62 f92 ?v0) f48) (= ?v0 f48))))
(assert (forall ((?v0 S3)) (= (= (f3 f93 ?v0) f11) (= ?v0 f11))))
(assert (forall ((?v0 S5)) (= (= (f59 f91 ?v0) f6) (= ?v0 f6))))
(assert (forall ((?v0 S27)) (= (= (f62 f92 ?v0) ?v0) (= ?v0 f48))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f3 f93 (f3 ?v_0 ?v1)) (f3 ?v_0 (f3 f93 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 f93 (f3 (f8 f9 ?v0) ?v1)) (f3 (f8 f9 (f3 f93 ?v0)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f8 f9 (f3 f93 ?v0)) ?v1) (f3 (f8 f9 ?v0) (f3 f93 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f8 f9 (f3 f93 ?v0)) (f3 f93 ?v1)) (f3 (f8 f9 ?v0) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f8 f9 ?v0) ?v0) (f3 (f8 f9 ?v1) ?v1)) (or (= ?v0 ?v1) (= ?v0 (f3 f93 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f12 (f13 (f3 f93 ?v0)) ?v1) f1) (= (f12 (f13 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f13 ?v0))) (= (= (f12 ?v_0 (f3 f93 ?v1)) f1) (= (f12 ?v_0 ?v1) f1)))))
(assert (= (f3 f93 f11) f11))
(assert (forall ((?v0 S27)) (= (= (f62 (f63 f64 ?v0) ?v0) f46) (or (= ?v0 f46) (= ?v0 (f62 f92 f46))))))
(assert (forall ((?v0 S5)) (= (= (f59 (f60 f61 ?v0) ?v0) f10) (or (= ?v0 f10) (= ?v0 (f59 f91 f10))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f8 f9 ?v0) ?v0) f19) (or (= ?v0 f19) (= ?v0 (f3 f93 f19))))))
(assert (forall ((?v0 S27)) (= (f62 f92 ?v0) (f62 (f63 f64 (f62 f92 f46)) ?v0))))
(assert (forall ((?v0 S5)) (= (f59 f91 ?v0) (f59 (f60 f61 (f59 f91 f10)) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 f93 ?v0) (f3 (f8 f9 (f3 f93 f19)) ?v0))))
(assert (forall ((?v0 S5)) (= (f94 (f95 f97 f11) ?v0) f11)))
(assert (forall ((?v0 S5)) (= (f94 (f95 f96 f11) ?v0) f11)))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f94 (f95 f96 ?v0) ?v1) f11) (= ?v0 f11))))
(assert (forall ((?v0 S5) (?v1 S3)) (= (f3 (f8 f99 (f3 (f8 f9 (f3 (f4 f5 (f59 f91 ?v0)) (f3 (f4 f5 f10) f11))) (f94 (f95 f97 ?v1) ?v0))) (f3 (f4 f5 (f59 (f74 f75 ?v1) ?v0)) f11)) ?v1)))
(assert (forall ((?v0 S27) (?v1 S18)) (= (f43 (f52 f100 (f43 (f52 f53 (f43 (f44 f45 (f62 f92 ?v0)) (f43 (f44 f45 f46) f47))) (f101 (f102 f103 ?v1) ?v0))) (f43 (f44 f45 (f62 (f78 f79 ?v1) ?v0)) f47)) ?v1)))
(assert (forall ((?v0 S5) (?v1 S3)) (= (f12 (f13 (f104 (f105 f106 (f3 (f4 f5 (f59 f91 ?v0)) (f3 (f4 f5 f10) f11))) (f82 (f83 f84 ?v0) ?v1))) ?v1) f1)))
(assert (forall ((?v0 S27) (?v1 S18)) (= (f65 (f66 (f107 (f108 f109 (f43 (f44 f45 (f62 f92 ?v0)) (f43 (f44 f45 f46) f47))) (f85 (f86 f87 ?v0) ?v1))) ?v1) f1)))
(assert (forall ((?v0 S3)) (= (= (f82 f110 ?v0) f49) (= ?v0 f11))))
(assert (forall ((?v0 S14)) (= (f111 (f112 f113 f31) ?v0) (ite (= ?v0 f49) f46 f48))))
(assert (forall ((?v0 S14)) (= (f114 (f115 f116 f19) ?v0) (ite (= ?v0 f49) f10 f6))))
(assert (forall ((?v0 S14)) (= (f56 (f76 f117 f21) ?v0) (ite (= ?v0 f49) f25 f49))))
(assert (forall ((?v0 S14)) (= (f104 (f118 f119 f15) ?v0) (ite (= ?v0 f49) f19 f11))))
(assert (forall ((?v0 S5)) (= (f104 (f120 f121 ?v0) f49) (f3 (f4 f5 ?v0) f11))))
(assert (forall ((?v0 S3)) (= (= (f98 (f74 f75 ?v0)) f1) (= (f82 f122 ?v0) f49))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S5)) (= (f59 (f74 f75 (f3 (f8 f99 ?v0) ?v1)) ?v2) (f59 (f60 f123 (f59 (f74 f75 ?v0) ?v2)) (f59 (f74 f75 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S14) (?v2 S5)) (= (f59 (f74 f75 (f104 (f105 f106 ?v0) ?v1)) ?v2) (f114 (f124 f125 (f59 (f74 f75 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f114 (f115 f116 ?v0) (f82 f122 ?v0)) (f114 (f115 f116 ?v1) (f82 f122 ?v1))) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (= (f12 (f13 ?v1) ?v0) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (= (f56 (f76 f117 (f126 (f127 f128 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f49))))
(assert (forall ((?v0 S27) (?v1 S14) (?v2 S14)) (= (f111 (f112 f113 (f107 (f129 f130 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f48))))
(assert (forall ((?v0 S3) (?v1 S14) (?v2 S14)) (= (f104 (f118 f119 (f131 (f132 f133 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f11))))
(assert (forall ((?v0 S5) (?v1 S14) (?v2 S14)) (= (f114 (f115 f116 (f104 (f120 f121 ?v0) ?v1)) ?v2) (ite (= ?v1 ?v2) ?v0 f6))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (not (= ?v0 f49)) (= (f134 f135 (f126 (f127 f128 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S27) (?v1 S14)) (=> (not (= ?v0 f48)) (= (f85 f136 (f107 (f129 f130 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S14)) (=> (not (= ?v0 f11)) (= (f88 f137 (f131 (f132 f133 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S5) (?v1 S14)) (=> (not (= ?v0 f6)) (= (f82 f122 (f104 (f120 f121 ?v0) ?v1)) ?v1))))
(assert (forall ((?v0 S3)) (= (= (f114 (f115 f116 ?v0) (f82 f122 ?v0)) f6) (= ?v0 f11))))
(assert (forall ((?v0 S11)) (= (= (f56 (f76 f117 ?v0) (f134 f135 ?v0)) f49) (= ?v0 f26))))
(assert (forall ((?v0 S18)) (= (= (f111 (f112 f113 ?v0) (f85 f136 ?v0)) f48) (= ?v0 f47))))
(assert (forall ((?v0 S8)) (= (= (f104 (f118 f119 ?v0) (f88 f137 ?v0)) f11) (= ?v0 f20))))
(assert (forall ((?v0 S11)) (=> (not (= ?v0 f26)) (not (= (f56 (f76 f117 ?v0) (f134 f135 ?v0)) f49)))))
(assert (forall ((?v0 S18)) (=> (not (= ?v0 f47)) (not (= (f111 (f112 f113 ?v0) (f85 f136 ?v0)) f48)))))
(assert (forall ((?v0 S8)) (=> (not (= ?v0 f20)) (not (= (f104 (f118 f119 ?v0) (f88 f137 ?v0)) f11)))))
(assert (forall ((?v0 S3)) (=> (not (= ?v0 f11)) (not (= (f114 (f115 f116 ?v0) (f82 f122 ?v0)) f6)))))
(assert (forall ((?v0 S5) (?v1 S3) (?v2 S5) (?v3 S3)) (= (f3 (f8 f99 (f3 (f4 f5 ?v0) ?v1)) (f3 (f4 f5 ?v2) ?v3)) (f3 (f4 f5 (f59 (f60 f123 ?v0) ?v2)) (f3 (f8 f99 ?v1) ?v3)))))
(check-sat)
(exit)