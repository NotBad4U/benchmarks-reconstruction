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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () S1)
(declare-fun f4 (S3 S4 S5 S6 S2) S1)
(declare-fun f5 () S3)
(declare-fun f6 () S4)
(declare-fun f7 () S5)
(declare-fun f8 () S6)
(declare-fun f9 (S7 S6) S6)
(declare-fun f10 (S8 S9) S7)
(declare-fun f11 (S10 S9) S8)
(declare-fun f12 (S11 S6) S10)
(declare-fun f13 () S11)
(declare-fun f14 () S6)
(declare-fun f15 () S9)
(declare-fun f16 () S9)
(declare-fun f17 () S2)
(declare-fun f18 () S2)
(declare-fun f19 (S12 S3) S1)
(declare-fun f20 () S12)
(declare-fun f21 () S4)
(declare-fun f22 () S6)
(declare-fun f23 (S13 S14) S1)
(declare-fun f24 (S15 S5) S13)
(declare-fun f25 (S3) S15)
(declare-fun f26 (S16 S17) S14)
(declare-fun f27 (S18 S4) S16)
(declare-fun f28 () S18)
(declare-fun f29 () S17)
(declare-fun f30 (S3 S2 S2) S1)
(declare-fun f31 () S2)
(declare-fun f32 (S19 S4) S1)
(declare-fun f33 (S4) S19)
(declare-fun f34 (S5 S5) S1)
(declare-fun f35 (S20 S6) S7)
(declare-fun f36 () S20)
(declare-fun f37 (S21 S22) S1)
(declare-fun f38 (S23 S24) S21)
(declare-fun f39 (S25 S24) S23)
(declare-fun f40 () S25)
(declare-fun f41 (S26 S14) S24)
(declare-fun f42 (S27 S6) S26)
(declare-fun f43 () S27)
(declare-fun f44 () S17)
(declare-fun f45 (S3) S22)
(declare-fun f46 (S3) S19)
(declare-fun f47 (S3 S4 S17 S5) S1)
(declare-fun f48 (S14) S4)
(declare-fun f49 (S29 S21) S28)
(declare-fun f50 (S30 S21) S29)
(declare-fun f51 () S30)
(declare-fun f52 (S33 S32) S31)
(declare-fun f53 (S34 S32) S33)
(declare-fun f54 () S34)
(declare-fun f55 (S35 S14) S32)
(declare-fun f56 (S36 S14) S35)
(declare-fun f57 () S36)
(declare-fun f58 (S38 S28) S37)
(declare-fun f59 (S39 S28) S38)
(declare-fun f60 () S39)
(declare-fun f61 (S40 S28) S1)
(declare-fun f62 (S22 S21) S1)
(declare-fun f63 (S41 S31) S1)
(declare-fun f64 (S42 S37) S1)
(declare-fun f65 (S43 S6) S1)
(declare-fun f66 (S32 S45) S1)
(declare-fun f67 (S44 S6) S45)
(declare-fun f68 (S46 S44) S22)
(declare-fun f69 (S43) S46)
(declare-fun f70 (S47 S24) S1)
(declare-fun f71 (S48 S24) S22)
(declare-fun f72 (S28 S40) S1)
(declare-fun f73 (S49 S48) S40)
(declare-fun f74 (S47) S49)
(declare-fun f75 (S51 S52) S1)
(declare-fun f76 (S53 S17) S51)
(declare-fun f77 (S54 S17) S53)
(declare-fun f78 () S54)
(declare-fun f79 (S50 S4) S52)
(declare-fun f80 (S55 S50) S45)
(declare-fun f81 (S19) S55)
(declare-fun f82 (S45 S32) S1)
(declare-fun f83 (S31 S41) S1)
(declare-fun f84 (S56 S32) S41)
(declare-fun f85 (S57 S58) S1)
(declare-fun f86 (S31 S31) S57)
(declare-fun f87 (S45 S56) S58)
(declare-fun f88 (S37 S42) S1)
(declare-fun f89 (S59 S28) S42)
(declare-fun f90 (S60 S61) S1)
(declare-fun f91 (S37 S37) S60)
(declare-fun f92 (S40 S59) S61)
(declare-fun f93 (S52 S51) S1)
(declare-fun f94 (S63 S64) S1)
(declare-fun f95 (S65 S51) S63)
(declare-fun f96 (S66 S51) S65)
(declare-fun f97 () S66)
(declare-fun f98 (S62 S51) S64)
(declare-fun f99 (S67 S68) S1)
(declare-fun f100 (S63 S63) S67)
(declare-fun f101 (S52 S62) S68)
(declare-fun f102 (S69 S17) S1)
(declare-fun f103 (S70 S17) S52)
(declare-fun f104 (S71 S70) S64)
(declare-fun f105 (S69) S71)
(declare-fun f106 (S72 S21) S40)
(declare-fun f107 (S73 S72) S42)
(declare-fun f108 (S22) S73)
(declare-fun f109 (S74 S14) S45)
(declare-fun f110 (S75 S74) S41)
(declare-fun f111 (S13) S75)
(declare-fun f112 (S76 S17) S17)
(declare-fun f113 (S17) S76)
(declare-fun f114 (S64 S63) S1)
(declare-fun f115 (S77 S5) S5)
(declare-fun f116 (S5) S77)
(declare-fun f117 (S17) S69)
(declare-fun f118 (S22) S22)
(declare-fun f119 (S41) S41)
(declare-fun f120 (S42) S42)
(declare-fun f121 (S64) S64)
(declare-fun f122 (S52) S52)
(declare-fun f123 (S40) S40)
(declare-fun f124 (S45) S45)
(assert (not (= f1 f2)))
(assert (not (= f3 f1)))
(assert (forall ((?v0 S2)) (=> (= (f4 f5 f6 f7 f8 ?v0) f1) (= f3 f1))))
(assert (= (f4 f5 f6 f7 (f9 (f10 (f11 (f12 f13 f14) f15) f16) f8) f17) f1))
(assert (= (f4 f5 f6 f7 (f9 (f10 (f11 (f12 f13 f14) f15) f16) f8) f17) f1))
(assert (= (f4 f5 f6 f7 f14 f18) f1))
(assert (= (f19 f20 f5) f1))
(assert (= (f4 f5 f6 f7 (f9 (f10 (f11 (f12 f13 f14) f15) f16) f8) f17) f1))
(assert (= (f4 f5 f21 f7 f22 f18) f1))
(assert (= (f23 (f24 (f25 f5) f7) (f26 (f27 f28 f6) f29)) f1))
(assert (= (f23 (f24 (f25 f5) f7) (f26 (f27 f28 f6) f29)) f1))
(assert (forall ((?v0 S5) (?v1 S2)) (=> (= (f23 (f24 (f25 f5) ?v0) (f26 (f27 f28 f6) f29)) f1) (=> (= (f4 f5 f6 ?v0 f14 ?v1) f1) (exists ((?v2 S2)) (and (= (f4 f5 f21 ?v0 f22 ?v2) f1) (= (f30 f5 ?v2 ?v1) f1)))))))
(assert (= f17 f31))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S5) (?v3 S6) (?v4 S2) (?v5 S4)) (=> (= (f4 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f32 (f33 ?v1) ?v5) f1) (= (f4 ?v0 ?v5 ?v2 ?v3 ?v4) f1)))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S5) (?v3 S6) (?v4 S2) (?v5 S5)) (=> (= (f4 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f34 ?v2 ?v5) f1) (= (f4 ?v0 ?v1 ?v5 ?v3 ?v4) f1)))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S5) (?v3 S6) (?v4 S2) (?v5 S6) (?v6 S2)) (=> (= (f4 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f4 ?v0 ?v1 ?v2 ?v5 ?v6) f1) (= (f4 ?v0 ?v1 ?v2 (f9 (f35 f36 ?v3) ?v5) ?v6) f1)))))
(assert (forall ((?v0 S5) (?v1 S2)) (=> (= (f23 (f24 (f25 f5) ?v0) (f26 (f27 f28 f6) f29)) f1) (=> (= (f4 f5 f6 ?v0 f14 ?v1) f1) (exists ((?v2 S2)) (and (= (f4 f5 f21 ?v0 f22 ?v2) f1) (= (f30 f5 ?v2 ?v1) f1)))))))
(assert (= (f37 (f38 (f39 f40 (f41 (f42 f43 f14) (f26 (f27 f28 f6) f29))) (f41 (f42 f43 f22) (f26 (f27 f28 f21) f44))) (f45 f5)) f1))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S5) (?v3 S6) (?v4 S6) (?v5 S2) (?v6 S9) (?v7 S9)) (=> (= (f4 ?v0 ?v1 ?v2 ?v3 f18) f1) (=> (= (f4 ?v0 ?v1 ?v2 ?v4 ?v5) f1) (= (f4 ?v0 ?v1 ?v2 (f9 (f10 (f11 (f12 f13 ?v3) ?v6) ?v7) ?v4) f31) f1)))))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S17) (?v3 S6) (?v4 S4) (?v5 S17) (?v6 S3)) (=> (= (f37 (f38 (f39 f40 (f41 (f42 f43 ?v0) (f26 (f27 f28 ?v1) ?v2))) (f41 (f42 f43 ?v3) (f26 (f27 f28 ?v4) ?v5))) (f45 ?v6)) f1) (= (f32 (f33 ?v1) ?v4) f1))))
(assert (forall ((?v0 S6) (?v1 S14) (?v2 S6) (?v3 S14) (?v4 S3) (?v5 S9) (?v6 S9) (?v7 S6)) (let ((?v_0 (f45 ?v4))) (=> (= (f37 (f38 (f39 f40 (f41 (f42 f43 ?v0) ?v1)) (f41 (f42 f43 ?v2) ?v3)) ?v_0) f1) (= (f37 (f38 (f39 f40 (f41 (f42 f43 (f9 (f10 (f11 (f12 f13 ?v0) ?v5) ?v6) ?v7)) ?v1)) (f41 (f42 f43 (f9 (f10 (f11 (f12 f13 ?v2) ?v5) ?v6) ?v7)) ?v3)) ?v_0) f1)))))
(assert (forall ((?v0 S6) (?v1 S14) (?v2 S6) (?v3 S14) (?v4 S3) (?v5 S6)) (let ((?v_0 (f45 ?v4))) (=> (= (f37 (f38 (f39 f40 (f41 (f42 f43 ?v0) ?v1)) (f41 (f42 f43 ?v2) ?v3)) ?v_0) f1) (= (f37 (f38 (f39 f40 (f41 (f42 f43 (f9 (f35 f36 ?v0) ?v5)) ?v1)) (f41 (f42 f43 (f9 (f35 f36 ?v2) ?v5)) ?v3)) ?v_0) f1)))))
(assert (forall ((?v0 S4)) (= (f32 (f33 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f30 ?v0 ?v1 ?v1) f1)))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S17) (?v3 S6) (?v4 S4) (?v5 S17) (?v6 S3) (?v7 S5) (?v8 S2)) (let ((?v_0 (f46 ?v6))) (=> (= (f37 (f38 (f39 f40 (f41 (f42 f43 ?v0) (f26 (f27 f28 ?v1) ?v2))) (f41 (f42 f43 ?v3) (f26 (f27 f28 ?v4) ?v5))) (f45 ?v6)) f1) (=> (= (f4 ?v6 ?v1 ?v7 ?v0 ?v8) f1) (=> (= (f32 ?v_0 ?v1) f1) (= (f32 ?v_0 ?v4) f1)))))))
(assert (not (= f18 f31)))
(assert (not (= f31 f18)))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S17) (?v3 S6) (?v4 S4) (?v5 S17) (?v6 S3) (?v7 S5) (?v8 S2)) (=> (= (f37 (f38 (f39 f40 (f41 (f42 f43 ?v0) (f26 (f27 f28 ?v1) ?v2))) (f41 (f42 f43 ?v3) (f26 (f27 f28 ?v4) ?v5))) (f45 ?v6)) f1) (=> (= (f4 ?v6 ?v1 ?v7 ?v0 ?v8) f1) (=> (= (f47 ?v6 ?v1 ?v2 ?v7) f1) (= (f47 ?v6 ?v4 ?v5 ?v7) f1))))))
(assert (forall ((?v0 S6) (?v1 S14) (?v2 S6) (?v3 S14) (?v4 S3) (?v5 S5) (?v6 S2)) (let ((?v_0 (f24 (f25 ?v4) ?v5))) (=> (= (f37 (f38 (f39 f40 (f41 (f42 f43 ?v0) ?v1)) (f41 (f42 f43 ?v2) ?v3)) (f45 ?v4)) f1) (=> (= (f4 ?v4 (f48 ?v1) ?v5 ?v0 ?v6) f1) (=> (= (f23 ?v_0 ?v1) f1) (= (f23 ?v_0 ?v3) f1)))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S9) (?v4 S9) (?v5 S6)) (not (= (f9 (f35 f36 ?v0) ?v1) (f9 (f10 (f11 (f12 f13 ?v2) ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (= (f9 (f35 f36 ?v0) ?v1) (f9 (f35 f36 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f30 ?v0 ?v1 ?v2) f1) (=> (= (f30 ?v0 ?v2 ?v3) f1) (= (f30 ?v0 ?v1 ?v3) f1)))))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S9) (?v3 S6) (?v4 S6) (?v5 S9) (?v6 S9) (?v7 S6)) (= (= (f9 (f10 (f11 (f12 f13 ?v0) ?v1) ?v2) ?v3) (f9 (f10 (f11 (f12 f13 ?v4) ?v5) ?v6) ?v7)) (and (= ?v0 ?v4) (and (= ?v1 ?v5) (and (= ?v2 ?v6) (= ?v3 ?v7)))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f33 ?v0))) (=> (= (f32 ?v_0 ?v1) f1) (=> (= (f32 (f33 ?v1) ?v2) f1) (= (f32 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S9) (?v3 S6) (?v4 S6) (?v5 S6)) (not (= (f9 (f10 (f11 (f12 f13 ?v0) ?v1) ?v2) ?v3) (f9 (f35 f36 ?v4) ?v5)))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S17) (?v3 S5) (?v4 S4)) (=> (= (f47 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f32 (f33 ?v1) ?v4) f1) (= (f47 ?v0 ?v4 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S28)) (=> (forall ((?v1 S21) (?v2 S24) (?v3 S6) (?v4 S14)) (=> (= ?v0 (f49 (f50 f51 ?v1) (f38 (f39 f40 ?v2) (f41 (f42 f43 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S21)) (=> (forall ((?v1 S24) (?v2 S6) (?v3 S4) (?v4 S17)) (=> (= ?v0 (f38 (f39 f40 ?v1) (f41 (f42 f43 ?v2) (f26 (f27 f28 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S31)) (=> (forall ((?v1 S32) (?v2 S14) (?v3 S4) (?v4 S17)) (=> (= ?v0 (f52 (f53 f54 ?v1) (f55 (f56 f57 ?v2) (f26 (f27 f28 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S37)) (=> (forall ((?v1 S28) (?v2 S21) (?v3 S24) (?v4 S24)) (=> (= ?v0 (f58 (f59 f60 ?v1) (f49 (f50 f51 ?v2) (f38 (f39 f40 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S40) (?v1 S28)) (=> (forall ((?v2 S21) (?v3 S24) (?v4 S6) (?v5 S14)) (= (f61 ?v0 (f49 (f50 f51 ?v2) (f38 (f39 f40 ?v3) (f41 (f42 f43 ?v4) ?v5)))) f1)) (= (f61 ?v0 ?v1) f1))))
(assert (forall ((?v0 S22) (?v1 S21)) (=> (forall ((?v2 S24) (?v3 S6) (?v4 S4) (?v5 S17)) (= (f62 ?v0 (f38 (f39 f40 ?v2) (f41 (f42 f43 ?v3) (f26 (f27 f28 ?v4) ?v5)))) f1)) (= (f62 ?v0 ?v1) f1))))
(assert (forall ((?v0 S41) (?v1 S31)) (=> (forall ((?v2 S32) (?v3 S14) (?v4 S4) (?v5 S17)) (= (f63 ?v0 (f52 (f53 f54 ?v2) (f55 (f56 f57 ?v3) (f26 (f27 f28 ?v4) ?v5)))) f1)) (= (f63 ?v0 ?v1) f1))))
(assert (forall ((?v0 S42) (?v1 S37)) (=> (forall ((?v2 S28) (?v3 S21) (?v4 S24) (?v5 S24)) (= (f64 ?v0 (f58 (f59 f60 ?v2) (f49 (f50 f51 ?v3) (f38 (f39 f40 ?v4) ?v5)))) f1)) (= (f64 ?v0 ?v1) f1))))
(assert (forall ((?v0 S28)) (=> (forall ((?v1 S21) (?v2 S24) (?v3 S6) (?v4 S4) (?v5 S17)) (=> (= ?v0 (f49 (f50 f51 ?v1) (f38 (f39 f40 ?v2) (f41 (f42 f43 ?v3) (f26 (f27 f28 ?v4) ?v5))))) false)) false)))
(assert (forall ((?v0 S37)) (=> (forall ((?v1 S28) (?v2 S21) (?v3 S24) (?v4 S6) (?v5 S14)) (=> (= ?v0 (f58 (f59 f60 ?v1) (f49 (f50 f51 ?v2) (f38 (f39 f40 ?v3) (f41 (f42 f43 ?v4) ?v5))))) false)) false)))
(assert (forall ((?v0 S40) (?v1 S28)) (=> (forall ((?v2 S21) (?v3 S24) (?v4 S6) (?v5 S4) (?v6 S17)) (= (f61 ?v0 (f49 (f50 f51 ?v2) (f38 (f39 f40 ?v3) (f41 (f42 f43 ?v4) (f26 (f27 f28 ?v5) ?v6))))) f1)) (= (f61 ?v0 ?v1) f1))))
(assert (forall ((?v0 S42) (?v1 S37)) (=> (forall ((?v2 S28) (?v3 S21) (?v4 S24) (?v5 S6) (?v6 S14)) (= (f64 ?v0 (f58 (f59 f60 ?v2) (f49 (f50 f51 ?v3) (f38 (f39 f40 ?v4) (f41 (f42 f43 ?v5) ?v6))))) f1)) (= (f64 ?v0 ?v1) f1))))
(assert (forall ((?v0 S37)) (=> (forall ((?v1 S28) (?v2 S21) (?v3 S24) (?v4 S6) (?v5 S4) (?v6 S17)) (=> (= ?v0 (f58 (f59 f60 ?v1) (f49 (f50 f51 ?v2) (f38 (f39 f40 ?v3) (f41 (f42 f43 ?v4) (f26 (f27 f28 ?v5) ?v6)))))) false)) false)))
(assert (forall ((?v0 S42) (?v1 S37)) (=> (forall ((?v2 S28) (?v3 S21) (?v4 S24) (?v5 S6) (?v6 S4) (?v7 S17)) (= (f64 ?v0 (f58 (f59 f60 ?v2) (f49 (f50 f51 ?v3) (f38 (f39 f40 ?v4) (f41 (f42 f43 ?v5) (f26 (f27 f28 ?v6) ?v7)))))) f1)) (= (f64 ?v0 ?v1) f1))))
(assert (forall ((?v0 S43) (?v1 S6) (?v2 S14) (?v3 S14) (?v4 S44)) (let ((?v_0 (f42 f43 ?v1))) (=> (= (f65 ?v0 ?v1) f1) (=> (= (f66 (f55 (f56 f57 ?v2) ?v3) (f67 ?v4 ?v1)) f1) (= (f37 (f38 (f39 f40 (f41 ?v_0 ?v2)) (f41 ?v_0 ?v3)) (f68 (f69 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S47) (?v1 S24) (?v2 S24) (?v3 S24) (?v4 S48)) (let ((?v_0 (f39 f40 ?v1))) (=> (= (f70 ?v0 ?v1) f1) (=> (= (f37 (f38 (f39 f40 ?v2) ?v3) (f71 ?v4 ?v1)) f1) (= (f72 (f49 (f50 f51 (f38 ?v_0 ?v2)) (f38 ?v_0 ?v3)) (f73 (f74 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S19) (?v1 S4) (?v2 S17) (?v3 S17) (?v4 S50)) (let ((?v_0 (f27 f28 ?v1))) (=> (= (f32 ?v0 ?v1) f1) (=> (= (f75 (f76 (f77 f78 ?v2) ?v3) (f79 ?v4 ?v1)) f1) (= (f66 (f55 (f56 f57 (f26 ?v_0 ?v2)) (f26 ?v_0 ?v3)) (f80 (f81 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S45) (?v1 S32) (?v2 S32) (?v3 S32) (?v4 S56)) (let ((?v_0 (f53 f54 ?v1))) (=> (= (f82 ?v0 ?v1) f1) (=> (= (f83 (f52 (f53 f54 ?v2) ?v3) (f84 ?v4 ?v1)) f1) (= (f85 (f86 (f52 ?v_0 ?v2) (f52 ?v_0 ?v3)) (f87 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S40) (?v1 S28) (?v2 S28) (?v3 S28) (?v4 S59)) (let ((?v_0 (f59 f60 ?v1))) (=> (= (f61 ?v0 ?v1) f1) (=> (= (f88 (f58 (f59 f60 ?v2) ?v3) (f89 ?v4 ?v1)) f1) (= (f90 (f91 (f58 ?v_0 ?v2) (f58 ?v_0 ?v3)) (f92 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S52) (?v1 S51) (?v2 S51) (?v3 S51) (?v4 S62)) (let ((?v_0 (f96 f97 ?v1))) (=> (= (f93 ?v0 ?v1) f1) (=> (= (f94 (f95 (f96 f97 ?v2) ?v3) (f98 ?v4 ?v1)) f1) (= (f99 (f100 (f95 ?v_0 ?v2) (f95 ?v_0 ?v3)) (f101 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S69) (?v1 S17) (?v2 S17) (?v3 S17) (?v4 S70)) (let ((?v_0 (f77 f78 ?v1))) (=> (= (f102 ?v0 ?v1) f1) (=> (= (f75 (f76 (f77 f78 ?v2) ?v3) (f103 ?v4 ?v1)) f1) (= (f94 (f95 (f96 f97 (f76 ?v_0 ?v2)) (f76 ?v_0 ?v3)) (f104 (f105 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S22) (?v1 S21) (?v2 S21) (?v3 S21) (?v4 S72)) (let ((?v_0 (f50 f51 ?v1))) (=> (= (f62 ?v0 ?v1) f1) (=> (= (f72 (f49 (f50 f51 ?v2) ?v3) (f106 ?v4 ?v1)) f1) (= (f88 (f58 (f59 f60 (f49 ?v_0 ?v2)) (f49 ?v_0 ?v3)) (f107 (f108 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S14) (?v3 S14) (?v4 S74)) (let ((?v_0 (f56 f57 ?v1))) (=> (= (f23 ?v0 ?v1) f1) (=> (= (f66 (f55 (f56 f57 ?v2) ?v3) (f109 ?v4 ?v1)) f1) (= (f83 (f52 (f53 f54 (f55 ?v_0 ?v2)) (f55 ?v_0 ?v3)) (f110 (f111 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S17) (?v3 S6) (?v4 S4) (?v5 S17) (?v6 S3) (?v7 S17)) (let ((?v_0 (f42 f43 ?v0)) (?v_1 (f27 f28 ?v1)) (?v_2 (f42 f43 ?v3)) (?v_3 (f27 f28 ?v4)) (?v_5 (f45 ?v6)) (?v_4 (f113 ?v7))) (=> (= (f37 (f38 (f39 f40 (f41 ?v_0 (f26 ?v_1 ?v2))) (f41 ?v_2 (f26 ?v_3 ?v5))) ?v_5) f1) (= (f37 (f38 (f39 f40 (f41 ?v_0 (f26 ?v_1 (f112 ?v_4 ?v2)))) (f41 ?v_2 (f26 ?v_3 (f112 ?v_4 ?v5)))) ?v_5) f1)))))
(assert (forall ((?v0 S47)) (= (forall ((?v1 S24)) (= (f70 ?v0 ?v1) f1)) (forall ((?v1 S6) (?v2 S14)) (= (f70 ?v0 (f41 (f42 f43 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S22)) (= (forall ((?v1 S21)) (= (f62 ?v0 ?v1) f1)) (forall ((?v1 S24) (?v2 S24)) (= (f62 ?v0 (f38 (f39 f40 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S13)) (= (forall ((?v1 S14)) (= (f23 ?v0 ?v1) f1)) (forall ((?v1 S4) (?v2 S17)) (= (f23 ?v0 (f26 (f27 f28 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S41)) (= (forall ((?v1 S31)) (= (f63 ?v0 ?v1) f1)) (forall ((?v1 S32) (?v2 S32)) (= (f63 ?v0 (f52 (f53 f54 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S42)) (= (forall ((?v1 S37)) (= (f64 ?v0 ?v1) f1)) (forall ((?v1 S28) (?v2 S28)) (= (f64 ?v0 (f58 (f59 f60 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S64)) (= (forall ((?v1 S63)) (= (f114 ?v0 ?v1) f1)) (forall ((?v1 S51) (?v2 S51)) (= (f114 ?v0 (f95 (f96 f97 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S52)) (= (forall ((?v1 S51)) (= (f93 ?v0 ?v1) f1)) (forall ((?v1 S17) (?v2 S17)) (= (f93 ?v0 (f76 (f77 f78 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S40)) (= (forall ((?v1 S28)) (= (f61 ?v0 ?v1) f1)) (forall ((?v1 S21) (?v2 S21)) (= (f61 ?v0 (f49 (f50 f51 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S45)) (= (forall ((?v1 S32)) (= (f82 ?v0 ?v1) f1)) (forall ((?v1 S14) (?v2 S14)) (= (f82 ?v0 (f55 (f56 f57 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S6) (?v1 S14) (?v2 S6) (?v3 S14)) (= (= (f41 (f42 f43 ?v0) ?v1) (f41 (f42 f43 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24) (?v3 S24)) (= (= (f38 (f39 f40 ?v0) ?v1) (f38 (f39 f40 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S17) (?v2 S4) (?v3 S17)) (= (= (f26 (f27 f28 ?v0) ?v1) (f26 (f27 f28 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S32) (?v1 S32) (?v2 S32) (?v3 S32)) (= (= (f52 (f53 f54 ?v0) ?v1) (f52 (f53 f54 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (= (= (f58 (f59 f60 ?v0) ?v1) (f58 (f59 f60 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S51) (?v1 S51) (?v2 S51) (?v3 S51)) (= (= (f95 (f96 f97 ?v0) ?v1) (f95 (f96 f97 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17) (?v3 S17)) (= (= (f76 (f77 f78 ?v0) ?v1) (f76 (f77 f78 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21) (?v3 S21)) (= (= (f49 (f50 f51 ?v0) ?v1) (f49 (f50 f51 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (= (= (f55 (f56 f57 ?v0) ?v1) (f55 (f56 f57 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S6) (?v1 S14) (?v2 S6) (?v3 S14)) (=> (= (f41 (f42 f43 ?v0) ?v1) (f41 (f42 f43 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24) (?v3 S24)) (=> (= (f38 (f39 f40 ?v0) ?v1) (f38 (f39 f40 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S4) (?v1 S17) (?v2 S4) (?v3 S17)) (=> (= (f26 (f27 f28 ?v0) ?v1) (f26 (f27 f28 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S32) (?v1 S32) (?v2 S32) (?v3 S32)) (=> (= (f52 (f53 f54 ?v0) ?v1) (f52 (f53 f54 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f58 (f59 f60 ?v0) ?v1) (f58 (f59 f60 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S51) (?v1 S51) (?v2 S51) (?v3 S51)) (=> (= (f95 (f96 f97 ?v0) ?v1) (f95 (f96 f97 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17) (?v3 S17)) (=> (= (f76 (f77 f78 ?v0) ?v1) (f76 (f77 f78 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21) (?v3 S21)) (=> (= (f49 (f50 f51 ?v0) ?v1) (f49 (f50 f51 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (=> (= (f55 (f56 f57 ?v0) ?v1) (f55 (f56 f57 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f34 ?v0 (f115 (f116 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S17) (?v1 S17)) (= (f102 (f117 ?v0) (f112 (f113 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S5) (?v1 S5)) (let ((?v_0 (f115 (f116 ?v0) ?v1))) (= (= (f34 ?v0 ?v_0) f1) (= ?v_0 (f115 (f116 ?v1) ?v0))))))
(assert (forall ((?v0 S17) (?v1 S17)) (let ((?v_0 (f112 (f113 ?v0) ?v1))) (= (= (f102 (f117 ?v0) ?v_0) f1) (= ?v_0 (f112 (f113 ?v1) ?v0))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f115 (f116 ?v0) ?v2))) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f34 ?v2 ?v1) f1) (=> (= (f34 ?v0 ?v_0) f1) (= (f34 ?v_0 ?v1) f1)))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17)) (let ((?v_0 (f117 ?v0)) (?v_1 (f112 (f113 ?v0) ?v2))) (=> (= (f102 ?v_0 ?v1) f1) (=> (= (f102 (f117 ?v2) ?v1) f1) (=> (= (f102 ?v_0 ?v_1) f1) (= (f102 (f117 ?v_1) ?v1) f1)))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f34 (f115 (f116 ?v0) ?v1) ?v2) f1) (= (f34 ?v1 ?v2) f1))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17)) (=> (= (f102 (f117 (f112 (f113 ?v0) ?v1)) ?v2) f1) (= (f102 (f117 ?v1) ?v2) f1))))
(assert (forall ((?v0 S40) (?v1 S28)) (=> (forall ((?v2 S21) (?v3 S24) (?v4 S24)) (= (f61 ?v0 (f49 (f50 f51 ?v2) (f38 (f39 f40 ?v3) ?v4))) f1)) (= (f61 ?v0 ?v1) f1))))
(assert (forall ((?v0 S45) (?v1 S32)) (=> (forall ((?v2 S14) (?v3 S4) (?v4 S17)) (= (f82 ?v0 (f55 (f56 f57 ?v2) (f26 (f27 f28 ?v3) ?v4))) f1)) (= (f82 ?v0 ?v1) f1))))
(assert (forall ((?v0 S47) (?v1 S24)) (=> (forall ((?v2 S6) (?v3 S4) (?v4 S17)) (= (f70 ?v0 (f41 (f42 f43 ?v2) (f26 (f27 f28 ?v3) ?v4))) f1)) (= (f70 ?v0 ?v1) f1))))
(assert (forall ((?v0 S22) (?v1 S21)) (=> (forall ((?v2 S24) (?v3 S6) (?v4 S14)) (= (f62 ?v0 (f38 (f39 f40 ?v2) (f41 (f42 f43 ?v3) ?v4))) f1)) (= (f62 ?v0 ?v1) f1))))
(assert (forall ((?v0 S64) (?v1 S63)) (=> (forall ((?v2 S51) (?v3 S17) (?v4 S17)) (= (f114 ?v0 (f95 (f96 f97 ?v2) (f76 (f77 f78 ?v3) ?v4))) f1)) (= (f114 ?v0 ?v1) f1))))
(assert (forall ((?v0 S42) (?v1 S37)) (=> (forall ((?v2 S28) (?v3 S21) (?v4 S21)) (= (f64 ?v0 (f58 (f59 f60 ?v2) (f49 (f50 f51 ?v3) ?v4))) f1)) (= (f64 ?v0 ?v1) f1))))
(assert (forall ((?v0 S41) (?v1 S31)) (=> (forall ((?v2 S32) (?v3 S14) (?v4 S14)) (= (f63 ?v0 (f52 (f53 f54 ?v2) (f55 (f56 f57 ?v3) ?v4))) f1)) (= (f63 ?v0 ?v1) f1))))
(assert (forall ((?v0 S28)) (=> (forall ((?v1 S21) (?v2 S24) (?v3 S24)) (=> (= ?v0 (f49 (f50 f51 ?v1) (f38 (f39 f40 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S32)) (=> (forall ((?v1 S14) (?v2 S4) (?v3 S17)) (=> (= ?v0 (f55 (f56 f57 ?v1) (f26 (f27 f28 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S24)) (=> (forall ((?v1 S6) (?v2 S4) (?v3 S17)) (=> (= ?v0 (f41 (f42 f43 ?v1) (f26 (f27 f28 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S21)) (=> (forall ((?v1 S24) (?v2 S6) (?v3 S14)) (=> (= ?v0 (f38 (f39 f40 ?v1) (f41 (f42 f43 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S63)) (=> (forall ((?v1 S51) (?v2 S17) (?v3 S17)) (=> (= ?v0 (f95 (f96 f97 ?v1) (f76 (f77 f78 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S37)) (=> (forall ((?v1 S28) (?v2 S21) (?v3 S21)) (=> (= ?v0 (f58 (f59 f60 ?v1) (f49 (f50 f51 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S31)) (=> (forall ((?v1 S32) (?v2 S14) (?v3 S14)) (=> (= ?v0 (f52 (f53 f54 ?v1) (f55 (f56 f57 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S17) (?v3 S6) (?v4 S4) (?v5 S17) (?v6 S3) (?v7 S17)) (let ((?v_0 (f42 f43 ?v0)) (?v_1 (f27 f28 ?v1)) (?v_2 (f42 f43 ?v3)) (?v_3 (f27 f28 ?v4)) (?v_5 (f118 (f45 ?v6))) (?v_4 (f113 ?v7))) (=> (= (f37 (f38 (f39 f40 (f41 ?v_0 (f26 ?v_1 ?v2))) (f41 ?v_2 (f26 ?v_3 ?v5))) ?v_5) f1) (= (f37 (f38 (f39 f40 (f41 ?v_0 (f26 ?v_1 (f112 ?v_4 ?v2)))) (f41 ?v_2 (f26 ?v_3 (f112 ?v_4 ?v5)))) ?v_5) f1)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17)) (let ((?v_0 (f113 ?v0))) (= (f112 ?v_0 (f112 (f113 ?v1) ?v2)) (f112 (f113 (f112 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f116 ?v0))) (= (f115 ?v_0 (f115 (f116 ?v1) ?v2)) (f115 (f116 (f115 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f34 ?v1 ?v2) f1) (= (f34 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17)) (let ((?v_0 (f117 ?v0))) (=> (= (f102 ?v_0 ?v1) f1) (=> (= (f102 (f117 ?v1) ?v2) f1) (= (f102 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f34 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S17) (?v1 S17)) (=> (= (f102 (f117 ?v0) ?v1) f1) (=> (= (f102 (f117 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5)) (= (f34 ?v0 ?v0) f1)))
(assert (forall ((?v0 S17)) (= (f102 (f117 ?v0) ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S14) (?v2 S6) (?v3 S14) (?v4 S3) (?v5 S9) (?v6 S9) (?v7 S6)) (let ((?v_0 (f118 (f45 ?v4)))) (=> (= (f37 (f38 (f39 f40 (f41 (f42 f43 ?v0) ?v1)) (f41 (f42 f43 ?v2) ?v3)) ?v_0) f1) (= (f37 (f38 (f39 f40 (f41 (f42 f43 (f9 (f10 (f11 (f12 f13 ?v0) ?v5) ?v6) ?v7)) ?v1)) (f41 (f42 f43 (f9 (f10 (f11 (f12 f13 ?v2) ?v5) ?v6) ?v7)) ?v3)) ?v_0) f1)))))
(assert (forall ((?v0 S6) (?v1 S14) (?v2 S6) (?v3 S14) (?v4 S3) (?v5 S6)) (let ((?v_0 (f118 (f45 ?v4)))) (=> (= (f37 (f38 (f39 f40 (f41 (f42 f43 ?v0) ?v1)) (f41 (f42 f43 ?v2) ?v3)) ?v_0) f1) (= (f37 (f38 (f39 f40 (f41 (f42 f43 (f9 (f35 f36 ?v0) ?v5)) ?v1)) (f41 (f42 f43 (f9 (f35 f36 ?v2) ?v5)) ?v3)) ?v_0) f1)))))
(assert (forall ((?v0 S24) (?v1 S22)) (= (f37 (f38 (f39 f40 ?v0) ?v0) (f118 ?v1)) f1)))
(assert (forall ((?v0 S32) (?v1 S41)) (= (f83 (f52 (f53 f54 ?v0) ?v0) (f119 ?v1)) f1)))
(assert (forall ((?v0 S28) (?v1 S42)) (= (f88 (f58 (f59 f60 ?v0) ?v0) (f120 ?v1)) f1)))
(assert (forall ((?v0 S51) (?v1 S64)) (= (f94 (f95 (f96 f97 ?v0) ?v0) (f121 ?v1)) f1)))
(assert (forall ((?v0 S17) (?v1 S52)) (= (f75 (f76 (f77 f78 ?v0) ?v0) (f122 ?v1)) f1)))
(assert (forall ((?v0 S21) (?v1 S40)) (= (f72 (f49 (f50 f51 ?v0) ?v0) (f123 ?v1)) f1)))
(assert (forall ((?v0 S14) (?v1 S45)) (= (f66 (f55 (f56 f57 ?v0) ?v0) (f124 ?v1)) f1)))
(assert (forall ((?v0 S21) (?v1 S22)) (=> (= (f37 ?v0 ?v1) f1) (= (f37 ?v0 (f118 ?v1)) f1))))
(assert (forall ((?v0 S31) (?v1 S41)) (=> (= (f83 ?v0 ?v1) f1) (= (f83 ?v0 (f119 ?v1)) f1))))
(assert (forall ((?v0 S37) (?v1 S42)) (=> (= (f88 ?v0 ?v1) f1) (= (f88 ?v0 (f120 ?v1)) f1))))
(assert (forall ((?v0 S63) (?v1 S64)) (=> (= (f94 ?v0 ?v1) f1) (= (f94 ?v0 (f121 ?v1)) f1))))
(assert (forall ((?v0 S51) (?v1 S52)) (=> (= (f75 ?v0 ?v1) f1) (= (f75 ?v0 (f122 ?v1)) f1))))
(assert (forall ((?v0 S28) (?v1 S40)) (=> (= (f72 ?v0 ?v1) f1) (= (f72 ?v0 (f123 ?v1)) f1))))
(assert (forall ((?v0 S32) (?v1 S45)) (=> (= (f66 ?v0 ?v1) f1) (= (f66 ?v0 (f124 ?v1)) f1))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S22) (?v3 S24)) (let ((?v_1 (f39 f40 ?v0)) (?v_0 (f118 ?v2))) (=> (= (f37 (f38 ?v_1 ?v1) ?v_0) f1) (=> (= (f37 (f38 (f39 f40 ?v1) ?v3) ?v_0) f1) (= (f37 (f38 ?v_1 ?v3) ?v_0) f1))))))
(assert (forall ((?v0 S32) (?v1 S32) (?v2 S41) (?v3 S32)) (let ((?v_1 (f53 f54 ?v0)) (?v_0 (f119 ?v2))) (=> (= (f83 (f52 ?v_1 ?v1) ?v_0) f1) (=> (= (f83 (f52 (f53 f54 ?v1) ?v3) ?v_0) f1) (= (f83 (f52 ?v_1 ?v3) ?v_0) f1))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S42) (?v3 S28)) (let ((?v_1 (f59 f60 ?v0)) (?v_0 (f120 ?v2))) (=> (= (f88 (f58 ?v_1 ?v1) ?v_0) f1) (=> (= (f88 (f58 (f59 f60 ?v1) ?v3) ?v_0) f1) (= (f88 (f58 ?v_1 ?v3) ?v_0) f1))))))
(assert (forall ((?v0 S51) (?v1 S51) (?v2 S64) (?v3 S51)) (let ((?v_1 (f96 f97 ?v0)) (?v_0 (f121 ?v2))) (=> (= (f94 (f95 ?v_1 ?v1) ?v_0) f1) (=> (= (f94 (f95 (f96 f97 ?v1) ?v3) ?v_0) f1) (= (f94 (f95 ?v_1 ?v3) ?v_0) f1))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S52) (?v3 S17)) (let ((?v_1 (f77 f78 ?v0)) (?v_0 (f122 ?v2))) (=> (= (f75 (f76 ?v_1 ?v1) ?v_0) f1) (=> (= (f75 (f76 (f77 f78 ?v1) ?v3) ?v_0) f1) (= (f75 (f76 ?v_1 ?v3) ?v_0) f1))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S40) (?v3 S21)) (let ((?v_1 (f50 f51 ?v0)) (?v_0 (f123 ?v2))) (=> (= (f72 (f49 ?v_1 ?v1) ?v_0) f1) (=> (= (f72 (f49 (f50 f51 ?v1) ?v3) ?v_0) f1) (= (f72 (f49 ?v_1 ?v3) ?v_0) f1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S45) (?v3 S14)) (let ((?v_1 (f56 f57 ?v0)) (?v_0 (f124 ?v2))) (=> (= (f66 (f55 ?v_1 ?v1) ?v_0) f1) (=> (= (f66 (f55 (f56 f57 ?v1) ?v3) ?v_0) f1) (= (f66 (f55 ?v_1 ?v3) ?v_0) f1))))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S22) (?v3 S24)) (let ((?v_0 (f39 f40 ?v0)) (?v_1 (f118 ?v2))) (=> (= (f37 (f38 ?v_0 ?v1) ?v_1) f1) (=> (= (f37 (f38 (f39 f40 ?v1) ?v3) ?v2) f1) (= (f37 (f38 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S32) (?v1 S32) (?v2 S41) (?v3 S32)) (let ((?v_0 (f53 f54 ?v0)) (?v_1 (f119 ?v2))) (=> (= (f83 (f52 ?v_0 ?v1) ?v_1) f1) (=> (= (f83 (f52 (f53 f54 ?v1) ?v3) ?v2) f1) (= (f83 (f52 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S42) (?v3 S28)) (let ((?v_0 (f59 f60 ?v0)) (?v_1 (f120 ?v2))) (=> (= (f88 (f58 ?v_0 ?v1) ?v_1) f1) (=> (= (f88 (f58 (f59 f60 ?v1) ?v3) ?v2) f1) (= (f88 (f58 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S51) (?v1 S51) (?v2 S64) (?v3 S51)) (let ((?v_0 (f96 f97 ?v0)) (?v_1 (f121 ?v2))) (=> (= (f94 (f95 ?v_0 ?v1) ?v_1) f1) (=> (= (f94 (f95 (f96 f97 ?v1) ?v3) ?v2) f1) (= (f94 (f95 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S52) (?v3 S17)) (let ((?v_0 (f77 f78 ?v0)) (?v_1 (f122 ?v2))) (=> (= (f75 (f76 ?v_0 ?v1) ?v_1) f1) (=> (= (f75 (f76 (f77 f78 ?v1) ?v3) ?v2) f1) (= (f75 (f76 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S40) (?v3 S21)) (let ((?v_0 (f50 f51 ?v0)) (?v_1 (f123 ?v2))) (=> (= (f72 (f49 ?v_0 ?v1) ?v_1) f1) (=> (= (f72 (f49 (f50 f51 ?v1) ?v3) ?v2) f1) (= (f72 (f49 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S45) (?v3 S14)) (let ((?v_0 (f56 f57 ?v0)) (?v_1 (f124 ?v2))) (=> (= (f66 (f55 ?v_0 ?v1) ?v_1) f1) (=> (= (f66 (f55 (f56 f57 ?v1) ?v3) ?v2) f1) (= (f66 (f55 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S22) (?v3 S24)) (let ((?v_0 (f39 f40 ?v0)) (?v_1 (f118 ?v2))) (=> (= (f37 (f38 ?v_0 ?v1) ?v2) f1) (=> (= (f37 (f38 (f39 f40 ?v1) ?v3) ?v_1) f1) (= (f37 (f38 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S32) (?v1 S32) (?v2 S41) (?v3 S32)) (let ((?v_0 (f53 f54 ?v0)) (?v_1 (f119 ?v2))) (=> (= (f83 (f52 ?v_0 ?v1) ?v2) f1) (=> (= (f83 (f52 (f53 f54 ?v1) ?v3) ?v_1) f1) (= (f83 (f52 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S42) (?v3 S28)) (let ((?v_0 (f59 f60 ?v0)) (?v_1 (f120 ?v2))) (=> (= (f88 (f58 ?v_0 ?v1) ?v2) f1) (=> (= (f88 (f58 (f59 f60 ?v1) ?v3) ?v_1) f1) (= (f88 (f58 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S51) (?v1 S51) (?v2 S64) (?v3 S51)) (let ((?v_0 (f96 f97 ?v0)) (?v_1 (f121 ?v2))) (=> (= (f94 (f95 ?v_0 ?v1) ?v2) f1) (=> (= (f94 (f95 (f96 f97 ?v1) ?v3) ?v_1) f1) (= (f94 (f95 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S52) (?v3 S17)) (let ((?v_0 (f77 f78 ?v0)) (?v_1 (f122 ?v2))) (=> (= (f75 (f76 ?v_0 ?v1) ?v2) f1) (=> (= (f75 (f76 (f77 f78 ?v1) ?v3) ?v_1) f1) (= (f75 (f76 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S40) (?v3 S21)) (let ((?v_0 (f50 f51 ?v0)) (?v_1 (f123 ?v2))) (=> (= (f72 (f49 ?v_0 ?v1) ?v2) f1) (=> (= (f72 (f49 (f50 f51 ?v1) ?v3) ?v_1) f1) (= (f72 (f49 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S45) (?v3 S14)) (let ((?v_0 (f56 f57 ?v0)) (?v_1 (f124 ?v2))) (=> (= (f66 (f55 ?v_0 ?v1) ?v2) f1) (=> (= (f66 (f55 (f56 f57 ?v1) ?v3) ?v_1) f1) (= (f66 (f55 ?v_0 ?v3) ?v_1) f1))))))
(check-sat)
(exit)