(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status sat)
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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S5) S1)
(declare-fun f4 (S6 S7) S4)
(declare-fun f5 (S8 S7) S6)
(declare-fun f6 () S8)
(declare-fun f7 (S9 S3) S7)
(declare-fun f8 (S10 S2) S9)
(declare-fun f9 () S10)
(declare-fun f10 () S2)
(declare-fun f11 () S3)
(declare-fun f12 (S11) S5)
(declare-fun f13 () S11)
(declare-fun f14 (S11 S12 S3 S2 S13) S1)
(declare-fun f15 () S12)
(declare-fun f16 () S13)
(declare-fun f17 (S2 S14) S1)
(declare-fun f18 (S15) S14)
(declare-fun f19 (S16) S15)
(declare-fun f20 (S3) S16)
(declare-fun f21 (S2) S1)
(declare-fun f22 (S18 S17) S1)
(declare-fun f23 (S11) S18)
(declare-fun f24 (S11 S17 S12 S2 S13) S1)
(declare-fun f25 (S19 S16) S3)
(declare-fun f26 (S20 S17) S19)
(declare-fun f27 () S20)
(declare-fun f28 (S16 S21) S23)
(declare-fun f29 (S22) S23)
(declare-fun f30 (S21 S15) S1)
(declare-fun f31 (S24 S4) S23)
(declare-fun f32 (S24) S5)
(declare-fun f33 (S25 S26) S14)
(declare-fun f34 (S26 S27) S1)
(declare-fun f35 (S25) S27)
(declare-fun f36 (S28 S29) S14)
(declare-fun f37 (S29 S30) S1)
(declare-fun f38 (S28) S30)
(declare-fun f39 (S31 S32) S14)
(declare-fun f40 (S32 S33) S1)
(declare-fun f41 (S31) S33)
(declare-fun f42 (S34 S35) S14)
(declare-fun f43 (S35 S36) S1)
(declare-fun f44 (S34) S36)
(declare-fun f45 (S37 S38) S14)
(declare-fun f46 (S38 S39) S1)
(declare-fun f47 (S37) S39)
(declare-fun f48 (S40 S41) S14)
(declare-fun f49 (S41 S42) S1)
(declare-fun f50 (S40) S42)
(declare-fun f51 (S43 S21) S14)
(declare-fun f52 (S43) S15)
(declare-fun f53 (S44 S11) S1)
(declare-fun f54 () S44)
(declare-fun f55 (S33 S32) S1)
(declare-fun f56 (S45 S35) S32)
(declare-fun f57 (S46 S35) S45)
(declare-fun f58 () S46)
(declare-fun f59 (S47 S4) S35)
(declare-fun f60 (S48 S4) S47)
(declare-fun f61 () S48)
(declare-fun f62 (S36 S35) S1)
(declare-fun f63 (S5 S4) S1)
(declare-fun f64 (S27 S26) S1)
(declare-fun f65 (S49 S41) S26)
(declare-fun f66 (S50 S41) S49)
(declare-fun f67 () S50)
(declare-fun f68 (S51 S3) S41)
(declare-fun f69 (S52 S3) S51)
(declare-fun f70 () S52)
(declare-fun f71 (S53 S2) S1)
(declare-fun f72 (S54 S2) S42)
(declare-fun f73 (S55 S54) S5)
(declare-fun f74 (S53) S55)
(declare-fun f75 (S57 S16) S38)
(declare-fun f76 (S58 S16) S57)
(declare-fun f77 () S58)
(declare-fun f78 (S56 S17) S39)
(declare-fun f79 (S59 S56) S42)
(declare-fun f80 (S18) S59)
(declare-fun f81 (S60 S7) S1)
(declare-fun f82 (S61 S7) S5)
(declare-fun f83 (S62 S61) S36)
(declare-fun f84 (S60) S62)
(declare-fun f85 (S42 S41) S1)
(declare-fun f86 (S63 S41) S27)
(declare-fun f87 (S64 S65) S1)
(declare-fun f88 (S26 S26) S64)
(declare-fun f89 (S42 S63) S65)
(declare-fun f90 (S39 S38) S1)
(declare-fun f91 (S67 S38) S29)
(declare-fun f92 (S68 S38) S67)
(declare-fun f93 () S68)
(declare-fun f94 (S66 S38) S30)
(declare-fun f95 (S69 S70) S1)
(declare-fun f96 (S29 S29) S69)
(declare-fun f97 (S39 S66) S70)
(declare-fun f98 (S71 S35) S33)
(declare-fun f99 (S72 S73) S1)
(declare-fun f100 (S32 S32) S72)
(declare-fun f101 (S36 S71) S73)
(declare-fun f102 (S74 S4) S36)
(declare-fun f103 (S75 S74) S33)
(declare-fun f104 (S5) S75)
(declare-fun f105 (S76 S16) S1)
(declare-fun f106 (S77 S16) S39)
(declare-fun f107 (S78 S77) S30)
(declare-fun f108 (S76) S78)
(declare-fun f109 (S79 S3) S1)
(declare-fun f110 (S80 S3) S42)
(declare-fun f111 (S81 S80) S27)
(declare-fun f112 (S79) S81)
(declare-fun f113 (S30 S29) S1)
(declare-fun f114 (S5) S5)
(declare-fun f115 () S44)
(declare-fun f116 (S11 S17 S16 S12) S1)
(declare-fun f117 (S11 S13 S13) S1)
(declare-fun f118 (S27) S27)
(declare-fun f119 (S30) S30)
(declare-fun f120 (S33) S33)
(declare-fun f121 (S36) S36)
(declare-fun f122 (S39) S39)
(declare-fun f123 (S42) S42)
(declare-fun f124 (S82 S12) S79)
(declare-fun f125 (S11) S82)
(assert (not (= f1 f2)))
(assert (not (exists ((?v0 S2) (?v1 S3)) (= (f3 (f4 (f5 f6 (f7 (f8 f9 f10) f11)) (f7 (f8 f9 ?v0) ?v1)) (f12 f13)) f1))))
(assert (= (f14 f13 f15 f11 f10 f16) f1))
(assert (= (f17 f10 (f18 (f19 (f20 f11)))) f1))
(assert (not (= (f21 f10) f1)))
(assert (forall ((?v0 S17) (?v1 S12) (?v2 S2) (?v3 S13) (?v4 S16)) (=> (= (f22 (f23 f13) ?v0) f1) (=> (= (f24 f13 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f17 ?v2 (f18 (f19 ?v4))) f1) (=> (not (= (f21 ?v2) f1)) (exists ((?v5 S2) (?v6 S3)) (= (f3 (f4 (f5 f6 (f7 (f8 f9 ?v2) (f25 (f26 f27 ?v0) ?v4))) (f7 (f8 f9 ?v5) ?v6)) (f12 f13)) f1))))))))
(assert (forall ((?v0 S17) (?v1 S12) (?v2 S2) (?v3 S13) (?v4 S16)) (=> (= (f22 (f23 f13) ?v0) f1) (=> (= (f24 f13 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f17 ?v2 (f18 (f19 ?v4))) f1) (=> (not (= (f21 ?v2) f1)) (exists ((?v5 S2) (?v6 S3)) (= (f3 (f4 (f5 f6 (f7 (f8 f9 ?v2) (f25 (f26 f27 ?v0) ?v4))) (f7 (f8 f9 ?v5) ?v6)) (f12 f13)) f1))))))))
(assert (forall ((?v0 S16) (?v1 S21) (?v2 S22)) (=> (= (f28 ?v0 ?v1) (f29 ?v2)) (= (f30 ?v1 (f19 ?v0)) f1))))
(assert (forall ((?v0 S24) (?v1 S4) (?v2 S22)) (=> (= (f31 ?v0 ?v1) (f29 ?v2)) (= (f3 ?v1 (f32 ?v0)) f1))))
(assert (forall ((?v0 S25) (?v1 S26) (?v2 S15)) (=> (= (f33 ?v0 ?v1) (f18 ?v2)) (= (f34 ?v1 (f35 ?v0)) f1))))
(assert (forall ((?v0 S28) (?v1 S29) (?v2 S15)) (=> (= (f36 ?v0 ?v1) (f18 ?v2)) (= (f37 ?v1 (f38 ?v0)) f1))))
(assert (forall ((?v0 S31) (?v1 S32) (?v2 S15)) (=> (= (f39 ?v0 ?v1) (f18 ?v2)) (= (f40 ?v1 (f41 ?v0)) f1))))
(assert (forall ((?v0 S34) (?v1 S35) (?v2 S15)) (=> (= (f42 ?v0 ?v1) (f18 ?v2)) (= (f43 ?v1 (f44 ?v0)) f1))))
(assert (forall ((?v0 S37) (?v1 S38) (?v2 S15)) (=> (= (f45 ?v0 ?v1) (f18 ?v2)) (= (f46 ?v1 (f47 ?v0)) f1))))
(assert (forall ((?v0 S40) (?v1 S41) (?v2 S15)) (=> (= (f48 ?v0 ?v1) (f18 ?v2)) (= (f49 ?v1 (f50 ?v0)) f1))))
(assert (forall ((?v0 S43) (?v1 S21) (?v2 S15)) (=> (= (f51 ?v0 ?v1) (f18 ?v2)) (= (f30 ?v1 (f52 ?v0)) f1))))
(assert (= (f53 f54 f13) f1))
(assert (forall ((?v0 S33) (?v1 S32)) (=> (forall ((?v2 S35) (?v3 S4) (?v4 S7) (?v5 S2) (?v6 S17) (?v7 S16)) (= (f55 ?v0 (f56 (f57 f58 ?v2) (f59 (f60 f61 ?v3) (f4 (f5 f6 ?v4) (f7 (f8 f9 ?v5) (f25 (f26 f27 ?v6) ?v7)))))) f1)) (= (f55 ?v0 ?v1) f1))))
(assert (forall ((?v0 S32)) (=> (forall ((?v1 S35) (?v2 S4) (?v3 S7) (?v4 S2) (?v5 S17) (?v6 S16)) (=> (= ?v0 (f56 (f57 f58 ?v1) (f59 (f60 f61 ?v2) (f4 (f5 f6 ?v3) (f7 (f8 f9 ?v4) (f25 (f26 f27 ?v5) ?v6)))))) false)) false)))
(assert (forall ((?v0 S36) (?v1 S35)) (=> (forall ((?v2 S4) (?v3 S7) (?v4 S2) (?v5 S17) (?v6 S16)) (= (f62 ?v0 (f59 (f60 f61 ?v2) (f4 (f5 f6 ?v3) (f7 (f8 f9 ?v4) (f25 (f26 f27 ?v5) ?v6))))) f1)) (= (f62 ?v0 ?v1) f1))))
(assert (forall ((?v0 S33) (?v1 S32)) (=> (forall ((?v2 S35) (?v3 S4) (?v4 S7) (?v5 S2) (?v6 S3)) (= (f55 ?v0 (f56 (f57 f58 ?v2) (f59 (f60 f61 ?v3) (f4 (f5 f6 ?v4) (f7 (f8 f9 ?v5) ?v6))))) f1)) (= (f55 ?v0 ?v1) f1))))
(assert (forall ((?v0 S35)) (=> (forall ((?v1 S4) (?v2 S7) (?v3 S2) (?v4 S17) (?v5 S16)) (=> (= ?v0 (f59 (f60 f61 ?v1) (f4 (f5 f6 ?v2) (f7 (f8 f9 ?v3) (f25 (f26 f27 ?v4) ?v5))))) false)) false)))
(assert (forall ((?v0 S32)) (=> (forall ((?v1 S35) (?v2 S4) (?v3 S7) (?v4 S2) (?v5 S3)) (=> (= ?v0 (f56 (f57 f58 ?v1) (f59 (f60 f61 ?v2) (f4 (f5 f6 ?v3) (f7 (f8 f9 ?v4) ?v5))))) false)) false)))
(assert (forall ((?v0 S36) (?v1 S35)) (=> (forall ((?v2 S4) (?v3 S7) (?v4 S2) (?v5 S3)) (= (f62 ?v0 (f59 (f60 f61 ?v2) (f4 (f5 f6 ?v3) (f7 (f8 f9 ?v4) ?v5)))) f1)) (= (f62 ?v0 ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S4)) (=> (forall ((?v2 S7) (?v3 S2) (?v4 S17) (?v5 S16)) (= (f63 ?v0 (f4 (f5 f6 ?v2) (f7 (f8 f9 ?v3) (f25 (f26 f27 ?v4) ?v5)))) f1)) (= (f63 ?v0 ?v1) f1))))
(assert (forall ((?v0 S27) (?v1 S26)) (=> (forall ((?v2 S41) (?v3 S3) (?v4 S17) (?v5 S16)) (= (f64 ?v0 (f65 (f66 f67 ?v2) (f68 (f69 f70 ?v3) (f25 (f26 f27 ?v4) ?v5)))) f1)) (= (f64 ?v0 ?v1) f1))))
(assert (forall ((?v0 S33) (?v1 S32)) (=> (forall ((?v2 S35) (?v3 S4) (?v4 S7) (?v5 S7)) (= (f55 ?v0 (f56 (f57 f58 ?v2) (f59 (f60 f61 ?v3) (f4 (f5 f6 ?v4) ?v5)))) f1)) (= (f55 ?v0 ?v1) f1))))
(assert (forall ((?v0 S35)) (=> (forall ((?v1 S4) (?v2 S7) (?v3 S2) (?v4 S3)) (=> (= ?v0 (f59 (f60 f61 ?v1) (f4 (f5 f6 ?v2) (f7 (f8 f9 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S7) (?v2 S2) (?v3 S17) (?v4 S16)) (=> (= ?v0 (f4 (f5 f6 ?v1) (f7 (f8 f9 ?v2) (f25 (f26 f27 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S41) (?v2 S3) (?v3 S17) (?v4 S16)) (=> (= ?v0 (f65 (f66 f67 ?v1) (f68 (f69 f70 ?v2) (f25 (f26 f27 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S32)) (=> (forall ((?v1 S35) (?v2 S4) (?v3 S7) (?v4 S7)) (=> (= ?v0 (f56 (f57 f58 ?v1) (f59 (f60 f61 ?v2) (f4 (f5 f6 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S53) (?v1 S2) (?v2 S3) (?v3 S3) (?v4 S54)) (let ((?v_0 (f8 f9 ?v1))) (=> (= (f71 ?v0 ?v1) f1) (=> (= (f49 (f68 (f69 f70 ?v2) ?v3) (f72 ?v4 ?v1)) f1) (= (f3 (f4 (f5 f6 (f7 ?v_0 ?v2)) (f7 ?v_0 ?v3)) (f73 (f74 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S18) (?v1 S17) (?v2 S16) (?v3 S16) (?v4 S56)) (let ((?v_0 (f26 f27 ?v1))) (=> (= (f22 ?v0 ?v1) f1) (=> (= (f46 (f75 (f76 f77 ?v2) ?v3) (f78 ?v4 ?v1)) f1) (= (f49 (f68 (f69 f70 (f25 ?v_0 ?v2)) (f25 ?v_0 ?v3)) (f79 (f80 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S60) (?v1 S7) (?v2 S7) (?v3 S7) (?v4 S61)) (let ((?v_0 (f5 f6 ?v1))) (=> (= (f81 ?v0 ?v1) f1) (=> (= (f3 (f4 (f5 f6 ?v2) ?v3) (f82 ?v4 ?v1)) f1) (= (f43 (f59 (f60 f61 (f4 ?v_0 ?v2)) (f4 ?v_0 ?v3)) (f83 (f84 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S42) (?v1 S41) (?v2 S41) (?v3 S41) (?v4 S63)) (let ((?v_0 (f66 f67 ?v1))) (=> (= (f85 ?v0 ?v1) f1) (=> (= (f34 (f65 (f66 f67 ?v2) ?v3) (f86 ?v4 ?v1)) f1) (= (f87 (f88 (f65 ?v_0 ?v2) (f65 ?v_0 ?v3)) (f89 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S39) (?v1 S38) (?v2 S38) (?v3 S38) (?v4 S66)) (let ((?v_0 (f92 f93 ?v1))) (=> (= (f90 ?v0 ?v1) f1) (=> (= (f37 (f91 (f92 f93 ?v2) ?v3) (f94 ?v4 ?v1)) f1) (= (f95 (f96 (f91 ?v_0 ?v2) (f91 ?v_0 ?v3)) (f97 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S36) (?v1 S35) (?v2 S35) (?v3 S35) (?v4 S71)) (let ((?v_0 (f57 f58 ?v1))) (=> (= (f62 ?v0 ?v1) f1) (=> (= (f40 (f56 (f57 f58 ?v2) ?v3) (f98 ?v4 ?v1)) f1) (= (f99 (f100 (f56 ?v_0 ?v2) (f56 ?v_0 ?v3)) (f101 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S5) (?v1 S4) (?v2 S4) (?v3 S4) (?v4 S74)) (let ((?v_0 (f60 f61 ?v1))) (=> (= (f63 ?v0 ?v1) f1) (=> (= (f43 (f59 (f60 f61 ?v2) ?v3) (f102 ?v4 ?v1)) f1) (= (f40 (f56 (f57 f58 (f59 ?v_0 ?v2)) (f59 ?v_0 ?v3)) (f103 (f104 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S76) (?v1 S16) (?v2 S16) (?v3 S16) (?v4 S77)) (let ((?v_0 (f76 f77 ?v1))) (=> (= (f105 ?v0 ?v1) f1) (=> (= (f46 (f75 (f76 f77 ?v2) ?v3) (f106 ?v4 ?v1)) f1) (= (f37 (f91 (f92 f93 (f75 ?v_0 ?v2)) (f75 ?v_0 ?v3)) (f107 (f108 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S79) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S80)) (let ((?v_0 (f69 f70 ?v1))) (=> (= (f109 ?v0 ?v1) f1) (=> (= (f49 (f68 (f69 f70 ?v2) ?v3) (f110 ?v4 ?v1)) f1) (= (f34 (f65 (f66 f67 (f68 ?v_0 ?v2)) (f68 ?v_0 ?v3)) (f111 (f112 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S2) (?v1 S17) (?v2 S16) (?v3 S2) (?v4 S17) (?v5 S16) (?v6 S11) (?v7 S12) (?v8 S13)) (let ((?v_0 (f23 ?v6))) (=> (= (f3 (f4 (f5 f6 (f7 (f8 f9 ?v0) (f25 (f26 f27 ?v1) ?v2))) (f7 (f8 f9 ?v3) (f25 (f26 f27 ?v4) ?v5))) (f12 ?v6)) f1) (=> (= (f24 ?v6 ?v1 ?v7 ?v0 ?v8) f1) (=> (= (f22 ?v_0 ?v1) f1) (= (f22 ?v_0 ?v4) f1)))))))
(assert (forall ((?v0 S21) (?v1 S16)) (=> (= (f30 ?v0 (f19 ?v1)) f1) (exists ((?v2 S22)) (= (f28 ?v1 ?v0) (f29 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S24)) (=> (= (f3 ?v0 (f32 ?v1)) f1) (exists ((?v2 S22)) (= (f31 ?v1 ?v0) (f29 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S25)) (=> (= (f34 ?v0 (f35 ?v1)) f1) (exists ((?v2 S15)) (= (f33 ?v1 ?v0) (f18 ?v2))))))
(assert (forall ((?v0 S29) (?v1 S28)) (=> (= (f37 ?v0 (f38 ?v1)) f1) (exists ((?v2 S15)) (= (f36 ?v1 ?v0) (f18 ?v2))))))
(assert (forall ((?v0 S32) (?v1 S31)) (=> (= (f40 ?v0 (f41 ?v1)) f1) (exists ((?v2 S15)) (= (f39 ?v1 ?v0) (f18 ?v2))))))
(assert (forall ((?v0 S35) (?v1 S34)) (=> (= (f43 ?v0 (f44 ?v1)) f1) (exists ((?v2 S15)) (= (f42 ?v1 ?v0) (f18 ?v2))))))
(assert (forall ((?v0 S38) (?v1 S37)) (=> (= (f46 ?v0 (f47 ?v1)) f1) (exists ((?v2 S15)) (= (f45 ?v1 ?v0) (f18 ?v2))))))
(assert (forall ((?v0 S41) (?v1 S40)) (=> (= (f49 ?v0 (f50 ?v1)) f1) (exists ((?v2 S15)) (= (f48 ?v1 ?v0) (f18 ?v2))))))
(assert (forall ((?v0 S21) (?v1 S43)) (=> (= (f30 ?v0 (f52 ?v1)) f1) (exists ((?v2 S15)) (= (f51 ?v1 ?v0) (f18 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S17) (?v3 S16) (?v4 S2) (?v5 S17) (?v6 S16)) (=> (= (f53 f54 ?v0) f1) (=> (= (f3 (f4 (f5 f6 (f7 (f8 f9 ?v1) (f25 (f26 f27 ?v2) ?v3))) (f7 (f8 f9 ?v4) (f25 (f26 f27 ?v5) ?v6))) (f12 ?v0)) f1) (=> (= (f17 ?v1 (f18 (f19 ?v3))) f1) (= (f17 ?v4 (f18 (f19 ?v6))) f1))))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S17) (?v3 S16)) (=> (= (f25 (f26 f27 ?v0) ?v1) (f25 (f26 f27 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S3)) (=> (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (=> (= (f4 (f5 f6 ?v0) ?v1) (f4 (f5 f6 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S41) (?v1 S41) (?v2 S41) (?v3 S41)) (=> (= (f65 (f66 f67 ?v0) ?v1) (f65 (f66 f67 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S38) (?v1 S38) (?v2 S38) (?v3 S38)) (=> (= (f91 (f92 f93 ?v0) ?v1) (f91 (f92 f93 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35) (?v3 S35)) (=> (= (f56 (f57 f58 ?v0) ?v1) (f56 (f57 f58 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (=> (= (f59 (f60 f61 ?v0) ?v1) (f59 (f60 f61 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16) (?v3 S16)) (=> (= (f75 (f76 f77 ?v0) ?v1) (f75 (f76 f77 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f68 (f69 f70 ?v0) ?v1) (f68 (f69 f70 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S17) (?v3 S16)) (= (= (f25 (f26 f27 ?v0) ?v1) (f25 (f26 f27 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S3)) (= (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (= (= (f4 (f5 f6 ?v0) ?v1) (f4 (f5 f6 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S41) (?v1 S41) (?v2 S41) (?v3 S41)) (= (= (f65 (f66 f67 ?v0) ?v1) (f65 (f66 f67 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S38) (?v1 S38) (?v2 S38) (?v3 S38)) (= (= (f91 (f92 f93 ?v0) ?v1) (f91 (f92 f93 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35) (?v3 S35)) (= (= (f56 (f57 f58 ?v0) ?v1) (f56 (f57 f58 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (= (= (f59 (f60 f61 ?v0) ?v1) (f59 (f60 f61 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16) (?v3 S16)) (= (= (f75 (f76 f77 ?v0) ?v1) (f75 (f76 f77 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (= (f68 (f69 f70 ?v0) ?v1) (f68 (f69 f70 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S79)) (= (forall ((?v1 S3)) (= (f109 ?v0 ?v1) f1)) (forall ((?v1 S17) (?v2 S16)) (= (f109 ?v0 (f25 (f26 f27 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S60)) (= (forall ((?v1 S7)) (= (f81 ?v0 ?v1) f1)) (forall ((?v1 S2) (?v2 S3)) (= (f81 ?v0 (f7 (f8 f9 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S5)) (= (forall ((?v1 S4)) (= (f63 ?v0 ?v1) f1)) (forall ((?v1 S7) (?v2 S7)) (= (f63 ?v0 (f4 (f5 f6 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S27)) (= (forall ((?v1 S26)) (= (f64 ?v0 ?v1) f1)) (forall ((?v1 S41) (?v2 S41)) (= (f64 ?v0 (f65 (f66 f67 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S30)) (= (forall ((?v1 S29)) (= (f113 ?v0 ?v1) f1)) (forall ((?v1 S38) (?v2 S38)) (= (f113 ?v0 (f91 (f92 f93 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S33)) (= (forall ((?v1 S32)) (= (f55 ?v0 ?v1) f1)) (forall ((?v1 S35) (?v2 S35)) (= (f55 ?v0 (f56 (f57 f58 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S36)) (= (forall ((?v1 S35)) (= (f62 ?v0 ?v1) f1)) (forall ((?v1 S4) (?v2 S4)) (= (f62 ?v0 (f59 (f60 f61 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S39)) (= (forall ((?v1 S38)) (= (f90 ?v0 ?v1) f1)) (forall ((?v1 S16) (?v2 S16)) (= (f90 ?v0 (f75 (f76 f77 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S42)) (= (forall ((?v1 S41)) (= (f85 ?v0 ?v1) f1)) (forall ((?v1 S3) (?v2 S3)) (= (f85 ?v0 (f68 (f69 f70 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S3) (?v3 S2) (?v4 S3)) (=> (= (f53 f54 ?v0) f1) (=> (= (f3 (f4 (f5 f6 (f7 (f8 f9 ?v1) ?v2)) (f7 (f8 f9 ?v3) ?v4)) (f114 (f12 ?v0))) f1) (=> (= (f17 ?v1 (f18 (f19 (f20 ?v2)))) f1) (= (f17 ?v3 (f18 (f19 (f20 ?v4)))) f1))))))
(assert (forall ((?v0 S11) (?v1 S17) (?v2 S12) (?v3 S2) (?v4 S13) (?v5 S16)) (=> (= (f53 f115 ?v0) f1) (=> (= (f22 (f23 ?v0) ?v1) f1) (=> (= (f24 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f17 ?v3 (f18 (f19 ?v5))) f1) (=> (not (= (f21 ?v3) f1)) (exists ((?v6 S2) (?v7 S3)) (= (f3 (f4 (f5 f6 (f7 (f8 f9 ?v3) (f25 (f26 f27 ?v1) ?v5))) (f7 (f8 f9 ?v6) ?v7)) (f12 ?v0)) f1)))))))))
(assert (forall ((?v0 S2) (?v1 S17) (?v2 S16) (?v3 S2) (?v4 S17) (?v5 S16) (?v6 S11) (?v7 S12) (?v8 S13)) (=> (= (f3 (f4 (f5 f6 (f7 (f8 f9 ?v0) (f25 (f26 f27 ?v1) ?v2))) (f7 (f8 f9 ?v3) (f25 (f26 f27 ?v4) ?v5))) (f12 ?v6)) f1) (=> (= (f24 ?v6 ?v1 ?v7 ?v0 ?v8) f1) (=> (= (f116 ?v6 ?v1 ?v2 ?v7) f1) (= (f116 ?v6 ?v4 ?v5 ?v7) f1))))))
(assert (forall ((?v0 S41)) (=> (forall ((?v1 S3) (?v2 S17) (?v3 S16)) (=> (= ?v0 (f68 (f69 f70 ?v1) (f25 (f26 f27 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S35)) (=> (forall ((?v1 S4) (?v2 S7) (?v3 S7)) (=> (= ?v0 (f59 (f60 f61 ?v1) (f4 (f5 f6 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S7)) (=> (forall ((?v1 S2) (?v2 S17) (?v3 S16)) (=> (= ?v0 (f7 (f8 f9 ?v1) (f25 (f26 f27 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S7) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f4 (f5 f6 ?v1) (f7 (f8 f9 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S32)) (=> (forall ((?v1 S35) (?v2 S4) (?v3 S4)) (=> (= ?v0 (f56 (f57 f58 ?v1) (f59 (f60 f61 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S29)) (=> (forall ((?v1 S38) (?v2 S16) (?v3 S16)) (=> (= ?v0 (f91 (f92 f93 ?v1) (f75 (f76 f77 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S41) (?v2 S3) (?v3 S3)) (=> (= ?v0 (f65 (f66 f67 ?v1) (f68 (f69 f70 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S42) (?v1 S41)) (=> (forall ((?v2 S3) (?v3 S17) (?v4 S16)) (= (f85 ?v0 (f68 (f69 f70 ?v2) (f25 (f26 f27 ?v3) ?v4))) f1)) (= (f85 ?v0 ?v1) f1))))
(assert (forall ((?v0 S36) (?v1 S35)) (=> (forall ((?v2 S4) (?v3 S7) (?v4 S7)) (= (f62 ?v0 (f59 (f60 f61 ?v2) (f4 (f5 f6 ?v3) ?v4))) f1)) (= (f62 ?v0 ?v1) f1))))
(assert (forall ((?v0 S60) (?v1 S7)) (=> (forall ((?v2 S2) (?v3 S17) (?v4 S16)) (= (f81 ?v0 (f7 (f8 f9 ?v2) (f25 (f26 f27 ?v3) ?v4))) f1)) (= (f81 ?v0 ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S4)) (=> (forall ((?v2 S7) (?v3 S2) (?v4 S3)) (= (f63 ?v0 (f4 (f5 f6 ?v2) (f7 (f8 f9 ?v3) ?v4))) f1)) (= (f63 ?v0 ?v1) f1))))
(assert (forall ((?v0 S33) (?v1 S32)) (=> (forall ((?v2 S35) (?v3 S4) (?v4 S4)) (= (f55 ?v0 (f56 (f57 f58 ?v2) (f59 (f60 f61 ?v3) ?v4))) f1)) (= (f55 ?v0 ?v1) f1))))
(assert (forall ((?v0 S30) (?v1 S29)) (=> (forall ((?v2 S38) (?v3 S16) (?v4 S16)) (= (f113 ?v0 (f91 (f92 f93 ?v2) (f75 (f76 f77 ?v3) ?v4))) f1)) (= (f113 ?v0 ?v1) f1))))
(assert (forall ((?v0 S27) (?v1 S26)) (=> (forall ((?v2 S41) (?v3 S3) (?v4 S3)) (= (f64 ?v0 (f65 (f66 f67 ?v2) (f68 (f69 f70 ?v3) ?v4))) f1)) (= (f64 ?v0 ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S3) (?v3 S2) (?v4 S3) (?v5 S12) (?v6 S13)) (=> (= (f53 f54 ?v0) f1) (=> (= (f3 (f4 (f5 f6 (f7 (f8 f9 ?v1) ?v2)) (f7 (f8 f9 ?v3) ?v4)) (f12 ?v0)) f1) (=> (= (f14 ?v0 ?v5 ?v2 ?v1 ?v6) f1) (exists ((?v7 S13)) (and (= (f14 ?v0 ?v5 ?v4 ?v3 ?v7) f1) (= (f117 ?v0 ?v7 ?v6) f1))))))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S17) (?v2 S16)) (=> (= ?v0 (f25 (f26 f27 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S7)) (=> (forall ((?v1 S2) (?v2 S3)) (=> (= ?v0 (f7 (f8 f9 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S7) (?v2 S7)) (=> (= ?v0 (f4 (f5 f6 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S41) (?v2 S41)) (=> (= ?v0 (f65 (f66 f67 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S29)) (=> (forall ((?v1 S38) (?v2 S38)) (=> (= ?v0 (f91 (f92 f93 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S32)) (=> (forall ((?v1 S35) (?v2 S35)) (=> (= ?v0 (f56 (f57 f58 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S35)) (=> (forall ((?v1 S4) (?v2 S4)) (=> (= ?v0 (f59 (f60 f61 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S38)) (=> (forall ((?v1 S16) (?v2 S16)) (=> (= ?v0 (f75 (f76 f77 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S41)) (=> (forall ((?v1 S3) (?v2 S3)) (=> (= ?v0 (f68 (f69 f70 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S17) (?v2 S16)) (=> (= ?v0 (f25 (f26 f27 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S7)) (=> (forall ((?v1 S2) (?v2 S3)) (=> (= ?v0 (f7 (f8 f9 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S7) (?v2 S7)) (=> (= ?v0 (f4 (f5 f6 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S41) (?v2 S41)) (=> (= ?v0 (f65 (f66 f67 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S29)) (=> (forall ((?v1 S38) (?v2 S38)) (=> (= ?v0 (f91 (f92 f93 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S32)) (=> (forall ((?v1 S35) (?v2 S35)) (=> (= ?v0 (f56 (f57 f58 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S35)) (=> (forall ((?v1 S4) (?v2 S4)) (=> (= ?v0 (f59 (f60 f61 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S38)) (=> (forall ((?v1 S16) (?v2 S16)) (=> (= ?v0 (f75 (f76 f77 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S41)) (=> (forall ((?v1 S3) (?v2 S3)) (=> (= ?v0 (f68 (f69 f70 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S79)) (= (exists ((?v1 S3)) (= (f109 ?v0 ?v1) f1)) (exists ((?v1 S17) (?v2 S16)) (= (f109 ?v0 (f25 (f26 f27 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S60)) (= (exists ((?v1 S7)) (= (f81 ?v0 ?v1) f1)) (exists ((?v1 S2) (?v2 S3)) (= (f81 ?v0 (f7 (f8 f9 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S5)) (= (exists ((?v1 S4)) (= (f63 ?v0 ?v1) f1)) (exists ((?v1 S7) (?v2 S7)) (= (f63 ?v0 (f4 (f5 f6 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S27)) (= (exists ((?v1 S26)) (= (f64 ?v0 ?v1) f1)) (exists ((?v1 S41) (?v2 S41)) (= (f64 ?v0 (f65 (f66 f67 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S30)) (= (exists ((?v1 S29)) (= (f113 ?v0 ?v1) f1)) (exists ((?v1 S38) (?v2 S38)) (= (f113 ?v0 (f91 (f92 f93 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S33)) (= (exists ((?v1 S32)) (= (f55 ?v0 ?v1) f1)) (exists ((?v1 S35) (?v2 S35)) (= (f55 ?v0 (f56 (f57 f58 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S36)) (= (exists ((?v1 S35)) (= (f62 ?v0 ?v1) f1)) (exists ((?v1 S4) (?v2 S4)) (= (f62 ?v0 (f59 (f60 f61 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S39)) (= (exists ((?v1 S38)) (= (f90 ?v0 ?v1) f1)) (exists ((?v1 S16) (?v2 S16)) (= (f90 ?v0 (f75 (f76 f77 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S42)) (= (exists ((?v1 S41)) (= (f85 ?v0 ?v1) f1)) (exists ((?v1 S3) (?v2 S3)) (= (f85 ?v0 (f68 (f69 f70 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S3) (?v3 S2) (?v4 S3) (?v5 S12) (?v6 S13)) (=> (= (f53 f54 ?v0) f1) (=> (= (f3 (f4 (f5 f6 (f7 (f8 f9 ?v1) ?v2)) (f7 (f8 f9 ?v3) ?v4)) (f114 (f12 ?v0))) f1) (=> (= (f14 ?v0 ?v5 ?v2 ?v1 ?v6) f1) (exists ((?v7 S13)) (and (= (f14 ?v0 ?v5 ?v4 ?v3 ?v7) f1) (= (f117 ?v0 ?v7 ?v6) f1))))))))
(assert (forall ((?v0 S7) (?v1 S5)) (= (f3 (f4 (f5 f6 ?v0) ?v0) (f114 ?v1)) f1)))
(assert (forall ((?v0 S41) (?v1 S27)) (= (f34 (f65 (f66 f67 ?v0) ?v0) (f118 ?v1)) f1)))
(assert (forall ((?v0 S38) (?v1 S30)) (= (f37 (f91 (f92 f93 ?v0) ?v0) (f119 ?v1)) f1)))
(assert (forall ((?v0 S35) (?v1 S33)) (= (f40 (f56 (f57 f58 ?v0) ?v0) (f120 ?v1)) f1)))
(assert (forall ((?v0 S4) (?v1 S36)) (= (f43 (f59 (f60 f61 ?v0) ?v0) (f121 ?v1)) f1)))
(assert (forall ((?v0 S16) (?v1 S39)) (= (f46 (f75 (f76 f77 ?v0) ?v0) (f122 ?v1)) f1)))
(assert (forall ((?v0 S3) (?v1 S42)) (= (f49 (f68 (f69 f70 ?v0) ?v0) (f123 ?v1)) f1)))
(assert (forall ((?v0 S11)) (=> (= (f53 f54 ?v0) f1) (= (f53 f115 ?v0) f1))))
(assert (forall ((?v0 S11) (?v1 S13)) (= (f117 ?v0 ?v1 ?v1) f1)))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S17) (?v3 S16) (?v4 S2) (?v5 S17) (?v6 S16) (?v7 S12) (?v8 S13)) (let ((?v_0 (f25 (f26 f27 ?v2) ?v3))) (=> (= (f53 f54 ?v0) f1) (=> (= (f3 (f4 (f5 f6 (f7 (f8 f9 ?v1) ?v_0)) (f7 (f8 f9 ?v4) (f25 (f26 f27 ?v5) ?v6))) (f12 ?v0)) f1) (=> (= (f109 (f124 (f125 ?v0) ?v7) ?v_0) f1) (=> (= (f24 ?v0 ?v2 ?v7 ?v1 ?v8) f1) (exists ((?v9 S13)) (and (= (f24 ?v0 ?v5 ?v7 ?v4 ?v9) f1) (= (f117 ?v0 ?v9 ?v8) f1))))))))))
(check-sat)
(exit)
