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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S3) S1)
(declare-fun f4 (S5 S3) S4)
(declare-fun f5 (S2) S5)
(declare-fun f6 (S6 S2) S1)
(declare-fun f7 (S7 S3) S6)
(declare-fun f8 (S8 S3) S7)
(declare-fun f9 () S8)
(declare-fun f10 (S10 S9) S1)
(declare-fun f11 (S11 S9) S10)
(declare-fun f12 (S4) S11)
(declare-fun f13 (S3 S4) S1)
(declare-fun f14 (S12 S9) S3)
(declare-fun f15 (S13 S9) S12)
(declare-fun f16 () S13)
(declare-fun f17 (S16 S15) S1)
(declare-fun f18 (S17 S15) S16)
(declare-fun f19 (S14) S17)
(declare-fun f20 (S18 S14) S1)
(declare-fun f21 (S19 S15) S18)
(declare-fun f22 (S20 S15) S19)
(declare-fun f23 () S20)
(declare-fun f24 (S22 S21) S1)
(declare-fun f25 (S23 S21) S22)
(declare-fun f26 (S10) S23)
(declare-fun f27 (S9 S10) S1)
(declare-fun f28 (S24 S21) S9)
(declare-fun f29 (S25 S21) S24)
(declare-fun f30 () S25)
(declare-fun f31 (S28 S27) S1)
(declare-fun f32 (S29 S27) S28)
(declare-fun f33 (S26) S29)
(declare-fun f34 (S30 S26) S1)
(declare-fun f35 (S31 S27) S30)
(declare-fun f36 (S32 S27) S31)
(declare-fun f37 () S32)
(declare-fun f38 (S34 S33) S1)
(declare-fun f39 (S35 S33) S34)
(declare-fun f40 (S16) S35)
(declare-fun f41 (S15 S16) S1)
(declare-fun f42 (S36 S33) S15)
(declare-fun f43 (S37 S33) S36)
(declare-fun f44 () S37)
(declare-fun f45 (S39 S38) S34)
(declare-fun f46 (S22) S39)
(declare-fun f47 (S21 S22) S1)
(declare-fun f48 (S40 S33) S21)
(declare-fun f49 (S41 S38) S40)
(declare-fun f50 () S41)
(declare-fun f51 (S43 S42) S1)
(declare-fun f52 (S44 S42) S43)
(declare-fun f53 (S28) S44)
(declare-fun f54 (S27 S28) S1)
(declare-fun f55 (S45 S42) S27)
(declare-fun f56 (S46 S42) S45)
(declare-fun f57 () S46)
(declare-fun f58 (S48 S47) S43)
(declare-fun f59 (S34) S48)
(declare-fun f60 (S33 S34) S1)
(declare-fun f61 (S49 S42) S33)
(declare-fun f62 (S50 S47) S49)
(declare-fun f63 () S50)
(declare-fun f64 (S51 S47 S52 S38 S53) S1)
(declare-fun f65 () S51)
(declare-fun f66 () S47)
(declare-fun f67 () S52)
(declare-fun f68 (S54 S38) S38)
(declare-fun f69 (S55 S56) S54)
(declare-fun f70 (S57 S38) S55)
(declare-fun f71 () S57)
(declare-fun f72 () S38)
(declare-fun f73 () S56)
(declare-fun f74 () S38)
(declare-fun f75 () S53)
(declare-fun f76 (S51 S53 S53) S1)
(declare-fun f77 () S53)
(declare-fun f78 () S56)
(declare-fun f79 () S47)
(declare-fun f80 () S38)
(declare-fun f81 (S58 S51) S1)
(declare-fun f82 () S58)
(declare-fun f83 (S59 S52) S34)
(declare-fun f84 (S51) S59)
(declare-fun f85 () S42)
(declare-fun f86 () S56)
(declare-fun f87 () S53)
(declare-fun f88 () S42)
(declare-fun f89 (S51) S10)
(declare-fun f90 (S60 S47) S1)
(declare-fun f91 (S51) S60)
(declare-fun f92 (S51 S47 S42 S52) S1)
(declare-fun f93 (S33) S47)
(declare-fun f94 (S47) S60)
(declare-fun f95 (S14 S18) S1)
(declare-fun f96 (S2 S6) S1)
(declare-fun f97 (S61 S38) S1)
(declare-fun f98 (S62 S38) S16)
(declare-fun f99 (S63 S62) S10)
(declare-fun f100 (S61) S63)
(declare-fun f101 (S64 S21) S10)
(declare-fun f102 (S65 S64) S4)
(declare-fun f103 (S22) S65)
(declare-fun f104 (S66 S47) S28)
(declare-fun f105 (S67 S66) S16)
(declare-fun f106 (S60) S67)
(declare-fun f107 (S68 S15) S14)
(declare-fun f108 (S69 S70) S1)
(declare-fun f109 (S18 S18) S69)
(declare-fun f110 (S16 S68) S70)
(declare-fun f111 (S71 S3) S2)
(declare-fun f112 (S72 S73) S1)
(declare-fun f113 (S6 S6) S72)
(declare-fun f114 (S4 S71) S73)
(declare-fun f115 (S74 S27) S26)
(declare-fun f116 (S75 S76) S1)
(declare-fun f117 (S30 S30) S75)
(declare-fun f118 (S28 S74) S76)
(declare-fun f119 (S77 S42) S28)
(declare-fun f120 (S78 S77) S26)
(declare-fun f121 (S43) S78)
(declare-fun f122 (S79 S9) S4)
(declare-fun f123 (S80 S79) S2)
(declare-fun f124 (S10) S80)
(declare-fun f125 (S81 S33) S16)
(declare-fun f126 (S82 S81) S14)
(declare-fun f127 (S34) S82)
(declare-fun f128 (S51 S52 S38 S53) S1)
(declare-fun f129 (S26 S30) S1)
(declare-fun f130 (S83 S42) S42)
(declare-fun f131 (S42) S83)
(declare-fun f132 (S10) S10)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (= (f6 (f7 (f8 f9 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S4) (?v1 S9) (?v2 S9)) (= (= (f10 (f11 (f12 ?v0) ?v1) ?v2) f1) (= (f13 (f14 (f15 f16 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S14) (?v1 S15) (?v2 S15)) (= (= (f17 (f18 (f19 ?v0) ?v1) ?v2) f1) (= (f20 (f21 (f22 f23 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S21) (?v2 S21)) (= (= (f24 (f25 (f26 ?v0) ?v1) ?v2) f1) (= (f27 (f28 (f29 f30 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S26) (?v1 S27) (?v2 S27)) (= (= (f31 (f32 (f33 ?v0) ?v1) ?v2) f1) (= (f34 (f35 (f36 f37 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S16) (?v1 S33) (?v2 S33)) (= (= (f38 (f39 (f40 ?v0) ?v1) ?v2) f1) (= (f41 (f42 (f43 f44 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S22) (?v1 S38) (?v2 S33)) (= (= (f38 (f45 (f46 ?v0) ?v1) ?v2) f1) (= (f47 (f48 (f49 f50 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S28) (?v1 S42) (?v2 S42)) (= (= (f51 (f52 (f53 ?v0) ?v1) ?v2) f1) (= (f54 (f55 (f56 f57 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S34) (?v1 S47) (?v2 S42)) (= (= (f51 (f58 (f59 ?v0) ?v1) ?v2) f1) (= (f60 (f61 (f62 f63 ?v1) ?v2) ?v0) f1))))
(assert (not (= (f64 f65 f66 f67 (f68 (f69 (f70 f71 f72) f73) f74) f75) f1)))
(assert (exists ((?v0 S53)) (and (= (f64 f65 f66 f67 f72 ?v0) f1) (= (f76 f65 ?v0 f77) f1))))
(assert (= (f64 f65 f66 f67 f74 f77) f1))
(assert (= f73 f78))
(assert (= (f64 f65 f66 f67 f74 f77) f1))
(assert (= f75 f77))
(assert (exists ((?v0 S53)) (and (= (f64 f65 f66 f67 f72 ?v0) f1) (= (f76 f65 ?v0 f77) f1))))
(assert (= (f64 f65 f79 f67 f74 f77) f1))
(assert (= (f64 f65 f79 f67 (f68 (f69 (f70 f71 f80) f73) f74) f75) f1))
(assert (= (f81 f82 f65) f1))
(assert (= (f64 f65 f79 f67 (f68 (f69 (f70 f71 f80) f73) f74) f75) f1))
(assert (= (f64 f65 f79 f67 f80 f77) f1))
(assert (forall ((?v0 S38) (?v1 S56) (?v2 S38) (?v3 S38) (?v4 S56) (?v5 S38)) (= (= (f68 (f69 (f70 f71 ?v0) ?v1) ?v2) (f68 (f69 (f70 f71 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S52) (?v1 S53)) (=> (= (f38 (f83 (f84 f65) ?v0) (f61 (f62 f63 f79) f85)) f1) (=> (= (f64 f65 f79 ?v0 f80 ?v1) f1) (exists ((?v2 S53)) (and (= (f64 f65 f66 ?v0 f72 ?v2) f1) (= (f76 f65 ?v2 ?v1) f1)))))))
(assert (forall ((?v0 S51) (?v1 S47) (?v2 S52) (?v3 S38) (?v4 S38)) (=> (= (f64 ?v0 ?v1 ?v2 ?v3 f77) f1) (=> (= (f64 ?v0 ?v1 ?v2 ?v4 f77) f1) (= (f64 ?v0 ?v1 ?v2 (f68 (f69 (f70 f71 ?v3) f78) ?v4) f77) f1)))))
(assert (= (f38 (f83 (f84 f65) f67) (f61 (f62 f63 f79) f85)) f1))
(assert (forall ((?v0 S51) (?v1 S47) (?v2 S52) (?v3 S38) (?v4 S53) (?v5 S38) (?v6 S53)) (=> (= (f64 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f64 ?v0 ?v1 ?v2 ?v5 ?v6) f1) (= (f64 ?v0 ?v1 ?v2 (f68 (f69 (f70 f71 ?v3) f86) ?v5) f87) f1)))))
(assert (forall ((?v0 S52) (?v1 S53)) (=> (= (f38 (f83 (f84 f65) ?v0) (f61 (f62 f63 f79) f85)) f1) (=> (= (f64 f65 f79 ?v0 f80 ?v1) f1) (exists ((?v2 S53)) (and (= (f64 f65 f66 ?v0 f72 ?v2) f1) (= (f76 f65 ?v2 ?v1) f1)))))))
(assert (= (f27 (f28 (f29 f30 (f48 (f49 f50 f80) (f61 (f62 f63 f79) f85))) (f48 (f49 f50 f72) (f61 (f62 f63 f66) f88))) (f89 f65)) f1))
(assert (= (f38 (f83 (f84 f65) f67) (f61 (f62 f63 f79) f85)) f1))
(assert (not (= f86 f78)))
(assert (not (= f78 f86)))
(assert (forall ((?v0 S56)) (=> (=> (= ?v0 f86) false) (=> (=> (= ?v0 f78) false) false))))
(assert (forall ((?v0 S51) (?v1 S47) (?v2 S52) (?v3 S38) (?v4 S56) (?v5 S38) (?v6 S53)) (=> (= (f64 ?v0 ?v1 ?v2 (f68 (f69 (f70 f71 ?v3) ?v4) ?v5) ?v6) f1) (=> (forall ((?v7 S53) (?v8 S53)) (=> (= ?v6 f87) (=> (= (f64 ?v0 ?v1 ?v2 ?v3 ?v7) f1) (=> (= (f64 ?v0 ?v1 ?v2 ?v5 ?v8) f1) (=> (= ?v4 f86) false))))) (=> (=> (= ?v6 f77) (=> (= (f64 ?v0 ?v1 ?v2 ?v3 f77) f1) (=> (= (f64 ?v0 ?v1 ?v2 ?v5 f77) f1) (=> (= ?v4 f78) false)))) false)))))
(assert (forall ((?v0 S38) (?v1 S33) (?v2 S38) (?v3 S33) (?v4 S51) (?v5 S56) (?v6 S38)) (let ((?v_0 (f89 ?v4))) (=> (= (f27 (f28 (f29 f30 (f48 (f49 f50 ?v0) ?v1)) (f48 (f49 f50 ?v2) ?v3)) ?v_0) f1) (= (f27 (f28 (f29 f30 (f48 (f49 f50 (f68 (f69 (f70 f71 ?v0) ?v5) ?v6)) ?v1)) (f48 (f49 f50 (f68 (f69 (f70 f71 ?v2) ?v5) ?v6)) ?v3)) ?v_0) f1)))))
(assert (forall ((?v0 S51) (?v1 S53)) (= (f76 ?v0 ?v1 ?v1) f1)))
(assert (forall ((?v0 S38) (?v1 S47) (?v2 S42) (?v3 S38) (?v4 S47) (?v5 S42) (?v6 S51) (?v7 S52) (?v8 S53)) (let ((?v_0 (f91 ?v6))) (=> (= (f27 (f28 (f29 f30 (f48 (f49 f50 ?v0) (f61 (f62 f63 ?v1) ?v2))) (f48 (f49 f50 ?v3) (f61 (f62 f63 ?v4) ?v5))) (f89 ?v6)) f1) (=> (= (f64 ?v6 ?v1 ?v7 ?v0 ?v8) f1) (=> (= (f90 ?v_0 ?v1) f1) (= (f90 ?v_0 ?v4) f1)))))))
(assert (not (= f87 f77)))
(assert (not (= f77 f87)))
(assert (forall ((?v0 S38) (?v1 S47) (?v2 S42) (?v3 S38) (?v4 S47) (?v5 S42) (?v6 S51) (?v7 S52) (?v8 S53)) (=> (= (f27 (f28 (f29 f30 (f48 (f49 f50 ?v0) (f61 (f62 f63 ?v1) ?v2))) (f48 (f49 f50 ?v3) (f61 (f62 f63 ?v4) ?v5))) (f89 ?v6)) f1) (=> (= (f64 ?v6 ?v1 ?v7 ?v0 ?v8) f1) (=> (= (f92 ?v6 ?v1 ?v2 ?v7) f1) (= (f92 ?v6 ?v4 ?v5 ?v7) f1))))))
(assert (forall ((?v0 S38) (?v1 S33) (?v2 S38) (?v3 S33) (?v4 S51) (?v5 S52) (?v6 S53)) (let ((?v_0 (f83 (f84 ?v4) ?v5))) (=> (= (f27 (f28 (f29 f30 (f48 (f49 f50 ?v0) ?v1)) (f48 (f49 f50 ?v2) ?v3)) (f89 ?v4)) f1) (=> (= (f64 ?v4 (f93 ?v1) ?v5 ?v0 ?v6) f1) (=> (= (f38 ?v_0 ?v1) f1) (= (f38 ?v_0 ?v3) f1)))))))
(assert (forall ((?v0 S51) (?v1 S53) (?v2 S53) (?v3 S53)) (=> (= (f76 ?v0 ?v1 ?v2) f1) (=> (= (f76 ?v0 ?v2 ?v3) f1) (= (f76 ?v0 ?v1 ?v3) f1)))))
(assert (forall ((?v0 S38) (?v1 S47) (?v2 S42) (?v3 S38) (?v4 S47) (?v5 S42) (?v6 S51)) (=> (= (f27 (f28 (f29 f30 (f48 (f49 f50 ?v0) (f61 (f62 f63 ?v1) ?v2))) (f48 (f49 f50 ?v3) (f61 (f62 f63 ?v4) ?v5))) (f89 ?v6)) f1) (= (f90 (f94 ?v1) ?v4) f1))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S9) (?v2 S21) (?v3 S38) (?v4 S33)) (=> (= ?v0 (f14 (f15 f16 ?v1) (f28 (f29 f30 ?v2) (f48 (f49 f50 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S9)) (=> (forall ((?v1 S21) (?v2 S38) (?v3 S47) (?v4 S42)) (=> (= ?v0 (f28 (f29 f30 ?v1) (f48 (f49 f50 ?v2) (f61 (f62 f63 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S18)) (=> (forall ((?v1 S15) (?v2 S33) (?v3 S47) (?v4 S42)) (=> (= ?v0 (f21 (f22 f23 ?v1) (f42 (f43 f44 ?v2) (f61 (f62 f63 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S3) (?v2 S9) (?v3 S21) (?v4 S21)) (=> (= ?v0 (f7 (f8 f9 ?v1) (f14 (f15 f16 ?v2) (f28 (f29 f30 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S4) (?v1 S3)) (=> (forall ((?v2 S9) (?v3 S21) (?v4 S38) (?v5 S33)) (= (f3 ?v0 (f14 (f15 f16 ?v2) (f28 (f29 f30 ?v3) (f48 (f49 f50 ?v4) ?v5)))) f1)) (= (f3 ?v0 ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S9)) (=> (forall ((?v2 S21) (?v3 S38) (?v4 S47) (?v5 S42)) (= (f10 ?v0 (f28 (f29 f30 ?v2) (f48 (f49 f50 ?v3) (f61 (f62 f63 ?v4) ?v5)))) f1)) (= (f10 ?v0 ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S18)) (=> (forall ((?v2 S15) (?v3 S33) (?v4 S47) (?v5 S42)) (= (f95 ?v0 (f21 (f22 f23 ?v2) (f42 (f43 f44 ?v3) (f61 (f62 f63 ?v4) ?v5)))) f1)) (= (f95 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S6)) (=> (forall ((?v2 S3) (?v3 S9) (?v4 S21) (?v5 S21)) (= (f96 ?v0 (f7 (f8 f9 ?v2) (f14 (f15 f16 ?v3) (f28 (f29 f30 ?v4) ?v5)))) f1)) (= (f96 ?v0 ?v1) f1))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S9) (?v2 S21) (?v3 S38) (?v4 S47) (?v5 S42)) (=> (= ?v0 (f14 (f15 f16 ?v1) (f28 (f29 f30 ?v2) (f48 (f49 f50 ?v3) (f61 (f62 f63 ?v4) ?v5))))) false)) false)))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S3) (?v2 S9) (?v3 S21) (?v4 S38) (?v5 S33)) (=> (= ?v0 (f7 (f8 f9 ?v1) (f14 (f15 f16 ?v2) (f28 (f29 f30 ?v3) (f48 (f49 f50 ?v4) ?v5))))) false)) false)))
(assert (forall ((?v0 S4) (?v1 S3)) (=> (forall ((?v2 S9) (?v3 S21) (?v4 S38) (?v5 S47) (?v6 S42)) (= (f3 ?v0 (f14 (f15 f16 ?v2) (f28 (f29 f30 ?v3) (f48 (f49 f50 ?v4) (f61 (f62 f63 ?v5) ?v6))))) f1)) (= (f3 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S6)) (=> (forall ((?v2 S3) (?v3 S9) (?v4 S21) (?v5 S38) (?v6 S33)) (= (f96 ?v0 (f7 (f8 f9 ?v2) (f14 (f15 f16 ?v3) (f28 (f29 f30 ?v4) (f48 (f49 f50 ?v5) ?v6))))) f1)) (= (f96 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S3) (?v2 S9) (?v3 S21) (?v4 S38) (?v5 S47) (?v6 S42)) (=> (= ?v0 (f7 (f8 f9 ?v1) (f14 (f15 f16 ?v2) (f28 (f29 f30 ?v3) (f48 (f49 f50 ?v4) (f61 (f62 f63 ?v5) ?v6)))))) false)) false)))
(assert (forall ((?v0 S2) (?v1 S6)) (=> (forall ((?v2 S3) (?v3 S9) (?v4 S21) (?v5 S38) (?v6 S47) (?v7 S42)) (= (f96 ?v0 (f7 (f8 f9 ?v2) (f14 (f15 f16 ?v3) (f28 (f29 f30 ?v4) (f48 (f49 f50 ?v5) (f61 (f62 f63 ?v6) ?v7)))))) f1)) (= (f96 ?v0 ?v1) f1))))
(assert (forall ((?v0 S61) (?v1 S38) (?v2 S33) (?v3 S33) (?v4 S62)) (let ((?v_0 (f49 f50 ?v1))) (=> (= (f97 ?v0 ?v1) f1) (=> (= (f41 (f42 (f43 f44 ?v2) ?v3) (f98 ?v4 ?v1)) f1) (= (f27 (f28 (f29 f30 (f48 ?v_0 ?v2)) (f48 ?v_0 ?v3)) (f99 (f100 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S22) (?v1 S21) (?v2 S21) (?v3 S21) (?v4 S64)) (let ((?v_0 (f29 f30 ?v1))) (=> (= (f24 ?v0 ?v1) f1) (=> (= (f27 (f28 (f29 f30 ?v2) ?v3) (f101 ?v4 ?v1)) f1) (= (f13 (f14 (f15 f16 (f28 ?v_0 ?v2)) (f28 ?v_0 ?v3)) (f102 (f103 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S60) (?v1 S47) (?v2 S42) (?v3 S42) (?v4 S66)) (let ((?v_0 (f62 f63 ?v1))) (=> (= (f90 ?v0 ?v1) f1) (=> (= (f54 (f55 (f56 f57 ?v2) ?v3) (f104 ?v4 ?v1)) f1) (= (f41 (f42 (f43 f44 (f61 ?v_0 ?v2)) (f61 ?v_0 ?v3)) (f105 (f106 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S16) (?v1 S15) (?v2 S15) (?v3 S15) (?v4 S68)) (let ((?v_0 (f22 f23 ?v1))) (=> (= (f17 ?v0 ?v1) f1) (=> (= (f20 (f21 (f22 f23 ?v2) ?v3) (f107 ?v4 ?v1)) f1) (= (f108 (f109 (f21 ?v_0 ?v2) (f21 ?v_0 ?v3)) (f110 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S71)) (let ((?v_0 (f8 f9 ?v1))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f6 (f7 (f8 f9 ?v2) ?v3) (f111 ?v4 ?v1)) f1) (= (f112 (f113 (f7 ?v_0 ?v2) (f7 ?v_0 ?v3)) (f114 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S28) (?v1 S27) (?v2 S27) (?v3 S27) (?v4 S74)) (let ((?v_0 (f36 f37 ?v1))) (=> (= (f31 ?v0 ?v1) f1) (=> (= (f34 (f35 (f36 f37 ?v2) ?v3) (f115 ?v4 ?v1)) f1) (= (f116 (f117 (f35 ?v_0 ?v2) (f35 ?v_0 ?v3)) (f118 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S43) (?v1 S42) (?v2 S42) (?v3 S42) (?v4 S77)) (let ((?v_0 (f56 f57 ?v1))) (=> (= (f51 ?v0 ?v1) f1) (=> (= (f54 (f55 (f56 f57 ?v2) ?v3) (f119 ?v4 ?v1)) f1) (= (f34 (f35 (f36 f37 (f55 ?v_0 ?v2)) (f55 ?v_0 ?v3)) (f120 (f121 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S10) (?v1 S9) (?v2 S9) (?v3 S9) (?v4 S79)) (let ((?v_0 (f15 f16 ?v1))) (=> (= (f10 ?v0 ?v1) f1) (=> (= (f13 (f14 (f15 f16 ?v2) ?v3) (f122 ?v4 ?v1)) f1) (= (f6 (f7 (f8 f9 (f14 ?v_0 ?v2)) (f14 ?v_0 ?v3)) (f123 (f124 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S34) (?v1 S33) (?v2 S33) (?v3 S33) (?v4 S81)) (let ((?v_0 (f43 f44 ?v1))) (=> (= (f38 ?v0 ?v1) f1) (=> (= (f41 (f42 (f43 f44 ?v2) ?v3) (f125 ?v4 ?v1)) f1) (= (f20 (f21 (f22 f23 (f42 ?v_0 ?v2)) (f42 ?v_0 ?v3)) (f126 (f127 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S51) (?v1 S52) (?v2 S38) (?v3 S56) (?v4 S38) (?v5 S53)) (=> (= (f128 ?v0 ?v1 (f68 (f69 (f70 f71 ?v2) ?v3) ?v4) ?v5) f1) (=> (forall ((?v6 S53) (?v7 S53)) (=> (= ?v5 f87) (=> (= (f128 ?v0 ?v1 ?v2 ?v6) f1) (=> (= (f128 ?v0 ?v1 ?v4 ?v7) f1) (=> (or (= (f76 ?v0 ?v6 ?v7) f1) (= (f76 ?v0 ?v7 ?v6) f1)) (=> (= ?v3 f86) false)))))) (=> (=> (= ?v5 f77) (=> (= (f128 ?v0 ?v1 ?v2 f77) f1) (=> (= (f128 ?v0 ?v1 ?v4 f77) f1) (=> (= ?v3 f78) false)))) false)))))
(assert (forall ((?v0 S51) (?v1 S52) (?v2 S38) (?v3 S38)) (=> (= (f128 ?v0 ?v1 ?v2 f77) f1) (=> (= (f128 ?v0 ?v1 ?v3 f77) f1) (= (f128 ?v0 ?v1 (f68 (f69 (f70 f71 ?v2) f78) ?v3) f77) f1)))))
(assert (forall ((?v0 S51) (?v1 S52) (?v2 S38) (?v3 S53) (?v4 S38) (?v5 S53)) (=> (= (f128 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f128 ?v0 ?v1 ?v4 ?v5) f1) (=> (or (= (f76 ?v0 ?v3 ?v5) f1) (= (f76 ?v0 ?v5 ?v3) f1)) (= (f128 ?v0 ?v1 (f68 (f69 (f70 f71 ?v2) f86) ?v4) f87) f1))))))
(assert (forall ((?v0 S51) (?v1 S52) (?v2 S38) (?v3 S53) (?v4 S47)) (=> (= (f128 ?v0 ?v1 ?v2 ?v3) f1) (= (f64 ?v0 ?v4 ?v1 ?v2 ?v3) f1))))
(assert (forall ((?v0 S51) (?v1 S47) (?v2 S52) (?v3 S38) (?v4 S53) (?v5 S47)) (=> (= (f64 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f90 (f94 ?v1) ?v5) f1) (= (f64 ?v0 ?v5 ?v2 ?v3 ?v4) f1)))))
(assert (forall ((?v0 S22)) (= (forall ((?v1 S21)) (= (f24 ?v0 ?v1) f1)) (forall ((?v1 S38) (?v2 S33)) (= (f24 ?v0 (f48 (f49 f50 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S10)) (= (forall ((?v1 S9)) (= (f10 ?v0 ?v1) f1)) (forall ((?v1 S21) (?v2 S21)) (= (f10 ?v0 (f28 (f29 f30 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S34)) (= (forall ((?v1 S33)) (= (f38 ?v0 ?v1) f1)) (forall ((?v1 S47) (?v2 S42)) (= (f38 ?v0 (f61 (f62 f63 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S14)) (= (forall ((?v1 S18)) (= (f95 ?v0 ?v1) f1)) (forall ((?v1 S15) (?v2 S15)) (= (f95 ?v0 (f21 (f22 f23 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2)) (= (forall ((?v1 S6)) (= (f96 ?v0 ?v1) f1)) (forall ((?v1 S3) (?v2 S3)) (= (f96 ?v0 (f7 (f8 f9 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S26)) (= (forall ((?v1 S30)) (= (f129 ?v0 ?v1) f1)) (forall ((?v1 S27) (?v2 S27)) (= (f129 ?v0 (f35 (f36 f37 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S28)) (= (forall ((?v1 S27)) (= (f31 ?v0 ?v1) f1)) (forall ((?v1 S42) (?v2 S42)) (= (f31 ?v0 (f55 (f56 f57 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S4)) (= (forall ((?v1 S3)) (= (f3 ?v0 ?v1) f1)) (forall ((?v1 S9) (?v2 S9)) (= (f3 ?v0 (f14 (f15 f16 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S16)) (= (forall ((?v1 S15)) (= (f17 ?v0 ?v1) f1)) (forall ((?v1 S33) (?v2 S33)) (= (f17 ?v0 (f42 (f43 f44 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S38) (?v1 S33) (?v2 S38) (?v3 S33)) (= (= (f48 (f49 f50 ?v0) ?v1) (f48 (f49 f50 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21) (?v3 S21)) (= (= (f28 (f29 f30 ?v0) ?v1) (f28 (f29 f30 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S47) (?v1 S42) (?v2 S47) (?v3 S42)) (= (= (f61 (f62 f63 ?v0) ?v1) (f61 (f62 f63 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (= (= (f21 (f22 f23 ?v0) ?v1) (f21 (f22 f23 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S27) (?v3 S27)) (= (= (f35 (f36 f37 ?v0) ?v1) (f35 (f36 f37 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S42) (?v1 S42) (?v2 S42) (?v3 S42)) (= (= (f55 (f56 f57 ?v0) ?v1) (f55 (f56 f57 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (= (= (f14 (f15 f16 ?v0) ?v1) (f14 (f15 f16 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33) (?v3 S33)) (= (= (f42 (f43 f44 ?v0) ?v1) (f42 (f43 f44 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S38) (?v1 S33) (?v2 S38) (?v3 S33)) (=> (= (f48 (f49 f50 ?v0) ?v1) (f48 (f49 f50 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21) (?v3 S21)) (=> (= (f28 (f29 f30 ?v0) ?v1) (f28 (f29 f30 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S47) (?v1 S42) (?v2 S47) (?v3 S42)) (=> (= (f61 (f62 f63 ?v0) ?v1) (f61 (f62 f63 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (=> (= (f21 (f22 f23 ?v0) ?v1) (f21 (f22 f23 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S27) (?v3 S27)) (=> (= (f35 (f36 f37 ?v0) ?v1) (f35 (f36 f37 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S42) (?v1 S42) (?v2 S42) (?v3 S42)) (=> (= (f55 (f56 f57 ?v0) ?v1) (f55 (f56 f57 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (=> (= (f14 (f15 f16 ?v0) ?v1) (f14 (f15 f16 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S33) (?v1 S33) (?v2 S33) (?v3 S33)) (=> (= (f42 (f43 f44 ?v0) ?v1) (f42 (f43 f44 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S47)) (= (f90 (f94 ?v0) ?v0) f1)))
(assert (forall ((?v0 S51) (?v1 S47) (?v2 S42) (?v3 S52) (?v4 S47)) (=> (= (f92 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f90 (f94 ?v1) ?v4) f1) (= (f92 ?v0 ?v4 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S4) (?v1 S3)) (=> (forall ((?v2 S9) (?v3 S21) (?v4 S21)) (= (f3 ?v0 (f14 (f15 f16 ?v2) (f28 (f29 f30 ?v3) ?v4))) f1)) (= (f3 ?v0 ?v1) f1))))
(assert (forall ((?v0 S16) (?v1 S15)) (=> (forall ((?v2 S33) (?v3 S47) (?v4 S42)) (= (f17 ?v0 (f42 (f43 f44 ?v2) (f61 (f62 f63 ?v3) ?v4))) f1)) (= (f17 ?v0 ?v1) f1))))
(assert (forall ((?v0 S22) (?v1 S21)) (=> (forall ((?v2 S38) (?v3 S47) (?v4 S42)) (= (f24 ?v0 (f48 (f49 f50 ?v2) (f61 (f62 f63 ?v3) ?v4))) f1)) (= (f24 ?v0 ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S9)) (=> (forall ((?v2 S21) (?v3 S38) (?v4 S33)) (= (f10 ?v0 (f28 (f29 f30 ?v2) (f48 (f49 f50 ?v3) ?v4))) f1)) (= (f10 ?v0 ?v1) f1))))
(assert (forall ((?v0 S26) (?v1 S30)) (=> (forall ((?v2 S27) (?v3 S42) (?v4 S42)) (= (f129 ?v0 (f35 (f36 f37 ?v2) (f55 (f56 f57 ?v3) ?v4))) f1)) (= (f129 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S6)) (=> (forall ((?v2 S3) (?v3 S9) (?v4 S9)) (= (f96 ?v0 (f7 (f8 f9 ?v2) (f14 (f15 f16 ?v3) ?v4))) f1)) (= (f96 ?v0 ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S18)) (=> (forall ((?v2 S15) (?v3 S33) (?v4 S33)) (= (f95 ?v0 (f21 (f22 f23 ?v2) (f42 (f43 f44 ?v3) ?v4))) f1)) (= (f95 ?v0 ?v1) f1))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S9) (?v2 S21) (?v3 S21)) (=> (= ?v0 (f14 (f15 f16 ?v1) (f28 (f29 f30 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S15)) (=> (forall ((?v1 S33) (?v2 S47) (?v3 S42)) (=> (= ?v0 (f42 (f43 f44 ?v1) (f61 (f62 f63 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S21)) (=> (forall ((?v1 S38) (?v2 S47) (?v3 S42)) (=> (= ?v0 (f48 (f49 f50 ?v1) (f61 (f62 f63 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S9)) (=> (forall ((?v1 S21) (?v2 S38) (?v3 S33)) (=> (= ?v0 (f28 (f29 f30 ?v1) (f48 (f49 f50 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S30)) (=> (forall ((?v1 S27) (?v2 S42) (?v3 S42)) (=> (= ?v0 (f35 (f36 f37 ?v1) (f55 (f56 f57 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S3) (?v2 S9) (?v3 S9)) (=> (= ?v0 (f7 (f8 f9 ?v1) (f14 (f15 f16 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S18)) (=> (forall ((?v1 S15) (?v2 S33) (?v3 S33)) (=> (= ?v0 (f21 (f22 f23 ?v1) (f42 (f43 f44 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S38) (?v1 S47) (?v2 S42) (?v3 S38) (?v4 S47) (?v5 S42) (?v6 S51) (?v7 S42)) (let ((?v_0 (f49 f50 ?v0)) (?v_1 (f62 f63 ?v1)) (?v_2 (f49 f50 ?v3)) (?v_3 (f62 f63 ?v4)) (?v_5 (f89 ?v6)) (?v_4 (f131 ?v7))) (=> (= (f27 (f28 (f29 f30 (f48 ?v_0 (f61 ?v_1 ?v2))) (f48 ?v_2 (f61 ?v_3 ?v5))) ?v_5) f1) (= (f27 (f28 (f29 f30 (f48 ?v_0 (f61 ?v_1 (f130 ?v_4 ?v2)))) (f48 ?v_2 (f61 ?v_3 (f130 ?v_4 ?v5)))) ?v_5) f1)))))
(assert (forall ((?v0 S22)) (= (exists ((?v1 S21)) (= (f24 ?v0 ?v1) f1)) (exists ((?v1 S38) (?v2 S33)) (= (f24 ?v0 (f48 (f49 f50 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S10)) (= (exists ((?v1 S9)) (= (f10 ?v0 ?v1) f1)) (exists ((?v1 S21) (?v2 S21)) (= (f10 ?v0 (f28 (f29 f30 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S34)) (= (exists ((?v1 S33)) (= (f38 ?v0 ?v1) f1)) (exists ((?v1 S47) (?v2 S42)) (= (f38 ?v0 (f61 (f62 f63 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S14)) (= (exists ((?v1 S18)) (= (f95 ?v0 ?v1) f1)) (exists ((?v1 S15) (?v2 S15)) (= (f95 ?v0 (f21 (f22 f23 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2)) (= (exists ((?v1 S6)) (= (f96 ?v0 ?v1) f1)) (exists ((?v1 S3) (?v2 S3)) (= (f96 ?v0 (f7 (f8 f9 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S26)) (= (exists ((?v1 S30)) (= (f129 ?v0 ?v1) f1)) (exists ((?v1 S27) (?v2 S27)) (= (f129 ?v0 (f35 (f36 f37 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S28)) (= (exists ((?v1 S27)) (= (f31 ?v0 ?v1) f1)) (exists ((?v1 S42) (?v2 S42)) (= (f31 ?v0 (f55 (f56 f57 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S4)) (= (exists ((?v1 S3)) (= (f3 ?v0 ?v1) f1)) (exists ((?v1 S9) (?v2 S9)) (= (f3 ?v0 (f14 (f15 f16 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S16)) (= (exists ((?v1 S15)) (= (f17 ?v0 ?v1) f1)) (exists ((?v1 S33) (?v2 S33)) (= (f17 ?v0 (f42 (f43 f44 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S21)) (=> (forall ((?v1 S38) (?v2 S33)) (=> (= ?v0 (f48 (f49 f50 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S9)) (=> (forall ((?v1 S21) (?v2 S21)) (=> (= ?v0 (f28 (f29 f30 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S33)) (=> (forall ((?v1 S47) (?v2 S42)) (=> (= ?v0 (f61 (f62 f63 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S18)) (=> (forall ((?v1 S15) (?v2 S15)) (=> (= ?v0 (f21 (f22 f23 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S3) (?v2 S3)) (=> (= ?v0 (f7 (f8 f9 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S30)) (=> (forall ((?v1 S27) (?v2 S27)) (=> (= ?v0 (f35 (f36 f37 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S27)) (=> (forall ((?v1 S42) (?v2 S42)) (=> (= ?v0 (f55 (f56 f57 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S9) (?v2 S9)) (=> (= ?v0 (f14 (f15 f16 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S15)) (=> (forall ((?v1 S33) (?v2 S33)) (=> (= ?v0 (f42 (f43 f44 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S47) (?v1 S47) (?v2 S47)) (let ((?v_0 (f94 ?v0))) (=> (= (f90 ?v_0 ?v1) f1) (=> (= (f90 (f94 ?v1) ?v2) f1) (= (f90 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S38) (?v1 S47) (?v2 S42) (?v3 S38) (?v4 S47) (?v5 S42) (?v6 S51) (?v7 S42)) (let ((?v_0 (f49 f50 ?v0)) (?v_1 (f62 f63 ?v1)) (?v_2 (f49 f50 ?v3)) (?v_3 (f62 f63 ?v4)) (?v_5 (f132 (f89 ?v6))) (?v_4 (f131 ?v7))) (=> (= (f27 (f28 (f29 f30 (f48 ?v_0 (f61 ?v_1 ?v2))) (f48 ?v_2 (f61 ?v_3 ?v5))) ?v_5) f1) (= (f27 (f28 (f29 f30 (f48 ?v_0 (f61 ?v_1 (f130 ?v_4 ?v2)))) (f48 ?v_2 (f61 ?v_3 (f130 ?v_4 ?v5)))) ?v_5) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f26 ?v0) (f26 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S22) (?v1 S22)) (= (= (f46 ?v0) (f46 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S34) (?v1 S34)) (= (= (f59 ?v0) (f59 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f19 ?v0) (f19 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f5 ?v0) (f5 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S26) (?v1 S26)) (= (= (f33 ?v0) (f33 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S28) (?v1 S28)) (= (= (f53 ?v0) (f53 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f12 ?v0) (f12 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S16) (?v1 S16)) (= (= (f40 ?v0) (f40 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S21)) (=> (forall ((?v1 S38) (?v2 S33)) (=> (= ?v0 (f48 (f49 f50 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S9)) (=> (forall ((?v1 S21) (?v2 S21)) (=> (= ?v0 (f28 (f29 f30 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S33)) (=> (forall ((?v1 S47) (?v2 S42)) (=> (= ?v0 (f61 (f62 f63 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S18)) (=> (forall ((?v1 S15) (?v2 S15)) (=> (= ?v0 (f21 (f22 f23 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S3) (?v2 S3)) (=> (= ?v0 (f7 (f8 f9 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S30)) (=> (forall ((?v1 S27) (?v2 S27)) (=> (= ?v0 (f35 (f36 f37 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S27)) (=> (forall ((?v1 S42) (?v2 S42)) (=> (= ?v0 (f55 (f56 f57 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S9) (?v2 S9)) (=> (= ?v0 (f14 (f15 f16 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S15)) (=> (forall ((?v1 S33) (?v2 S33)) (=> (= ?v0 (f42 (f43 f44 ?v1) ?v2)) false)) false)))
(check-sat)
(exit)