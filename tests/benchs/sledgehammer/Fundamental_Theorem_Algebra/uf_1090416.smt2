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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () S3)
(declare-fun f4 () S2)
(declare-fun f5 (S5 S2) S2)
(declare-fun f6 (S6 S2) S5)
(declare-fun f7 () S6)
(declare-fun f8 (S7 S4) S2)
(declare-fun f9 () S7)
(declare-fun f10 () S2)
(declare-fun f11 (S8 S4) S4)
(declare-fun f12 (S9 S3) S8)
(declare-fun f13 () S9)
(declare-fun f14 () S3)
(declare-fun f15 () S4)
(declare-fun f16 (S10 S3) S3)
(declare-fun f17 (S11 S4) S10)
(declare-fun f18 () S11)
(declare-fun f19 (S12 S3) S10)
(declare-fun f20 () S12)
(declare-fun f21 () S12)
(declare-fun f22 (S13 S2) S3)
(declare-fun f23 (S14 S3) S13)
(declare-fun f24 () S14)
(declare-fun f25 () S5)
(declare-fun f26 (S10) S1)
(declare-fun f27 () S4)
(declare-fun f28 (S16 S15) S5)
(declare-fun f29 () S16)
(declare-fun f30 (S17 S15) S15)
(declare-fun f31 (S18 S2) S17)
(declare-fun f32 () S18)
(declare-fun f33 () S6)
(declare-fun f34 (S20 S19) S8)
(declare-fun f35 () S20)
(declare-fun f36 (S21 S19) S19)
(declare-fun f37 (S22 S4) S21)
(declare-fun f38 () S22)
(declare-fun f39 (S23 S4) S8)
(declare-fun f40 () S23)
(declare-fun f41 () S23)
(declare-fun f42 (S26 S24) S24)
(declare-fun f43 (S27 S25) S26)
(declare-fun f44 () S27)
(declare-fun f45 (S28 S25) S25)
(declare-fun f46 (S29 S24) S28)
(declare-fun f47 () S29)
(declare-fun f48 (S30 S24) S26)
(declare-fun f49 () S30)
(declare-fun f50 () S30)
(declare-fun f51 (S32 S31) S17)
(declare-fun f52 () S32)
(declare-fun f53 (S33 S31) S31)
(declare-fun f54 (S34 S15) S33)
(declare-fun f55 () S34)
(declare-fun f56 (S35 S15) S17)
(declare-fun f57 () S35)
(declare-fun f58 () S35)
(declare-fun f59 (S37 S36) S36)
(declare-fun f60 (S38 S24) S37)
(declare-fun f61 () S38)
(declare-fun f62 (S39 S36) S26)
(declare-fun f63 () S39)
(declare-fun f64 (S40 S36) S37)
(declare-fun f65 () S40)
(declare-fun f66 () S40)
(declare-fun f67 (S41 S2) S36)
(declare-fun f68 (S42 S36) S41)
(declare-fun f69 () S42)
(declare-fun f70 () S36)
(declare-fun f71 () S36)
(declare-fun f72 () S6)
(declare-fun f73 () S3)
(declare-fun f74 (S43 S2) S19)
(declare-fun f75 (S44 S19) S43)
(declare-fun f76 () S44)
(declare-fun f77 () S19)
(declare-fun f78 () S19)
(declare-fun f79 (S45 S2) S25)
(declare-fun f80 (S46 S25) S45)
(declare-fun f81 () S46)
(declare-fun f82 () S25)
(declare-fun f83 () S25)
(declare-fun f84 (S47 S2) S31)
(declare-fun f85 (S48 S31) S47)
(declare-fun f86 () S48)
(declare-fun f87 () S31)
(declare-fun f88 () S31)
(declare-fun f89 (S49 S2) S15)
(declare-fun f90 (S50 S15) S49)
(declare-fun f91 () S50)
(declare-fun f92 () S15)
(declare-fun f93 () S15)
(declare-fun f94 (S51 S2) S24)
(declare-fun f95 (S52 S24) S51)
(declare-fun f96 () S52)
(declare-fun f97 () S24)
(declare-fun f98 () S24)
(declare-fun f99 (S53 S2) S4)
(declare-fun f100 (S54 S4) S53)
(declare-fun f101 () S54)
(declare-fun f102 () S4)
(declare-fun f103 () S4)
(declare-fun f104 (S55 S19) S21)
(declare-fun f105 () S55)
(declare-fun f106 () S55)
(declare-fun f107 (S56 S25) S28)
(declare-fun f108 () S56)
(declare-fun f109 () S56)
(declare-fun f110 (S57 S31) S33)
(declare-fun f111 () S57)
(declare-fun f112 () S57)
(declare-fun f113 () S58)
(declare-fun f114 (S19 S58) S58)
(declare-fun f115 () S58)
(declare-fun f116 () S59)
(declare-fun f117 (S25 S59) S59)
(declare-fun f118 () S59)
(declare-fun f119 () S60)
(declare-fun f120 (S31 S60) S60)
(declare-fun f121 () S60)
(declare-fun f122 (S61 S19) S2)
(declare-fun f123 () S61)
(declare-fun f124 (S62 S25) S2)
(declare-fun f125 () S62)
(declare-fun f126 (S63 S31) S2)
(declare-fun f127 () S63)
(declare-fun f128 (S64 S15) S2)
(declare-fun f129 () S64)
(declare-fun f130 (S65 S24) S2)
(declare-fun f131 () S65)
(assert (not (= f1 f2)))
(assert (not (exists ((?v0 S2) (?v1 S3) (?v2 S4)) (and (not (= ?v1 f3)) (and (not (= ?v0 f4)) (and (= (f5 (f6 f7 (f5 (f6 f7 (f8 f9 ?v2)) ?v0)) f10) (f8 f9 (f11 (f12 f13 f14) f15))) (forall ((?v3 S3)) (let ((?v_0 (f17 f18 (f11 (f12 f13 f14) f15)))) (= (f16 ?v_0 ?v3) (f16 (f19 f20 (f16 ?v_0 f3)) (f16 (f19 f21 (f22 (f23 f24 ?v3) ?v0)) (f16 (f17 f18 (f11 (f12 f13 ?v1) ?v2)) ?v3))))))))))))
(assert (exists ((?v0 S2) (?v1 S3) (?v2 S4)) (and (not (= ?v1 f3)) (and (= (f5 f25 (f5 (f6 f7 (f8 f9 ?v2)) ?v0)) (f8 f9 f15)) (forall ((?v3 S3)) (= (f16 (f17 f18 f15) ?v3) (f16 (f19 f21 (f22 (f23 f24 ?v3) ?v0)) (f16 (f17 f18 (f11 (f12 f13 ?v1) ?v2)) ?v3))))))))
(assert (not (= (f26 (f17 f18 f27)) f1)))
(assert (not (forall ((?v0 S3)) (=> (not (= ?v0 f3)) (= (f16 (f17 f18 f15) ?v0) f3)))))
(assert (=> (forall ((?v0 S3)) (=> (not (= ?v0 f3)) (= (f16 (f17 f18 f15) ?v0) f3))) false))
(assert (exists ((?v0 S2) (?v1 S3) (?v2 S4)) (and (not (= ?v1 f3)) (and (= (f5 f25 (f5 (f6 f7 (f8 f9 ?v2)) ?v0)) (f8 f9 f15)) (forall ((?v3 S3)) (= (f16 (f17 f18 f15) ?v3) (f16 (f19 f21 (f22 (f23 f24 ?v3) ?v0)) (f16 (f17 f18 (f11 (f12 f13 ?v1) ?v2)) ?v3))))))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S3)) (= (f16 (f17 f18 (f11 (f12 f13 ?v0) ?v1)) ?v2) (f16 (f19 f20 ?v0) (f16 (f19 f21 ?v2) (f16 (f17 f18 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S15) (?v2 S2)) (= (f5 (f28 f29 (f30 (f31 f32 ?v0) ?v1)) ?v2) (f5 (f6 f7 ?v0) (f5 (f6 f33 ?v2) (f5 (f28 f29 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S19) (?v2 S4)) (= (f11 (f34 f35 (f36 (f37 f38 ?v0) ?v1)) ?v2) (f11 (f39 f40 ?v0) (f11 (f39 f41 ?v2) (f11 (f34 f35 ?v1) ?v2))))))
(assert (forall ((?v0 S24) (?v1 S25) (?v2 S24)) (= (f42 (f43 f44 (f45 (f46 f47 ?v0) ?v1)) ?v2) (f42 (f48 f49 ?v0) (f42 (f48 f50 ?v2) (f42 (f43 f44 ?v1) ?v2))))))
(assert (forall ((?v0 S15) (?v1 S31) (?v2 S15)) (= (f30 (f51 f52 (f53 (f54 f55 ?v0) ?v1)) ?v2) (f30 (f56 f57 ?v0) (f30 (f56 f58 ?v2) (f30 (f51 f52 ?v1) ?v2))))))
(assert (forall ((?v0 S36) (?v1 S24) (?v2 S36)) (= (f59 (f60 f61 (f42 (f62 f63 ?v0) ?v1)) ?v2) (f59 (f64 f65 ?v0) (f59 (f64 f66 ?v2) (f59 (f60 f61 ?v1) ?v2))))))
(assert (forall ((?v0 S2)) (= (f67 (f68 f69 f70) ?v0) (ite (= ?v0 f4) f71 f70))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f72 f4) ?v0) (ite (= ?v0 f4) f10 f4))))
(assert (forall ((?v0 S2)) (= (f22 (f23 f24 f3) ?v0) (ite (= ?v0 f4) f73 f3))))
(assert (forall ((?v0 S2)) (= (f74 (f75 f76 f77) ?v0) (ite (= ?v0 f4) f78 f77))))
(assert (forall ((?v0 S2)) (= (f79 (f80 f81 f82) ?v0) (ite (= ?v0 f4) f83 f82))))
(assert (forall ((?v0 S2)) (= (f84 (f85 f86 f87) ?v0) (ite (= ?v0 f4) f88 f87))))
(assert (forall ((?v0 S2)) (= (f89 (f90 f91 f92) ?v0) (ite (= ?v0 f4) f93 f92))))
(assert (forall ((?v0 S2)) (= (f94 (f95 f96 f97) ?v0) (ite (= ?v0 f4) f98 f97))))
(assert (forall ((?v0 S2)) (= (f99 (f100 f101 f102) ?v0) (ite (= ?v0 f4) f103 f102))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f72 ?v0))) (= (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f5 (f6 f33 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f23 f24 ?v0))) (= (f22 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f16 (f19 f21 (f22 ?v_0 ?v1)) (f22 ?v_0 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f100 f101 ?v0))) (= (f99 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f11 (f39 f41 (f99 ?v_0 ?v1)) (f99 ?v_0 ?v2))))))
(assert (forall ((?v0 S24) (?v1 S2) (?v2 S2)) (let ((?v_0 (f95 f96 ?v0))) (= (f94 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f42 (f48 f50 (f94 ?v_0 ?v1)) (f94 ?v_0 ?v2))))))
(assert (forall ((?v0 S15) (?v1 S2) (?v2 S2)) (let ((?v_0 (f90 f91 ?v0))) (= (f89 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f30 (f56 f58 (f89 ?v_0 ?v1)) (f89 ?v_0 ?v2))))))
(assert (forall ((?v0 S36) (?v1 S2) (?v2 S2)) (let ((?v_0 (f68 f69 ?v0))) (= (f67 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f59 (f64 f66 (f67 ?v_0 ?v1)) (f67 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f72 ?v0))) (= (f5 (f6 f33 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f23 f24 ?v0))) (= (f16 (f19 f21 (f22 ?v_0 ?v1)) (f22 ?v_0 ?v2)) (f22 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f100 f101 ?v0))) (= (f11 (f39 f41 (f99 ?v_0 ?v1)) (f99 ?v_0 ?v2)) (f99 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S24) (?v1 S2) (?v2 S2)) (let ((?v_0 (f95 f96 ?v0))) (= (f42 (f48 f50 (f94 ?v_0 ?v1)) (f94 ?v_0 ?v2)) (f94 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S15) (?v1 S2) (?v2 S2)) (let ((?v_0 (f90 f91 ?v0))) (= (f30 (f56 f58 (f89 ?v_0 ?v1)) (f89 ?v_0 ?v2)) (f89 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S36) (?v1 S2) (?v2 S2)) (let ((?v_0 (f68 f69 ?v0))) (= (f59 (f64 f66 (f67 ?v_0 ?v1)) (f67 ?v_0 ?v2)) (f67 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S36)) (= (f67 (f68 f69 ?v0) f4) f71)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f72 ?v0) f4) f10)))
(assert (forall ((?v0 S3)) (= (f22 (f23 f24 ?v0) f4) f73)))
(assert (forall ((?v0 S19)) (= (f74 (f75 f76 ?v0) f4) f78)))
(assert (forall ((?v0 S25)) (= (f79 (f80 f81 ?v0) f4) f83)))
(assert (forall ((?v0 S31)) (= (f84 (f85 f86 ?v0) f4) f88)))
(assert (forall ((?v0 S15)) (= (f89 (f90 f91 ?v0) f4) f93)))
(assert (forall ((?v0 S24)) (= (f94 (f95 f96 ?v0) f4) f98)))
(assert (forall ((?v0 S4)) (= (f99 (f100 f101 ?v0) f4) f103)))
(assert (forall ((?v0 S36)) (= (f67 (f68 f69 ?v0) f4) f71)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f72 ?v0) f4) f10)))
(assert (forall ((?v0 S3)) (= (f22 (f23 f24 ?v0) f4) f73)))
(assert (forall ((?v0 S19)) (= (f74 (f75 f76 ?v0) f4) f78)))
(assert (forall ((?v0 S25)) (= (f79 (f80 f81 ?v0) f4) f83)))
(assert (forall ((?v0 S31)) (= (f84 (f85 f86 ?v0) f4) f88)))
(assert (forall ((?v0 S15)) (= (f89 (f90 f91 ?v0) f4) f93)))
(assert (forall ((?v0 S24)) (= (f94 (f95 f96 ?v0) f4) f98)))
(assert (forall ((?v0 S4)) (= (f99 (f100 f101 ?v0) f4) f103)))
(assert (forall ((?v0 S36) (?v1 S2)) (= (= (f67 (f68 f69 ?v0) ?v1) f70) (and (= ?v0 f70) (not (= ?v1 f4))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f5 (f6 f72 ?v0) ?v1) f4) (and (= ?v0 f4) (not (= ?v1 f4))))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (= (f22 (f23 f24 ?v0) ?v1) f3) (and (= ?v0 f3) (not (= ?v1 f4))))))
(assert (forall ((?v0 S19) (?v1 S2)) (= (= (f74 (f75 f76 ?v0) ?v1) f77) (and (= ?v0 f77) (not (= ?v1 f4))))))
(assert (forall ((?v0 S25) (?v1 S2)) (= (= (f79 (f80 f81 ?v0) ?v1) f82) (and (= ?v0 f82) (not (= ?v1 f4))))))
(assert (forall ((?v0 S24) (?v1 S2)) (= (= (f94 (f95 f96 ?v0) ?v1) f97) (and (= ?v0 f97) (not (= ?v1 f4))))))
(assert (forall ((?v0 S4) (?v1 S2)) (= (= (f99 (f100 f101 ?v0) ?v1) f102) (and (= ?v0 f102) (not (= ?v1 f4))))))
(assert (forall ((?v0 S36)) (= (f59 (f64 f65 ?v0) ?v0) (f59 (f64 f66 (f59 (f64 f65 f71) f71)) ?v0))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 ?v0) ?v0) (f5 (f6 f33 (f5 (f6 f7 f10) f10)) ?v0))))
(assert (forall ((?v0 S3)) (= (f16 (f19 f20 ?v0) ?v0) (f16 (f19 f21 (f16 (f19 f20 f73) f73)) ?v0))))
(assert (forall ((?v0 S19)) (= (f36 (f104 f105 ?v0) ?v0) (f36 (f104 f106 (f36 (f104 f105 f78) f78)) ?v0))))
(assert (forall ((?v0 S25)) (= (f45 (f107 f108 ?v0) ?v0) (f45 (f107 f109 (f45 (f107 f108 f83) f83)) ?v0))))
(assert (forall ((?v0 S31)) (= (f53 (f110 f111 ?v0) ?v0) (f53 (f110 f112 (f53 (f110 f111 f88) f88)) ?v0))))
(assert (forall ((?v0 S15)) (= (f30 (f56 f57 ?v0) ?v0) (f30 (f56 f58 (f30 (f56 f57 f93) f93)) ?v0))))
(assert (forall ((?v0 S24)) (= (f42 (f48 f49 ?v0) ?v0) (f42 (f48 f50 (f42 (f48 f49 f98) f98)) ?v0))))
(assert (forall ((?v0 S4)) (= (f11 (f39 f40 ?v0) ?v0) (f11 (f39 f41 (f11 (f39 f40 f103) f103)) ?v0))))
(assert (forall ((?v0 S36) (?v1 S36)) (= (f59 (f64 f65 ?v0) (f59 (f64 f66 ?v1) ?v0)) (f59 (f64 f66 (f59 (f64 f65 ?v1) f71)) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f5 (f6 f7 ?v0) (f5 (f6 f33 ?v1) ?v0)) (f5 (f6 f33 (f5 (f6 f7 ?v1) f10)) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f16 (f19 f20 ?v0) (f16 (f19 f21 ?v1) ?v0)) (f16 (f19 f21 (f16 (f19 f20 ?v1) f73)) ?v0))))
(assert (forall ((?v0 S19) (?v1 S19)) (= (f36 (f104 f105 ?v0) (f36 (f104 f106 ?v1) ?v0)) (f36 (f104 f106 (f36 (f104 f105 ?v1) f78)) ?v0))))
(assert (forall ((?v0 S25) (?v1 S25)) (= (f45 (f107 f108 ?v0) (f45 (f107 f109 ?v1) ?v0)) (f45 (f107 f109 (f45 (f107 f108 ?v1) f83)) ?v0))))
(assert (forall ((?v0 S31) (?v1 S31)) (= (f53 (f110 f111 ?v0) (f53 (f110 f112 ?v1) ?v0)) (f53 (f110 f112 (f53 (f110 f111 ?v1) f88)) ?v0))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (f30 (f56 f57 ?v0) (f30 (f56 f58 ?v1) ?v0)) (f30 (f56 f58 (f30 (f56 f57 ?v1) f93)) ?v0))))
(assert (forall ((?v0 S24) (?v1 S24)) (= (f42 (f48 f49 ?v0) (f42 (f48 f50 ?v1) ?v0)) (f42 (f48 f50 (f42 (f48 f49 ?v1) f98)) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f11 (f39 f40 ?v0) (f11 (f39 f41 ?v1) ?v0)) (f11 (f39 f41 (f11 (f39 f40 ?v1) f103)) ?v0))))
(assert (forall ((?v0 S36) (?v1 S36)) (= (f59 (f64 f65 (f59 (f64 f66 ?v0) ?v1)) ?v1) (f59 (f64 f66 (f59 (f64 f65 ?v0) f71)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f5 (f6 f7 (f5 (f6 f33 ?v0) ?v1)) ?v1) (f5 (f6 f33 (f5 (f6 f7 ?v0) f10)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f16 (f19 f20 (f16 (f19 f21 ?v0) ?v1)) ?v1) (f16 (f19 f21 (f16 (f19 f20 ?v0) f73)) ?v1))))
(assert (forall ((?v0 S19) (?v1 S19)) (= (f36 (f104 f105 (f36 (f104 f106 ?v0) ?v1)) ?v1) (f36 (f104 f106 (f36 (f104 f105 ?v0) f78)) ?v1))))
(assert (forall ((?v0 S25) (?v1 S25)) (= (f45 (f107 f108 (f45 (f107 f109 ?v0) ?v1)) ?v1) (f45 (f107 f109 (f45 (f107 f108 ?v0) f83)) ?v1))))
(assert (forall ((?v0 S31) (?v1 S31)) (= (f53 (f110 f111 (f53 (f110 f112 ?v0) ?v1)) ?v1) (f53 (f110 f112 (f53 (f110 f111 ?v0) f88)) ?v1))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (f30 (f56 f57 (f30 (f56 f58 ?v0) ?v1)) ?v1) (f30 (f56 f58 (f30 (f56 f57 ?v0) f93)) ?v1))))
(assert (forall ((?v0 S24) (?v1 S24)) (= (f42 (f48 f49 (f42 (f48 f50 ?v0) ?v1)) ?v1) (f42 (f48 f50 (f42 (f48 f49 ?v0) f98)) ?v1))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f11 (f39 f40 (f11 (f39 f41 ?v0) ?v1)) ?v1) (f11 (f39 f41 (f11 (f39 f40 ?v0) f103)) ?v1))))
(assert (forall ((?v0 S36) (?v1 S36)) (= (= (f59 (f64 f65 (f59 (f64 f66 ?v0) ?v0)) (f59 (f64 f66 ?v1) ?v1)) f70) (and (= ?v0 f70) (= ?v1 f70)))))
(assert (forall ((?v0 S25) (?v1 S25)) (= (= (f45 (f107 f108 (f45 (f107 f109 ?v0) ?v0)) (f45 (f107 f109 ?v1) ?v1)) f82) (and (= ?v0 f82) (= ?v1 f82)))))
(assert (forall ((?v0 S24) (?v1 S24)) (= (= (f42 (f48 f49 (f42 (f48 f50 ?v0) ?v0)) (f42 (f48 f50 ?v1) ?v1)) f97) (and (= ?v0 f97) (= ?v1 f97)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f19 f21 ?v0))) (=> (not (= ?v0 f3)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f16 (f19 f20 ?v1) (f16 ?v_0 ?v3)) (f16 (f19 f20 ?v2) (f16 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (let ((?v_0 (f6 f33 ?v0))) (=> (not (= ?v0 f4)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f5 (f6 f7 ?v1) (f5 ?v_0 ?v3)) (f5 (f6 f7 ?v2) (f5 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36) (?v3 S36) (?v4 S36)) (let ((?v_0 (f64 f66 ?v0))) (=> (not (= ?v0 f70)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f59 (f64 f65 ?v1) (f59 ?v_0 ?v3)) (f59 (f64 f65 ?v2) (f59 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19) (?v3 S19) (?v4 S19)) (let ((?v_0 (f104 f106 ?v0))) (=> (not (= ?v0 f77)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f36 (f104 f105 ?v1) (f36 ?v_0 ?v3)) (f36 (f104 f105 ?v2) (f36 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S25) (?v1 S25) (?v2 S25) (?v3 S25) (?v4 S25)) (let ((?v_0 (f107 f109 ?v0))) (=> (not (= ?v0 f82)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f45 (f107 f108 ?v1) (f45 ?v_0 ?v3)) (f45 (f107 f108 ?v2) (f45 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24) (?v3 S24) (?v4 S24)) (let ((?v_0 (f48 f50 ?v0))) (=> (not (= ?v0 f97)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f42 (f48 f49 ?v1) (f42 ?v_0 ?v3)) (f42 (f48 f49 ?v2) (f42 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4) (?v4 S4)) (let ((?v_0 (f39 f41 ?v0))) (=> (not (= ?v0 f102)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f11 (f39 f40 ?v1) (f11 ?v_0 ?v3)) (f11 (f39 f40 ?v2) (f11 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f5 f25 f4))) (= (= (f5 (f6 f72 ?v0) ?v1) ?v_0) (or (= ?v1 f4) (= ?v0 ?v_0))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f25 f4))) (= (f5 (f6 f72 ?v_0) ?v0) ?v_0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f72 ?v0))) (= (f5 (f6 f72 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f23 f24 ?v0))) (= (f22 (f23 f24 (f22 ?v_0 ?v1)) ?v2) (f22 ?v_0 (f5 (f6 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f100 f101 ?v0))) (= (f99 (f100 f101 (f99 ?v_0 ?v1)) ?v2) (f99 ?v_0 (f5 (f6 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S24) (?v1 S2) (?v2 S2)) (let ((?v_0 (f95 f96 ?v0))) (= (f94 (f95 f96 (f94 ?v_0 ?v1)) ?v2) (f94 ?v_0 (f5 (f6 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S15) (?v1 S2) (?v2 S2)) (let ((?v_0 (f90 f91 ?v0))) (= (f89 (f90 f91 (f89 ?v_0 ?v1)) ?v2) (f89 ?v_0 (f5 (f6 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S36) (?v1 S2) (?v2 S2)) (let ((?v_0 (f68 f69 ?v0))) (= (f67 (f68 f69 (f67 ?v_0 ?v1)) ?v2) (f67 ?v_0 (f5 (f6 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f72 ?v0))) (= (f5 ?v_0 (f5 (f6 f33 ?v1) ?v2)) (f5 (f6 f72 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f23 f24 ?v0))) (= (f22 ?v_0 (f5 (f6 f33 ?v1) ?v2)) (f22 (f23 f24 (f22 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f100 f101 ?v0))) (= (f99 ?v_0 (f5 (f6 f33 ?v1) ?v2)) (f99 (f100 f101 (f99 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S24) (?v1 S2) (?v2 S2)) (let ((?v_0 (f95 f96 ?v0))) (= (f94 ?v_0 (f5 (f6 f33 ?v1) ?v2)) (f94 (f95 f96 (f94 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S15) (?v1 S2) (?v2 S2)) (let ((?v_0 (f90 f91 ?v0))) (= (f89 ?v_0 (f5 (f6 f33 ?v1) ?v2)) (f89 (f90 f91 (f89 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S36) (?v1 S2) (?v2 S2)) (let ((?v_0 (f68 f69 ?v0))) (= (f67 ?v_0 (f5 (f6 f33 ?v1) ?v2)) (f67 (f68 f69 (f67 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S25)) (= (= (f43 f44 ?v0) (f43 f44 f82)) (= ?v0 f82))))
(assert (forall ((?v0 S24)) (= (= (f60 f61 ?v0) (f60 f61 f97)) (= ?v0 f97))))
(assert (forall ((?v0 S10)) (= (= (f26 ?v0) f1) (forall ((?v1 S3) (?v2 S3)) (= (f16 ?v0 ?v1) (f16 ?v0 ?v2))))))
(assert (= f103 (f11 (f12 f13 f73) f102)))
(assert (= f98 (f42 (f62 f63 f71) f97)))
(assert (= f93 (f30 (f31 f32 f10) f92)))
(assert (= f113 (f114 f78 f115)))
(assert (= f116 (f117 f83 f118)))
(assert (= f119 (f120 f88 f121)))
(assert (= f88 (f53 (f54 f55 f93) f87)))
(assert (= f83 (f45 (f46 f47 f98) f82)))
(assert (= f78 (f36 (f37 f38 f103) f77)))
(assert (forall ((?v0 S4)) (= (= (f8 f9 ?v0) f4) (= ?v0 f102))))
(assert (forall ((?v0 S19)) (= (= (f122 f123 ?v0) f4) (= ?v0 f77))))
(assert (forall ((?v0 S25)) (= (= (f124 f125 ?v0) f4) (= ?v0 f82))))
(assert (forall ((?v0 S31)) (= (= (f126 f127 ?v0) f4) (= ?v0 f87))))
(assert (forall ((?v0 S15)) (= (= (f128 f129 ?v0) f4) (= ?v0 f92))))
(assert (forall ((?v0 S24)) (= (= (f130 f131 ?v0) f4) (= ?v0 f97))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f6 f33 ?v0))) (= (f5 (f6 f33 (f5 ?v_0 ?v1)) (f5 (f6 f33 ?v2) ?v3)) (f5 (f6 f33 (f5 ?v_0 ?v2)) (f5 (f6 f33 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f19 f21 ?v0))) (= (f16 (f19 f21 (f16 ?v_0 ?v1)) (f16 (f19 f21 ?v2) ?v3)) (f16 (f19 f21 (f16 ?v_0 ?v2)) (f16 (f19 f21 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f39 f41 ?v0))) (= (f11 (f39 f41 (f11 ?v_0 ?v1)) (f11 (f39 f41 ?v2) ?v3)) (f11 (f39 f41 (f11 ?v_0 ?v2)) (f11 (f39 f41 ?v1) ?v3))))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24) (?v3 S24)) (let ((?v_0 (f48 f50 ?v0))) (= (f42 (f48 f50 (f42 ?v_0 ?v1)) (f42 (f48 f50 ?v2) ?v3)) (f42 (f48 f50 (f42 ?v_0 ?v2)) (f42 (f48 f50 ?v1) ?v3))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (let ((?v_0 (f56 f58 ?v0))) (= (f30 (f56 f58 (f30 ?v_0 ?v1)) (f30 (f56 f58 ?v2) ?v3)) (f30 (f56 f58 (f30 ?v_0 ?v2)) (f30 (f56 f58 ?v1) ?v3))))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36) (?v3 S36)) (let ((?v_0 (f64 f66 ?v0))) (= (f59 (f64 f66 (f59 ?v_0 ?v1)) (f59 (f64 f66 ?v2) ?v3)) (f59 (f64 f66 (f59 ?v_0 ?v2)) (f59 (f64 f66 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_1 (f6 f33 (f5 (f6 f33 ?v0) ?v1))) (?v_0 (f6 f33 ?v2))) (= (f5 ?v_1 (f5 ?v_0 ?v3)) (f5 ?v_0 (f5 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f19 f21 (f16 (f19 f21 ?v0) ?v1))) (?v_0 (f19 f21 ?v2))) (= (f16 ?v_1 (f16 ?v_0 ?v3)) (f16 ?v_0 (f16 ?v_1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_1 (f39 f41 (f11 (f39 f41 ?v0) ?v1))) (?v_0 (f39 f41 ?v2))) (= (f11 ?v_1 (f11 ?v_0 ?v3)) (f11 ?v_0 (f11 ?v_1 ?v3))))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24) (?v3 S24)) (let ((?v_1 (f48 f50 (f42 (f48 f50 ?v0) ?v1))) (?v_0 (f48 f50 ?v2))) (= (f42 ?v_1 (f42 ?v_0 ?v3)) (f42 ?v_0 (f42 ?v_1 ?v3))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (let ((?v_1 (f56 f58 (f30 (f56 f58 ?v0) ?v1))) (?v_0 (f56 f58 ?v2))) (= (f30 ?v_1 (f30 ?v_0 ?v3)) (f30 ?v_0 (f30 ?v_1 ?v3))))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36) (?v3 S36)) (let ((?v_1 (f64 f66 (f59 (f64 f66 ?v0) ?v1))) (?v_0 (f64 f66 ?v2))) (= (f59 ?v_1 (f59 ?v_0 ?v3)) (f59 ?v_0 (f59 ?v_1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f6 f33 ?v0)) (?v_1 (f5 (f6 f33 ?v2) ?v3))) (= (f5 (f6 f33 (f5 ?v_0 ?v1)) ?v_1) (f5 ?v_0 (f5 (f6 f33 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f19 f21 ?v0)) (?v_1 (f16 (f19 f21 ?v2) ?v3))) (= (f16 (f19 f21 (f16 ?v_0 ?v1)) ?v_1) (f16 ?v_0 (f16 (f19 f21 ?v1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f39 f41 ?v0)) (?v_1 (f11 (f39 f41 ?v2) ?v3))) (= (f11 (f39 f41 (f11 ?v_0 ?v1)) ?v_1) (f11 ?v_0 (f11 (f39 f41 ?v1) ?v_1))))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24) (?v3 S24)) (let ((?v_0 (f48 f50 ?v0)) (?v_1 (f42 (f48 f50 ?v2) ?v3))) (= (f42 (f48 f50 (f42 ?v_0 ?v1)) ?v_1) (f42 ?v_0 (f42 (f48 f50 ?v1) ?v_1))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (let ((?v_0 (f56 f58 ?v0)) (?v_1 (f30 (f56 f58 ?v2) ?v3))) (= (f30 (f56 f58 (f30 ?v_0 ?v1)) ?v_1) (f30 ?v_0 (f30 (f56 f58 ?v1) ?v_1))))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36) (?v3 S36)) (let ((?v_0 (f64 f66 ?v0)) (?v_1 (f59 (f64 f66 ?v2) ?v3))) (= (f59 (f64 f66 (f59 ?v_0 ?v1)) ?v_1) (f59 ?v_0 (f59 (f64 f66 ?v1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f33 ?v0))) (= (f5 (f6 f33 (f5 ?v_0 ?v1)) ?v2) (f5 (f6 f33 (f5 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f19 f21 ?v0))) (= (f16 (f19 f21 (f16 ?v_0 ?v1)) ?v2) (f16 (f19 f21 (f16 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f39 f41 ?v0))) (= (f11 (f39 f41 (f11 ?v_0 ?v1)) ?v2) (f11 (f39 f41 (f11 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24)) (let ((?v_0 (f48 f50 ?v0))) (= (f42 (f48 f50 (f42 ?v_0 ?v1)) ?v2) (f42 (f48 f50 (f42 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f56 f58 ?v0))) (= (f30 (f56 f58 (f30 ?v_0 ?v1)) ?v2) (f30 (f56 f58 (f30 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (let ((?v_0 (f64 f66 ?v0))) (= (f59 (f64 f66 (f59 ?v_0 ?v1)) ?v2) (f59 (f64 f66 (f59 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f33 ?v0))) (= (f5 (f6 f33 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f19 f21 ?v0))) (= (f16 (f19 f21 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f19 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f39 f41 ?v0))) (= (f11 (f39 f41 (f11 ?v_0 ?v1)) ?v2) (f11 ?v_0 (f11 (f39 f41 ?v1) ?v2))))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24)) (let ((?v_0 (f48 f50 ?v0))) (= (f42 (f48 f50 (f42 ?v_0 ?v1)) ?v2) (f42 ?v_0 (f42 (f48 f50 ?v1) ?v2))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f56 f58 ?v0))) (= (f30 (f56 f58 (f30 ?v_0 ?v1)) ?v2) (f30 ?v_0 (f30 (f56 f58 ?v1) ?v2))))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (let ((?v_0 (f64 f66 ?v0))) (= (f59 (f64 f66 (f59 ?v_0 ?v1)) ?v2) (f59 ?v_0 (f59 (f64 f66 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f33 ?v0))) (= (f5 ?v_0 (f5 (f6 f33 ?v1) ?v2)) (f5 (f6 f33 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f19 f21 ?v0))) (= (f16 ?v_0 (f16 (f19 f21 ?v1) ?v2)) (f16 (f19 f21 (f16 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f39 f41 ?v0))) (= (f11 ?v_0 (f11 (f39 f41 ?v1) ?v2)) (f11 (f39 f41 (f11 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24)) (let ((?v_0 (f48 f50 ?v0))) (= (f42 ?v_0 (f42 (f48 f50 ?v1) ?v2)) (f42 (f48 f50 (f42 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f56 f58 ?v0))) (= (f30 ?v_0 (f30 (f56 f58 ?v1) ?v2)) (f30 (f56 f58 (f30 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (let ((?v_0 (f64 f66 ?v0))) (= (f59 ?v_0 (f59 (f64 f66 ?v1) ?v2)) (f59 (f64 f66 (f59 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f6 f33 ?v0)) (?v_0 (f6 f33 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f19 f21 ?v0)) (?v_0 (f19 f21 ?v1))) (= (f16 ?v_1 (f16 ?v_0 ?v2)) (f16 ?v_0 (f16 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f39 f41 ?v0)) (?v_0 (f39 f41 ?v1))) (= (f11 ?v_1 (f11 ?v_0 ?v2)) (f11 ?v_0 (f11 ?v_1 ?v2))))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S24)) (let ((?v_1 (f48 f50 ?v0)) (?v_0 (f48 f50 ?v1))) (= (f42 ?v_1 (f42 ?v_0 ?v2)) (f42 ?v_0 (f42 ?v_1 ?v2))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_1 (f56 f58 ?v0)) (?v_0 (f56 f58 ?v1))) (= (f30 ?v_1 (f30 ?v_0 ?v2)) (f30 ?v_0 (f30 ?v_1 ?v2))))))
(assert (forall ((?v0 S36) (?v1 S36) (?v2 S36)) (let ((?v_1 (f64 f66 ?v0)) (?v_0 (f64 f66 ?v1))) (= (f59 ?v_1 (f59 ?v_0 ?v2)) (f59 ?v_0 (f59 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f5 (f6 f33 ?v0) ?v1) (f5 (f6 f33 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f16 (f19 f21 ?v0) ?v1) (f16 (f19 f21 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f11 (f39 f41 ?v0) ?v1) (f11 (f39 f41 ?v1) ?v0))))
(assert (forall ((?v0 S24) (?v1 S24)) (= (f42 (f48 f50 ?v0) ?v1) (f42 (f48 f50 ?v1) ?v0))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (f30 (f56 f58 ?v0) ?v1) (f30 (f56 f58 ?v1) ?v0))))
(assert (forall ((?v0 S36) (?v1 S36)) (= (f59 (f64 f66 ?v0) ?v1) (f59 (f64 f66 ?v1) ?v0))))
(check-sat)
(exit)