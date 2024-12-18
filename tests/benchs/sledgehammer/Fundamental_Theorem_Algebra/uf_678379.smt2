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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 () S2)
(declare-fun f6 (S6 S5) S5)
(declare-fun f7 (S7 S2) S6)
(declare-fun f8 () S7)
(declare-fun f9 (S8 S5) S6)
(declare-fun f10 () S8)
(declare-fun f11 () S5)
(declare-fun f12 (S9 S2) S2)
(declare-fun f13 (S10 S2) S9)
(declare-fun f14 () S10)
(declare-fun f15 (S13 S12) S12)
(declare-fun f16 (S14 S11) S13)
(declare-fun f17 () S14)
(declare-fun f18 (S15 S11) S11)
(declare-fun f19 (S16 S11) S15)
(declare-fun f20 () S16)
(declare-fun f21 (S17 S12) S13)
(declare-fun f22 () S17)
(declare-fun f23 (S19 S18) S18)
(declare-fun f24 (S20 S12) S19)
(declare-fun f25 () S20)
(declare-fun f26 (S21 S18) S19)
(declare-fun f27 () S21)
(declare-fun f28 (S24 S23) S23)
(declare-fun f29 (S25 S22) S24)
(declare-fun f30 () S25)
(declare-fun f31 (S26 S22) S22)
(declare-fun f32 (S27 S22) S26)
(declare-fun f33 () S27)
(declare-fun f34 (S28 S23) S24)
(declare-fun f35 () S28)
(declare-fun f36 (S29 S23) S9)
(declare-fun f37 () S29)
(declare-fun f38 (S30 S5) S2)
(declare-fun f39 (S31 S2) S30)
(declare-fun f40 () S31)
(declare-fun f41 (S32 S12) S11)
(declare-fun f42 (S33 S11) S32)
(declare-fun f43 () S33)
(declare-fun f44 (S34 S18) S12)
(declare-fun f45 (S35 S12) S34)
(declare-fun f46 () S35)
(declare-fun f47 (S36 S23) S22)
(declare-fun f48 (S37 S22) S36)
(declare-fun f49 () S37)
(declare-fun f50 (S38 S2) S23)
(declare-fun f51 (S39 S23) S38)
(declare-fun f52 () S39)
(declare-fun f53 () S10)
(declare-fun f54 () S28)
(declare-fun f55 () S17)
(declare-fun f56 (S40 S4) S2)
(declare-fun f57 (S41 S5) S40)
(declare-fun f58 () S41)
(declare-fun f59 (S42 S4) S11)
(declare-fun f60 (S43 S12) S42)
(declare-fun f61 () S43)
(declare-fun f62 (S44 S4) S22)
(declare-fun f63 (S45 S23) S44)
(declare-fun f64 () S45)
(declare-fun f65 (S46 S4) S23)
(declare-fun f66 (S47 S2) S46)
(declare-fun f67 () S47)
(declare-fun f68 (S48 S4) S12)
(declare-fun f69 (S49 S18) S48)
(declare-fun f70 () S49)
(declare-fun f71 (S12) S1)
(declare-fun f72 (S50 S5) S9)
(declare-fun f73 () S50)
(declare-fun f74 (S51 S12) S15)
(declare-fun f75 () S51)
(declare-fun f76 (S52 S23) S26)
(declare-fun f77 () S52)
(declare-fun f78 (S53 S2) S24)
(declare-fun f79 () S53)
(declare-fun f80 (S54 S18) S13)
(declare-fun f81 () S54)
(declare-fun f82 (S55 S4) S5)
(declare-fun f83 (S56 S2) S55)
(declare-fun f84 () S56)
(declare-fun f85 (S57 S11) S48)
(declare-fun f86 () S57)
(declare-fun f87 (S58 S22) S46)
(declare-fun f88 () S58)
(declare-fun f89 (S59 S23) S40)
(declare-fun f90 () S59)
(declare-fun f91 (S60 S4) S18)
(declare-fun f92 (S61 S12) S60)
(declare-fun f93 () S61)
(declare-fun f94 () S50)
(declare-fun f95 () S51)
(declare-fun f96 () S52)
(declare-fun f97 () S53)
(declare-fun f98 () S54)
(declare-fun f99 () S11)
(declare-fun f100 () S23)
(declare-fun f101 () S2)
(declare-fun f102 () S12)
(declare-fun f103 (S11) S1)
(declare-fun f104 () S18)
(declare-fun f105 (S62 S63) S63)
(declare-fun f106 (S64 S11) S62)
(declare-fun f107 () S64)
(declare-fun f108 () S63)
(declare-fun f109 () S5)
(declare-fun f110 (S65 S63) S42)
(declare-fun f111 () S65)
(declare-fun f112 (S66 S4) S63)
(declare-fun f113 (S67 S11) S66)
(declare-fun f114 () S67)
(declare-fun f115 () S64)
(declare-fun f116 () S16)
(assert (not (= f1 f2)))
(assert (not (exists ((?v0 S2)) (and (= (f3 f4 ?v0) (f3 f4 f5)) (forall ((?v1 S5)) (= (f6 (f7 f8 ?v0) ?v1) (f6 (f7 f8 f5) (f6 (f9 f10 f11) ?v1))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S5)) (= (f6 (f7 f8 (f12 (f13 f14 ?v0) ?v1)) ?v2) (f6 (f9 f10 (f6 (f7 f8 ?v0) ?v2)) (f6 (f7 f8 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (= (f15 (f16 f17 (f18 (f19 f20 ?v0) ?v1)) ?v2) (f15 (f21 f22 (f15 (f16 f17 ?v0) ?v2)) (f15 (f16 f17 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S18)) (= (f23 (f24 f25 (f15 (f21 f22 ?v0) ?v1)) ?v2) (f23 (f26 f27 (f23 (f24 f25 ?v0) ?v2)) (f23 (f24 f25 ?v1) ?v2)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S23)) (= (f28 (f29 f30 (f31 (f32 f33 ?v0) ?v1)) ?v2) (f28 (f34 f35 (f28 (f29 f30 ?v0) ?v2)) (f28 (f29 f30 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S2)) (= (f12 (f36 f37 (f28 (f34 f35 ?v0) ?v1)) ?v2) (f12 (f13 f14 (f12 (f36 f37 ?v0) ?v2)) (f12 (f36 f37 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S5)) (= (f6 (f7 f8 (f38 (f39 f40 ?v0) ?v1)) ?v2) (f6 (f7 f8 ?v0) (f6 (f9 f10 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S12)) (= (f15 (f16 f17 (f41 (f42 f43 ?v0) ?v1)) ?v2) (f15 (f16 f17 ?v0) (f15 (f21 f22 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S18) (?v2 S18)) (= (f23 (f24 f25 (f44 (f45 f46 ?v0) ?v1)) ?v2) (f23 (f24 f25 ?v0) (f23 (f26 f27 ?v1) ?v2)))))
(assert (forall ((?v0 S22) (?v1 S23) (?v2 S23)) (= (f28 (f29 f30 (f47 (f48 f49 ?v0) ?v1)) ?v2) (f28 (f29 f30 ?v0) (f28 (f34 f35 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S2) (?v2 S2)) (= (f12 (f36 f37 (f50 (f51 f52 ?v0) ?v1)) ?v2) (f12 (f36 f37 ?v0) (f12 (f13 f14 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f7 f8 ?v0) (f7 f8 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f6 (f9 f10 ?v0) ?v1) (f6 (f9 f10 ?v1) ?v0))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (f15 (f21 f22 ?v0) ?v1) (f15 (f21 f22 ?v1) ?v0))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f23 (f26 f27 ?v0) ?v1) (f23 (f26 f27 ?v1) ?v0))))
(assert (forall ((?v0 S23) (?v1 S23)) (= (f28 (f34 f35 ?v0) ?v1) (f28 (f34 f35 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f12 (f13 f14 ?v0) ?v1) (f12 (f13 f14 ?v1) ?v0))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_1 (f9 f10 ?v0)) (?v_0 (f9 f10 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_1 (f21 f22 ?v0)) (?v_0 (f21 f22 ?v1))) (= (f15 ?v_1 (f15 ?v_0 ?v2)) (f15 ?v_0 (f15 ?v_1 ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_1 (f26 f27 ?v0)) (?v_0 (f26 f27 ?v1))) (= (f23 ?v_1 (f23 ?v_0 ?v2)) (f23 ?v_0 (f23 ?v_1 ?v2))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_1 (f34 f35 ?v0)) (?v_0 (f34 f35 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f13 f14 ?v0)) (?v_0 (f13 f14 ?v1))) (= (f12 ?v_1 (f12 ?v_0 ?v2)) (f12 ?v_0 (f12 ?v_1 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (f6 ?v_0 (f6 (f9 f10 ?v1) ?v2)) (f6 (f9 f10 (f6 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f21 f22 ?v0))) (= (f15 ?v_0 (f15 (f21 f22 ?v1) ?v2)) (f15 (f21 f22 (f15 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f26 f27 ?v0))) (= (f23 ?v_0 (f23 (f26 f27 ?v1) ?v2)) (f23 (f26 f27 (f23 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f34 f35 ?v0))) (= (f28 ?v_0 (f28 (f34 f35 ?v1) ?v2)) (f28 (f34 f35 (f28 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (f12 ?v_0 (f12 (f13 f14 ?v1) ?v2)) (f12 (f13 f14 (f12 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (f6 (f9 f10 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f9 f10 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f21 f22 ?v0))) (= (f15 (f21 f22 (f15 ?v_0 ?v1)) ?v2) (f15 ?v_0 (f15 (f21 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f26 f27 ?v0))) (= (f23 (f26 f27 (f23 ?v_0 ?v1)) ?v2) (f23 ?v_0 (f23 (f26 f27 ?v1) ?v2))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f34 f35 ?v0))) (= (f28 (f34 f35 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f34 f35 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (f12 (f13 f14 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f13 f14 ?v1) ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (f6 (f9 f10 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f9 f10 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f21 f22 ?v0))) (= (f15 (f21 f22 (f15 ?v_0 ?v1)) ?v2) (f15 ?v_0 (f15 (f21 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f26 f27 ?v0))) (= (f23 (f26 f27 (f23 ?v_0 ?v1)) ?v2) (f23 ?v_0 (f23 (f26 f27 ?v1) ?v2))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f34 f35 ?v0))) (= (f28 (f34 f35 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f34 f35 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (f12 (f13 f14 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f13 f14 ?v1) ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (f6 (f9 f10 (f6 ?v_0 ?v1)) ?v2) (f6 (f9 f10 (f6 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f21 f22 ?v0))) (= (f15 (f21 f22 (f15 ?v_0 ?v1)) ?v2) (f15 (f21 f22 (f15 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f26 f27 ?v0))) (= (f23 (f26 f27 (f23 ?v_0 ?v1)) ?v2) (f23 (f26 f27 (f23 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f34 f35 ?v0))) (= (f28 (f34 f35 (f28 ?v_0 ?v1)) ?v2) (f28 (f34 f35 (f28 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (f12 (f13 f14 (f12 ?v_0 ?v1)) ?v2) (f12 (f13 f14 (f12 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (= (f6 ?v_0 ?v1) (f6 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f21 f22 ?v0))) (= (= (f15 ?v_0 ?v1) (f15 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f26 f27 ?v0))) (= (= (f23 ?v_0 ?v1) (f23 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f34 f35 ?v0))) (= (= (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (= (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (= (= (f6 (f9 f10 ?v0) ?v1) (f6 (f9 f10 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (= (= (f15 (f21 f22 ?v0) ?v1) (f15 (f21 f22 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (= (= (f23 (f26 f27 ?v0) ?v1) (f23 (f26 f27 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (= (= (f28 (f34 f35 ?v0) ?v1) (f28 (f34 f35 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f12 (f13 f14 ?v0) ?v1) (f12 (f13 f14 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (f6 (f9 f10 (f6 ?v_0 ?v1)) (f6 (f9 f10 ?v2) ?v3)) (f6 (f9 f10 (f6 ?v_0 ?v2)) (f6 (f9 f10 ?v1) ?v3))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (let ((?v_0 (f21 f22 ?v0))) (= (f15 (f21 f22 (f15 ?v_0 ?v1)) (f15 (f21 f22 ?v2) ?v3)) (f15 (f21 f22 (f15 ?v_0 ?v2)) (f15 (f21 f22 ?v1) ?v3))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18) (?v3 S18)) (let ((?v_0 (f26 f27 ?v0))) (= (f23 (f26 f27 (f23 ?v_0 ?v1)) (f23 (f26 f27 ?v2) ?v3)) (f23 (f26 f27 (f23 ?v_0 ?v2)) (f23 (f26 f27 ?v1) ?v3))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23) (?v3 S23)) (let ((?v_0 (f34 f35 ?v0))) (= (f28 (f34 f35 (f28 ?v_0 ?v1)) (f28 (f34 f35 ?v2) ?v3)) (f28 (f34 f35 (f28 ?v_0 ?v2)) (f28 (f34 f35 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (f12 (f13 f14 (f12 ?v_0 ?v1)) (f12 (f13 f14 ?v2) ?v3)) (f12 (f13 f14 (f12 ?v_0 ?v2)) (f12 (f13 f14 ?v1) ?v3))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f6 (f9 f10 ?v0) ?v1) (f6 (f9 f10 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= (f15 (f21 f22 ?v0) ?v1) (f15 (f21 f22 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f23 (f26 f27 ?v0) ?v1) (f23 (f26 f27 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (=> (= (f28 (f34 f35 ?v0) ?v1) (f28 (f34 f35 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f12 (f13 f14 ?v0) ?v1) (f12 (f13 f14 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (=> (= (f6 ?v_0 ?v1) (f6 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f21 f22 ?v0))) (=> (= (f15 ?v_0 ?v1) (f15 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f26 f27 ?v0))) (=> (= (f23 ?v_0 ?v1) (f23 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f34 f35 ?v0))) (=> (= (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (=> (= (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (=> (= (f6 ?v_0 ?v1) (f6 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f21 f22 ?v0))) (=> (= (f15 ?v_0 ?v1) (f15 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f26 f27 ?v0))) (=> (= (f23 ?v_0 ?v1) (f23 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f34 f35 ?v0))) (=> (= (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f14 ?v0))) (=> (= (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S5)) (= (f6 (f7 f8 (f12 (f13 f53 ?v0) ?v1)) ?v2) (f6 (f7 f8 ?v0) (f6 (f7 f8 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S2)) (= (f12 (f36 f37 (f28 (f34 f54 ?v0) ?v1)) ?v2) (f12 (f36 f37 ?v0) (f12 (f36 f37 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S18)) (= (f23 (f24 f25 (f15 (f21 f55 ?v0) ?v1)) ?v2) (f23 (f24 f25 ?v0) (f23 (f24 f25 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S4) (?v2 S5)) (= (f12 (f13 f14 (f56 (f57 f58 ?v0) ?v1)) (f56 (f57 f58 ?v2) ?v1)) (f56 (f57 f58 (f6 (f9 f10 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S12) (?v1 S4) (?v2 S12)) (= (f18 (f19 f20 (f59 (f60 f61 ?v0) ?v1)) (f59 (f60 f61 ?v2) ?v1)) (f59 (f60 f61 (f15 (f21 f22 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S23) (?v1 S4) (?v2 S23)) (= (f31 (f32 f33 (f62 (f63 f64 ?v0) ?v1)) (f62 (f63 f64 ?v2) ?v1)) (f62 (f63 f64 (f28 (f34 f35 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S2)) (= (f28 (f34 f35 (f65 (f66 f67 ?v0) ?v1)) (f65 (f66 f67 ?v2) ?v1)) (f65 (f66 f67 (f12 (f13 f14 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S18) (?v1 S4) (?v2 S18)) (= (f15 (f21 f22 (f68 (f69 f70 ?v0) ?v1)) (f68 (f69 f70 ?v2) ?v1)) (f68 (f69 f70 (f23 (f26 f27 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f71 ?v0) f1) (=> (= (f71 ?v1) f1) (= (f71 (f15 (f21 f22 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S2)) (= (f12 (f72 f73 (f6 (f9 f10 ?v0) ?v1)) ?v2) (f12 (f13 f14 (f12 (f72 f73 ?v0) ?v2)) (f12 (f72 f73 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S11)) (= (f18 (f74 f75 (f15 (f21 f22 ?v0) ?v1)) ?v2) (f18 (f19 f20 (f18 (f74 f75 ?v0) ?v2)) (f18 (f74 f75 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S22)) (= (f31 (f76 f77 (f28 (f34 f35 ?v0) ?v1)) ?v2) (f31 (f32 f33 (f31 (f76 f77 ?v0) ?v2)) (f31 (f76 f77 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S23)) (= (f28 (f78 f79 (f12 (f13 f14 ?v0) ?v1)) ?v2) (f28 (f34 f35 (f28 (f78 f79 ?v0) ?v2)) (f28 (f78 f79 ?v1) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S12)) (= (f15 (f80 f81 (f23 (f26 f27 ?v0) ?v1)) ?v2) (f15 (f21 f22 (f15 (f80 f81 ?v0) ?v2)) (f15 (f80 f81 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S4)) (= (f82 (f83 f84 (f12 (f13 f14 ?v0) ?v1)) ?v2) (f6 (f9 f10 (f82 (f83 f84 ?v0) ?v2)) (f82 (f83 f84 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S4)) (= (f68 (f85 f86 (f18 (f19 f20 ?v0) ?v1)) ?v2) (f15 (f21 f22 (f68 (f85 f86 ?v0) ?v2)) (f68 (f85 f86 ?v1) ?v2)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S4)) (= (f65 (f87 f88 (f31 (f32 f33 ?v0) ?v1)) ?v2) (f28 (f34 f35 (f65 (f87 f88 ?v0) ?v2)) (f65 (f87 f88 ?v1) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S4)) (= (f56 (f89 f90 (f28 (f34 f35 ?v0) ?v1)) ?v2) (f12 (f13 f14 (f56 (f89 f90 ?v0) ?v2)) (f56 (f89 f90 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S4)) (= (f91 (f92 f93 (f15 (f21 f22 ?v0) ?v1)) ?v2) (f23 (f26 f27 (f91 (f92 f93 ?v0) ?v2)) (f91 (f92 f93 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S5) (?v3 S2)) (= (f12 (f13 f14 (f12 (f72 f94 ?v0) ?v1)) (f12 (f72 f94 ?v2) ?v3)) (f12 (f72 f94 (f6 (f9 f10 ?v0) ?v2)) (f12 (f13 f14 ?v1) ?v3)))))
(assert (forall ((?v0 S12) (?v1 S11) (?v2 S12) (?v3 S11)) (= (f18 (f19 f20 (f18 (f74 f95 ?v0) ?v1)) (f18 (f74 f95 ?v2) ?v3)) (f18 (f74 f95 (f15 (f21 f22 ?v0) ?v2)) (f18 (f19 f20 ?v1) ?v3)))))
(assert (forall ((?v0 S23) (?v1 S22) (?v2 S23) (?v3 S22)) (= (f31 (f32 f33 (f31 (f76 f96 ?v0) ?v1)) (f31 (f76 f96 ?v2) ?v3)) (f31 (f76 f96 (f28 (f34 f35 ?v0) ?v2)) (f31 (f32 f33 ?v1) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S2) (?v3 S23)) (= (f28 (f34 f35 (f28 (f78 f97 ?v0) ?v1)) (f28 (f78 f97 ?v2) ?v3)) (f28 (f78 f97 (f12 (f13 f14 ?v0) ?v2)) (f28 (f34 f35 ?v1) ?v3)))))
(assert (forall ((?v0 S18) (?v1 S12) (?v2 S18) (?v3 S12)) (= (f15 (f21 f22 (f15 (f80 f98 ?v0) ?v1)) (f15 (f80 f98 ?v2) ?v3)) (f15 (f80 f98 (f23 (f26 f27 ?v0) ?v2)) (f15 (f21 f22 ?v1) ?v3)))))
(assert (forall ((?v0 S12)) (= (f41 (f42 f43 f99) ?v0) f99)))
(assert (forall ((?v0 S2)) (= (f50 (f51 f52 f100) ?v0) f100)))
(assert (forall ((?v0 S5)) (= (f38 (f39 f40 f101) ?v0) f101)))
(assert (forall ((?v0 S18)) (= (f44 (f45 f46 f102) ?v0) f102)))
(assert (forall ((?v0 S11) (?v1 S12)) (= (= (f41 (f42 f43 ?v0) ?v1) f99) (= ?v0 f99))))
(assert (forall ((?v0 S23) (?v1 S2)) (= (= (f50 (f51 f52 ?v0) ?v1) f100) (= ?v0 f100))))
(assert (forall ((?v0 S2) (?v1 S5)) (= (= (f38 (f39 f40 ?v0) ?v1) f101) (= ?v0 f101))))
(assert (forall ((?v0 S12) (?v1 S18)) (= (= (f44 (f45 f46 ?v0) ?v1) f102) (= ?v0 f102))))
(assert (forall ((?v0 S23)) (= (f28 (f34 f35 f100) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f18 (f19 f20 f99) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f15 (f21 f22 f102) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f12 (f13 f14 f101) ?v0) ?v0)))
(assert (not (= (f103 f99) f1)))
(assert (not (= (f71 f102) f1)))
(assert (= (f15 (f80 f98 f104) f102) f102))
(assert (= (f28 (f78 f97 f101) f100) f100))
(assert (= (f105 (f106 f107 f99) f108) f108))
(assert (= (f18 (f74 f95 f102) f99) f99))
(assert (= (f12 (f72 f94 f109) f101) f101))
(assert (forall ((?v0 S4)) (= (f91 (f92 f93 f102) ?v0) f104)))
(assert (forall ((?v0 S4)) (= (f56 (f89 f90 f100) ?v0) f101)))
(assert (forall ((?v0 S4)) (= (f59 (f110 f111 f108) ?v0) f99)))
(assert (forall ((?v0 S4)) (= (f68 (f85 f86 f99) ?v0) f102)))
(assert (forall ((?v0 S4)) (= (f82 (f83 f84 f101) ?v0) f109)))
(assert (forall ((?v0 S4)) (= (f68 (f69 f70 f104) ?v0) f102)))
(assert (forall ((?v0 S4)) (= (f65 (f66 f67 f101) ?v0) f100)))
(assert (forall ((?v0 S4)) (= (f112 (f113 f114 f99) ?v0) f108)))
(assert (forall ((?v0 S4)) (= (f59 (f60 f61 f102) ?v0) f99)))
(assert (forall ((?v0 S4)) (= (f56 (f57 f58 f109) ?v0) f101)))
(assert (forall ((?v0 S12)) (= (f15 (f80 f81 f104) ?v0) f102)))
(assert (forall ((?v0 S23)) (= (f28 (f78 f79 f101) ?v0) f100)))
(assert (forall ((?v0 S63)) (= (f105 (f106 f115 f99) ?v0) f108)))
(assert (forall ((?v0 S11)) (= (f18 (f74 f75 f102) ?v0) f99)))
(assert (forall ((?v0 S2)) (= (f12 (f72 f73 f109) ?v0) f101)))
(assert (forall ((?v0 S11)) (= (f18 (f19 f116 f99) ?v0) f99)))
(assert (forall ((?v0 S12)) (= (f15 (f21 f55 f102) ?v0) f102)))
(assert (forall ((?v0 S2)) (= (f12 (f13 f53 f101) ?v0) f101)))
(check-sat)
(exit)
