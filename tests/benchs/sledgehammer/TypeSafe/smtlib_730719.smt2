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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 () S2)
(declare-fun f5 () S3)
(declare-fun f6 (S4 S5) S1)
(declare-fun f7 (S6 S7) S4)
(declare-fun f8 (S8 S7) S6)
(declare-fun f9 () S8)
(declare-fun f10 (S9 S10) S7)
(declare-fun f11 (S11 S12) S9)
(declare-fun f12 () S11)
(declare-fun f13 () S12)
(declare-fun f14 (S13 S14) S10)
(declare-fun f15 (S15 S16) S13)
(declare-fun f16 () S15)
(declare-fun f17 () S16)
(declare-fun f18 () S14)
(declare-fun f19 () S12)
(declare-fun f20 () S16)
(declare-fun f21 () S14)
(declare-fun f22 (S17) S5)
(declare-fun f23 () S17)
(declare-fun f24 (S18 S12) S19)
(declare-fun f25 () S18)
(declare-fun f26 () S19)
(declare-fun f27 () S12)
(declare-fun f28 (S20 S3) S19)
(declare-fun f29 () S20)
(declare-fun f30 (S14 S2) S21)
(declare-fun f31 (S22 S23) S21)
(declare-fun f32 () S22)
(declare-fun f33 () S23)
(declare-fun f34 () S21)
(declare-fun f35 (S24 S25) S1)
(declare-fun f36 (S27 S26) S25)
(declare-fun f37 (S28 S26) S27)
(declare-fun f38 () S28)
(declare-fun f39 (S29 S4) S26)
(declare-fun f40 (S30 S4) S29)
(declare-fun f41 () S30)
(declare-fun f42 (S31 S26) S1)
(declare-fun f43 (S5 S4) S1)
(declare-fun f44 (S32 S33) S1)
(declare-fun f45 (S35 S34) S33)
(declare-fun f46 (S36 S34) S35)
(declare-fun f47 () S36)
(declare-fun f48 (S37 S10) S34)
(declare-fun f49 (S38 S10) S37)
(declare-fun f50 () S38)
(declare-fun f51 (S39 S12) S1)
(declare-fun f52 (S34 S41) S1)
(declare-fun f53 (S40 S12) S41)
(declare-fun f54 (S42 S40) S5)
(declare-fun f55 (S39) S42)
(declare-fun f56 (S43 S16) S1)
(declare-fun f57 (S45 S46) S1)
(declare-fun f58 (S47 S14) S45)
(declare-fun f59 (S48 S14) S47)
(declare-fun f60 () S48)
(declare-fun f61 (S44 S16) S46)
(declare-fun f62 (S49 S44) S41)
(declare-fun f63 (S43) S49)
(declare-fun f64 (S50 S7) S1)
(declare-fun f65 (S51 S7) S5)
(declare-fun f66 (S26 S31) S1)
(declare-fun f67 (S52 S51) S31)
(declare-fun f68 (S50) S52)
(declare-fun f69 (S41 S34) S1)
(declare-fun f70 (S33 S32) S1)
(declare-fun f71 (S53 S34) S32)
(declare-fun f72 (S54 S55) S1)
(declare-fun f73 (S33 S33) S54)
(declare-fun f74 (S41 S53) S55)
(declare-fun f75 (S46 S45) S1)
(declare-fun f76 (S57 S58) S1)
(declare-fun f77 (S59 S45) S57)
(declare-fun f78 (S60 S45) S59)
(declare-fun f79 () S60)
(declare-fun f80 (S56 S45) S58)
(declare-fun f81 (S61 S62) S1)
(declare-fun f82 (S57 S57) S61)
(declare-fun f83 (S46 S56) S62)
(declare-fun f84 (S25 S24) S1)
(declare-fun f85 (S63 S26) S24)
(declare-fun f86 (S64 S65) S1)
(declare-fun f87 (S25 S25) S64)
(declare-fun f88 (S31 S63) S65)
(declare-fun f89 (S66 S4) S31)
(declare-fun f90 (S67 S66) S24)
(declare-fun f91 (S5) S67)
(declare-fun f92 (S68 S14) S1)
(declare-fun f93 (S69 S14) S46)
(declare-fun f94 (S70 S69) S58)
(declare-fun f95 (S68) S70)
(declare-fun f96 (S71 S10) S1)
(declare-fun f97 (S72 S10) S41)
(declare-fun f98 (S73 S72) S32)
(declare-fun f99 (S71) S73)
(declare-fun f100 (S16) S43)
(declare-fun f101 (S58 S57) S1)
(declare-fun f102 (S74 S14) S14)
(declare-fun f103 (S75 S14) S74)
(declare-fun f104 () S75)
(assert (not (= f1 f2)))
(assert (not (= (f3 f4 f5) f1)))
(assert (= (f6 (f7 (f8 f9 (f10 (f11 f12 f13) (f14 (f15 f16 f17) f18))) (f10 (f11 f12 f19) (f14 (f15 f16 f20) f21))) (f22 f23)) f1))
(assert (= (f24 f25 f19) f26))
(assert (= (f24 f25 f13) f26))
(assert (= (f24 f25 f27) (f28 f29 f5)))
(assert (= (f30 f18 f4) (f31 f32 f33)))
(assert (= (f30 f21 f4) f34))
(assert (forall ((?v0 S23)) (not (= f34 (f31 f32 ?v0)))))
(assert (forall ((?v0 S3)) (not (= f26 (f28 f29 ?v0)))))
(assert (forall ((?v0 S23)) (not (= (f31 f32 ?v0) f34))))
(assert (forall ((?v0 S3)) (not (= (f28 f29 ?v0) f26))))
(assert (forall ((?v0 S21)) (= (forall ((?v1 S23)) (not (= ?v0 (f31 f32 ?v1)))) (= ?v0 f34))))
(assert (forall ((?v0 S19)) (= (forall ((?v1 S3)) (not (= ?v0 (f28 f29 ?v1)))) (= ?v0 f26))))
(assert (forall ((?v0 S21)) (= (not (= ?v0 f34)) (exists ((?v1 S23)) (= ?v0 (f31 f32 ?v1))))))
(assert (forall ((?v0 S19)) (= (not (= ?v0 f26)) (exists ((?v1 S3)) (= ?v0 (f28 f29 ?v1))))))
(assert (forall ((?v0 S24) (?v1 S25)) (=> (forall ((?v2 S26) (?v3 S4) (?v4 S7) (?v5 S12) (?v6 S16) (?v7 S14)) (= (f35 ?v0 (f36 (f37 f38 ?v2) (f39 (f40 f41 ?v3) (f7 (f8 f9 ?v4) (f10 (f11 f12 ?v5) (f14 (f15 f16 ?v6) ?v7)))))) f1)) (= (f35 ?v0 ?v1) f1))))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S26) (?v2 S4) (?v3 S7) (?v4 S12) (?v5 S16) (?v6 S14)) (=> (= ?v0 (f36 (f37 f38 ?v1) (f39 (f40 f41 ?v2) (f7 (f8 f9 ?v3) (f10 (f11 f12 ?v4) (f14 (f15 f16 ?v5) ?v6)))))) false)) false)))
(assert (forall ((?v0 S31) (?v1 S26)) (=> (forall ((?v2 S4) (?v3 S7) (?v4 S12) (?v5 S16) (?v6 S14)) (= (f42 ?v0 (f39 (f40 f41 ?v2) (f7 (f8 f9 ?v3) (f10 (f11 f12 ?v4) (f14 (f15 f16 ?v5) ?v6))))) f1)) (= (f42 ?v0 ?v1) f1))))
(assert (forall ((?v0 S24) (?v1 S25)) (=> (forall ((?v2 S26) (?v3 S4) (?v4 S7) (?v5 S12) (?v6 S10)) (= (f35 ?v0 (f36 (f37 f38 ?v2) (f39 (f40 f41 ?v3) (f7 (f8 f9 ?v4) (f10 (f11 f12 ?v5) ?v6))))) f1)) (= (f35 ?v0 ?v1) f1))))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S4) (?v2 S7) (?v3 S12) (?v4 S16) (?v5 S14)) (=> (= ?v0 (f39 (f40 f41 ?v1) (f7 (f8 f9 ?v2) (f10 (f11 f12 ?v3) (f14 (f15 f16 ?v4) ?v5))))) false)) false)))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S26) (?v2 S4) (?v3 S7) (?v4 S12) (?v5 S10)) (=> (= ?v0 (f36 (f37 f38 ?v1) (f39 (f40 f41 ?v2) (f7 (f8 f9 ?v3) (f10 (f11 f12 ?v4) ?v5))))) false)) false)))
(assert (forall ((?v0 S31) (?v1 S26)) (=> (forall ((?v2 S4) (?v3 S7) (?v4 S12) (?v5 S10)) (= (f42 ?v0 (f39 (f40 f41 ?v2) (f7 (f8 f9 ?v3) (f10 (f11 f12 ?v4) ?v5)))) f1)) (= (f42 ?v0 ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S4)) (=> (forall ((?v2 S7) (?v3 S12) (?v4 S16) (?v5 S14)) (= (f43 ?v0 (f7 (f8 f9 ?v2) (f10 (f11 f12 ?v3) (f14 (f15 f16 ?v4) ?v5)))) f1)) (= (f43 ?v0 ?v1) f1))))
(assert (forall ((?v0 S32) (?v1 S33)) (=> (forall ((?v2 S34) (?v3 S10) (?v4 S16) (?v5 S14)) (= (f44 ?v0 (f45 (f46 f47 ?v2) (f48 (f49 f50 ?v3) (f14 (f15 f16 ?v4) ?v5)))) f1)) (= (f44 ?v0 ?v1) f1))))
(assert (forall ((?v0 S24) (?v1 S25)) (=> (forall ((?v2 S26) (?v3 S4) (?v4 S7) (?v5 S7)) (= (f35 ?v0 (f36 (f37 f38 ?v2) (f39 (f40 f41 ?v3) (f7 (f8 f9 ?v4) ?v5)))) f1)) (= (f35 ?v0 ?v1) f1))))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S4) (?v2 S7) (?v3 S12) (?v4 S10)) (=> (= ?v0 (f39 (f40 f41 ?v1) (f7 (f8 f9 ?v2) (f10 (f11 f12 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S7) (?v2 S12) (?v3 S16) (?v4 S14)) (=> (= ?v0 (f7 (f8 f9 ?v1) (f10 (f11 f12 ?v2) (f14 (f15 f16 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S33)) (=> (forall ((?v1 S34) (?v2 S10) (?v3 S16) (?v4 S14)) (=> (= ?v0 (f45 (f46 f47 ?v1) (f48 (f49 f50 ?v2) (f14 (f15 f16 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S26) (?v2 S4) (?v3 S7) (?v4 S7)) (=> (= ?v0 (f36 (f37 f38 ?v1) (f39 (f40 f41 ?v2) (f7 (f8 f9 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S39) (?v1 S12) (?v2 S10) (?v3 S10) (?v4 S40)) (let ((?v_0 (f11 f12 ?v1))) (=> (= (f51 ?v0 ?v1) f1) (=> (= (f52 (f48 (f49 f50 ?v2) ?v3) (f53 ?v4 ?v1)) f1) (= (f6 (f7 (f8 f9 (f10 ?v_0 ?v2)) (f10 ?v_0 ?v3)) (f54 (f55 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S43) (?v1 S16) (?v2 S14) (?v3 S14) (?v4 S44)) (let ((?v_0 (f15 f16 ?v1))) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f57 (f58 (f59 f60 ?v2) ?v3) (f61 ?v4 ?v1)) f1) (= (f52 (f48 (f49 f50 (f14 ?v_0 ?v2)) (f14 ?v_0 ?v3)) (f62 (f63 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S50) (?v1 S7) (?v2 S7) (?v3 S7) (?v4 S51)) (let ((?v_0 (f8 f9 ?v1))) (=> (= (f64 ?v0 ?v1) f1) (=> (= (f6 (f7 (f8 f9 ?v2) ?v3) (f65 ?v4 ?v1)) f1) (= (f66 (f39 (f40 f41 (f7 ?v_0 ?v2)) (f7 ?v_0 ?v3)) (f67 (f68 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S41) (?v1 S34) (?v2 S34) (?v3 S34) (?v4 S53)) (let ((?v_0 (f46 f47 ?v1))) (=> (= (f69 ?v0 ?v1) f1) (=> (= (f70 (f45 (f46 f47 ?v2) ?v3) (f71 ?v4 ?v1)) f1) (= (f72 (f73 (f45 ?v_0 ?v2) (f45 ?v_0 ?v3)) (f74 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S46) (?v1 S45) (?v2 S45) (?v3 S45) (?v4 S56)) (let ((?v_0 (f78 f79 ?v1))) (=> (= (f75 ?v0 ?v1) f1) (=> (= (f76 (f77 (f78 f79 ?v2) ?v3) (f80 ?v4 ?v1)) f1) (= (f81 (f82 (f77 ?v_0 ?v2) (f77 ?v_0 ?v3)) (f83 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S31) (?v1 S26) (?v2 S26) (?v3 S26) (?v4 S63)) (let ((?v_0 (f37 f38 ?v1))) (=> (= (f42 ?v0 ?v1) f1) (=> (= (f84 (f36 (f37 f38 ?v2) ?v3) (f85 ?v4 ?v1)) f1) (= (f86 (f87 (f36 ?v_0 ?v2) (f36 ?v_0 ?v3)) (f88 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S5) (?v1 S4) (?v2 S4) (?v3 S4) (?v4 S66)) (let ((?v_0 (f40 f41 ?v1))) (=> (= (f43 ?v0 ?v1) f1) (=> (= (f66 (f39 (f40 f41 ?v2) ?v3) (f89 ?v4 ?v1)) f1) (= (f84 (f36 (f37 f38 (f39 ?v_0 ?v2)) (f39 ?v_0 ?v3)) (f90 (f91 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S68) (?v1 S14) (?v2 S14) (?v3 S14) (?v4 S69)) (let ((?v_0 (f59 f60 ?v1))) (=> (= (f92 ?v0 ?v1) f1) (=> (= (f57 (f58 (f59 f60 ?v2) ?v3) (f93 ?v4 ?v1)) f1) (= (f76 (f77 (f78 f79 (f58 ?v_0 ?v2)) (f58 ?v_0 ?v3)) (f94 (f95 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S71) (?v1 S10) (?v2 S10) (?v3 S10) (?v4 S72)) (let ((?v_0 (f49 f50 ?v1))) (=> (= (f96 ?v0 ?v1) f1) (=> (= (f52 (f48 (f49 f50 ?v2) ?v3) (f97 ?v4 ?v1)) f1) (= (f70 (f45 (f46 f47 (f48 ?v_0 ?v2)) (f48 ?v_0 ?v3)) (f98 (f99 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S12) (?v1 S16) (?v2 S14) (?v3 S12) (?v4 S16) (?v5 S14) (?v6 S17)) (=> (= (f6 (f7 (f8 f9 (f10 (f11 f12 ?v0) (f14 (f15 f16 ?v1) ?v2))) (f10 (f11 f12 ?v3) (f14 (f15 f16 ?v4) ?v5))) (f22 ?v6)) f1) (= (f56 (f100 ?v1) ?v4) f1))))
(assert (forall ((?v0 S16) (?v1 S14) (?v2 S16) (?v3 S14)) (=> (= (f14 (f15 f16 ?v0) ?v1) (f14 (f15 f16 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S12) (?v1 S10) (?v2 S12) (?v3 S10)) (=> (= (f10 (f11 f12 ?v0) ?v1) (f10 (f11 f12 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (=> (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S34) (?v1 S34) (?v2 S34) (?v3 S34)) (=> (= (f45 (f46 f47 ?v0) ?v1) (f45 (f46 f47 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S45) (?v1 S45) (?v2 S45) (?v3 S45)) (=> (= (f77 (f78 f79 ?v0) ?v1) (f77 (f78 f79 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26) (?v3 S26)) (=> (= (f36 (f37 f38 ?v0) ?v1) (f36 (f37 f38 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (=> (= (f39 (f40 f41 ?v0) ?v1) (f39 (f40 f41 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (=> (= (f58 (f59 f60 ?v0) ?v1) (f58 (f59 f60 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f48 (f49 f50 ?v0) ?v1) (f48 (f49 f50 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S16) (?v1 S14) (?v2 S16) (?v3 S14)) (= (= (f14 (f15 f16 ?v0) ?v1) (f14 (f15 f16 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S12) (?v1 S10) (?v2 S12) (?v3 S10)) (= (= (f10 (f11 f12 ?v0) ?v1) (f10 (f11 f12 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (= (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S34) (?v1 S34) (?v2 S34) (?v3 S34)) (= (= (f45 (f46 f47 ?v0) ?v1) (f45 (f46 f47 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S45) (?v1 S45) (?v2 S45) (?v3 S45)) (= (= (f77 (f78 f79 ?v0) ?v1) (f77 (f78 f79 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26) (?v3 S26)) (= (= (f36 (f37 f38 ?v0) ?v1) (f36 (f37 f38 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (= (= (f39 (f40 f41 ?v0) ?v1) (f39 (f40 f41 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (= (= (f58 (f59 f60 ?v0) ?v1) (f58 (f59 f60 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (= (= (f48 (f49 f50 ?v0) ?v1) (f48 (f49 f50 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S71)) (= (forall ((?v1 S10)) (= (f96 ?v0 ?v1) f1)) (forall ((?v1 S16) (?v2 S14)) (= (f96 ?v0 (f14 (f15 f16 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S50)) (= (forall ((?v1 S7)) (= (f64 ?v0 ?v1) f1)) (forall ((?v1 S12) (?v2 S10)) (= (f64 ?v0 (f10 (f11 f12 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S5)) (= (forall ((?v1 S4)) (= (f43 ?v0 ?v1) f1)) (forall ((?v1 S7) (?v2 S7)) (= (f43 ?v0 (f7 (f8 f9 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S32)) (= (forall ((?v1 S33)) (= (f44 ?v0 ?v1) f1)) (forall ((?v1 S34) (?v2 S34)) (= (f44 ?v0 (f45 (f46 f47 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S58)) (= (forall ((?v1 S57)) (= (f101 ?v0 ?v1) f1)) (forall ((?v1 S45) (?v2 S45)) (= (f101 ?v0 (f77 (f78 f79 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S24)) (= (forall ((?v1 S25)) (= (f35 ?v0 ?v1) f1)) (forall ((?v1 S26) (?v2 S26)) (= (f35 ?v0 (f36 (f37 f38 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S31)) (= (forall ((?v1 S26)) (= (f42 ?v0 ?v1) f1)) (forall ((?v1 S4) (?v2 S4)) (= (f42 ?v0 (f39 (f40 f41 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S46)) (= (forall ((?v1 S45)) (= (f75 ?v0 ?v1) f1)) (forall ((?v1 S14) (?v2 S14)) (= (f75 ?v0 (f58 (f59 f60 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S41)) (= (forall ((?v1 S34)) (= (f69 ?v0 ?v1) f1)) (forall ((?v1 S10) (?v2 S10)) (= (f69 ?v0 (f48 (f49 f50 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S23) (?v1 S23)) (= (= (f31 f32 ?v0) (f31 f32 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f28 f29 ?v0) (f28 f29 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S16)) (= (f56 (f100 ?v0) ?v0) f1)))
(assert (forall ((?v0 S21)) (=> (=> (= ?v0 f34) false) (=> (forall ((?v1 S23)) (=> (= ?v0 (f31 f32 ?v1)) false)) false))))
(assert (forall ((?v0 S19)) (=> (=> (= ?v0 f26) false) (=> (forall ((?v1 S3)) (=> (= ?v0 (f28 f29 ?v1)) false)) false))))
(assert (forall ((?v0 S34)) (=> (forall ((?v1 S10) (?v2 S16) (?v3 S14)) (=> (= ?v0 (f48 (f49 f50 ?v1) (f14 (f15 f16 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S4) (?v2 S7) (?v3 S7)) (=> (= ?v0 (f39 (f40 f41 ?v1) (f7 (f8 f9 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S7)) (=> (forall ((?v1 S12) (?v2 S16) (?v3 S14)) (=> (= ?v0 (f10 (f11 f12 ?v1) (f14 (f15 f16 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S7) (?v2 S12) (?v3 S10)) (=> (= ?v0 (f7 (f8 f9 ?v1) (f10 (f11 f12 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S26) (?v2 S4) (?v3 S4)) (=> (= ?v0 (f36 (f37 f38 ?v1) (f39 (f40 f41 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S57)) (=> (forall ((?v1 S45) (?v2 S14) (?v3 S14)) (=> (= ?v0 (f77 (f78 f79 ?v1) (f58 (f59 f60 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S33)) (=> (forall ((?v1 S34) (?v2 S10) (?v3 S10)) (=> (= ?v0 (f45 (f46 f47 ?v1) (f48 (f49 f50 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S41) (?v1 S34)) (=> (forall ((?v2 S10) (?v3 S16) (?v4 S14)) (= (f69 ?v0 (f48 (f49 f50 ?v2) (f14 (f15 f16 ?v3) ?v4))) f1)) (= (f69 ?v0 ?v1) f1))))
(assert (forall ((?v0 S31) (?v1 S26)) (=> (forall ((?v2 S4) (?v3 S7) (?v4 S7)) (= (f42 ?v0 (f39 (f40 f41 ?v2) (f7 (f8 f9 ?v3) ?v4))) f1)) (= (f42 ?v0 ?v1) f1))))
(assert (forall ((?v0 S50) (?v1 S7)) (=> (forall ((?v2 S12) (?v3 S16) (?v4 S14)) (= (f64 ?v0 (f10 (f11 f12 ?v2) (f14 (f15 f16 ?v3) ?v4))) f1)) (= (f64 ?v0 ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S4)) (=> (forall ((?v2 S7) (?v3 S12) (?v4 S10)) (= (f43 ?v0 (f7 (f8 f9 ?v2) (f10 (f11 f12 ?v3) ?v4))) f1)) (= (f43 ?v0 ?v1) f1))))
(assert (forall ((?v0 S24) (?v1 S25)) (=> (forall ((?v2 S26) (?v3 S4) (?v4 S4)) (= (f35 ?v0 (f36 (f37 f38 ?v2) (f39 (f40 f41 ?v3) ?v4))) f1)) (= (f35 ?v0 ?v1) f1))))
(assert (forall ((?v0 S58) (?v1 S57)) (=> (forall ((?v2 S45) (?v3 S14) (?v4 S14)) (= (f101 ?v0 (f77 (f78 f79 ?v2) (f58 (f59 f60 ?v3) ?v4))) f1)) (= (f101 ?v0 ?v1) f1))))
(assert (forall ((?v0 S32) (?v1 S33)) (=> (forall ((?v2 S34) (?v3 S10) (?v4 S10)) (= (f44 ?v0 (f45 (f46 f47 ?v2) (f48 (f49 f50 ?v3) ?v4))) f1)) (= (f44 ?v0 ?v1) f1))))
(assert (forall ((?v0 S12) (?v1 S16) (?v2 S14) (?v3 S12) (?v4 S16) (?v5 S14) (?v6 S17) (?v7 S14)) (let ((?v_0 (f11 f12 ?v0)) (?v_1 (f15 f16 ?v1)) (?v_2 (f11 f12 ?v3)) (?v_3 (f15 f16 ?v4)) (?v_5 (f22 ?v6)) (?v_4 (f103 f104 ?v7))) (=> (= (f6 (f7 (f8 f9 (f10 ?v_0 (f14 ?v_1 ?v2))) (f10 ?v_2 (f14 ?v_3 ?v5))) ?v_5) f1) (= (f6 (f7 (f8 f9 (f10 ?v_0 (f14 ?v_1 (f102 ?v_4 ?v2)))) (f10 ?v_2 (f14 ?v_3 (f102 ?v_4 ?v5)))) ?v_5) f1)))))
(assert (forall ((?v0 S10)) (=> (forall ((?v1 S16) (?v2 S14)) (=> (= ?v0 (f14 (f15 f16 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S7)) (=> (forall ((?v1 S12) (?v2 S10)) (=> (= ?v0 (f10 (f11 f12 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S7) (?v2 S7)) (=> (= ?v0 (f7 (f8 f9 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S33)) (=> (forall ((?v1 S34) (?v2 S34)) (=> (= ?v0 (f45 (f46 f47 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S57)) (=> (forall ((?v1 S45) (?v2 S45)) (=> (= ?v0 (f77 (f78 f79 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S26) (?v2 S26)) (=> (= ?v0 (f36 (f37 f38 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S4) (?v2 S4)) (=> (= ?v0 (f39 (f40 f41 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S45)) (=> (forall ((?v1 S14) (?v2 S14)) (=> (= ?v0 (f58 (f59 f60 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S34)) (=> (forall ((?v1 S10) (?v2 S10)) (=> (= ?v0 (f48 (f49 f50 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S10)) (=> (forall ((?v1 S16) (?v2 S14)) (=> (= ?v0 (f14 (f15 f16 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S7)) (=> (forall ((?v1 S12) (?v2 S10)) (=> (= ?v0 (f10 (f11 f12 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S7) (?v2 S7)) (=> (= ?v0 (f7 (f8 f9 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S33)) (=> (forall ((?v1 S34) (?v2 S34)) (=> (= ?v0 (f45 (f46 f47 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S57)) (=> (forall ((?v1 S45) (?v2 S45)) (=> (= ?v0 (f77 (f78 f79 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S26) (?v2 S26)) (=> (= ?v0 (f36 (f37 f38 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S4) (?v2 S4)) (=> (= ?v0 (f39 (f40 f41 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S45)) (=> (forall ((?v1 S14) (?v2 S14)) (=> (= ?v0 (f58 (f59 f60 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S34)) (=> (forall ((?v1 S10) (?v2 S10)) (=> (= ?v0 (f48 (f49 f50 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S71)) (= (exists ((?v1 S10)) (= (f96 ?v0 ?v1) f1)) (exists ((?v1 S16) (?v2 S14)) (= (f96 ?v0 (f14 (f15 f16 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S50)) (= (exists ((?v1 S7)) (= (f64 ?v0 ?v1) f1)) (exists ((?v1 S12) (?v2 S10)) (= (f64 ?v0 (f10 (f11 f12 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S5)) (= (exists ((?v1 S4)) (= (f43 ?v0 ?v1) f1)) (exists ((?v1 S7) (?v2 S7)) (= (f43 ?v0 (f7 (f8 f9 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S32)) (= (exists ((?v1 S33)) (= (f44 ?v0 ?v1) f1)) (exists ((?v1 S34) (?v2 S34)) (= (f44 ?v0 (f45 (f46 f47 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S58)) (= (exists ((?v1 S57)) (= (f101 ?v0 ?v1) f1)) (exists ((?v1 S45) (?v2 S45)) (= (f101 ?v0 (f77 (f78 f79 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S24)) (= (exists ((?v1 S25)) (= (f35 ?v0 ?v1) f1)) (exists ((?v1 S26) (?v2 S26)) (= (f35 ?v0 (f36 (f37 f38 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S31)) (= (exists ((?v1 S26)) (= (f42 ?v0 ?v1) f1)) (exists ((?v1 S4) (?v2 S4)) (= (f42 ?v0 (f39 (f40 f41 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S46)) (= (exists ((?v1 S45)) (= (f75 ?v0 ?v1) f1)) (exists ((?v1 S14) (?v2 S14)) (= (f75 ?v0 (f58 (f59 f60 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S41)) (= (exists ((?v1 S34)) (= (f69 ?v0 ?v1) f1)) (exists ((?v1 S10) (?v2 S10)) (= (f69 ?v0 (f48 (f49 f50 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16)) (let ((?v_0 (f100 ?v0))) (=> (= (f56 ?v_0 ?v1) f1) (=> (= (f56 (f100 ?v1) ?v2) f1) (= (f56 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2) (?v3 S23)) (let ((?v_0 (f31 f32 ?v3)) (?v_1 (f30 ?v1 ?v2))) (= (= (f30 (f102 (f103 f104 ?v0) ?v1) ?v2) ?v_0) (or (= ?v_1 ?v_0) (and (= ?v_1 f34) (= (f30 ?v0 ?v2) ?v_0)))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2) (?v3 S23)) (let ((?v_0 (f31 f32 ?v3)) (?v_1 (f30 ?v1 ?v2))) (=> (= (f30 (f102 (f103 f104 ?v0) ?v1) ?v2) ?v_0) (or (= ?v_1 ?v_0) (and (= ?v_1 f34) (= (f30 ?v0 ?v2) ?v_0)))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (= (f30 (f102 (f103 f104 ?v0) ?v1) ?v2) f34) (and (= (f30 ?v1 ?v2) f34) (= (f30 ?v0 ?v2) f34)))))
(assert (forall ((?v0 S14) (?v1 S2) (?v2 S23) (?v3 S14)) (let ((?v_0 (f31 f32 ?v2))) (=> (= (f30 ?v0 ?v1) ?v_0) (= (f30 (f102 (f103 f104 ?v3) ?v0) ?v1) ?v_0)))))
(check-sat)
(exit)