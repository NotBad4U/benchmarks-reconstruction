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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 (S6 S7 S8 S9 S5) S1)
(declare-fun f7 () S6)
(declare-fun f8 (S10) S7)
(declare-fun f9 () S10)
(declare-fun f10 () S8)
(declare-fun f11 () S9)
(declare-fun f12 (S4 S5 S5) S1)
(declare-fun f13 (S6) S4)
(declare-fun f14 () S5)
(declare-fun f15 (S11 S6) S1)
(declare-fun f16 () S11)
(declare-fun f17 (S12 S13) S1)
(declare-fun f18 (S14 S15) S12)
(declare-fun f19 (S16 S15) S14)
(declare-fun f20 () S16)
(declare-fun f21 (S17 S10) S15)
(declare-fun f22 (S18 S9) S17)
(declare-fun f23 () S18)
(declare-fun f24 () S9)
(declare-fun f25 () S10)
(declare-fun f26 (S6) S13)
(declare-fun f27 (S19 S10) S1)
(declare-fun f28 (S20 S8) S19)
(declare-fun f29 (S6) S20)
(declare-fun f30 (S22 S21) S10)
(declare-fun f31 (S23 S7) S22)
(declare-fun f32 () S23)
(declare-fun f33 (S24 S25) S1)
(declare-fun f34 (S27 S26) S25)
(declare-fun f35 (S28 S26) S27)
(declare-fun f36 () S28)
(declare-fun f37 (S29 S12) S26)
(declare-fun f38 (S30 S12) S29)
(declare-fun f39 () S30)
(declare-fun f40 (S31 S26) S1)
(declare-fun f41 (S13 S12) S1)
(declare-fun f42 (S32 S33) S1)
(declare-fun f43 (S35 S34) S33)
(declare-fun f44 (S36 S34) S35)
(declare-fun f45 () S36)
(declare-fun f46 (S37 S10) S34)
(declare-fun f47 (S38 S10) S37)
(declare-fun f48 () S38)
(declare-fun f49 (S39 S9) S1)
(declare-fun f50 (S34 S41) S1)
(declare-fun f51 (S40 S9) S41)
(declare-fun f52 (S42 S40) S13)
(declare-fun f53 (S39) S42)
(declare-fun f54 (S43 S7) S1)
(declare-fun f55 (S45 S46) S1)
(declare-fun f56 (S47 S21) S45)
(declare-fun f57 (S48 S21) S47)
(declare-fun f58 () S48)
(declare-fun f59 (S44 S7) S46)
(declare-fun f60 (S49 S44) S41)
(declare-fun f61 (S43) S49)
(declare-fun f62 (S50 S15) S1)
(declare-fun f63 (S51 S15) S13)
(declare-fun f64 (S26 S31) S1)
(declare-fun f65 (S52 S51) S31)
(declare-fun f66 (S50) S52)
(declare-fun f67 (S41 S34) S1)
(declare-fun f68 (S33 S32) S1)
(declare-fun f69 (S53 S34) S32)
(declare-fun f70 (S54 S55) S1)
(declare-fun f71 (S33 S33) S54)
(declare-fun f72 (S41 S53) S55)
(declare-fun f73 (S46 S45) S1)
(declare-fun f74 (S57 S58) S1)
(declare-fun f75 (S59 S45) S57)
(declare-fun f76 (S60 S45) S59)
(declare-fun f77 () S60)
(declare-fun f78 (S56 S45) S58)
(declare-fun f79 (S61 S62) S1)
(declare-fun f80 (S57 S57) S61)
(declare-fun f81 (S46 S56) S62)
(declare-fun f82 (S25 S24) S1)
(declare-fun f83 (S63 S26) S24)
(declare-fun f84 (S64 S65) S1)
(declare-fun f85 (S25 S25) S64)
(declare-fun f86 (S31 S63) S65)
(declare-fun f87 (S66 S12) S31)
(declare-fun f88 (S67 S66) S24)
(declare-fun f89 (S13) S67)
(declare-fun f90 (S68 S21) S1)
(declare-fun f91 (S69 S21) S46)
(declare-fun f92 (S70 S69) S58)
(declare-fun f93 (S68) S70)
(declare-fun f94 (S71 S10) S41)
(declare-fun f95 (S72 S71) S32)
(declare-fun f96 (S19) S72)
(declare-fun f97 (S58 S57) S1)
(declare-fun f98 (S6) S43)
(declare-fun f99 (S6 S7 S21 S8) S1)
(declare-fun f100 (S7) S43)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (not (exists ((?v0 S5)) (and (= (f6 f7 (f8 f9) f10 f11 ?v0) f1) (= (f12 (f13 f7) ?v0 f14) f1)))))
(assert (= (f15 f16 f7) f1))
(assert (= (f17 (f18 (f19 f20 (f21 (f22 f23 f24) f25)) (f21 (f22 f23 f11) f9)) (f26 f7)) f1))
(assert (= (f27 (f28 (f29 f7) f10) f25) f1))
(assert (= (f6 f7 (f8 f25) f10 f24 f14) f1))
(assert (forall ((?v0 S9) (?v1 S10) (?v2 S9) (?v3 S10) (?v4 S6) (?v5 S8) (?v6 S5)) (let ((?v_0 (f28 (f29 ?v4) ?v5))) (=> (= (f17 (f18 (f19 f20 (f21 (f22 f23 ?v0) ?v1)) (f21 (f22 f23 ?v2) ?v3)) (f26 ?v4)) f1) (=> (= (f6 ?v4 (f8 ?v1) ?v5 ?v0 ?v6) f1) (=> (= (f27 ?v_0 ?v1) f1) (= (f27 ?v_0 ?v3) f1)))))))
(assert (forall ((?v0 S6) (?v1 S5)) (= (f12 (f13 ?v0) ?v1 ?v1) f1)))
(assert (forall ((?v0 S6) (?v1 S2)) (= (f3 (f4 (f13 ?v0) ?v1) ?v1) f1)))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S7) (?v3 S21) (?v4 S9) (?v5 S7) (?v6 S21) (?v7 S8) (?v8 S5)) (let ((?v_0 (f30 (f31 f32 ?v2) ?v3))) (=> (= (f15 f16 ?v0) f1) (=> (= (f17 (f18 (f19 f20 (f21 (f22 f23 ?v1) ?v_0)) (f21 (f22 f23 ?v4) (f30 (f31 f32 ?v5) ?v6))) (f26 ?v0)) f1) (=> (= (f27 (f28 (f29 ?v0) ?v7) ?v_0) f1) (=> (= (f6 ?v0 ?v2 ?v7 ?v1 ?v8) f1) (exists ((?v9 S5)) (and (= (f6 ?v0 ?v5 ?v7 ?v4 ?v9) f1) (= (f12 (f13 ?v0) ?v9 ?v8) f1))))))))))
(assert (forall ((?v0 S6) (?v1 S5) (?v2 S5) (?v3 S5)) (let ((?v_0 (f13 ?v0))) (=> (= (f12 ?v_0 ?v1 ?v2) f1) (=> (= (f12 ?v_0 ?v2 ?v3) f1) (= (f12 ?v_0 ?v1 ?v3) f1))))))
(assert (forall ((?v0 S24) (?v1 S25)) (=> (forall ((?v2 S26) (?v3 S12) (?v4 S15) (?v5 S9) (?v6 S7) (?v7 S21)) (= (f33 ?v0 (f34 (f35 f36 ?v2) (f37 (f38 f39 ?v3) (f18 (f19 f20 ?v4) (f21 (f22 f23 ?v5) (f30 (f31 f32 ?v6) ?v7)))))) f1)) (= (f33 ?v0 ?v1) f1))))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S26) (?v2 S12) (?v3 S15) (?v4 S9) (?v5 S7) (?v6 S21)) (=> (= ?v0 (f34 (f35 f36 ?v1) (f37 (f38 f39 ?v2) (f18 (f19 f20 ?v3) (f21 (f22 f23 ?v4) (f30 (f31 f32 ?v5) ?v6)))))) false)) false)))
(assert (forall ((?v0 S31) (?v1 S26)) (=> (forall ((?v2 S12) (?v3 S15) (?v4 S9) (?v5 S7) (?v6 S21)) (= (f40 ?v0 (f37 (f38 f39 ?v2) (f18 (f19 f20 ?v3) (f21 (f22 f23 ?v4) (f30 (f31 f32 ?v5) ?v6))))) f1)) (= (f40 ?v0 ?v1) f1))))
(assert (forall ((?v0 S24) (?v1 S25)) (=> (forall ((?v2 S26) (?v3 S12) (?v4 S15) (?v5 S9) (?v6 S10)) (= (f33 ?v0 (f34 (f35 f36 ?v2) (f37 (f38 f39 ?v3) (f18 (f19 f20 ?v4) (f21 (f22 f23 ?v5) ?v6))))) f1)) (= (f33 ?v0 ?v1) f1))))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S12) (?v2 S15) (?v3 S9) (?v4 S7) (?v5 S21)) (=> (= ?v0 (f37 (f38 f39 ?v1) (f18 (f19 f20 ?v2) (f21 (f22 f23 ?v3) (f30 (f31 f32 ?v4) ?v5))))) false)) false)))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S26) (?v2 S12) (?v3 S15) (?v4 S9) (?v5 S10)) (=> (= ?v0 (f34 (f35 f36 ?v1) (f37 (f38 f39 ?v2) (f18 (f19 f20 ?v3) (f21 (f22 f23 ?v4) ?v5))))) false)) false)))
(assert (forall ((?v0 S31) (?v1 S26)) (=> (forall ((?v2 S12) (?v3 S15) (?v4 S9) (?v5 S10)) (= (f40 ?v0 (f37 (f38 f39 ?v2) (f18 (f19 f20 ?v3) (f21 (f22 f23 ?v4) ?v5)))) f1)) (= (f40 ?v0 ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S12)) (=> (forall ((?v2 S15) (?v3 S9) (?v4 S7) (?v5 S21)) (= (f41 ?v0 (f18 (f19 f20 ?v2) (f21 (f22 f23 ?v3) (f30 (f31 f32 ?v4) ?v5)))) f1)) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S32) (?v1 S33)) (=> (forall ((?v2 S34) (?v3 S10) (?v4 S7) (?v5 S21)) (= (f42 ?v0 (f43 (f44 f45 ?v2) (f46 (f47 f48 ?v3) (f30 (f31 f32 ?v4) ?v5)))) f1)) (= (f42 ?v0 ?v1) f1))))
(assert (forall ((?v0 S24) (?v1 S25)) (=> (forall ((?v2 S26) (?v3 S12) (?v4 S15) (?v5 S15)) (= (f33 ?v0 (f34 (f35 f36 ?v2) (f37 (f38 f39 ?v3) (f18 (f19 f20 ?v4) ?v5)))) f1)) (= (f33 ?v0 ?v1) f1))))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S12) (?v2 S15) (?v3 S9) (?v4 S10)) (=> (= ?v0 (f37 (f38 f39 ?v1) (f18 (f19 f20 ?v2) (f21 (f22 f23 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S12)) (=> (forall ((?v1 S15) (?v2 S9) (?v3 S7) (?v4 S21)) (=> (= ?v0 (f18 (f19 f20 ?v1) (f21 (f22 f23 ?v2) (f30 (f31 f32 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S33)) (=> (forall ((?v1 S34) (?v2 S10) (?v3 S7) (?v4 S21)) (=> (= ?v0 (f43 (f44 f45 ?v1) (f46 (f47 f48 ?v2) (f30 (f31 f32 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S26) (?v2 S12) (?v3 S15) (?v4 S15)) (=> (= ?v0 (f34 (f35 f36 ?v1) (f37 (f38 f39 ?v2) (f18 (f19 f20 ?v3) ?v4)))) false)) false)))
(assert (forall ((?v0 S39) (?v1 S9) (?v2 S10) (?v3 S10) (?v4 S40)) (let ((?v_0 (f22 f23 ?v1))) (=> (= (f49 ?v0 ?v1) f1) (=> (= (f50 (f46 (f47 f48 ?v2) ?v3) (f51 ?v4 ?v1)) f1) (= (f17 (f18 (f19 f20 (f21 ?v_0 ?v2)) (f21 ?v_0 ?v3)) (f52 (f53 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S43) (?v1 S7) (?v2 S21) (?v3 S21) (?v4 S44)) (let ((?v_0 (f31 f32 ?v1))) (=> (= (f54 ?v0 ?v1) f1) (=> (= (f55 (f56 (f57 f58 ?v2) ?v3) (f59 ?v4 ?v1)) f1) (= (f50 (f46 (f47 f48 (f30 ?v_0 ?v2)) (f30 ?v_0 ?v3)) (f60 (f61 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S50) (?v1 S15) (?v2 S15) (?v3 S15) (?v4 S51)) (let ((?v_0 (f19 f20 ?v1))) (=> (= (f62 ?v0 ?v1) f1) (=> (= (f17 (f18 (f19 f20 ?v2) ?v3) (f63 ?v4 ?v1)) f1) (= (f64 (f37 (f38 f39 (f18 ?v_0 ?v2)) (f18 ?v_0 ?v3)) (f65 (f66 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S41) (?v1 S34) (?v2 S34) (?v3 S34) (?v4 S53)) (let ((?v_0 (f44 f45 ?v1))) (=> (= (f67 ?v0 ?v1) f1) (=> (= (f68 (f43 (f44 f45 ?v2) ?v3) (f69 ?v4 ?v1)) f1) (= (f70 (f71 (f43 ?v_0 ?v2) (f43 ?v_0 ?v3)) (f72 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S46) (?v1 S45) (?v2 S45) (?v3 S45) (?v4 S56)) (let ((?v_0 (f76 f77 ?v1))) (=> (= (f73 ?v0 ?v1) f1) (=> (= (f74 (f75 (f76 f77 ?v2) ?v3) (f78 ?v4 ?v1)) f1) (= (f79 (f80 (f75 ?v_0 ?v2) (f75 ?v_0 ?v3)) (f81 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S31) (?v1 S26) (?v2 S26) (?v3 S26) (?v4 S63)) (let ((?v_0 (f35 f36 ?v1))) (=> (= (f40 ?v0 ?v1) f1) (=> (= (f82 (f34 (f35 f36 ?v2) ?v3) (f83 ?v4 ?v1)) f1) (= (f84 (f85 (f34 ?v_0 ?v2) (f34 ?v_0 ?v3)) (f86 ?v0 ?v4)) f1))))))
(assert (forall ((?v0 S13) (?v1 S12) (?v2 S12) (?v3 S12) (?v4 S66)) (let ((?v_0 (f38 f39 ?v1))) (=> (= (f41 ?v0 ?v1) f1) (=> (= (f64 (f37 (f38 f39 ?v2) ?v3) (f87 ?v4 ?v1)) f1) (= (f82 (f34 (f35 f36 (f37 ?v_0 ?v2)) (f37 ?v_0 ?v3)) (f88 (f89 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S68) (?v1 S21) (?v2 S21) (?v3 S21) (?v4 S69)) (let ((?v_0 (f57 f58 ?v1))) (=> (= (f90 ?v0 ?v1) f1) (=> (= (f55 (f56 (f57 f58 ?v2) ?v3) (f91 ?v4 ?v1)) f1) (= (f74 (f75 (f76 f77 (f56 ?v_0 ?v2)) (f56 ?v_0 ?v3)) (f92 (f93 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S19) (?v1 S10) (?v2 S10) (?v3 S10) (?v4 S71)) (let ((?v_0 (f47 f48 ?v1))) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f50 (f46 (f47 f48 ?v2) ?v3) (f94 ?v4 ?v1)) f1) (= (f68 (f43 (f44 f45 (f46 ?v_0 ?v2)) (f46 ?v_0 ?v3)) (f95 (f96 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f13 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (=> (= (f3 ?v_1 ?v2) f1) (=> (= (f3 (f4 ?v_0 ?v2) ?v3) f1) (= (f3 ?v_1 ?v3) f1)))))))
(assert (forall ((?v0 S7) (?v1 S21) (?v2 S7) (?v3 S21)) (=> (= (f30 (f31 f32 ?v0) ?v1) (f30 (f31 f32 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S9) (?v1 S10) (?v2 S9) (?v3 S10)) (=> (= (f21 (f22 f23 ?v0) ?v1) (f21 (f22 f23 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (=> (= (f18 (f19 f20 ?v0) ?v1) (f18 (f19 f20 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S34) (?v1 S34) (?v2 S34) (?v3 S34)) (=> (= (f43 (f44 f45 ?v0) ?v1) (f43 (f44 f45 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S45) (?v1 S45) (?v2 S45) (?v3 S45)) (=> (= (f75 (f76 f77 ?v0) ?v1) (f75 (f76 f77 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26) (?v3 S26)) (=> (= (f34 (f35 f36 ?v0) ?v1) (f34 (f35 f36 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (=> (= (f37 (f38 f39 ?v0) ?v1) (f37 (f38 f39 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21) (?v3 S21)) (=> (= (f56 (f57 f58 ?v0) ?v1) (f56 (f57 f58 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 f48 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S7) (?v1 S21) (?v2 S7) (?v3 S21)) (= (= (f30 (f31 f32 ?v0) ?v1) (f30 (f31 f32 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S9) (?v1 S10) (?v2 S9) (?v3 S10)) (= (= (f21 (f22 f23 ?v0) ?v1) (f21 (f22 f23 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15) (?v3 S15)) (= (= (f18 (f19 f20 ?v0) ?v1) (f18 (f19 f20 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S34) (?v1 S34) (?v2 S34) (?v3 S34)) (= (= (f43 (f44 f45 ?v0) ?v1) (f43 (f44 f45 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S45) (?v1 S45) (?v2 S45) (?v3 S45)) (= (= (f75 (f76 f77 ?v0) ?v1) (f75 (f76 f77 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26) (?v3 S26)) (= (= (f34 (f35 f36 ?v0) ?v1) (f34 (f35 f36 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (= (= (f37 (f38 f39 ?v0) ?v1) (f37 (f38 f39 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21) (?v3 S21)) (= (= (f56 (f57 f58 ?v0) ?v1) (f56 (f57 f58 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (= (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 f48 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S19)) (= (forall ((?v1 S10)) (= (f27 ?v0 ?v1) f1)) (forall ((?v1 S7) (?v2 S21)) (= (f27 ?v0 (f30 (f31 f32 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S50)) (= (forall ((?v1 S15)) (= (f62 ?v0 ?v1) f1)) (forall ((?v1 S9) (?v2 S10)) (= (f62 ?v0 (f21 (f22 f23 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S13)) (= (forall ((?v1 S12)) (= (f41 ?v0 ?v1) f1)) (forall ((?v1 S15) (?v2 S15)) (= (f41 ?v0 (f18 (f19 f20 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S32)) (= (forall ((?v1 S33)) (= (f42 ?v0 ?v1) f1)) (forall ((?v1 S34) (?v2 S34)) (= (f42 ?v0 (f43 (f44 f45 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S58)) (= (forall ((?v1 S57)) (= (f97 ?v0 ?v1) f1)) (forall ((?v1 S45) (?v2 S45)) (= (f97 ?v0 (f75 (f76 f77 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S24)) (= (forall ((?v1 S25)) (= (f33 ?v0 ?v1) f1)) (forall ((?v1 S26) (?v2 S26)) (= (f33 ?v0 (f34 (f35 f36 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S31)) (= (forall ((?v1 S26)) (= (f40 ?v0 ?v1) f1)) (forall ((?v1 S12) (?v2 S12)) (= (f40 ?v0 (f37 (f38 f39 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S46)) (= (forall ((?v1 S45)) (= (f73 ?v0 ?v1) f1)) (forall ((?v1 S21) (?v2 S21)) (= (f73 ?v0 (f56 (f57 f58 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S41)) (= (forall ((?v1 S34)) (= (f67 ?v0 ?v1) f1)) (forall ((?v1 S10) (?v2 S10)) (= (f67 ?v0 (f46 (f47 f48 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S9) (?v1 S7) (?v2 S21) (?v3 S9) (?v4 S7) (?v5 S21) (?v6 S6) (?v7 S8) (?v8 S5)) (let ((?v_0 (f98 ?v6))) (=> (= (f17 (f18 (f19 f20 (f21 (f22 f23 ?v0) (f30 (f31 f32 ?v1) ?v2))) (f21 (f22 f23 ?v3) (f30 (f31 f32 ?v4) ?v5))) (f26 ?v6)) f1) (=> (= (f6 ?v6 ?v1 ?v7 ?v0 ?v8) f1) (=> (= (f54 ?v_0 ?v1) f1) (= (f54 ?v_0 ?v4) f1)))))))
(assert (forall ((?v0 S9) (?v1 S7) (?v2 S21) (?v3 S9) (?v4 S7) (?v5 S21) (?v6 S6) (?v7 S8) (?v8 S5)) (=> (= (f17 (f18 (f19 f20 (f21 (f22 f23 ?v0) (f30 (f31 f32 ?v1) ?v2))) (f21 (f22 f23 ?v3) (f30 (f31 f32 ?v4) ?v5))) (f26 ?v6)) f1) (=> (= (f6 ?v6 ?v1 ?v7 ?v0 ?v8) f1) (=> (= (f99 ?v6 ?v1 ?v2 ?v7) f1) (= (f99 ?v6 ?v4 ?v5 ?v7) f1))))))
(assert (forall ((?v0 S34)) (=> (forall ((?v1 S10) (?v2 S7) (?v3 S21)) (=> (= ?v0 (f46 (f47 f48 ?v1) (f30 (f31 f32 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S12) (?v2 S15) (?v3 S15)) (=> (= ?v0 (f37 (f38 f39 ?v1) (f18 (f19 f20 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S15)) (=> (forall ((?v1 S9) (?v2 S7) (?v3 S21)) (=> (= ?v0 (f21 (f22 f23 ?v1) (f30 (f31 f32 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S12)) (=> (forall ((?v1 S15) (?v2 S9) (?v3 S10)) (=> (= ?v0 (f18 (f19 f20 ?v1) (f21 (f22 f23 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S26) (?v2 S12) (?v3 S12)) (=> (= ?v0 (f34 (f35 f36 ?v1) (f37 (f38 f39 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S57)) (=> (forall ((?v1 S45) (?v2 S21) (?v3 S21)) (=> (= ?v0 (f75 (f76 f77 ?v1) (f56 (f57 f58 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S33)) (=> (forall ((?v1 S34) (?v2 S10) (?v3 S10)) (=> (= ?v0 (f43 (f44 f45 ?v1) (f46 (f47 f48 ?v2) ?v3))) false)) false)))
(assert (forall ((?v0 S41) (?v1 S34)) (=> (forall ((?v2 S10) (?v3 S7) (?v4 S21)) (= (f67 ?v0 (f46 (f47 f48 ?v2) (f30 (f31 f32 ?v3) ?v4))) f1)) (= (f67 ?v0 ?v1) f1))))
(assert (forall ((?v0 S31) (?v1 S26)) (=> (forall ((?v2 S12) (?v3 S15) (?v4 S15)) (= (f40 ?v0 (f37 (f38 f39 ?v2) (f18 (f19 f20 ?v3) ?v4))) f1)) (= (f40 ?v0 ?v1) f1))))
(assert (forall ((?v0 S50) (?v1 S15)) (=> (forall ((?v2 S9) (?v3 S7) (?v4 S21)) (= (f62 ?v0 (f21 (f22 f23 ?v2) (f30 (f31 f32 ?v3) ?v4))) f1)) (= (f62 ?v0 ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S12)) (=> (forall ((?v2 S15) (?v3 S9) (?v4 S10)) (= (f41 ?v0 (f18 (f19 f20 ?v2) (f21 (f22 f23 ?v3) ?v4))) f1)) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S24) (?v1 S25)) (=> (forall ((?v2 S26) (?v3 S12) (?v4 S12)) (= (f33 ?v0 (f34 (f35 f36 ?v2) (f37 (f38 f39 ?v3) ?v4))) f1)) (= (f33 ?v0 ?v1) f1))))
(assert (forall ((?v0 S58) (?v1 S57)) (=> (forall ((?v2 S45) (?v3 S21) (?v4 S21)) (= (f97 ?v0 (f75 (f76 f77 ?v2) (f56 (f57 f58 ?v3) ?v4))) f1)) (= (f97 ?v0 ?v1) f1))))
(assert (forall ((?v0 S32) (?v1 S33)) (=> (forall ((?v2 S34) (?v3 S10) (?v4 S10)) (= (f42 ?v0 (f43 (f44 f45 ?v2) (f46 (f47 f48 ?v3) ?v4))) f1)) (= (f42 ?v0 ?v1) f1))))
(assert (forall ((?v0 S10)) (=> (forall ((?v1 S7) (?v2 S21)) (=> (= ?v0 (f30 (f31 f32 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S15)) (=> (forall ((?v1 S9) (?v2 S10)) (=> (= ?v0 (f21 (f22 f23 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S12)) (=> (forall ((?v1 S15) (?v2 S15)) (=> (= ?v0 (f18 (f19 f20 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S33)) (=> (forall ((?v1 S34) (?v2 S34)) (=> (= ?v0 (f43 (f44 f45 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S57)) (=> (forall ((?v1 S45) (?v2 S45)) (=> (= ?v0 (f75 (f76 f77 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S26) (?v2 S26)) (=> (= ?v0 (f34 (f35 f36 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S12) (?v2 S12)) (=> (= ?v0 (f37 (f38 f39 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S45)) (=> (forall ((?v1 S21) (?v2 S21)) (=> (= ?v0 (f56 (f57 f58 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S34)) (=> (forall ((?v1 S10) (?v2 S10)) (=> (= ?v0 (f46 (f47 f48 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S10)) (=> (forall ((?v1 S7) (?v2 S21)) (=> (= ?v0 (f30 (f31 f32 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S15)) (=> (forall ((?v1 S9) (?v2 S10)) (=> (= ?v0 (f21 (f22 f23 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S12)) (=> (forall ((?v1 S15) (?v2 S15)) (=> (= ?v0 (f18 (f19 f20 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S33)) (=> (forall ((?v1 S34) (?v2 S34)) (=> (= ?v0 (f43 (f44 f45 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S57)) (=> (forall ((?v1 S45) (?v2 S45)) (=> (= ?v0 (f75 (f76 f77 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S25)) (=> (forall ((?v1 S26) (?v2 S26)) (=> (= ?v0 (f34 (f35 f36 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S26)) (=> (forall ((?v1 S12) (?v2 S12)) (=> (= ?v0 (f37 (f38 f39 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S45)) (=> (forall ((?v1 S21) (?v2 S21)) (=> (= ?v0 (f56 (f57 f58 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S34)) (=> (forall ((?v1 S10) (?v2 S10)) (=> (= ?v0 (f46 (f47 f48 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S19)) (= (exists ((?v1 S10)) (= (f27 ?v0 ?v1) f1)) (exists ((?v1 S7) (?v2 S21)) (= (f27 ?v0 (f30 (f31 f32 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S50)) (= (exists ((?v1 S15)) (= (f62 ?v0 ?v1) f1)) (exists ((?v1 S9) (?v2 S10)) (= (f62 ?v0 (f21 (f22 f23 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S13)) (= (exists ((?v1 S12)) (= (f41 ?v0 ?v1) f1)) (exists ((?v1 S15) (?v2 S15)) (= (f41 ?v0 (f18 (f19 f20 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S32)) (= (exists ((?v1 S33)) (= (f42 ?v0 ?v1) f1)) (exists ((?v1 S34) (?v2 S34)) (= (f42 ?v0 (f43 (f44 f45 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S58)) (= (exists ((?v1 S57)) (= (f97 ?v0 ?v1) f1)) (exists ((?v1 S45) (?v2 S45)) (= (f97 ?v0 (f75 (f76 f77 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S24)) (= (exists ((?v1 S25)) (= (f33 ?v0 ?v1) f1)) (exists ((?v1 S26) (?v2 S26)) (= (f33 ?v0 (f34 (f35 f36 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S31)) (= (exists ((?v1 S26)) (= (f40 ?v0 ?v1) f1)) (exists ((?v1 S12) (?v2 S12)) (= (f40 ?v0 (f37 (f38 f39 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S46)) (= (exists ((?v1 S45)) (= (f73 ?v0 ?v1) f1)) (exists ((?v1 S21) (?v2 S21)) (= (f73 ?v0 (f56 (f57 f58 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S41)) (= (exists ((?v1 S34)) (= (f67 ?v0 ?v1) f1)) (exists ((?v1 S10) (?v2 S10)) (= (f67 ?v0 (f46 (f47 f48 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S9) (?v1 S7) (?v2 S21) (?v3 S9) (?v4 S7) (?v5 S21) (?v6 S6)) (=> (= (f17 (f18 (f19 f20 (f21 (f22 f23 ?v0) (f30 (f31 f32 ?v1) ?v2))) (f21 (f22 f23 ?v3) (f30 (f31 f32 ?v4) ?v5))) (f26 ?v6)) f1) (= (f54 (f100 ?v1) ?v4) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= ?v0 ?v1) (= (f12 f5 ?v0 ?v1) f1))))
(assert (forall ((?v0 S7)) (= (f54 (f100 ?v0) ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S21) (?v3 S8) (?v4 S7)) (=> (= (f99 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f54 (f100 ?v1) ?v4) f1) (= (f99 ?v0 ?v4 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S8) (?v3 S9) (?v4 S5) (?v5 S7)) (=> (= (f6 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f54 (f100 ?v1) ?v5) f1) (= (f6 ?v0 ?v5 ?v2 ?v3 ?v4) f1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S5) (?v3 S5)) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f4 ?v0 ?v4) ?v5) f1) (=> (= (f3 (f4 ?v1 ?v5) ?v4) f1) (= ?v4 ?v5)))) (=> (= (f12 ?v0 ?v2 ?v3) f1) (=> (= (f12 ?v1 ?v3 ?v2) f1) (= ?v2 ?v3))))))
(check-sat)
(exit)