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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S3) S1)
(declare-fun f4 (S5 S3) S4)
(declare-fun f5 () S5)
(declare-fun f6 (S6 S3) S3)
(declare-fun f7 () S6)
(declare-fun f8 (S7 S8) S3)
(declare-fun f9 (S9 S10) S7)
(declare-fun f10 () S9)
(declare-fun f11 () S10)
(declare-fun f12 () S8)
(declare-fun f13 (S11 S12) S1)
(declare-fun f14 (S13 S14) S11)
(declare-fun f15 () S13)
(declare-fun f16 (S15 S2) S14)
(declare-fun f17 () S15)
(declare-fun f18 (S16 S12) S12)
(declare-fun f19 () S16)
(declare-fun f20 (S17 S12) S16)
(declare-fun f21 () S17)
(declare-fun f22 (S18 S3) S12)
(declare-fun f23 (S19 S15) S18)
(declare-fun f24 () S19)
(declare-fun f25 (S20 S21) S12)
(declare-fun f26 (S22 S23) S20)
(declare-fun f27 () S22)
(declare-fun f28 () S23)
(declare-fun f29 () S21)
(declare-fun f30 (S24 S2) S4)
(declare-fun f31 () S24)
(declare-fun f32 (S25 S26) S1)
(declare-fun f33 (S27 S21) S25)
(declare-fun f34 () S27)
(declare-fun f35 () S26)
(declare-fun f36 (S10 S23) S2)
(declare-fun f37 () S3)
(declare-fun f38 () S12)
(declare-fun f39 (S28 S12) S11)
(declare-fun f40 () S28)
(declare-fun f41 () S16)
(declare-fun f42 (S29 S8) S8)
(declare-fun f43 () S29)
(declare-fun f44 (S31 S30) S29)
(declare-fun f45 () S31)
(declare-fun f46 (S32 S8) S1)
(declare-fun f47 (S33 S8) S32)
(declare-fun f48 () S33)
(declare-fun f49 (S35 S12) S8)
(declare-fun f50 (S36 S34) S35)
(declare-fun f51 () S36)
(declare-fun f52 (S38 S3) S8)
(declare-fun f53 (S39 S37) S38)
(declare-fun f54 () S39)
(declare-fun f55 (S41 S26) S8)
(declare-fun f56 (S42 S40) S41)
(declare-fun f57 () S42)
(declare-fun f58 () S26)
(declare-fun f59 (S43 S26) S26)
(declare-fun f60 () S43)
(declare-fun f61 (S45 S8) S12)
(declare-fun f62 (S46 S44) S45)
(declare-fun f63 () S46)
(declare-fun f64 (S48 S8) S26)
(declare-fun f65 (S49 S47) S48)
(declare-fun f66 () S49)
(declare-fun f67 (S50 S26) S25)
(declare-fun f68 () S50)
(declare-fun f69 (S52 S51) S6)
(declare-fun f70 () S52)
(declare-fun f71 (S54 S3) S26)
(declare-fun f72 (S55 S53) S54)
(declare-fun f73 () S55)
(declare-fun f74 (S57 S12) S3)
(declare-fun f75 (S58 S56) S57)
(declare-fun f76 () S58)
(declare-fun f77 (S60 S26) S3)
(declare-fun f78 (S61 S59) S60)
(declare-fun f79 () S61)
(declare-fun f80 (S63 S62) S16)
(declare-fun f81 () S63)
(declare-fun f82 (S65 S26) S12)
(declare-fun f83 (S66 S64) S65)
(declare-fun f84 () S66)
(declare-fun f85 (S67 S8) S29)
(declare-fun f86 () S67)
(declare-fun f87 (S68 S3) S6)
(declare-fun f88 () S68)
(declare-fun f89 (S69 S26) S43)
(declare-fun f90 () S69)
(declare-fun f91 (S70 S23) S32)
(declare-fun f92 () S70)
(declare-fun f93 () S8)
(declare-fun f94 (S64 S21) S14)
(declare-fun f95 (S62 S14) S14)
(declare-fun f96 (S59 S21) S2)
(declare-fun f97 (S56 S14) S2)
(declare-fun f98 (S53 S2) S21)
(declare-fun f99 (S51 S2) S2)
(declare-fun f100 (S47 S23) S21)
(declare-fun f101 (S44 S23) S14)
(declare-fun f102 (S40 S21) S23)
(declare-fun f103 (S37 S2) S23)
(declare-fun f104 (S34 S14) S23)
(declare-fun f105 (S30 S23) S23)
(assert (not (= f1 f2)))
(assert (not (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f14 f15 (f16 f17 ?v0))) (?v_1 (f25 (f26 f27 f28) f29))) (=> (= (f3 (f4 f5 ?v1) (f6 f7 (f8 (f9 f10 f11) f12))) f1) (= (= (f13 ?v_0 (f18 f19 (f18 (f20 f21 (f22 (f23 f24 f17) ?v1)) ?v_1))) f1) (or (= (f3 (f30 f31 ?v0) ?v1) f1) (= (f13 ?v_0 (f18 f19 ?v_1)) f1))))))))
(assert (= (f32 (f33 f34 f29) f35) f1))
(assert (forall ((?v0 S23) (?v1 S21)) (= (f13 (f14 f15 (f16 f17 (f36 f11 ?v0))) (f25 (f26 f27 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S12)) (let ((?v_0 (f14 f15 (f16 f17 ?v0)))) (let ((?v_1 (= (f13 ?v_0 (f18 f19 (f18 (f20 f21 (f22 (f23 f24 f17) ?v1)) ?v2))) f1)) (?v_2 (or (= (f3 (f30 f31 ?v0) ?v1) f1) (= (f13 ?v_0 (f18 f19 ?v2)) f1)))) (=> (=> ?v_1 ?v_2) (= ?v_1 ?v_2))))))
(assert (forall ((?v0 S15) (?v1 S3)) (let ((?v_0 (f23 f24 ?v0))) (=> (= (f22 ?v_0 f37) f38) (= (f13 (f39 f40 (f18 f41 (f22 ?v_0 ?v1))) (f22 ?v_0 (f6 f7 ?v1))) f1)))))
(assert (forall ((?v0 S10) (?v1 S8)) (let ((?v_0 (f9 f10 ?v0))) (=> (= (f8 ?v_0 f12) f37) (= (f3 (f4 f5 (f6 f7 (f8 ?v_0 ?v1))) (f8 ?v_0 (f42 f43 ?v1))) f1)))))
(assert (forall ((?v0 S30) (?v1 S8)) (let ((?v_0 (f44 f45 ?v0))) (=> (= (f42 ?v_0 f12) f12) (= (f46 (f47 f48 (f42 f43 (f42 ?v_0 ?v1))) (f42 ?v_0 (f42 f43 ?v1))) f1)))))
(assert (forall ((?v0 S34) (?v1 S12)) (let ((?v_0 (f50 f51 ?v0))) (=> (= (f49 ?v_0 f38) f12) (= (f46 (f47 f48 (f42 f43 (f49 ?v_0 ?v1))) (f49 ?v_0 (f18 f41 ?v1))) f1)))))
(assert (forall ((?v0 S37) (?v1 S3)) (let ((?v_0 (f53 f54 ?v0))) (=> (= (f52 ?v_0 f37) f12) (= (f46 (f47 f48 (f42 f43 (f52 ?v_0 ?v1))) (f52 ?v_0 (f6 f7 ?v1))) f1)))))
(assert (forall ((?v0 S40) (?v1 S26)) (let ((?v_0 (f56 f57 ?v0))) (=> (= (f55 ?v_0 f58) f12) (= (f46 (f47 f48 (f42 f43 (f55 ?v_0 ?v1))) (f55 ?v_0 (f59 f60 ?v1))) f1)))))
(assert (forall ((?v0 S44) (?v1 S8)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f61 ?v_0 f12) f38) (= (f13 (f39 f40 (f18 f41 (f61 ?v_0 ?v1))) (f61 ?v_0 (f42 f43 ?v1))) f1)))))
(assert (forall ((?v0 S47) (?v1 S8)) (let ((?v_0 (f65 f66 ?v0))) (=> (= (f64 ?v_0 f12) f58) (= (f32 (f67 f68 (f59 f60 (f64 ?v_0 ?v1))) (f64 ?v_0 (f42 f43 ?v1))) f1)))))
(assert (forall ((?v0 S51) (?v1 S3)) (let ((?v_0 (f69 f70 ?v0))) (=> (= (f6 ?v_0 f37) f37) (= (f3 (f4 f5 (f6 f7 (f6 ?v_0 ?v1))) (f6 ?v_0 (f6 f7 ?v1))) f1)))))
(assert (forall ((?v0 S53) (?v1 S3)) (let ((?v_0 (f72 f73 ?v0))) (=> (= (f71 ?v_0 f37) f58) (= (f32 (f67 f68 (f59 f60 (f71 ?v_0 ?v1))) (f71 ?v_0 (f6 f7 ?v1))) f1)))))
(assert (forall ((?v0 S56) (?v1 S12)) (let ((?v_0 (f75 f76 ?v0))) (=> (= (f74 ?v_0 f38) f37) (= (f3 (f4 f5 (f6 f7 (f74 ?v_0 ?v1))) (f74 ?v_0 (f18 f41 ?v1))) f1)))))
(assert (forall ((?v0 S59) (?v1 S26)) (let ((?v_0 (f78 f79 ?v0))) (=> (= (f77 ?v_0 f58) f37) (= (f3 (f4 f5 (f6 f7 (f77 ?v_0 ?v1))) (f77 ?v_0 (f59 f60 ?v1))) f1)))))
(assert (forall ((?v0 S62) (?v1 S12)) (let ((?v_0 (f80 f81 ?v0))) (=> (= (f18 ?v_0 f38) f38) (= (f13 (f39 f40 (f18 f41 (f18 ?v_0 ?v1))) (f18 ?v_0 (f18 f41 ?v1))) f1)))))
(assert (forall ((?v0 S64) (?v1 S26)) (let ((?v_0 (f83 f84 ?v0))) (=> (= (f82 ?v_0 f58) f38) (= (f13 (f39 f40 (f18 f41 (f82 ?v_0 ?v1))) (f82 ?v_0 (f59 f60 ?v1))) f1)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f22 (f23 f24 f17) ?v0))) (= (f18 f19 ?v_0) ?v_0))))
(assert (forall ((?v0 S14) (?v1 S21) (?v2 S1)) (let ((?v_0 (=> (not (= (f13 (f14 f15 ?v0) (f18 f19 (f25 (f26 f27 f28) ?v1))) f1)) (= ?v2 f1)))) (=> ?v_0 ?v_0))))
(assert (forall ((?v0 S8)) (= (f42 (f85 f86 ?v0) (f42 f43 ?v0)) f12)))
(assert (forall ((?v0 S3)) (= (f6 (f87 f88 ?v0) (f6 f7 ?v0)) f37)))
(assert (forall ((?v0 S12)) (= (f18 (f20 f21 ?v0) (f18 f41 ?v0)) f38)))
(assert (forall ((?v0 S26)) (= (f59 (f89 f90 ?v0) (f59 f60 ?v0)) f58)))
(assert (forall ((?v0 S8)) (= (f42 (f85 f86 (f42 f43 ?v0)) ?v0) f12)))
(assert (forall ((?v0 S3)) (= (f6 (f87 f88 (f6 f7 ?v0)) ?v0) f37)))
(assert (forall ((?v0 S12)) (= (f18 (f20 f21 (f18 f41 ?v0)) ?v0) f38)))
(assert (forall ((?v0 S26)) (= (f59 (f89 f90 (f59 f60 ?v0)) ?v0) f58)))
(assert (forall ((?v0 S21) (?v1 S23)) (=> (= (f32 (f33 f34 ?v0) f35) f1) (= (= (f13 (f14 f15 (f16 f17 (f36 f11 ?v1))) (f18 f19 (f25 (f26 f27 f28) ?v0))) f1) (= (f46 (f91 f92 ?v1) f93) f1)))))
(assert (forall ((?v0 S8)) (= (f42 (f85 f86 ?v0) (f42 f43 ?v0)) f12)))
(assert (forall ((?v0 S3)) (= (f6 (f87 f88 ?v0) (f6 f7 ?v0)) f37)))
(assert (forall ((?v0 S12)) (= (f18 (f20 f21 ?v0) (f18 f41 ?v0)) f38)))
(assert (forall ((?v0 S26)) (= (f59 (f89 f90 ?v0) (f59 f60 ?v0)) f58)))
(assert (forall ((?v0 S8)) (= (f42 (f85 f86 (f42 f43 ?v0)) ?v0) f12)))
(assert (forall ((?v0 S3)) (= (f6 (f87 f88 (f6 f7 ?v0)) ?v0) f37)))
(assert (forall ((?v0 S12)) (= (f18 (f20 f21 (f18 f41 ?v0)) ?v0) f38)))
(assert (forall ((?v0 S26)) (= (f59 (f89 f90 (f59 f60 ?v0)) ?v0) f58)))
(assert (forall ((?v0 S23) (?v1 S8)) (let ((?v_0 (f91 f92 ?v0))) (=> (=> (= (f46 ?v_0 ?v1) f1) false) (= (f46 ?v_0 (f42 f43 ?v1)) f1)))))
(assert (forall ((?v0 S21) (?v1 S26)) (let ((?v_0 (f33 f34 ?v0))) (=> (=> (= (f32 ?v_0 ?v1) f1) false) (= (f32 ?v_0 (f59 f60 ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f30 f31 ?v0))) (=> (=> (= (f3 ?v_0 ?v1) f1) false) (= (f3 ?v_0 (f6 f7 ?v1)) f1)))))
(assert (forall ((?v0 S14) (?v1 S12)) (let ((?v_0 (f14 f15 ?v0))) (=> (=> (= (f13 ?v_0 ?v1) f1) false) (= (f13 ?v_0 (f18 f41 ?v1)) f1)))))
(assert (forall ((?v0 S14) (?v1 S12)) (let ((?v_0 (f14 f15 ?v0))) (=> (= (f13 ?v_0 ?v1) f1) (= (f13 ?v_0 (f18 f19 ?v1)) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f13 (f39 f40 ?v0) ?v1) f1) (=> (= (f13 (f39 f40 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S26) (?v1 S26)) (=> (= (f32 (f67 f68 ?v0) ?v1) f1) (=> (= (f32 (f67 f68 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f46 (f47 f48 ?v0) ?v1) f1) (=> (= (f46 (f47 f48 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S23)) (let ((?v_0 (f91 f92 ?v2))) (=> (= (f46 (f47 f48 ?v0) ?v1) f1) (=> (= (f46 ?v_0 ?v0) f1) (= (f46 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S21)) (let ((?v_0 (f33 f34 ?v2))) (=> (= (f32 (f67 f68 ?v0) ?v1) f1) (=> (= (f32 ?v_0 ?v0) f1) (= (f32 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f30 f31 ?v2))) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S14)) (let ((?v_0 (f14 f15 ?v2))) (=> (= (f13 (f39 f40 ?v0) ?v1) f1) (=> (= (f13 ?v_0 ?v0) f1) (= (f13 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S14) (?v1 S15) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f16 ?v1 ?v2)) (=> (= (f3 (f30 f31 ?v2) ?v3) f1) (= (f13 (f14 f15 ?v0) (f22 (f23 f24 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S10) (?v2 S23) (?v3 S8)) (=> (= ?v0 (f36 ?v1 ?v2)) (=> (= (f46 (f91 f92 ?v2) ?v3) f1) (= (f3 (f30 f31 ?v0) (f8 (f9 f10 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S14) (?v1 S64) (?v2 S21) (?v3 S26)) (=> (= ?v0 (f94 ?v1 ?v2)) (=> (= (f32 (f33 f34 ?v2) ?v3) f1) (= (f13 (f14 f15 ?v0) (f82 (f83 f84 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S14) (?v1 S62) (?v2 S14) (?v3 S12)) (=> (= ?v0 (f95 ?v1 ?v2)) (=> (= (f13 (f14 f15 ?v2) ?v3) f1) (= (f13 (f14 f15 ?v0) (f18 (f80 f81 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S59) (?v2 S21) (?v3 S26)) (=> (= ?v0 (f96 ?v1 ?v2)) (=> (= (f32 (f33 f34 ?v2) ?v3) f1) (= (f3 (f30 f31 ?v0) (f77 (f78 f79 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S56) (?v2 S14) (?v3 S12)) (=> (= ?v0 (f97 ?v1 ?v2)) (=> (= (f13 (f14 f15 ?v2) ?v3) f1) (= (f3 (f30 f31 ?v0) (f74 (f75 f76 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S21) (?v1 S53) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f98 ?v1 ?v2)) (=> (= (f3 (f30 f31 ?v2) ?v3) f1) (= (f32 (f33 f34 ?v0) (f71 (f72 f73 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S51) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f99 ?v1 ?v2)) (=> (= (f3 (f30 f31 ?v2) ?v3) f1) (= (f3 (f30 f31 ?v0) (f6 (f69 f70 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S21) (?v1 S47) (?v2 S23) (?v3 S8)) (=> (= ?v0 (f100 ?v1 ?v2)) (=> (= (f46 (f91 f92 ?v2) ?v3) f1) (= (f32 (f33 f34 ?v0) (f64 (f65 f66 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S14) (?v1 S44) (?v2 S23) (?v3 S8)) (=> (= ?v0 (f101 ?v1 ?v2)) (=> (= (f46 (f91 f92 ?v2) ?v3) f1) (= (f13 (f14 f15 ?v0) (f61 (f62 f63 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S23) (?v1 S40) (?v2 S21) (?v3 S26)) (=> (= ?v0 (f102 ?v1 ?v2)) (=> (= (f32 (f33 f34 ?v2) ?v3) f1) (= (f46 (f91 f92 ?v0) (f55 (f56 f57 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S23) (?v1 S37) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f103 ?v1 ?v2)) (=> (= (f3 (f30 f31 ?v2) ?v3) f1) (= (f46 (f91 f92 ?v0) (f52 (f53 f54 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S23) (?v1 S34) (?v2 S14) (?v3 S12)) (=> (= ?v0 (f104 ?v1 ?v2)) (=> (= (f13 (f14 f15 ?v2) ?v3) f1) (= (f46 (f91 f92 ?v0) (f49 (f50 f51 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S23) (?v1 S30) (?v2 S23) (?v3 S8)) (=> (= ?v0 (f105 ?v1 ?v2)) (=> (= (f46 (f91 f92 ?v2) ?v3) f1) (= (f46 (f91 f92 ?v0) (f42 (f44 f45 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S23)) (= (f46 (f91 f92 ?v0) f12) f1)))
(assert (forall ((?v0 S21)) (= (f32 (f33 f34 ?v0) f58) f1)))
(assert (forall ((?v0 S2)) (= (f3 (f30 f31 ?v0) f37) f1)))
(assert (forall ((?v0 S14)) (= (f13 (f14 f15 ?v0) f38) f1)))
(assert (forall ((?v0 S23) (?v1 S8) (?v2 S8)) (let ((?v_0 (f91 f92 ?v0))) (=> (=> (not (= (f46 ?v_0 ?v1) f1)) (= (f46 ?v_0 ?v2) f1)) (= (f46 ?v_0 (f42 (f85 f86 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S21) (?v1 S26) (?v2 S26)) (let ((?v_0 (f33 f34 ?v0))) (=> (=> (not (= (f32 ?v_0 ?v1) f1)) (= (f32 ?v_0 ?v2) f1)) (= (f32 ?v_0 (f59 (f89 f90 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f30 f31 ?v0))) (=> (=> (not (= (f3 ?v_0 ?v1) f1)) (= (f3 ?v_0 ?v2) f1)) (= (f3 ?v_0 (f6 (f87 f88 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S14) (?v1 S12) (?v2 S12)) (let ((?v_0 (f14 f15 ?v0))) (=> (=> (not (= (f13 ?v_0 ?v1) f1)) (= (f13 ?v_0 ?v2) f1)) (= (f13 ?v_0 (f18 (f20 f21 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S23) (?v1 S8) (?v2 S8)) (let ((?v_0 (f91 f92 ?v0))) (=> (= (f46 ?v_0 (f42 (f85 f86 ?v1) ?v2)) f1) (=> (=> (= (f46 ?v_0 ?v1) f1) false) (=> (=> (= (f46 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S21) (?v1 S26) (?v2 S26)) (let ((?v_0 (f33 f34 ?v0))) (=> (= (f32 ?v_0 (f59 (f89 f90 ?v1) ?v2)) f1) (=> (=> (= (f32 ?v_0 ?v1) f1) false) (=> (=> (= (f32 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f30 f31 ?v0))) (=> (= (f3 ?v_0 (f6 (f87 f88 ?v1) ?v2)) f1) (=> (=> (= (f3 ?v_0 ?v1) f1) false) (=> (=> (= (f3 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S14) (?v1 S12) (?v2 S12)) (let ((?v_0 (f14 f15 ?v0))) (=> (= (f13 ?v_0 (f18 (f20 f21 ?v1) ?v2)) f1) (=> (=> (= (f13 ?v_0 ?v1) f1) false) (=> (=> (= (f13 ?v_0 ?v2) f1) false) false))))))
(assert (= (f46 (f91 f92 f28) f93) f1))
(assert (forall ((?v0 S23) (?v1 S21)) (=> (= (f46 (f91 f92 ?v0) f93) f1) (= (f13 (f14 f15 (f16 f17 (f36 f11 ?v0))) (f25 (f26 f27 f28) ?v1)) f1))))
(assert (forall ((?v0 S14) (?v1 S12) (?v2 S12)) (let ((?v_0 (f14 f15 ?v0)) (?v_1 (f18 f19 ?v2))) (=> (= (f13 ?v_0 (f18 f19 ?v1)) f1) (=> (= (f13 (f39 f40 ?v1) ?v_1) f1) (= (f13 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f13 (f39 f40 ?v0) ?v1) f1) (= (f13 (f39 f40 (f18 f19 ?v0)) (f18 f19 ?v1)) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f18 f19 ?v1))) (= (= (f13 (f39 f40 (f18 f19 ?v0)) ?v_0) f1) (= (f13 (f39 f40 ?v0) ?v_0) f1)))))
(assert (forall ((?v0 S12)) (= (f13 (f39 f40 ?v0) (f18 f19 ?v0)) f1)))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (=> (= (f13 (f39 f40 (f18 f19 ?v0)) (f18 f19 ?v1)) f1) (=> (= (f13 (f39 f40 (f18 f19 ?v2)) (f18 f19 ?v3)) f1) (= (f13 (f39 f40 (f18 f19 (f18 (f20 f21 ?v0) ?v2))) (f18 f19 (f18 (f20 f21 ?v1) ?v3))) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (f13 (f39 f40 (f18 (f20 f21 (f18 f19 ?v0)) (f18 f19 ?v1))) (f18 f19 (f18 (f20 f21 ?v0) ?v1))) f1)))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f20 f21 ?v0))) (= (f18 (f20 f21 (f18 ?v_0 ?v1)) ?v2) (f18 ?v_0 (f18 (f20 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f87 f88 ?v0))) (= (f6 (f87 f88 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f87 f88 ?v1) ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f89 f90 ?v0))) (= (f59 (f89 f90 (f59 ?v_0 ?v1)) ?v2) (f59 ?v_0 (f59 (f89 f90 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f85 f86 ?v0))) (= (f42 (f85 f86 (f42 ?v_0 ?v1)) ?v2) (f42 ?v_0 (f42 (f85 f86 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f20 f21 ?v0))) (= (f18 (f20 f21 (f18 ?v_0 ?v1)) ?v2) (f18 ?v_0 (f18 (f20 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f87 f88 ?v0))) (= (f6 (f87 f88 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f87 f88 ?v1) ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f89 f90 ?v0))) (= (f59 (f89 f90 (f59 ?v_0 ?v1)) ?v2) (f59 ?v_0 (f59 (f89 f90 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f85 f86 ?v0))) (= (f42 (f85 f86 (f42 ?v_0 ?v1)) ?v2) (f42 ?v_0 (f42 (f85 f86 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f20 f21 ?v0))) (= (f18 (f20 f21 (f18 ?v_0 ?v1)) ?v2) (f18 ?v_0 (f18 (f20 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f87 f88 ?v0))) (= (f6 (f87 f88 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f87 f88 ?v1) ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_0 (f89 f90 ?v0))) (= (f59 (f89 f90 (f59 ?v_0 ?v1)) ?v2) (f59 ?v_0 (f59 (f89 f90 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f85 f86 ?v0))) (= (f42 (f85 f86 (f42 ?v_0 ?v1)) ?v2) (f42 ?v_0 (f42 (f85 f86 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_1 (f20 f21 ?v0)) (?v_0 (f20 f21 ?v1))) (= (f18 ?v_1 (f18 ?v_0 ?v2)) (f18 ?v_0 (f18 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f87 f88 ?v0)) (?v_0 (f87 f88 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_1 (f89 f90 ?v0)) (?v_0 (f89 f90 ?v1))) (= (f59 ?v_1 (f59 ?v_0 ?v2)) (f59 ?v_0 (f59 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f85 f86 ?v0)) (?v_0 (f85 f86 ?v1))) (= (f42 ?v_1 (f42 ?v_0 ?v2)) (f42 ?v_0 (f42 ?v_1 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_1 (f20 f21 ?v0)) (?v_0 (f20 f21 ?v1))) (= (f18 ?v_1 (f18 ?v_0 ?v2)) (f18 ?v_0 (f18 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f87 f88 ?v0)) (?v_0 (f87 f88 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_1 (f89 f90 ?v0)) (?v_0 (f89 f90 ?v1))) (= (f59 ?v_1 (f59 ?v_0 ?v2)) (f59 ?v_0 (f59 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f85 f86 ?v0)) (?v_0 (f85 f86 ?v1))) (= (f42 ?v_1 (f42 ?v_0 ?v2)) (f42 ?v_0 (f42 ?v_1 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_1 (f20 f21 ?v0)) (?v_0 (f20 f21 ?v1))) (= (f18 ?v_1 (f18 ?v_0 ?v2)) (f18 ?v_0 (f18 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f87 f88 ?v0)) (?v_0 (f87 f88 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (let ((?v_1 (f89 f90 ?v0)) (?v_0 (f89 f90 ?v1))) (= (f59 ?v_1 (f59 ?v_0 ?v2)) (f59 ?v_0 (f59 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f85 f86 ?v0)) (?v_0 (f85 f86 ?v1))) (= (f42 ?v_1 (f42 ?v_0 ?v2)) (f42 ?v_0 (f42 ?v_1 ?v2))))))
(check-sat)
(exit)