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
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S6) S1)
(declare-fun f7 (S5) S5)
(declare-fun f8 (S7 S6) S6)
(declare-fun f9 () S7)
(declare-fun f10 (S10 S8) S1)
(declare-fun f11 (S11 S9) S10)
(declare-fun f12 (S12 S8) S11)
(declare-fun f13 () S12)
(declare-fun f14 (S8 S13) S3)
(declare-fun f15 (S14 S6) S3)
(declare-fun f16 (S15 S2) S14)
(declare-fun f17 (S9) S15)
(declare-fun f18 () S6)
(declare-fun f19 () S12)
(declare-fun f20 (S16 S4) S1)
(declare-fun f21 (S17 S9) S16)
(declare-fun f22 (S18 S4) S17)
(declare-fun f23 (S6) S18)
(declare-fun f24 (S6) S12)
(declare-fun f25 (S19 S20) S1)
(declare-fun f26 (S12) S19)
(declare-fun f27 () S20)
(declare-fun f28 (S6) S19)
(declare-fun f29 (S22 S21) S1)
(declare-fun f30 (S6) S22)
(declare-fun f31 (S18) S22)
(declare-fun f32 (S23 S8) S20)
(declare-fun f33 (S24 S9) S23)
(declare-fun f34 (S25 S8) S24)
(declare-fun f35 () S25)
(declare-fun f36 (S26 S4) S21)
(declare-fun f37 (S27 S9) S26)
(declare-fun f38 (S28 S4) S27)
(declare-fun f39 () S28)
(declare-fun f40 (S21 S22) S1)
(declare-fun f41 (S20 S19) S1)
(declare-fun f42 (S19 S19) S1)
(declare-fun f43 (S22 S22) S1)
(declare-fun f44 () S9)
(declare-fun f45 () S1)
(declare-fun f46 (S29 S9) S9)
(declare-fun f47 (S30 S9) S29)
(declare-fun f48 () S30)
(declare-fun f49 (S31 S3) S30)
(declare-fun f50 () S31)
(declare-fun f51 (S9) S1)
(declare-fun f52 (S34 S33) S9)
(declare-fun f53 (S35 S32) S34)
(declare-fun f54 () S35)
(declare-fun f55 (S37 S33) S29)
(declare-fun f56 (S38 S36) S37)
(declare-fun f57 () S38)
(declare-fun f58 (S39 S3) S29)
(declare-fun f59 () S39)
(declare-fun f60 (S9) S4)
(declare-fun f61 () S6)
(declare-fun f62 (S40 S21) S6)
(declare-fun f63 (S41 S33) S40)
(declare-fun f64 () S41)
(declare-fun f65 (S43 S20) S6)
(declare-fun f66 (S44 S42) S43)
(declare-fun f67 () S44)
(declare-fun f68 (S45 S9) S21)
(declare-fun f69 () S45)
(declare-fun f70 () S40)
(declare-fun f71 () S43)
(declare-fun f72 (S47 S46) S9)
(declare-fun f73 () S47)
(declare-fun f74 (S48 S6) S2)
(declare-fun f75 (S49 S32) S48)
(declare-fun f76 (S50 S2) S49)
(declare-fun f77 () S50)
(declare-fun f78 (S33 S2) S6)
(declare-fun f79 (S51 S52) S9)
(declare-fun f80 () S51)
(declare-fun f81 (S53 S46) S52)
(declare-fun f82 () S53)
(declare-fun f83 (S54 S9) S6)
(declare-fun f84 () S54)
(declare-fun f85 (S55 S5) S6)
(declare-fun f86 () S55)
(declare-fun f87 (S56 S6) S7)
(declare-fun f88 () S56)
(declare-fun f89 (S58 S57) S57)
(declare-fun f90 (S59 S57) S58)
(declare-fun f91 () S59)
(declare-fun f92 () S57)
(declare-fun f93 () S54)
(declare-fun f94 () S7)
(declare-fun f95 () S7)
(declare-fun f96 (S60 S1) S6)
(declare-fun f97 () S60)
(declare-fun f98 (S61 S46) S34)
(declare-fun f99 (S62 S32) S61)
(declare-fun f100 () S62)
(declare-fun f101 () S52)
(declare-fun f102 (S63 S54) S64)
(declare-fun f103 () S63)
(declare-fun f104 (S64 S52) S6)
(declare-fun f105 () S64)
(declare-fun f106 (S65 S9) S52)
(declare-fun f107 () S65)
(declare-fun f108 () S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S6)) (= (= (f6 (f7 ?v0) ?v1) f1) (= (f6 ?v0 (f8 f9 ?v1)) f1))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S8)) (= (= (f10 (f11 (f12 f13 ?v0) ?v1) ?v2) f1) (forall ((?v3 S13) (?v4 S2)) (=> (= (f3 (f14 ?v0 ?v3) ?v4) f1) (forall ((?v5 S2)) (=> (= (f3 (f15 (f16 (f17 ?v1) ?v4) (f8 f9 f18)) ?v5) f1) (= (f3 (f14 ?v2 ?v3) ?v5) f1))))))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S8)) (= (= (f10 (f11 (f12 f19 ?v0) ?v1) ?v2) f1) (forall ((?v3 S13) (?v4 S2)) (=> (= (f3 (f14 ?v0 ?v3) ?v4) f1) (forall ((?v5 S2)) (=> (= (f3 (f15 (f16 (f17 ?v1) ?v4) f18) ?v5) f1) (= (f3 (f14 ?v2 ?v3) ?v5) f1))))))))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S9) (?v3 S4)) (= (= (f20 (f21 (f22 (f23 ?v0) ?v1) ?v2) ?v3) f1) (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f4 ?v1 ?v4) ?v5) f1) (forall ((?v6 S2)) (=> (= (f3 (f15 (f16 (f17 ?v2) ?v5) ?v0) ?v6) f1) (= (f3 (f4 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S9) (?v3 S8)) (= (= (f10 (f11 (f12 (f24 ?v0) ?v1) ?v2) ?v3) f1) (forall ((?v4 S13) (?v5 S2)) (=> (= (f3 (f14 ?v1 ?v4) ?v5) f1) (forall ((?v6 S2)) (=> (= (f3 (f15 (f16 (f17 ?v2) ?v5) ?v0) ?v6) f1) (= (f3 (f14 ?v3 ?v4) ?v6) f1))))))))
(assert (not (=> (= (f25 (f26 f13) f27) f1) (= (f25 (f26 f19) f27) f1))))
(assert (forall ((?v0 S6) (?v1 S20)) (= (= (f25 (f28 ?v0) ?v1) f1) (= (f25 (f26 (f24 ?v0)) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S21)) (= (= (f29 (f30 ?v0) ?v1) f1) (= (f29 (f31 (f23 ?v0)) ?v1) f1))))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S6) (?v3 S2)) (let ((?v_0 (f16 (f17 ?v0) ?v1))) (=> (= (f3 (f15 ?v_0 ?v2) ?v3) f1) (= (f3 (f15 ?v_0 (f8 f9 ?v2)) ?v3) f1)))))
(assert (forall ((?v0 S6)) (not (= ?v0 (f8 f9 ?v0)))))
(assert (forall ((?v0 S6)) (not (= (f8 f9 ?v0) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f8 f9 ?v0) (f8 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f8 f9 ?v0) (f8 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S8) (?v2 S9) (?v3 S8)) (= (= (f25 (f26 ?v0) (f32 (f33 (f34 f35 ?v1) ?v2) ?v3)) f1) (= (f10 (f11 (f12 ?v0 ?v1) ?v2) ?v3) f1))))
(assert (forall ((?v0 S18) (?v1 S4) (?v2 S9) (?v3 S4)) (= (= (f29 (f31 ?v0) (f36 (f37 (f38 f39 ?v1) ?v2) ?v3)) f1) (= (f20 (f21 (f22 ?v0 ?v1) ?v2) ?v3) f1))))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S6) (?v3 S2) (?v4 S9) (?v5 S2) (?v6 S6) (?v7 S2)) (=> (= (f3 (f15 (f16 (f17 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f3 (f15 (f16 (f17 ?v4) ?v5) ?v6) ?v7) f1) (exists ((?v8 S6)) (and (= (f3 (f15 (f16 (f17 ?v0) ?v1) ?v8) ?v3) f1) (= (f3 (f15 (f16 (f17 ?v4) ?v5) ?v8) ?v7) f1)))))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (=> (forall ((?v3 S21)) (=> (= (f29 ?v0 ?v3) f1) (=> (= (f29 ?v1 ?v3) f1) (= (f29 ?v2 ?v3) f1)))) (=> (forall ((?v3 S21)) (= (f29 ?v1 ?v3) f1)) (forall ((?v3 S21)) (=> (= (f40 ?v3 ?v0) f1) (= (f29 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19)) (=> (forall ((?v3 S20)) (=> (= (f25 ?v0 ?v3) f1) (=> (= (f25 ?v1 ?v3) f1) (= (f25 ?v2 ?v3) f1)))) (=> (forall ((?v3 S20)) (= (f25 ?v1 ?v3) f1)) (forall ((?v3 S20)) (=> (= (f41 ?v3 ?v0) f1) (= (f25 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S4) (?v1 S9) (?v2 S4) (?v3 S4) (?v4 S9) (?v5 S4)) (= (= (f36 (f37 (f38 f39 ?v0) ?v1) ?v2) (f36 (f37 (f38 f39 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S8) (?v3 S8) (?v4 S9) (?v5 S8)) (= (= (f32 (f33 (f34 f35 ?v0) ?v1) ?v2) (f32 (f33 (f34 f35 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S9) (?v3 S4)) (= (= (f29 (f30 ?v0) (f36 (f37 (f38 f39 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f4 ?v1 ?v4) ?v5) f1) (forall ((?v6 S2)) (=> (= (f3 (f15 (f16 (f17 ?v2) ?v5) ?v0) ?v6) f1) (= (f3 (f4 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S9) (?v3 S8)) (= (= (f25 (f28 ?v0) (f32 (f33 (f34 f35 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S13) (?v5 S2)) (=> (= (f3 (f14 ?v1 ?v4) ?v5) f1) (forall ((?v6 S2)) (=> (= (f3 (f15 (f16 (f17 ?v2) ?v5) ?v0) ?v6) f1) (= (f3 (f14 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S19) (?v1 S19)) (= (= (f42 ?v0 ?v1) f1) (forall ((?v2 S6)) (=> (forall ((?v3 S20)) (=> (= (f41 ?v3 ?v0) f1) (= (f25 (f28 ?v2) ?v3) f1))) (forall ((?v3 S20)) (=> (= (f41 ?v3 ?v1) f1) (= (f25 (f28 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S22) (?v1 S22)) (= (= (f43 ?v0 ?v1) f1) (forall ((?v2 S6)) (=> (forall ((?v3 S21)) (=> (= (f40 ?v3 ?v0) f1) (= (f29 (f30 ?v2) ?v3) f1))) (forall ((?v3 S21)) (=> (= (f40 ?v3 ?v1) f1) (= (f29 (f30 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S21)) (=> (forall ((?v1 S4) (?v2 S9) (?v3 S4)) (=> (= ?v0 (f36 (f37 (f38 f39 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S20)) (=> (forall ((?v1 S8) (?v2 S9) (?v3 S8)) (=> (= ?v0 (f32 (f33 (f34 f35 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S2)) (=> (= (f3 (f15 (f16 (f17 f44) ?v0) ?v1) ?v2) f1) (=> (=> (= ?v2 ?v0) false) false))))
(assert (forall ((?v0 S2) (?v1 S6)) (= (f3 (f15 (f16 (f17 f44) ?v0) ?v1) ?v0) f1)))
(assert (= (= f45 f1) false))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S6) (?v3 S2) (?v4 S9) (?v5 S2)) (=> (= (f3 (f15 (f16 (f17 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f3 (f15 (f16 (f17 ?v4) ?v3) ?v2) ?v5) f1) (= (f3 (f15 (f16 (f17 (f46 (f47 f48 ?v0) ?v4)) ?v1) ?v2) ?v5) f1)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9) (?v3 S2) (?v4 S6) (?v5 S2)) (let ((?v_0 (= (f3 ?v0 ?v3) f1))) (=> (= (f3 (f15 (f16 (f17 (f46 (f47 (f49 f50 ?v0) ?v1) ?v2)) ?v3) ?v4) ?v5) f1) (=> (=> ?v_0 (=> (= (f3 (f15 (f16 (f17 ?v1) ?v3) ?v4) ?v5) f1) false)) (=> (=> (not ?v_0) (=> (= (f3 (f15 (f16 (f17 ?v2) ?v3) ?v4) ?v5) f1) false)) false))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S9) (?v3 S6) (?v4 S2) (?v5 S9)) (=> (not (= (f3 ?v0 ?v1) f1)) (=> (= (f3 (f15 (f16 (f17 ?v2) ?v1) ?v3) ?v4) f1) (= (f3 (f15 (f16 (f17 (f46 (f47 (f49 f50 ?v0) ?v5) ?v2)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S9) (?v3 S6) (?v4 S2) (?v5 S9)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 (f15 (f16 (f17 ?v2) ?v1) ?v3) ?v4) f1) (= (f3 (f15 (f16 (f17 (f46 (f47 (f49 f50 ?v0) ?v2) ?v5)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S2) (?v3 S6) (?v4 S2)) (=> (= (f3 (f15 (f16 (f17 (f46 (f47 f48 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (forall ((?v5 S2)) (=> (= (f3 (f15 (f16 (f17 ?v0) ?v2) ?v3) ?v5) f1) (=> (= (f3 (f15 (f16 (f17 ?v1) ?v5) ?v3) ?v4) f1) false))) false))))
(assert (forall ((?v0 S9) (?v1 S9)) (not (= (f46 (f47 f48 ?v0) ?v1) f44))))
(assert (forall ((?v0 S9) (?v1 S9)) (not (= f44 (f46 (f47 f48 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9)) (not (= (f46 (f47 (f49 f50 ?v0) ?v1) ?v2) f44))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9)) (not (= f44 (f46 (f47 (f49 f50 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9) (?v3 S9) (?v4 S9)) (not (= (f46 (f47 (f49 f50 ?v0) ?v1) ?v2) (f46 (f47 f48 ?v3) ?v4)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S3) (?v3 S9) (?v4 S9)) (not (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 (f49 f50 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (= (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 f48 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9) (?v3 S3) (?v4 S9) (?v5 S9)) (= (= (f46 (f47 (f49 f50 ?v0) ?v1) ?v2) (f46 (f47 (f49 f50 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (=> (= (f51 f44) f1) (=> false false)))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f51 (f46 (f47 f48 ?v0) ?v1)) f1) (=> (=> (= (f51 ?v0) f1) (=> (= (f51 ?v1) f1) false)) false))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9)) (=> (= (f51 (f46 (f47 (f49 f50 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f51 ?v1) f1) (=> (= (f51 ?v2) f1) false)) false))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S3)) (=> (= (f51 ?v0) f1) (=> (= (f51 ?v1) f1) (= (f51 (f46 (f47 (f49 f50 ?v2) ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f51 ?v0) f1) (=> (= (f51 ?v1) f1) (= (f51 (f46 (f47 f48 ?v0) ?v1)) f1)))))
(assert (= (f51 f44) f1))
(assert (forall ((?v0 S32) (?v1 S33)) (=> (= (f51 (f52 (f53 f54 ?v0) ?v1)) f1) (=> false false))))
(assert (forall ((?v0 S36) (?v1 S33) (?v2 S9)) (=> (= (f51 (f46 (f55 (f56 f57 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f51 ?v2) f1) false) false))))
(assert (forall ((?v0 S3) (?v1 S9)) (=> (= (f51 (f46 (f58 f59 ?v0) ?v1)) f1) (=> (=> (= (f51 ?v1) f1) false) false))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S9) (?v3 S6)) (=> (not (= (f3 ?v0 ?v1) f1)) (= (f3 (f15 (f16 (f17 (f46 (f58 f59 ?v0) ?v2)) ?v1) ?v3) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S9) (?v3 S6) (?v4 S2) (?v5 S2)) (let ((?v_0 (f17 (f46 (f58 f59 ?v0) ?v2)))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 (f15 (f16 (f17 ?v2) ?v1) ?v3) ?v4) f1) (=> (= (f3 (f15 (f16 ?v_0 ?v4) ?v3) ?v5) f1) (= (f3 (f15 (f16 ?v_0 ?v1) ?v3) ?v5) f1)))))))
(assert (forall ((?v0 S2)) (= (f3 (f4 (f60 f44) ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S9) (?v3 S2) (?v4 S2)) (let ((?v_0 (f60 (f46 (f58 f59 ?v0) ?v2)))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 (f4 (f60 ?v2) ?v1) ?v3) f1) (=> (= (f3 (f4 ?v_0 ?v3) ?v4) f1) (= (f3 (f4 ?v_0 ?v1) ?v4) f1)))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S9)) (=> (not (= (f3 ?v0 ?v1) f1)) (= (f3 (f4 (f60 (f46 (f58 f59 ?v0) ?v2)) ?v1) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9) (?v3 S2) (?v4 S2)) (let ((?v_0 (= (f3 ?v0 ?v3) f1))) (=> (= (f3 (f4 (f60 (f46 (f47 (f49 f50 ?v0) ?v1) ?v2)) ?v3) ?v4) f1) (=> (=> ?v_0 (=> (= (f3 (f4 (f60 ?v1) ?v3) ?v4) f1) false)) (=> (=> (not ?v_0) (=> (= (f3 (f4 (f60 ?v2) ?v3) ?v4) f1) false)) false))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S9) (?v3 S2) (?v4 S9)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 (f4 (f60 ?v2) ?v1) ?v3) f1) (= (f3 (f4 (f60 (f46 (f47 (f49 f50 ?v0) ?v2) ?v4)) ?v1) ?v3) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S9) (?v3 S2) (?v4 S9)) (=> (not (= (f3 ?v0 ?v1) f1)) (=> (= (f3 (f4 (f60 ?v2) ?v1) ?v3) f1) (= (f3 (f4 (f60 (f46 (f47 (f49 f50 ?v0) ?v4) ?v2)) ?v1) ?v3) f1)))))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S2) (?v3 S9) (?v4 S2)) (=> (= (f3 (f4 (f60 ?v0) ?v1) ?v2) f1) (=> (= (f3 (f4 (f60 ?v3) ?v2) ?v4) f1) (= (f3 (f4 (f60 (f46 (f47 f48 ?v0) ?v3)) ?v1) ?v4) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 (f60 f44) ?v0) ?v1) f1) (=> (=> (= ?v1 ?v0) false) false))))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f4 (f60 ?v0) ?v1))) (=> (= (f3 ?v_0 ?v2) f1) (=> (= (f3 ?v_0 ?v3) f1) (= ?v3 ?v2))))))
(assert (forall ((?v0 S36) (?v1 S33) (?v2 S9) (?v3 S36) (?v4 S33) (?v5 S9)) (= (= (f46 (f55 (f56 f57 ?v0) ?v1) ?v2) (f46 (f55 (f56 f57 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S3) (?v3 S9)) (= (= (f46 (f58 f59 ?v0) ?v1) (f46 (f58 f59 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S32) (?v1 S33) (?v2 S32) (?v3 S33)) (= (= (f52 (f53 f54 ?v0) ?v1) (f52 (f53 f54 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S36) (?v1 S33) (?v2 S9) (?v3 S32) (?v4 S33)) (not (= (f46 (f55 (f56 f57 ?v0) ?v1) ?v2) (f52 (f53 f54 ?v3) ?v4)))))
(assert (forall ((?v0 S36) (?v1 S33) (?v2 S9) (?v3 S3) (?v4 S9)) (not (= (f46 (f55 (f56 f57 ?v0) ?v1) ?v2) (f46 (f58 f59 ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S36) (?v3 S33) (?v4 S9)) (not (= (f46 (f58 f59 ?v0) ?v1) (f46 (f55 (f56 f57 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S32) (?v1 S33) (?v2 S36) (?v3 S33) (?v4 S9)) (not (= (f52 (f53 f54 ?v0) ?v1) (f46 (f55 (f56 f57 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S32) (?v3 S33)) (not (= (f46 (f58 f59 ?v0) ?v1) (f52 (f53 f54 ?v2) ?v3)))))
(assert (forall ((?v0 S32) (?v1 S33) (?v2 S3) (?v3 S9)) (not (= (f52 (f53 f54 ?v0) ?v1) (f46 (f58 f59 ?v2) ?v3)))))
(assert (forall ((?v0 S6)) (=> (= (f8 f9 ?v0) f61) false)))
(assert (forall ((?v0 S6)) (=> (= f61 (f8 f9 ?v0)) false)))
(assert (forall ((?v0 S6)) (not (= (f8 f9 ?v0) f61))))
(assert (forall ((?v0 S6)) (not (= (f8 f9 ?v0) f61))))
(assert (forall ((?v0 S6)) (not (= f61 (f8 f9 ?v0)))))
(assert (forall ((?v0 S6)) (not (= f61 (f8 f9 ?v0)))))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S6) (?v3 S2)) (=> (= (f3 (f15 (f16 (f17 ?v0) ?v1) ?v2) ?v3) f1) (= (f3 (f4 (f60 ?v0) ?v1) ?v3) f1))))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f60 ?v0) ?v1) ?v2) f1) (exists ((?v3 S6)) (= (f3 (f15 (f16 (f17 ?v0) ?v1) ?v3) ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S3)) (=> (= (f51 ?v0) f1) (= (f51 (f46 (f58 f59 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S9) (?v1 S36) (?v2 S33)) (=> (= (f51 ?v0) f1) (= (f51 (f46 (f55 (f56 f57 ?v1) ?v2) ?v0)) f1))))
(assert (forall ((?v0 S32) (?v1 S33)) (= (f51 (f52 (f53 f54 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S3) (?v3 S9) (?v4 S9)) (not (= (f46 (f58 f59 ?v0) ?v1) (f46 (f47 (f49 f50 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9) (?v3 S3) (?v4 S9)) (not (= (f46 (f47 (f49 f50 ?v0) ?v1) ?v2) (f46 (f58 f59 ?v3) ?v4)))))
(assert (forall ((?v0 S32) (?v1 S33) (?v2 S3) (?v3 S9) (?v4 S9)) (not (= (f52 (f53 f54 ?v0) ?v1) (f46 (f47 (f49 f50 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9) (?v3 S32) (?v4 S33)) (not (= (f46 (f47 (f49 f50 ?v0) ?v1) ?v2) (f52 (f53 f54 ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9) (?v3 S36) (?v4 S33) (?v5 S9)) (not (= (f46 (f47 (f49 f50 ?v0) ?v1) ?v2) (f46 (f55 (f56 f57 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S36) (?v1 S33) (?v2 S9) (?v3 S3) (?v4 S9) (?v5 S9)) (not (= (f46 (f55 (f56 f57 ?v0) ?v1) ?v2) (f46 (f47 (f49 f50 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S3) (?v3 S9)) (not (= (f46 (f47 f48 ?v0) ?v1) (f46 (f58 f59 ?v2) ?v3)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9) (?v3 S9)) (not (= (f46 (f58 f59 ?v0) ?v1) (f46 (f47 f48 ?v2) ?v3)))))
(assert (forall ((?v0 S32) (?v1 S33) (?v2 S9) (?v3 S9)) (not (= (f52 (f53 f54 ?v0) ?v1) (f46 (f47 f48 ?v2) ?v3)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S32) (?v3 S33)) (not (= (f46 (f47 f48 ?v0) ?v1) (f52 (f53 f54 ?v2) ?v3)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S36) (?v3 S33) (?v4 S9)) (not (= (f46 (f47 f48 ?v0) ?v1) (f46 (f55 (f56 f57 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S36) (?v1 S33) (?v2 S9) (?v3 S9) (?v4 S9)) (not (= (f46 (f55 (f56 f57 ?v0) ?v1) ?v2) (f46 (f47 f48 ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S9)) (not (= f44 (f46 (f58 f59 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S9)) (not (= (f46 (f58 f59 ?v0) ?v1) f44))))
(assert (forall ((?v0 S32) (?v1 S33)) (not (= f44 (f52 (f53 f54 ?v0) ?v1)))))
(assert (forall ((?v0 S36) (?v1 S33) (?v2 S9)) (not (= f44 (f46 (f55 (f56 f57 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S32) (?v1 S33)) (not (= (f52 (f53 f54 ?v0) ?v1) f44))))
(assert (forall ((?v0 S36) (?v1 S33) (?v2 S9)) (not (= (f46 (f55 (f56 f57 ?v0) ?v1) ?v2) f44))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S2) (?v3 S2)) (=> (= (f3 (f4 (f60 (f46 (f47 f48 ?v0) ?v1)) ?v2) ?v3) f1) (=> (forall ((?v4 S2)) (=> (= (f3 (f4 (f60 ?v0) ?v2) ?v4) f1) (=> (= (f3 (f4 (f60 ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S33) (?v1 S4) (?v2 S9) (?v3 S4)) (= (f62 (f63 f64 ?v0) (f36 (f37 (f38 f39 ?v1) ?v2) ?v3)) f61)))
(assert (forall ((?v0 S42) (?v1 S8) (?v2 S9) (?v3 S8)) (= (f65 (f66 f67 ?v0) (f32 (f33 (f34 f35 ?v1) ?v2) ?v3)) f61)))
(assert (forall ((?v0 S9)) (= (f68 f69 ?v0) (f36 (f37 (f38 f39 f5) ?v0) (f60 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S2) (?v3 S2)) (=> (= (f3 (f4 (f60 (f46 (f58 f59 ?v0) ?v1)) ?v2) ?v3) f1) (=> (=> (= ?v3 ?v2) (=> (not (= (f3 ?v0 ?v2) f1)) false)) (=> (forall ((?v4 S2)) (=> (= (f3 ?v0 ?v2) f1) (=> (= (f3 (f4 (f60 ?v1) ?v2) ?v4) f1) (=> (= (f3 (f4 (f60 (f46 (f58 f59 ?v0) ?v1)) ?v4) ?v3) f1) false)))) false)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S2) (?v3 S6) (?v4 S2)) (=> (= (f3 (f15 (f16 (f17 (f46 (f58 f59 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (=> (= ?v4 ?v2) (=> (not (= (f3 ?v0 ?v2) f1)) false)) (=> (forall ((?v5 S2)) (=> (= (f3 ?v0 ?v2) f1) (=> (= (f3 (f15 (f16 (f17 ?v1) ?v2) ?v3) ?v5) f1) (=> (= (f3 (f15 (f16 (f17 (f46 (f58 f59 ?v0) ?v1)) ?v5) ?v3) ?v4) f1) false)))) false)))))
(assert (forall ((?v0 S4) (?v1 S9) (?v2 S4)) (= (f62 f70 (f36 (f37 (f38 f39 ?v0) ?v1) ?v2)) f61)))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S8)) (= (f65 f71 (f32 (f33 (f34 f35 ?v0) ?v1) ?v2)) f61)))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 (f60 ?v0) ?v1) ?v2) f1) (exists ((?v3 S6)) (= (f3 (f15 (f16 (f17 ?v0) ?v1) ?v3) ?v2) f1)))))
(assert (forall ((?v0 S6)) (=> (not (= ?v0 f61)) (exists ((?v1 S6)) (= ?v0 (f8 f9 ?v1))))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f6 ?v0 f61) f1) (=> (forall ((?v2 S6)) (=> (= (f6 ?v0 ?v2) f1) (= (f6 ?v0 (f8 f9 ?v2)) f1))) (= (f6 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f6 ?v0 ?v1) f1) (=> (forall ((?v2 S6)) (=> (= (f6 ?v0 (f8 f9 ?v2)) f1) (= (f6 ?v0 ?v2) f1))) (= (f6 ?v0 f61) f1)))))
(assert (forall ((?v0 S6)) (=> (=> (= ?v0 f61) false) (=> (forall ((?v1 S6)) (=> (= ?v0 (f8 f9 ?v1)) false)) false))))
(assert (forall ((?v0 S4) (?v1 S46) (?v2 S4)) (= (f29 (f30 f61) (f36 (f37 (f38 f39 ?v0) (f72 f73 ?v1)) ?v2)) f1)))
(assert (forall ((?v0 S8) (?v1 S46) (?v2 S8)) (= (f25 (f28 f61) (f32 (f33 (f34 f35 ?v0) (f72 f73 ?v1)) ?v2)) f1)))
(assert (forall ((?v0 S32) (?v1 S33) (?v2 S2) (?v3 S2)) (=> (= (f3 (f4 (f60 (f52 (f53 f54 ?v0) ?v1)) ?v2) ?v3) f1) (=> (=> (= ?v3 (f74 (f75 (f76 f77 ?v2) ?v0) (f78 ?v1 ?v2))) false) false))))
(assert (forall ((?v0 S32) (?v1 S33) (?v2 S2)) (= (f3 (f4 (f60 (f52 (f53 f54 ?v0) ?v1)) ?v2) (f74 (f75 (f76 f77 ?v2) ?v0) (f78 ?v1 ?v2))) f1)))
(assert (forall ((?v0 S32) (?v1 S33) (?v2 S2) (?v3 S6)) (= (f3 (f15 (f16 (f17 (f52 (f53 f54 ?v0) ?v1)) ?v2) ?v3) (f74 (f75 (f76 f77 ?v2) ?v0) (f78 ?v1 ?v2))) f1)))
(assert (forall ((?v0 S32) (?v1 S33) (?v2 S2) (?v3 S6) (?v4 S2)) (=> (= (f3 (f15 (f16 (f17 (f52 (f53 f54 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (=> (= ?v4 (f74 (f75 (f76 f77 ?v2) ?v0) (f78 ?v1 ?v2))) false) false))))
(assert (forall ((?v0 S46) (?v1 S46)) (= (= (f72 f73 ?v0) (f72 f73 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S46) (?v1 S3) (?v2 S9)) (not (= (f72 f73 ?v0) (f46 (f58 f59 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S46)) (not (= (f46 (f58 f59 ?v0) ?v1) (f72 f73 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9) (?v3 S46)) (not (= (f46 (f47 (f49 f50 ?v0) ?v1) ?v2) (f72 f73 ?v3)))))
(assert (forall ((?v0 S46) (?v1 S3) (?v2 S9) (?v3 S9)) (not (= (f72 f73 ?v0) (f46 (f47 (f49 f50 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S46)) (not (= (f46 (f47 f48 ?v0) ?v1) (f72 f73 ?v2)))))
(assert (forall ((?v0 S46) (?v1 S9) (?v2 S9)) (not (= (f72 f73 ?v0) (f46 (f47 f48 ?v1) ?v2)))))
(assert (forall ((?v0 S46) (?v1 S32) (?v2 S33)) (not (= (f72 f73 ?v0) (f52 (f53 f54 ?v1) ?v2)))))
(assert (forall ((?v0 S46) (?v1 S36) (?v2 S33) (?v3 S9)) (not (= (f72 f73 ?v0) (f46 (f55 (f56 f57 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S32) (?v1 S33) (?v2 S46)) (not (= (f52 (f53 f54 ?v0) ?v1) (f72 f73 ?v2)))))
(assert (forall ((?v0 S36) (?v1 S33) (?v2 S9) (?v3 S46)) (not (= (f46 (f55 (f56 f57 ?v0) ?v1) ?v2) (f72 f73 ?v3)))))
(assert (forall ((?v0 S46)) (not (= (f72 f73 ?v0) f44))))
(assert (forall ((?v0 S46)) (not (= f44 (f72 f73 ?v0)))))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S46) (?v3 S4)) (let ((?v_0 (f38 f39 ?v1))) (= (= (f29 (f30 ?v0) (f36 (f37 ?v_0 (f79 f80 (f81 f82 ?v2))) ?v3)) f1) (= (f29 (f30 (f8 f9 ?v0)) (f36 (f37 ?v_0 (f72 f73 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S46) (?v3 S8)) (let ((?v_0 (f34 f35 ?v1))) (= (= (f25 (f28 ?v0) (f32 (f33 ?v_0 (f79 f80 (f81 f82 ?v2))) ?v3)) f1) (= (f25 (f28 (f8 f9 ?v0)) (f32 (f33 ?v_0 (f72 f73 ?v2)) ?v3)) f1)))))
(assert (= (f83 f84 f44) f61))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f6 ?v0 ?v1) f1) (=> (not (= (f6 ?v0 f61) f1)) (= (f85 f86 ?v0) (f8 f9 (f85 f86 (f7 ?v0))))))))
(assert (forall ((?v0 S32) (?v1 S33)) (= (f83 f84 (f52 (f53 f54 ?v0) ?v1)) f61)))
(assert (forall ((?v0 S46) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 (f60 (f72 f73 ?v0)) ?v1) ?v2) f1) (=> (=> (= (f3 (f4 (f60 (f79 f80 (f81 f82 ?v0))) ?v1) ?v2) f1) false) false))))
(assert (forall ((?v0 S46) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 (f60 (f79 f80 (f81 f82 ?v0))) ?v1) ?v2) f1) (= (f3 (f4 (f60 (f72 f73 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S46) (?v1 S2) (?v2 S6) (?v3 S2)) (=> (= (f3 (f15 (f16 (f17 (f79 f80 (f81 f82 ?v0))) ?v1) ?v2) ?v3) f1) (= (f3 (f15 (f16 (f17 (f72 f73 ?v0)) ?v1) (f8 f9 ?v2)) ?v3) f1))))
(assert (forall ((?v0 S46)) (= (f83 f84 (f72 f73 ?v0)) f61)))
(assert (forall ((?v0 S46) (?v1 S2) (?v2 S6) (?v3 S2)) (=> (= (f3 (f15 (f16 (f17 (f72 f73 ?v0)) ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S6)) (=> (= ?v2 (f8 f9 ?v4)) (=> (= (f3 (f15 (f16 (f17 (f79 f80 (f81 f82 ?v0))) ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5) (?v3 S6)) (=> (= (f6 ?v0 ?v1) f1) (=> (= (f6 ?v2 ?v3) f1) (=> (not (= (f6 ?v0 f61) f1)) (=> (forall ((?v4 S6)) (= (= (f6 ?v0 (f8 f9 ?v4)) f1) (= (f6 ?v2 ?v4) f1))) (= (f85 f86 ?v0) (f8 f9 (f85 f86 ?v2)))))))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f6 ?v0 ?v1) f1) (= (f6 ?v0 (f85 f86 ?v0)) f1))))
(assert (forall ((?v0 S5)) (=> (exists ((?v1 S6)) (= (f6 ?v0 ?v1) f1)) (= (f6 ?v0 (f85 f86 ?v0)) f1))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (=> (= (f6 ?v0 ?v1) f1) (=> (forall ((?v3 S6)) (=> (= (f6 ?v0 ?v3) f1) (= (f6 ?v2 ?v3) f1))) (= (f6 ?v2 (f85 f86 ?v0)) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (exists ((?v2 S6)) (= (f6 ?v0 ?v2) f1)) (=> (forall ((?v2 S6)) (=> (= (f6 ?v0 ?v2) f1) (= (f6 ?v1 ?v2) f1))) (= (f6 ?v1 (f85 f86 ?v0)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f83 f84 (f46 (f47 f48 ?v0) ?v1)) (f8 (f87 f88 (f8 (f87 f88 (f83 f84 ?v0)) (f83 f84 ?v1))) (f8 f9 f61)))))
(assert (forall ((?v0 S6)) (= (f8 (f87 f88 f61) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f8 (f87 f88 ?v0) f61) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f8 (f87 f88 ?v0) ?v1) f61) (and (= ?v0 f61) (= ?v1 f61)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f8 (f87 f88 ?v0) ?v1) ?v0) (= ?v1 f61))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f87 f88 ?v0))) (= (f8 ?v_0 (f8 f9 ?v1)) (f8 f9 (f8 ?v_0 ?v1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f8 (f87 f88 (f8 f9 ?v0)) ?v1) (f8 f9 (f8 (f87 f88 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f8 (f87 f88 (f8 f9 ?v0)) ?v1) (f8 (f87 f88 ?v0) (f8 f9 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f8 (f87 f88 ?v0) ?v1) (f8 (f87 f88 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f87 f88 ?v0))) (= (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f87 f88 ?v0))) (= (f8 (f87 f88 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f87 f88 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f87 f88 ?v0)) (?v_0 (f87 f88 ?v1))) (= (f8 ?v_1 (f8 ?v_0 ?v2)) (f8 ?v_0 (f8 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f8 (f87 f88 ?v0) ?v1) (f8 (f87 f88 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f8 f9 f61))) (= (= (f8 (f87 f88 ?v0) ?v1) ?v_0) (or (and (= ?v0 ?v_0) (= ?v1 f61)) (and (= ?v0 f61) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f8 f9 f61))) (= (= ?v_0 (f8 (f87 f88 ?v0) ?v1)) (or (and (= ?v0 ?v_0) (= ?v1 f61)) (and (= ?v0 f61) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S9)) (= (f83 f84 (f46 (f58 f59 ?v0) ?v1)) (f8 (f87 f88 (f83 f84 ?v1)) (f8 f9 f61)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9)) (= (f83 f84 (f46 (f47 (f49 f50 ?v0) ?v1) ?v2)) (f8 (f87 f88 (f8 (f87 f88 (f83 f84 ?v1)) (f83 f84 ?v2))) (f8 f9 f61)))))
(assert (forall ((?v0 S36) (?v1 S33) (?v2 S9)) (= (f83 f84 (f46 (f55 (f56 f57 ?v0) ?v1) ?v2)) (f8 (f87 f88 (f83 f84 ?v2)) (f8 f9 f61)))))
(assert (forall ((?v0 S57)) (= (= (f89 (f90 f91 ?v0) ?v0) f92) (= ?v0 f92))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= ?v0 (f8 (f87 f88 ?v0) ?v1)) (= ?v1 f61))))
(assert (forall ((?v0 S57) (?v1 S57)) (= (= ?v0 (f89 (f90 f91 ?v0) ?v1)) (= ?v1 f92))))
(assert (forall ((?v0 S6)) (= (f8 (f87 f88 ?v0) f61) ?v0)))
(assert (forall ((?v0 S57)) (= (f89 (f90 f91 ?v0) f92) ?v0)))
(assert (forall ((?v0 S6)) (= (= f61 ?v0) (= ?v0 f61))))
(assert (forall ((?v0 S57)) (= (= f92 ?v0) (= ?v0 f92))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f8 (f87 f88 ?v0) ?v1) (f8 (f87 f88 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S57) (?v1 S57) (?v2 S57)) (=> (= (f89 (f90 f91 ?v0) ?v1) (f89 (f90 f91 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f87 f88 ?v0))) (=> (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S57) (?v1 S57) (?v2 S57)) (let ((?v_0 (f90 f91 ?v0))) (=> (= (f89 ?v_0 ?v1) (f89 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f87 f88 ?v0))) (=> (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S57) (?v1 S57) (?v2 S57)) (let ((?v_0 (f90 f91 ?v0))) (=> (= (f89 ?v_0 ?v1) (f89 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f87 f88 ?v0))) (= (f8 (f87 f88 (f8 ?v_0 ?v1)) (f8 (f87 f88 ?v2) ?v3)) (f8 (f87 f88 (f8 ?v_0 ?v2)) (f8 (f87 f88 ?v1) ?v3))))))
(assert (forall ((?v0 S57) (?v1 S57) (?v2 S57) (?v3 S57)) (let ((?v_0 (f90 f91 ?v0))) (= (f89 (f90 f91 (f89 ?v_0 ?v1)) (f89 (f90 f91 ?v2) ?v3)) (f89 (f90 f91 (f89 ?v_0 ?v2)) (f89 (f90 f91 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f8 (f87 f88 ?v0) ?v1) (f8 (f87 f88 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S57) (?v1 S57) (?v2 S57)) (= (= (f89 (f90 f91 ?v0) ?v1) (f89 (f90 f91 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f87 f88 ?v0))) (= (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S57) (?v1 S57) (?v2 S57)) (let ((?v_0 (f90 f91 ?v0))) (= (= (f89 ?v_0 ?v1) (f89 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f87 f88 ?v0))) (= (f8 (f87 f88 (f8 ?v_0 ?v1)) ?v2) (f8 (f87 f88 (f8 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S57) (?v1 S57) (?v2 S57)) (let ((?v_0 (f90 f91 ?v0))) (= (f89 (f90 f91 (f89 ?v_0 ?v1)) ?v2) (f89 (f90 f91 (f89 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f87 f88 ?v0))) (= (f8 (f87 f88 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f87 f88 ?v1) ?v2))))))
(assert (forall ((?v0 S57) (?v1 S57) (?v2 S57)) (let ((?v_0 (f90 f91 ?v0))) (= (f89 (f90 f91 (f89 ?v_0 ?v1)) ?v2) (f89 ?v_0 (f89 (f90 f91 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f87 f88 ?v0))) (= (f8 (f87 f88 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f87 f88 ?v1) ?v2))))))
(assert (forall ((?v0 S57) (?v1 S57) (?v2 S57)) (let ((?v_0 (f90 f91 ?v0))) (= (f89 (f90 f91 (f89 ?v_0 ?v1)) ?v2) (f89 ?v_0 (f89 (f90 f91 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f87 f88 ?v0))) (= (f8 ?v_0 (f8 (f87 f88 ?v1) ?v2)) (f8 (f87 f88 (f8 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S57) (?v1 S57) (?v2 S57)) (let ((?v_0 (f90 f91 ?v0))) (= (f89 ?v_0 (f89 (f90 f91 ?v1) ?v2)) (f89 (f90 f91 (f89 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f87 f88 ?v0)) (?v_0 (f87 f88 ?v1))) (= (f8 ?v_1 (f8 ?v_0 ?v2)) (f8 ?v_0 (f8 ?v_1 ?v2))))))
(assert (forall ((?v0 S57) (?v1 S57) (?v2 S57)) (let ((?v_1 (f90 f91 ?v0)) (?v_0 (f90 f91 ?v1))) (= (f89 ?v_1 (f89 ?v_0 ?v2)) (f89 ?v_0 (f89 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f8 (f87 f88 ?v0) ?v1) (f8 (f87 f88 ?v1) ?v0))))
(assert (forall ((?v0 S57) (?v1 S57)) (= (f89 (f90 f91 ?v0) ?v1) (f89 (f90 f91 ?v1) ?v0))))
(assert (forall ((?v0 S6)) (= (f8 (f87 f88 f61) ?v0) ?v0)))
(assert (forall ((?v0 S57)) (= (f89 (f90 f91 f92) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f8 (f87 f88 f61) ?v0) ?v0)))
(assert (forall ((?v0 S57)) (= (f89 (f90 f91 f92) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f8 (f87 f88 f61) ?v0) ?v0)))
(assert (forall ((?v0 S57)) (= (f89 (f90 f91 f92) ?v0) ?v0)))
(assert (forall ((?v0 S57)) (= (= f92 (f89 (f90 f91 ?v0) ?v0)) (= ?v0 f92))))
(assert (forall ((?v0 S6)) (= (f8 (f87 f88 ?v0) f61) ?v0)))
(assert (forall ((?v0 S57)) (= (f89 (f90 f91 ?v0) f92) ?v0)))
(assert (forall ((?v0 S6)) (= (f8 (f87 f88 ?v0) f61) ?v0)))
(assert (forall ((?v0 S57)) (= (f89 (f90 f91 ?v0) f92) ?v0)))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f83 f93 (f46 (f47 f48 ?v0) ?v1)) (f8 (f87 f88 (f8 (f87 f88 (f83 f93 ?v0)) (f83 f93 ?v1))) (f8 f9 f61)))))
(assert (forall ((?v0 S36) (?v1 S33) (?v2 S9)) (= (f83 f93 (f46 (f55 (f56 f57 ?v0) ?v1) ?v2)) (f8 (f87 f88 (f83 f93 ?v2)) (f8 f9 f61)))))
(assert (forall ((?v0 S46)) (= (f83 f93 (f72 f73 ?v0)) f61)))
(assert (forall ((?v0 S32) (?v1 S33)) (= (f83 f93 (f52 (f53 f54 ?v0) ?v1)) f61)))
(assert (= (f83 f93 f44) f61))
(assert (forall ((?v0 S3) (?v1 S9)) (= (f83 f93 (f46 (f58 f59 ?v0) ?v1)) (f8 (f87 f88 (f83 f93 ?v1)) (f8 f9 f61)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9)) (= (f83 f93 (f46 (f47 (f49 f50 ?v0) ?v1) ?v2)) (f8 (f87 f88 (f8 (f87 f88 (f83 f93 ?v1)) (f83 f93 ?v2))) (f8 f9 f61)))))
(assert (forall ((?v0 S6)) (= (f8 f94 (f8 f9 ?v0)) (f8 (f87 f88 (f8 f94 ?v0)) (f8 f9 f61)))))
(assert (forall ((?v0 S6)) (= (f8 f95 (f8 f9 ?v0)) (f8 (f87 f88 (f8 f95 ?v0)) (f8 f9 f61)))))
(assert (= (f8 f95 f61) f61))
(assert (forall ((?v0 S6)) (= (f8 f95 ?v0) ?v0)))
(assert (= (f8 f94 f61) f61))
(assert (= (f96 f97 f2) f61))
(assert (= (f96 f97 f1) f61))
(assert (forall ((?v0 S32) (?v1 S46) (?v2 S33)) (=> (= (f51 (f52 (f98 (f99 f100 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f51 (f72 f73 ?v1)) f1) false) false))))
(assert (forall ((?v0 S46)) (=> (not (= (f81 f82 ?v0) f101)) (= (f51 (f72 f73 ?v0)) f1))))
(assert (forall ((?v0 S32) (?v1 S46) (?v2 S33) (?v3 S46)) (not (= (f52 (f98 (f99 f100 ?v0) ?v1) ?v2) (f72 f73 ?v3)))))
(assert (forall ((?v0 S46) (?v1 S32) (?v2 S46) (?v3 S33)) (not (= (f72 f73 ?v0) (f52 (f98 (f99 f100 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S32) (?v1 S46) (?v2 S33) (?v3 S3) (?v4 S9)) (not (= (f52 (f98 (f99 f100 ?v0) ?v1) ?v2) (f46 (f58 f59 ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S32) (?v3 S46) (?v4 S33)) (not (= (f46 (f58 f59 ?v0) ?v1) (f52 (f98 (f99 f100 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S32) (?v1 S46) (?v2 S33) (?v3 S3) (?v4 S9) (?v5 S9)) (not (= (f52 (f98 (f99 f100 ?v0) ?v1) ?v2) (f46 (f47 (f49 f50 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S9) (?v3 S32) (?v4 S46) (?v5 S33)) (not (= (f46 (f47 (f49 f50 ?v0) ?v1) ?v2) (f52 (f98 (f99 f100 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S36) (?v1 S33) (?v2 S9) (?v3 S32) (?v4 S46) (?v5 S33)) (not (= (f46 (f55 (f56 f57 ?v0) ?v1) ?v2) (f52 (f98 (f99 f100 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S32) (?v1 S46) (?v2 S33) (?v3 S36) (?v4 S33) (?v5 S9)) (not (= (f52 (f98 (f99 f100 ?v0) ?v1) ?v2) (f46 (f55 (f56 f57 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S32) (?v1 S46) (?v2 S33) (?v3 S32) (?v4 S33)) (not (= (f52 (f98 (f99 f100 ?v0) ?v1) ?v2) (f52 (f53 f54 ?v3) ?v4)))))
(assert (forall ((?v0 S32) (?v1 S33) (?v2 S32) (?v3 S46) (?v4 S33)) (not (= (f52 (f53 f54 ?v0) ?v1) (f52 (f98 (f99 f100 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S32) (?v3 S46) (?v4 S33)) (not (= (f46 (f47 f48 ?v0) ?v1) (f52 (f98 (f99 f100 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S32) (?v1 S46) (?v2 S33) (?v3 S9) (?v4 S9)) (not (= (f52 (f98 (f99 f100 ?v0) ?v1) ?v2) (f46 (f47 f48 ?v3) ?v4)))))
(assert (forall ((?v0 S32) (?v1 S46) (?v2 S33)) (not (= f44 (f52 (f98 (f99 f100 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S32) (?v1 S46) (?v2 S33)) (not (= (f52 (f98 (f99 f100 ?v0) ?v1) ?v2) f44))))
(assert (forall ((?v0 S32) (?v1 S46) (?v2 S33) (?v3 S32) (?v4 S46) (?v5 S33)) (= (= (f52 (f98 (f99 f100 ?v0) ?v1) ?v2) (f52 (f98 (f99 f100 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S32) (?v1 S46) (?v2 S33)) (= (f83 f84 (f52 (f98 (f99 f100 ?v0) ?v1) ?v2)) f61)))
(assert (forall ((?v0 S32) (?v1 S46) (?v2 S33)) (= (f83 f93 (f52 (f98 (f99 f100 ?v0) ?v1) ?v2)) f61)))
(assert (forall ((?v0 S46) (?v1 S32) (?v2 S33)) (=> (= (f51 (f72 f73 ?v0)) f1) (= (f51 (f52 (f98 (f99 f100 ?v1) ?v0) ?v2)) f1))))
(assert (forall ((?v0 S54)) (= (f104 (f102 f103 ?v0) f101) f61)))
(assert (= (f104 f105 f101) f61))
(assert (forall ((?v0 S9)) (= (= (f51 ?v0) f1) (or (= ?v0 f44) (or (exists ((?v1 S32) (?v2 S33)) (= ?v0 (f52 (f53 f54 ?v1) ?v2))) (or (exists ((?v1 S9) (?v2 S36) (?v3 S33)) (and (= ?v0 (f46 (f55 (f56 f57 ?v2) ?v3) ?v1)) (= (f51 ?v1) f1))) (or (exists ((?v1 S9) (?v2 S9)) (and (= ?v0 (f46 (f47 f48 ?v1) ?v2)) (and (= (f51 ?v1) f1) (= (f51 ?v2) f1)))) (or (exists ((?v1 S9) (?v2 S9) (?v3 S3)) (and (= ?v0 (f46 (f47 (f49 f50 ?v3) ?v1) ?v2)) (and (= (f51 ?v1) f1) (= (f51 ?v2) f1)))) (or (exists ((?v1 S9) (?v2 S3)) (and (= ?v0 (f46 (f58 f59 ?v2) ?v1)) (= (f51 ?v1) f1))) (or (exists ((?v1 S46)) (and (= ?v0 (f72 f73 ?v1)) (not (= (f81 f82 ?v1) f101)))) (exists ((?v1 S46) (?v2 S32) (?v3 S33)) (and (= ?v0 (f52 (f98 (f99 f100 ?v2) ?v1) ?v3)) (= (f51 (f72 f73 ?v1)) f1)))))))))))))
(assert (forall ((?v0 S9)) (=> (=> (= ?v0 f44) false) (=> (forall ((?v1 S32) (?v2 S33)) (=> (= ?v0 (f52 (f53 f54 ?v1) ?v2)) false)) (=> (forall ((?v1 S36) (?v2 S33) (?v3 S9)) (=> (= ?v0 (f46 (f55 (f56 f57 ?v1) ?v2) ?v3)) false)) (=> (forall ((?v1 S9) (?v2 S9)) (=> (= ?v0 (f46 (f47 f48 ?v1) ?v2)) false)) (=> (forall ((?v1 S3) (?v2 S9) (?v3 S9)) (=> (= ?v0 (f46 (f47 (f49 f50 ?v1) ?v2) ?v3)) false)) (=> (forall ((?v1 S3) (?v2 S9)) (=> (= ?v0 (f46 (f58 f59 ?v1) ?v2)) false)) (=> (forall ((?v1 S46)) (=> (= ?v0 (f72 f73 ?v1)) false)) (=> (forall ((?v1 S32) (?v2 S46) (?v3 S33)) (=> (= ?v0 (f52 (f98 (f99 f100 ?v1) ?v2) ?v3)) false)) false))))))))))
(assert (forall ((?v0 S54) (?v1 S9)) (= (f104 (f102 f103 ?v0) (f106 f107 ?v1)) (f8 (f87 f88 (f83 ?v0 ?v1)) (f8 f9 f61)))))
(assert (forall ((?v0 S9)) (= (f104 f105 (f106 f107 ?v0)) f61)))
(assert (forall ((?v0 S46)) (=> (= (f51 (f72 f73 ?v0)) f1) (=> (forall ((?v1 S9)) (=> (= (f81 f82 ?v0) (f106 f107 ?v1)) false)) false))))
(assert (forall ((?v0 S46) (?v1 S9)) (=> (= f108 f1) (=> (= (f81 f82 ?v0) (f106 f107 ?v1)) (= (f51 ?v1) f1)))))
(assert (forall ((?v0 S9)) (= (f79 f80 (f106 f107 ?v0)) ?v0)))
(assert (forall ((?v0 S52)) (= (not (= ?v0 f101)) (exists ((?v1 S9)) (= ?v0 (f106 f107 ?v1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f106 f107 ?v0) (f106 f107 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9)) (not (= f101 (f106 f107 ?v0)))))
(check-sat)
(exit)