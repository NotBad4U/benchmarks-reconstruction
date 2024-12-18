(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unsat)
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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S3) S3)
(declare-fun f4 (S5 S2) S4)
(declare-fun f5 () S5)
(declare-fun f6 () S3)
(declare-fun f7 () S2)
(declare-fun f8 (S6 S2) S7)
(declare-fun f9 (S8 S3) S6)
(declare-fun f10 () S8)
(declare-fun f11 () S7)
(declare-fun f12 (S10 S2) S2)
(declare-fun f13 (S11 S9) S10)
(declare-fun f14 () S11)
(declare-fun f15 () S9)
(declare-fun f16 (S12 S9) S7)
(declare-fun f17 (S13 S2) S12)
(declare-fun f18 () S13)
(declare-fun f19 (S16 S15) S15)
(declare-fun f20 (S17 S14) S16)
(declare-fun f21 () S17)
(declare-fun f22 () S15)
(declare-fun f23 () S14)
(declare-fun f24 (S18 S14) S7)
(declare-fun f25 (S19 S15) S18)
(declare-fun f26 () S19)
(declare-fun f27 (S22 S21) S21)
(declare-fun f28 (S23 S20) S22)
(declare-fun f29 () S23)
(declare-fun f30 () S21)
(declare-fun f31 () S20)
(declare-fun f32 (S24 S20) S7)
(declare-fun f33 (S25 S21) S24)
(declare-fun f34 () S25)
(declare-fun f35 (S26 S14) S14)
(declare-fun f36 (S27 S21) S26)
(declare-fun f37 () S27)
(declare-fun f38 (S28 S21) S7)
(declare-fun f39 (S29 S14) S28)
(declare-fun f40 () S29)
(declare-fun f41 (S30 S9) S9)
(declare-fun f42 (S31 S15) S30)
(declare-fun f43 () S31)
(declare-fun f44 (S32 S15) S7)
(declare-fun f45 (S33 S9) S32)
(declare-fun f46 () S33)
(declare-fun f47 (S34 S3) S10)
(declare-fun f48 () S34)
(declare-fun f49 (S35 S36) S36)
(declare-fun f50 (S37 S7) S35)
(declare-fun f51 () S37)
(declare-fun f52 () S36)
(declare-fun f53 (S38 S2) S30)
(declare-fun f54 () S38)
(declare-fun f55 (S39 S40) S40)
(declare-fun f56 (S41 S42) S39)
(declare-fun f57 () S41)
(declare-fun f58 () S42)
(declare-fun f59 () S40)
(declare-fun f60 (S43 S15) S26)
(declare-fun f61 () S43)
(declare-fun f62 (S44 S45) S45)
(declare-fun f63 () S44)
(declare-fun f64 () S45)
(declare-fun f65 (S46 S20) S20)
(declare-fun f66 (S47 S21) S46)
(declare-fun f67 () S47)
(declare-fun f68 (S48 S14) S22)
(declare-fun f69 () S48)
(declare-fun f70 (S49 S44) S44)
(declare-fun f71 (S50 S40) S49)
(declare-fun f72 () S50)
(declare-fun f73 (S51 S9) S16)
(declare-fun f74 () S51)
(declare-fun f75 (S52 S42) S42)
(declare-fun f76 (S53 S36) S52)
(declare-fun f77 () S53)
(declare-fun f78 (S54 S3) S4)
(declare-fun f79 () S54)
(declare-fun f80 (S55 S7) S7)
(declare-fun f81 (S56 S7) S55)
(declare-fun f82 () S56)
(declare-fun f83 (S57 S2) S10)
(declare-fun f84 () S57)
(declare-fun f85 (S58 S42) S52)
(declare-fun f86 () S58)
(declare-fun f87 (S59 S15) S16)
(declare-fun f88 () S59)
(declare-fun f89 (S60 S44) S49)
(declare-fun f90 () S60)
(declare-fun f91 (S61 S21) S22)
(declare-fun f92 () S61)
(declare-fun f93 (S62 S14) S26)
(declare-fun f94 () S62)
(declare-fun f95 (S63 S40) S39)
(declare-fun f96 () S63)
(declare-fun f97 (S64 S9) S30)
(declare-fun f98 () S64)
(declare-fun f99 (S65 S36) S35)
(declare-fun f100 () S65)
(declare-fun f101 () S6)
(declare-fun f102 (S66 S42) S7)
(declare-fun f103 () S66)
(declare-fun f104 () S32)
(declare-fun f105 (S67 S44) S7)
(declare-fun f106 () S67)
(declare-fun f107 () S28)
(declare-fun f108 () S18)
(declare-fun f109 (S68 S40) S7)
(declare-fun f110 () S68)
(declare-fun f111 () S12)
(declare-fun f112 (S69 S36) S7)
(declare-fun f113 () S69)
(declare-fun f114 () S55)
(declare-fun f115 () S54)
(declare-fun f116 () S2)
(declare-fun f117 (S70 S7) S3)
(declare-fun f118 (S71 S3) S70)
(declare-fun f119 () S71)
(declare-fun f120 (S7 S7) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f6) (or (= ?v0 f7) (not (= (f8 (f9 f10 ?v1) ?v0) f11))))))
(assert (forall ((?v0 S9) (?v1 S2)) (= (= (f12 (f13 f14 ?v0) ?v1) f7) (or (= ?v0 f15) (not (= (f16 (f17 f18 ?v1) ?v0) f11))))))
(assert (forall ((?v0 S14) (?v1 S15)) (= (= (f19 (f20 f21 ?v0) ?v1) f22) (or (= ?v0 f23) (not (= (f24 (f25 f26 ?v1) ?v0) f11))))))
(assert (forall ((?v0 S20) (?v1 S21)) (= (= (f27 (f28 f29 ?v0) ?v1) f30) (or (= ?v0 f31) (not (= (f32 (f33 f34 ?v1) ?v0) f11))))))
(assert (forall ((?v0 S21) (?v1 S14)) (= (= (f35 (f36 f37 ?v0) ?v1) f23) (or (= ?v0 f30) (not (= (f38 (f39 f40 ?v1) ?v0) f11))))))
(assert (forall ((?v0 S15) (?v1 S9)) (= (= (f41 (f42 f43 ?v0) ?v1) f15) (or (= ?v0 f22) (not (= (f44 (f45 f46 ?v1) ?v0) f11))))))
(assert (= (f12 (f47 f48 f6) f7) f7))
(assert (= (f49 (f50 f51 f11) f52) f52))
(assert (= (f41 (f53 f54 f7) f15) f15))
(assert (= (f55 (f56 f57 f58) f59) f59))
(assert (= (f35 (f60 f61 f22) f23) f23))
(assert (= (f62 f63 f64) f64))
(assert (= (f65 (f66 f67 f30) f31) f31))
(assert (= (f27 (f68 f69 f23) f30) f30))
(assert (= (f70 (f71 f72 f59) f63) f63))
(assert (= (f19 (f73 f74 f15) f22) f22))
(assert (= (f75 (f76 f77 f52) f58) f58))
(assert (forall ((?v0 S3)) (= (f3 (f78 f79 f6) ?v0) ?v0)))
(assert (forall ((?v0 S7)) (= (f80 (f81 f82 f11) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f12 (f83 f84 f7) ?v0) ?v0)))
(assert (forall ((?v0 S42)) (= (f75 (f85 f86 f58) ?v0) ?v0)))
(assert (forall ((?v0 S15)) (= (f19 (f87 f88 f22) ?v0) ?v0)))
(assert (forall ((?v0 S44)) (= (f70 (f89 f90 f63) ?v0) ?v0)))
(assert (forall ((?v0 S21)) (= (f27 (f91 f92 f30) ?v0) ?v0)))
(assert (forall ((?v0 S14)) (= (f35 (f93 f94 f23) ?v0) ?v0)))
(assert (forall ((?v0 S40)) (= (f55 (f95 f96 f59) ?v0) ?v0)))
(assert (forall ((?v0 S9)) (= (f41 (f97 f98 f15) ?v0) ?v0)))
(assert (forall ((?v0 S36)) (= (f49 (f99 f100 f52) ?v0) ?v0)))
(assert (= (f8 f101 f7) f11))
(assert (= (f102 f103 f58) f11))
(assert (= (f44 f104 f22) f11))
(assert (= (f105 f106 f63) f11))
(assert (= (f38 f107 f30) f11))
(assert (= (f24 f108 f23) f11))
(assert (= (f109 f110 f59) f11))
(assert (= (f16 f111 f15) f11))
(assert (= (f112 f113 f52) f11))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f80 (f81 f82 (f80 f114 ?v0)) ?v1) (f80 f114 (f80 (f81 f82 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f80 f114 ?v0) (f80 f114 ?v1)) (= ?v0 ?v1))))
(assert (not (forall ((?v0 S7) (?v1 S3) (?v2 S3) (?v3 S2)) (let ((?v_0 (= ?v3 f7)) (?v_2 (f8 f101 ?v3)) (?v_1 (f8 f101 f116))) (=> (not (= ?v1 f6)) (=> (not (= (f3 (f78 f79 ?v2) (f3 (f78 f115 ?v1) (f3 (f4 f5 ?v3) ?v1))) f6)) (=> (not (= ?v2 f6)) (=> (= (f80 (f81 f82 (ite ?v_0 f11 (f80 f114 ?v_2))) ?v0) ?v_1) (=> (forall ((?v4 S3)) (= (f3 (f4 f5 f116) ?v4) (f3 (f78 f115 (f117 (f118 f119 ?v4) ?v0)) (f3 (f78 f79 ?v2) (f3 (f78 f115 ?v4) (f3 (f4 f5 ?v3) ?v4)))))) (=> (not (= f116 f7)) (and (=> ?v_0 (and (= ?v0 ?v_1) (forall ((?v4 S3)) (let ((?v_3 (= ?v4 f6))) (or ?v_3 (or (and ?v_3 (= (f120 f11 ?v0) f1)) (or ?v_3 (= (f3 (f4 f5 ?v3) ?v4) f6)))))))) (=> (not ?v_0) (and (= (f80 f114 (f80 (f81 f82 ?v_2) ?v0)) ?v_1) (forall ((?v4 S3)) (let ((?v_4 (= ?v4 f6)) (?v_5 (f3 (f4 f5 ?v3) ?v4))) (or ?v_4 (or (and ?v_4 (= (f120 f11 ?v0) f1)) (or ?v_4 (= ?v_5 ?v_5)))))))))))))))))))
(check-sat)
(exit)
