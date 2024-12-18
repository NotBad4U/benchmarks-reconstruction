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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 () S2)
(declare-fun f5 (S5 S3) S3)
(declare-fun f6 (S6 S3) S5)
(declare-fun f7 () S6)
(declare-fun f8 (S7 S4) S3)
(declare-fun f9 () S7)
(declare-fun f10 () S4)
(declare-fun f11 (S8 S9) S5)
(declare-fun f12 () S8)
(declare-fun f13 () S9)
(declare-fun f14 () S3)
(declare-fun f15 (S4 S4) S1)
(declare-fun f16 (S10 S4) S4)
(declare-fun f17 (S11 S4) S10)
(declare-fun f18 () S11)
(declare-fun f19 () S4)
(declare-fun f20 (S4 S4) S1)
(declare-fun f21 () S3)
(declare-fun f22 () S4)
(declare-fun f23 () S4)
(declare-fun f24 () S11)
(declare-fun f25 (S13 S9) S9)
(declare-fun f26 (S14 S9) S13)
(declare-fun f27 () S14)
(declare-fun f28 (S16 S15) S10)
(declare-fun f29 () S16)
(declare-fun f30 (S17 S15) S15)
(declare-fun f31 (S18 S15) S17)
(declare-fun f32 () S18)
(declare-fun f33 (S21 S20) S20)
(declare-fun f34 (S22 S19) S21)
(declare-fun f35 () S22)
(declare-fun f36 (S23 S19) S19)
(declare-fun f37 (S24 S19) S23)
(declare-fun f38 () S24)
(declare-fun f39 (S25 S20) S21)
(declare-fun f40 () S25)
(declare-fun f41 (S28 S27) S27)
(declare-fun f42 (S29 S26) S28)
(declare-fun f43 () S29)
(declare-fun f44 (S30 S26) S26)
(declare-fun f45 (S31 S26) S30)
(declare-fun f46 () S31)
(declare-fun f47 (S32 S27) S28)
(declare-fun f48 () S32)
(declare-fun f49 (S33 S27) S17)
(declare-fun f50 () S33)
(declare-fun f51 (S34 S20) S13)
(declare-fun f52 () S34)
(declare-fun f53 () S10)
(declare-fun f54 () S10)
(declare-fun f55 (S35 S3) S13)
(declare-fun f56 () S35)
(declare-fun f57 () S3)
(declare-fun f58 () S3)
(declare-fun f59 () S6)
(declare-fun f60 () S9)
(declare-fun f61 (S36 S37) S37)
(declare-fun f62 () S36)
(declare-fun f63 () S37)
(declare-fun f64 (S38 S4) S17)
(declare-fun f65 () S38)
(declare-fun f66 () S15)
(declare-fun f67 (S39 S20) S23)
(declare-fun f68 () S39)
(declare-fun f69 () S20)
(declare-fun f70 () S19)
(declare-fun f71 (S40 S41) S41)
(declare-fun f72 () S40)
(declare-fun f73 () S41)
(declare-fun f74 (S42 S27) S30)
(declare-fun f75 () S42)
(declare-fun f76 () S27)
(declare-fun f77 () S26)
(declare-fun f78 (S43 S15) S28)
(declare-fun f79 () S43)
(declare-fun f80 (S37 S40) S40)
(declare-fun f81 (S44 S9) S21)
(declare-fun f82 () S44)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f8 f9 f10))) (not (not (= (f3 f4 (f5 (f6 f7 ?v_0) (f5 (f11 f12 f13) ?v_0))) (f3 f4 f14))))))
(assert (let ((?v_0 (f8 f9 f10))) (= (f15 (f3 f4 (f5 (f6 f7 ?v_0) (f5 (f11 f12 f13) ?v_0))) (f16 (f17 f18 f10) f19)) f1)))
(assert (= (f20 (f16 (f17 f18 f10) f19) (f3 f4 f14)) f1))
(assert (= (f20 (f16 (f17 f18 f10) f19) (f3 f4 f14)) f1))
(assert (let ((?v_0 (f8 f9 f10))) (= (f15 (f3 f4 (f5 (f6 f7 ?v_0) (f5 (f11 f12 f13) ?v_0))) (f16 (f17 f18 f10) f19)) f1)))
(assert (not (= f14 f21)))
(assert (let ((?v_0 (f8 f9 f10))) (= (f3 f4 (f5 (f6 f7 ?v_0) (f5 (f11 f12 f13) ?v_0))) (f3 f4 f14))))
(assert (= (f15 (f3 f4 (f5 (f11 f12 f13) (f8 f9 f10))) f19) f1))
(assert (= (f20 f22 f10) f1))
(assert (= (f20 f10 f23) f1))
(assert (forall ((?v0 S12) (?v1 S3)) (=> (= (f15 (f3 f4 ?v1) f23) f1) (= (f15 (f3 f4 (f5 (f11 f12 f13) ?v1)) f19) f1))))
(assert (= (f20 f10 (f16 (f17 f24 (f3 f4 f14)) f19)) f1))
(assert (not (= (f8 f9 f10) f21)))
(assert (= (f15 (f3 f4 (f8 f9 f10)) f23) f1))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S3)) (= (f5 (f11 f12 (f25 (f26 f27 ?v0) ?v1)) ?v2) (f5 (f6 f7 (f5 (f11 f12 ?v0) ?v2)) (f5 (f11 f12 ?v1) ?v2)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S4)) (= (f16 (f28 f29 (f30 (f31 f32 ?v0) ?v1)) ?v2) (f16 (f17 f18 (f16 (f28 f29 ?v0) ?v2)) (f16 (f28 f29 ?v1) ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S20)) (= (f33 (f34 f35 (f36 (f37 f38 ?v0) ?v1)) ?v2) (f33 (f39 f40 (f33 (f34 f35 ?v0) ?v2)) (f33 (f34 f35 ?v1) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S27)) (= (f41 (f42 f43 (f44 (f45 f46 ?v0) ?v1)) ?v2) (f41 (f47 f48 (f41 (f42 f43 ?v0) ?v2)) (f41 (f42 f43 ?v1) ?v2)))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S15)) (= (f30 (f49 f50 (f41 (f47 f48 ?v0) ?v1)) ?v2) (f30 (f31 f32 (f30 (f49 f50 ?v0) ?v2)) (f30 (f49 f50 ?v1) ?v2)))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S9)) (= (f25 (f51 f52 (f33 (f39 f40 ?v0) ?v1)) ?v2) (f25 (f26 f27 (f25 (f51 f52 ?v0) ?v2)) (f25 (f51 f52 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f8 f9 (f16 (f17 f18 ?v0) ?v1)) (f5 (f6 f7 (f8 f9 ?v0)) (f8 f9 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f16 f53 (f16 (f17 f18 ?v0) ?v1)) (f16 (f17 f18 (f16 f53 ?v0)) (f16 f53 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f16 f54 (f16 (f17 f18 ?v0) ?v1)) (f16 (f17 f18 (f16 f54 ?v0)) (f16 f54 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 f4 (f5 (f6 f7 ?v0) ?v1)) (f16 (f17 f18 (f3 f4 ?v0)) (f3 f4 ?v1)))))
(assert (forall ((?v0 S3)) (=> (not (= ?v0 f21)) (= (f5 (f11 f12 (f25 (f55 f56 f14) f13)) ?v0) f21))))
(assert (= (f5 (f11 f12 (f25 (f55 f56 f14) f13)) (f8 f9 f10)) f21))
(assert (forall ((?v0 S9)) (exists ((?v1 S3)) (forall ((?v2 S3)) (let ((?v_0 (f11 f12 ?v0))) (= (f15 (f3 f4 (f5 ?v_0 ?v1)) (f3 f4 (f5 ?v_0 ?v2))) f1))))))
(assert (not (= f57 f21)))
(assert (= (f20 f22 f19) f1))
(assert (= (f20 f22 (f16 (f17 f24 (f3 f4 f14)) f19)) f1))
(assert (exists ((?v0 S4)) (and (= (f20 f22 ?v0) f1) (forall ((?v1 S3)) (=> (= (f15 (f3 f4 ?v1) f23) f1) (= (f15 (f3 f4 (f5 (f11 f12 f13) ?v1)) ?v0) f1))))))
(assert (=> (forall ((?v0 S4)) (=> (= (f20 f22 ?v0) f1) (=> (= (f20 ?v0 (f16 (f17 f24 (f3 f4 f14)) f19)) f1) (=> (= (f20 ?v0 f23) f1) false)))) false))
(assert (exists ((?v0 S4)) (and (= (f20 f22 ?v0) f1) (and (= (f20 ?v0 (f16 (f17 f24 (f3 f4 f14)) f19)) f1) (= (f20 ?v0 f23) f1)))))
(assert (= (f8 f9 f23) f58))
(assert (= (f16 f53 f23) f23))
(assert (= (f8 f9 f22) f21))
(assert (= (f16 f53 f22) f22))
(assert (= (f8 f9 f22) f21))
(assert (= (f16 f53 f22) f22))
(assert (= (f16 f54 f23) f23))
(assert (= (f3 f4 f58) f23))
(assert (= (f16 f54 f22) f22))
(assert (= (f3 f4 f21) f22))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f8 f9 (f16 (f17 f24 ?v0) ?v1)) (f5 (f6 f59 (f8 f9 ?v0)) (f8 f9 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f16 f53 (f16 (f17 f24 ?v0) ?v1)) (f16 (f17 f24 (f16 f53 ?v0)) (f16 f53 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 f4 (f5 (f6 f59 ?v0) ?v1)) (f16 (f17 f24 (f3 f4 ?v0)) (f3 f4 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f16 f54 (f16 (f17 f24 ?v0) ?v1)) (f16 (f17 f24 (f16 f54 ?v0)) (f16 f54 ?v1)))))
(assert (= (f25 (f55 f56 f21) f60) f60))
(assert (= (f61 f62 f63) f63))
(assert (= (f30 (f64 f65 f22) f66) f66))
(assert (= (f36 (f67 f68 f69) f70) f70))
(assert (= (f71 f72 f73) f73))
(assert (= (f44 (f74 f75 f76) f77) f77))
(assert (= (f41 (f78 f79 f66) f76) f76))
(assert (= (f80 f63 f72) f72))
(assert (= (f33 (f81 f82 f60) f69) f69))
(check-sat)
(exit)
