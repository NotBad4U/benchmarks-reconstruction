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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S6) S4)
(declare-fun f6 (S7 S8) S5)
(declare-fun f7 (S9 S6) S7)
(declare-fun f8 () S9)
(declare-fun f9 (S10 S2) S6)
(declare-fun f10 () S10)
(declare-fun f11 (S11 S12) S8)
(declare-fun f12 () S11)
(declare-fun f13 (S2) S12)
(declare-fun f14 () S10)
(declare-fun f15 () S3)
(declare-fun f16 (S13 S2) S8)
(declare-fun f17 () S13)
(declare-fun f18 (S14 S4) S1)
(declare-fun f19 (S15 S14) S14)
(declare-fun f20 () S15)
(declare-fun f21 (S16 S14) S1)
(declare-fun f22 (S17 S4) S16)
(declare-fun f23 () S17)
(declare-fun f24 (S18 S2) S1)
(declare-fun f25 (S19 S18) S18)
(declare-fun f26 () S19)
(declare-fun f27 (S20 S18) S1)
(declare-fun f28 (S21 S2) S20)
(declare-fun f29 () S21)
(declare-fun f30 (S22 S10) S3)
(declare-fun f31 (S23 S10) S22)
(declare-fun f32 () S23)
(declare-fun f33 () S23)
(declare-fun f34 (S24 S14) S15)
(declare-fun f35 () S24)
(declare-fun f36 (S25 S18) S19)
(declare-fun f37 () S25)
(declare-fun f38 () S24)
(declare-fun f39 () S25)
(declare-fun f40 (S27 S2) S2)
(declare-fun f41 (S28 S3) S27)
(declare-fun f42 (S29 S26) S28)
(declare-fun f43 () S29)
(declare-fun f44 (S26 S4) S2)
(declare-fun f45 (S30 S4) S4)
(declare-fun f46 (S31 S26) S30)
(declare-fun f47 (S32 S3) S31)
(declare-fun f48 () S32)
(declare-fun f49 () S14)
(declare-fun f50 (S34 S33) S14)
(declare-fun f51 () S34)
(declare-fun f52 (S35 S18) S14)
(declare-fun f53 (S36 S3) S35)
(declare-fun f54 () S36)
(declare-fun f55 () S18)
(declare-fun f56 () S24)
(declare-fun f57 (S37 S14) S16)
(declare-fun f58 () S37)
(declare-fun f59 () S25)
(declare-fun f60 (S38 S14) S18)
(declare-fun f61 (S39 S26) S38)
(declare-fun f62 () S39)
(declare-fun f63 (S40 S1) S1)
(declare-fun f64 (S41 S1) S40)
(declare-fun f65 () S41)
(declare-fun f66 (S42 S33) S33)
(declare-fun f67 () S42)
(declare-fun f68 () S19)
(declare-fun f69 () S15)
(declare-fun f70 (S43 S27) S19)
(declare-fun f71 () S43)
(declare-fun f72 (S44 S30) S15)
(declare-fun f73 () S44)
(declare-fun f74 (S45 S4) S15)
(declare-fun f75 () S45)
(declare-fun f76 () S14)
(declare-fun f77 () S37)
(declare-fun f78 (S47 S46) S1)
(declare-fun f79 (S48 S33) S47)
(declare-fun f80 (S49 S46) S48)
(declare-fun f81 (S50 S8) S49)
(declare-fun f82 () S50)
(declare-fun f83 () S33)
(declare-fun f84 (S51 S46) S47)
(declare-fun f85 (S52 S8) S51)
(declare-fun f86 () S52)
(declare-fun f87 () S18)
(declare-fun f88 (S53 S2) S19)
(declare-fun f89 () S53)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 (f6 (f7 f8 (f9 f10 ?v0)) (f11 f12 (f13 ?v0))) (f9 f14 ?v0)))))
(assert (forall ((?v0 S2)) (= (f3 f15 ?v0) (f5 (f6 (f7 f8 (f9 f10 ?v0)) (f16 f17 ?v0)) (f9 f14 ?v0)))))
(assert (forall ((?v0 S14) (?v1 S4)) (= (= (f18 (f19 f20 ?v0) ?v1) f1) (= (f21 (f22 f23 ?v1) ?v0) f1))))
(assert (forall ((?v0 S18) (?v1 S2)) (= (= (f24 (f25 f26 ?v0) ?v1) f1) (= (f27 (f28 f29 ?v1) ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S2)) (= (f3 (f30 (f31 f32 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f9 ?v0 ?v2)) (f11 f12 (f13 ?v2))) (f9 ?v1 ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S2)) (= (f3 (f30 (f31 f33 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f9 ?v0 ?v2)) (f16 f17 ?v2)) (f9 ?v1 ?v2)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S4)) (let ((?v_0 (f22 f23 ?v2))) (= (= (f18 (f19 (f34 f35 ?v0) ?v1) ?v2) f1) (or (= (f21 ?v_0 ?v0) f1) (= (f21 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S2)) (let ((?v_0 (f28 f29 ?v2))) (= (= (f24 (f25 (f36 f37 ?v0) ?v1) ?v2) f1) (or (= (f27 ?v_0 ?v0) f1) (= (f27 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S4)) (= (= (f18 (f19 (f34 f38 ?v0) ?v1) ?v2) f1) (or (= (f18 ?v0 ?v2) f1) (= (f18 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S2)) (= (= (f24 (f25 (f36 f39 ?v0) ?v1) ?v2) f1) (or (= (f24 ?v0 ?v2) f1) (= (f24 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S26) (?v1 S3) (?v2 S2)) (= (f40 (f41 (f42 f43 ?v0) ?v1) ?v2) (f44 ?v0 (f3 ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S26) (?v2 S4)) (= (f45 (f46 (f47 f48 ?v0) ?v1) ?v2) (f3 ?v0 (f44 ?v1 ?v2)))))
(assert (not (forall ((?v0 S33)) (=> (forall ((?v1 S4)) (=> (= (f21 (f22 f23 ?v1) f49) f1) (= (f18 (f50 f51 ?v0) ?v1) f1))) (forall ((?v1 S4)) (=> (= (f21 (f22 f23 ?v1) (f52 (f53 f54 f15) f55)) f1) (= (f18 (f50 f51 ?v0) ?v1) f1)))))))
(assert (forall ((?v0 S33)) (=> (forall ((?v1 S4)) (=> (= (f21 (f22 f23 ?v1) (f19 (f34 f56 f49) (f52 (f53 f54 f15) f55))) f1) (= (f18 (f50 f51 ?v0) ?v1) f1))) (forall ((?v1 S4)) (=> (= (f21 (f22 f23 ?v1) (f52 (f53 f54 f4) f55)) f1) (= (f18 (f50 f51 ?v0) ?v1) f1))))))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6) (?v3 S6) (?v4 S8) (?v5 S6)) (= (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S14) (?v1 S10) (?v2 S10) (?v3 S18)) (let ((?v_0 (f52 (f53 f54 (f30 (f31 f33 ?v1) ?v2)) ?v3))) (=> (= (f21 (f57 f58 (f19 (f34 f56 ?v0) ?v_0)) (f52 (f53 f54 (f30 (f31 f32 ?v1) ?v2)) ?v3)) f1) (= (f21 (f57 f58 ?v0) ?v_0) f1)))))
(assert (forall ((?v0 S2) (?v1 S18) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (=> (= (f27 ?v_0 (f25 (f36 f59 ?v1) ?v2)) f1) (=> (=> (= (f27 ?v_0 ?v1) f1) false) (=> (=> (= (f27 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S4) (?v1 S14) (?v2 S14)) (let ((?v_0 (f22 f23 ?v0))) (=> (= (f21 ?v_0 (f19 (f34 f56 ?v1) ?v2)) f1) (=> (=> (= (f21 ?v_0 ?v1) f1) false) (=> (=> (= (f21 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S4)) (=> (= (f18 (f19 (f34 f56 ?v0) ?v1) ?v2) f1) (=> (=> (= (f18 ?v0 ?v2) f1) false) (=> (=> (= (f18 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S2)) (=> (= (f24 (f25 (f36 f59 ?v0) ?v1) ?v2) f1) (=> (=> (= (f24 ?v0 ?v2) f1) false) (=> (=> (= (f24 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S14) (?v1 S4) (?v2 S14)) (=> (=> (not (= (f18 ?v0 ?v1) f1)) (= (f18 ?v2 ?v1) f1)) (= (f18 (f19 (f34 f56 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S18) (?v1 S2) (?v2 S18)) (=> (=> (not (= (f24 ?v0 ?v1) f1)) (= (f24 ?v2 ?v1) f1)) (= (f24 (f25 (f36 f59 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S18) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (=> (=> (not (= (f27 ?v_0 ?v1) f1)) (= (f27 ?v_0 ?v2) f1)) (= (f27 ?v_0 (f25 (f36 f59 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S14) (?v2 S14)) (let ((?v_0 (f22 f23 ?v0))) (=> (=> (not (= (f21 ?v_0 ?v1) f1)) (= (f21 ?v_0 ?v2) f1)) (= (f21 ?v_0 (f19 (f34 f56 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S18)) (=> (= ?v0 (f3 ?v1 ?v2)) (=> (= (f27 (f28 f29 ?v2) ?v3) f1) (= (f21 (f22 f23 ?v0) (f52 (f53 f54 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S26) (?v2 S4) (?v3 S14)) (=> (= ?v0 (f44 ?v1 ?v2)) (=> (= (f21 (f22 f23 ?v2) ?v3) f1) (= (f27 (f28 f29 ?v0) (f60 (f61 f62 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S18) (?v2 S18)) (let ((?v_0 (f53 f54 ?v0))) (= (f52 ?v_0 (f25 (f36 f59 ?v1) ?v2)) (f19 (f34 f56 (f52 ?v_0 ?v1)) (f52 ?v_0 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S14) (?v2 S14)) (let ((?v_0 (f61 f62 ?v0))) (= (f60 ?v_0 (f19 (f34 f56 ?v1) ?v2)) (f25 (f36 f59 (f60 ?v_0 ?v1)) (f60 ?v_0 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S4)) (= (= (f18 (f19 (f34 f56 ?v0) ?v1) ?v2) f1) (= (f63 (f64 f65 (f18 ?v0 ?v2)) (f18 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S2)) (= (= (f24 (f25 (f36 f59 ?v0) ?v1) ?v2) f1) (= (f63 (f64 f65 (f24 ?v0 ?v2)) (f24 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S4)) (= (= (f18 (f19 (f34 f56 ?v0) ?v1) ?v2) f1) (= (f63 (f64 f65 (f18 ?v0 ?v2)) (f18 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S2)) (= (= (f24 (f25 (f36 f59 ?v0) ?v1) ?v2) f1) (= (f63 (f64 f65 (f24 ?v0 ?v2)) (f24 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S33) (?v1 S6) (?v2 S2) (?v3 S6)) (let ((?v_0 (f7 f8 ?v1))) (= (= (f18 (f50 f51 ?v0) (f5 (f6 ?v_0 (f11 f12 (f13 ?v2))) ?v3)) f1) (= (f18 (f50 f51 (f66 f67 ?v0)) (f5 (f6 ?v_0 (f16 f17 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f57 f58 ?v2))) (=> (= (f21 (f57 f58 ?v0) ?v1) f1) (=> (= (f21 ?v_0 ?v0) f1) (= (f21 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S33) (?v1 S4)) (=> (= (f18 (f50 f51 (f66 f67 ?v0)) ?v1) f1) (= (f18 (f50 f51 ?v0) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S33)) (=> (forall ((?v2 S4)) (=> (= (f21 (f22 f23 ?v2) ?v0) f1) (= (f18 (f50 f51 (f66 f67 ?v1)) ?v2) f1))) (forall ((?v2 S4)) (=> (= (f21 (f22 f23 ?v2) ?v0) f1) (= (f18 (f50 f51 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f34 f56 ?v0))) (= (f19 (f34 f56 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f34 f56 ?v1) ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f64 f65 ?v0))) (= (= (f63 (f64 f65 (f63 ?v_0 ?v1)) ?v2) f1) (= (f63 ?v_0 (f63 (f64 f65 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f36 f59 ?v0))) (= (f25 (f36 f59 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f36 f59 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f34 f56 ?v0))) (= (f19 (f34 f56 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f34 f56 ?v1) ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f64 f65 ?v0))) (= (= (f63 (f64 f65 (f63 ?v_0 ?v1)) ?v2) f1) (= (f63 ?v_0 (f63 (f64 f65 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f36 f59 ?v0))) (= (f25 (f36 f59 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f36 f59 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f34 f56 ?v0))) (= (f19 (f34 f56 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f34 f56 ?v1) ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f64 f65 ?v0))) (= (= (f63 (f64 f65 (f63 ?v_0 ?v1)) ?v2) f1) (= (f63 ?v_0 (f63 (f64 f65 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f36 f59 ?v0))) (= (f25 (f36 f59 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f36 f59 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_1 (f34 f56 ?v0)) (?v_0 (f34 f56 ?v1))) (= (f19 ?v_1 (f19 ?v_0 ?v2)) (f19 ?v_0 (f19 ?v_1 ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_1 (f64 f65 ?v0)) (?v_0 (f64 f65 ?v1))) (= (= (f63 ?v_1 (f63 ?v_0 ?v2)) f1) (= (f63 ?v_0 (f63 ?v_1 ?v2)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_1 (f36 f59 ?v0)) (?v_0 (f36 f59 ?v1))) (= (f25 ?v_1 (f25 ?v_0 ?v2)) (f25 ?v_0 (f25 ?v_1 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_1 (f34 f56 ?v0)) (?v_0 (f34 f56 ?v1))) (= (f19 ?v_1 (f19 ?v_0 ?v2)) (f19 ?v_0 (f19 ?v_1 ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_1 (f64 f65 ?v0)) (?v_0 (f64 f65 ?v1))) (= (= (f63 ?v_1 (f63 ?v_0 ?v2)) f1) (= (f63 ?v_0 (f63 ?v_1 ?v2)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_1 (f36 f59 ?v0)) (?v_0 (f36 f59 ?v1))) (= (f25 ?v_1 (f25 ?v_0 ?v2)) (f25 ?v_0 (f25 ?v_1 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_1 (f34 f56 ?v0)) (?v_0 (f34 f56 ?v1))) (= (f19 ?v_1 (f19 ?v_0 ?v2)) (f19 ?v_0 (f19 ?v_1 ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_1 (f64 f65 ?v0)) (?v_0 (f64 f65 ?v1))) (= (= (f63 ?v_1 (f63 ?v_0 ?v2)) f1) (= (f63 ?v_0 (f63 ?v_1 ?v2)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_1 (f36 f59 ?v0)) (?v_0 (f36 f59 ?v1))) (= (f25 ?v_1 (f25 ?v_0 ?v2)) (f25 ?v_0 (f25 ?v_1 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14)) (let ((?v_0 (f34 f56 ?v0))) (let ((?v_1 (f19 ?v_0 ?v1))) (= (f19 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (let ((?v_0 (f64 f65 ?v0))) (let ((?v_1 (f63 ?v_0 ?v1))) (= (= (f63 ?v_0 ?v_1) f1) (= ?v_1 f1))))))
(assert (forall ((?v0 S18) (?v1 S18)) (let ((?v_0 (f36 f59 ?v0))) (let ((?v_1 (f25 ?v_0 ?v1))) (= (f25 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (let ((?v_0 (f34 f56 ?v0))) (let ((?v_1 (f19 ?v_0 ?v1))) (= (f19 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (let ((?v_0 (f64 f65 ?v0))) (let ((?v_1 (f63 ?v_0 ?v1))) (= (= (f63 ?v_0 ?v_1) f1) (= ?v_1 f1))))))
(assert (forall ((?v0 S18) (?v1 S18)) (let ((?v_0 (f36 f59 ?v0))) (let ((?v_1 (f25 ?v_0 ?v1))) (= (f25 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (let ((?v_0 (f34 f56 ?v0))) (let ((?v_1 (f19 ?v_0 ?v1))) (= (f19 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (let ((?v_0 (f64 f65 ?v0))) (let ((?v_1 (f63 ?v_0 ?v1))) (= (= (f63 ?v_0 ?v_1) f1) (= ?v_1 f1))))))
(assert (forall ((?v0 S18) (?v1 S18)) (let ((?v_0 (f36 f59 ?v0))) (let ((?v_1 (f25 ?v_0 ?v1))) (= (f25 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f19 (f34 f56 ?v0) ?v1) (f19 (f34 f56 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f63 (f64 f65 ?v0) ?v1) f1) (= (f63 (f64 f65 ?v1) ?v0) f1))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f25 (f36 f59 ?v0) ?v1) (f25 (f36 f59 ?v1) ?v0))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f19 (f34 f56 ?v0) ?v1) (f19 (f34 f56 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f63 (f64 f65 ?v0) ?v1) f1) (= (f63 (f64 f65 ?v1) ?v0) f1))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f25 (f36 f59 ?v0) ?v1) (f25 (f36 f59 ?v1) ?v0))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f19 (f34 f56 ?v0) ?v1) (f19 (f34 f56 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f63 (f64 f65 ?v0) ?v1) f1) (= (f63 (f64 f65 ?v1) ?v0) f1))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f25 (f36 f59 ?v0) ?v1) (f25 (f36 f59 ?v1) ?v0))))
(assert (forall ((?v0 S14)) (= (f19 (f34 f56 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S1)) (= (= (f63 (f64 f65 ?v0) ?v0) f1) (= ?v0 f1))))
(assert (forall ((?v0 S18)) (= (f25 (f36 f59 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S14)) (= (f19 (f34 f56 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S1)) (= (= (f63 (f64 f65 ?v0) ?v0) f1) (= ?v0 f1))))
(assert (forall ((?v0 S18)) (= (f25 (f36 f59 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S18) (?v2 S4) (?v3 S3)) (=> (= (f27 (f28 f29 ?v0) ?v1) f1) (=> (= ?v2 (f3 ?v3 ?v0)) (= (f21 (f22 f23 ?v2) (f52 (f53 f54 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S14) (?v2 S2) (?v3 S26)) (=> (= (f21 (f22 f23 ?v0) ?v1) f1) (=> (= ?v2 (f44 ?v3 ?v0)) (= (f27 (f28 f29 ?v2) (f60 (f61 f62 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S18) (?v2 S3)) (=> (= (f27 (f28 f29 ?v0) ?v1) f1) (= (f21 (f22 f23 (f3 ?v2 ?v0)) (f52 (f53 f54 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S14) (?v2 S26)) (=> (= (f21 (f22 f23 ?v0) ?v1) f1) (= (f27 (f28 f29 (f44 ?v2 ?v0)) (f60 (f61 f62 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S18)) (= (= (f21 (f22 f23 ?v0) (f52 (f53 f54 ?v1) ?v2)) f1) (exists ((?v3 S2)) (and (= (f27 (f28 f29 ?v3) ?v2) f1) (= ?v0 (f3 ?v1 ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S26) (?v2 S14)) (= (= (f27 (f28 f29 ?v0) (f60 (f61 f62 ?v1) ?v2)) f1) (exists ((?v3 S4)) (and (= (f21 (f22 f23 ?v3) ?v2) f1) (= ?v0 (f44 ?v1 ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S18) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (=> (= (f27 ?v_0 ?v1) f1) (= (f27 ?v_0 (f25 (f36 f59 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S14) (?v2 S14)) (let ((?v_0 (f22 f23 ?v0))) (=> (= (f21 ?v_0 ?v1) f1) (= (f21 ?v_0 (f19 (f34 f56 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S18) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (=> (= (f27 ?v_0 ?v1) f1) (= (f27 ?v_0 (f25 (f36 f59 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S4) (?v1 S14) (?v2 S14)) (let ((?v_0 (f22 f23 ?v0))) (=> (= (f21 ?v_0 ?v1) f1) (= (f21 ?v_0 (f19 (f34 f56 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S14) (?v1 S4) (?v2 S14)) (=> (= (f18 ?v0 ?v1) f1) (= (f18 (f19 (f34 f56 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S18) (?v1 S2) (?v2 S18)) (=> (= (f24 ?v0 ?v1) f1) (= (f24 (f25 (f36 f59 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S4) (?v2 S14)) (=> (= (f18 ?v0 ?v1) f1) (= (f18 (f19 (f34 f56 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S18) (?v1 S2) (?v2 S18)) (=> (= (f24 ?v0 ?v1) f1) (= (f24 (f25 (f36 f59 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (= (forall ((?v3 S2)) (=> (= (f27 (f28 f29 ?v3) (f25 (f36 f59 ?v0) ?v1)) f1) (= (f24 ?v2 ?v3) f1))) (and (forall ((?v3 S2)) (=> (= (f27 (f28 f29 ?v3) ?v0) f1) (= (f24 ?v2 ?v3) f1))) (forall ((?v3 S2)) (=> (= (f27 (f28 f29 ?v3) ?v1) f1) (= (f24 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (= (forall ((?v3 S4)) (=> (= (f21 (f22 f23 ?v3) (f19 (f34 f56 ?v0) ?v1)) f1) (= (f18 ?v2 ?v3) f1))) (and (forall ((?v3 S4)) (=> (= (f21 (f22 f23 ?v3) ?v0) f1) (= (f18 ?v2 ?v3) f1))) (forall ((?v3 S4)) (=> (= (f21 (f22 f23 ?v3) ?v1) f1) (= (f18 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (= (exists ((?v3 S2)) (and (= (f27 (f28 f29 ?v3) (f25 (f36 f59 ?v0) ?v1)) f1) (= (f24 ?v2 ?v3) f1))) (or (exists ((?v3 S2)) (and (= (f27 (f28 f29 ?v3) ?v0) f1) (= (f24 ?v2 ?v3) f1))) (exists ((?v3 S2)) (and (= (f27 (f28 f29 ?v3) ?v1) f1) (= (f24 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (= (exists ((?v3 S4)) (and (= (f21 (f22 f23 ?v3) (f19 (f34 f56 ?v0) ?v1)) f1) (= (f18 ?v2 ?v3) f1))) (or (exists ((?v3 S4)) (and (= (f21 (f22 f23 ?v3) ?v0) f1) (= (f18 ?v2 ?v3) f1))) (exists ((?v3 S4)) (and (= (f21 (f22 f23 ?v3) ?v1) f1) (= (f18 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f34 f56 ?v0))) (= (f19 (f34 f56 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f34 f56 ?v1) ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f36 f59 ?v0))) (= (f25 (f36 f59 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f36 f59 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S18) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (= (= (f27 ?v_0 (f25 (f36 f59 ?v1) ?v2)) f1) (or (= (f27 ?v_0 ?v1) f1) (= (f27 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S4) (?v1 S14) (?v2 S14)) (let ((?v_0 (f22 f23 ?v0))) (= (= (f21 ?v_0 (f19 (f34 f56 ?v1) ?v2)) f1) (or (= (f21 ?v_0 ?v1) f1) (= (f21 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_1 (f34 f56 ?v0)) (?v_0 (f34 f56 ?v1))) (= (f19 ?v_1 (f19 ?v_0 ?v2)) (f19 ?v_0 (f19 ?v_1 ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_1 (f36 f59 ?v0)) (?v_0 (f36 f59 ?v1))) (= (f25 ?v_1 (f25 ?v_0 ?v2)) (f25 ?v_0 (f25 ?v_1 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14)) (let ((?v_0 (f34 f56 ?v0))) (let ((?v_1 (f19 ?v_0 ?v1))) (= (f19 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (let ((?v_0 (f36 f59 ?v0))) (let ((?v_1 (f25 ?v_0 ?v1))) (= (f25 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f19 (f34 f56 ?v0) ?v1) (f19 (f34 f56 ?v1) ?v0))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f25 (f36 f59 ?v0) ?v1) (f25 (f36 f59 ?v1) ?v0))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f25 (f36 f59 ?v0) ?v1) (f25 f68 (f25 (f36 f37 ?v0) ?v1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f19 (f34 f56 ?v0) ?v1) (f19 f69 (f19 (f34 f35 ?v0) ?v1)))))
(assert (forall ((?v0 S14)) (= (f19 (f34 f56 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S18)) (= (f25 (f36 f59 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S26) (?v1 S3) (?v2 S18)) (= (f60 (f61 f62 ?v0) (f52 (f53 f54 ?v1) ?v2)) (f25 (f70 f71 (f41 (f42 f43 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S3) (?v1 S26) (?v2 S14)) (= (f52 (f53 f54 ?v0) (f60 (f61 f62 ?v1) ?v2)) (f19 (f72 f73 (f46 (f47 f48 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S2)) (= (= (f24 (f25 (f36 f59 (f25 f26 ?v0)) (f25 f26 ?v1)) ?v2) f1) (= (f27 (f28 f29 ?v2) (f25 (f36 f59 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S4)) (= (= (f18 (f19 (f34 f56 (f19 f20 ?v0)) (f19 f20 ?v1)) ?v2) f1) (= (f21 (f22 f23 ?v2) (f19 (f34 f56 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f19 f69 (f19 (f34 f38 ?v0) ?v1)) (f19 (f34 f56 (f19 f69 ?v0)) (f19 f69 ?v1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f25 f68 (f25 (f36 f39 ?v0) ?v1)) (f25 (f36 f59 (f25 f68 ?v0)) (f25 f68 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S18)) (=> (= (f21 (f22 f23 ?v0) (f52 (f53 f54 ?v1) ?v2)) f1) (=> (forall ((?v3 S2)) (=> (= ?v0 (f3 ?v1 ?v3)) (=> (= (f27 (f28 f29 ?v3) ?v2) f1) false))) false))))
(assert (forall ((?v0 S2) (?v1 S26) (?v2 S14)) (=> (= (f27 (f28 f29 ?v0) (f60 (f61 f62 ?v1) ?v2)) f1) (=> (forall ((?v3 S4)) (=> (= ?v0 (f44 ?v1 ?v3)) (=> (= (f21 (f22 f23 ?v3) ?v2) f1) false))) false))))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S6) (?v2 S8) (?v3 S6)) (=> (= ?v0 (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S14) (?v1 S10) (?v2 S10) (?v3 S18) (?v4 S2)) (=> (= (f21 (f57 f58 (f19 (f34 f56 ?v0) (f52 (f53 f54 (f30 (f31 f33 ?v1) ?v2)) ?v3))) (f52 (f53 f54 (f30 (f31 f32 ?v1) ?v2)) ?v3)) f1) (=> (= (f27 (f28 f29 ?v4) ?v3) f1) (= (f21 (f57 f58 ?v0) (f19 (f74 f75 (f5 (f6 (f7 f8 (f9 ?v1 ?v4)) (f16 f17 ?v4)) (f9 ?v2 ?v4))) f76)) f1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f21 (f57 f77 ?v0) ?v1) f1) (forall ((?v2 S33)) (=> (forall ((?v3 S4)) (=> (= (f21 (f22 f23 ?v3) ?v0) f1) (= (f18 (f50 f51 ?v2) ?v3) f1))) (forall ((?v3 S4)) (=> (= (f21 (f22 f23 ?v3) ?v1) f1) (= (f18 (f50 f51 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S3) (?v3 S3)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S2)) (=> (= (f27 (f28 f29 ?v4) ?v1) f1) (= (f3 ?v2 ?v4) (f3 ?v3 ?v4)))) (= (f52 (f53 f54 ?v2) ?v0) (f52 (f53 f54 ?v3) ?v1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S26) (?v3 S26)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S4)) (=> (= (f21 (f22 f23 ?v4) ?v1) f1) (= (f44 ?v2 ?v4) (f44 ?v3 ?v4)))) (= (f60 (f61 f62 ?v2) ?v0) (f60 (f61 f62 ?v3) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S46) (?v2 S33) (?v3 S46)) (=> (= (f78 (f79 (f80 (f81 f82 (f11 f12 (f13 ?v0))) ?v1) ?v2) ?v3) f1) (= (f78 (f79 (f80 (f81 f82 (f16 f17 ?v0)) ?v1) (f66 f67 ?v2)) ?v3) f1))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6)) (= (f18 (f50 f51 f83) (f5 (f6 (f7 f8 ?v0) (f16 f17 ?v1)) ?v2)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f16 f17 ?v0) (f16 f17 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S46) (?v2 S46)) (=> (= (f78 (f84 (f85 f86 (f11 f12 (f13 ?v0))) ?v1) ?v2) f1) (= (f78 (f84 (f85 f86 (f16 f17 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S46) (?v2 S46)) (=> (= (f78 (f84 (f85 f86 (f16 f17 ?v0)) ?v1) ?v2) f1) (=> (=> (= (f78 (f84 (f85 f86 (f11 f12 (f13 ?v0))) ?v1) ?v2) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S46) (?v2 S33) (?v3 S46)) (=> (= (f78 (f79 (f80 (f81 f82 (f16 f17 ?v0)) ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S33)) (=> (= ?v2 (f66 f67 ?v4)) (=> (= (f78 (f79 (f80 (f81 f82 (f11 f12 (f13 ?v0))) ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S2)) (=> (= (f27 (f28 f29 ?v0) f87) f1) false)))
(assert (forall ((?v0 S4)) (=> (= (f21 (f22 f23 ?v0) f76) f1) false)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S18)) (let ((?v_0 (f28 f29 ?v0))) (=> (= (f27 ?v_0 (f25 (f88 f89 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f27 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S14)) (let ((?v_0 (f22 f23 ?v0))) (=> (= (f21 ?v_0 (f19 (f74 f75 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f21 ?v_0 ?v2) f1) false) false))))))
(check-sat)
(exit)
