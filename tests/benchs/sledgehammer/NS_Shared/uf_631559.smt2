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
(declare-fun f32 (S10 S23) S2)
(declare-fun f33 () S3)
(declare-fun f34 () S12)
(declare-fun f35 (S25 S12) S11)
(declare-fun f36 () S25)
(declare-fun f37 () S16)
(declare-fun f38 (S26 S8) S8)
(declare-fun f39 () S26)
(declare-fun f40 (S28 S27) S26)
(declare-fun f41 () S28)
(declare-fun f42 (S29 S8) S1)
(declare-fun f43 (S30 S8) S29)
(declare-fun f44 () S30)
(declare-fun f45 (S32 S12) S8)
(declare-fun f46 (S33 S31) S32)
(declare-fun f47 () S33)
(declare-fun f48 (S35 S3) S8)
(declare-fun f49 (S36 S34) S35)
(declare-fun f50 () S36)
(declare-fun f51 (S38 S8) S12)
(declare-fun f52 (S39 S37) S38)
(declare-fun f53 () S39)
(declare-fun f54 (S41 S40) S6)
(declare-fun f55 () S41)
(declare-fun f56 (S43 S12) S3)
(declare-fun f57 (S44 S42) S43)
(declare-fun f58 () S44)
(declare-fun f59 (S46 S45) S16)
(declare-fun f60 () S46)
(declare-fun f61 (S47 S8) S26)
(declare-fun f62 () S47)
(declare-fun f63 (S48 S3) S6)
(declare-fun f64 () S48)
(declare-fun f65 (S49 S23) S29)
(declare-fun f66 () S49)
(declare-fun f67 (S37 S23) S14)
(declare-fun f68 (S34 S2) S23)
(declare-fun f69 (S31 S14) S23)
(declare-fun f70 (S45 S14) S14)
(declare-fun f71 (S42 S14) S2)
(declare-fun f72 (S40 S2) S2)
(declare-fun f73 (S27 S23) S23)
(assert (not (= f1 f2)))
(assert (not (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f14 f15 (f16 f17 ?v0))) (?v_1 (f25 (f26 f27 f28) f29))) (=> (= (f3 (f4 f5 ?v1) (f6 f7 (f8 (f9 f10 f11) f12))) f1) (= (= (f13 ?v_0 (f18 f19 (f18 (f20 f21 (f22 (f23 f24 f17) ?v1)) ?v_1))) f1) (or (= (f3 (f30 f31 ?v0) ?v1) f1) (= (f13 ?v_0 (f18 f19 ?v_1)) f1))))))))
(assert (forall ((?v0 S23) (?v1 S21)) (= (f13 (f14 f15 (f16 f17 (f32 f11 ?v0))) (f25 (f26 f27 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S12)) (let ((?v_0 (f14 f15 (f16 f17 ?v0)))) (let ((?v_1 (= (f13 ?v_0 (f18 f19 (f18 (f20 f21 (f22 (f23 f24 f17) ?v1)) ?v2))) f1)) (?v_2 (or (= (f3 (f30 f31 ?v0) ?v1) f1) (= (f13 ?v_0 (f18 f19 ?v2)) f1)))) (=> (=> ?v_1 ?v_2) (= ?v_1 ?v_2))))))
(assert (forall ((?v0 S15) (?v1 S3)) (let ((?v_0 (f23 f24 ?v0))) (=> (= (f22 ?v_0 f33) f34) (= (f13 (f35 f36 (f18 f37 (f22 ?v_0 ?v1))) (f22 ?v_0 (f6 f7 ?v1))) f1)))))
(assert (forall ((?v0 S10) (?v1 S8)) (let ((?v_0 (f9 f10 ?v0))) (=> (= (f8 ?v_0 f12) f33) (= (f3 (f4 f5 (f6 f7 (f8 ?v_0 ?v1))) (f8 ?v_0 (f38 f39 ?v1))) f1)))))
(assert (forall ((?v0 S27) (?v1 S8)) (let ((?v_0 (f40 f41 ?v0))) (=> (= (f38 ?v_0 f12) f12) (= (f42 (f43 f44 (f38 f39 (f38 ?v_0 ?v1))) (f38 ?v_0 (f38 f39 ?v1))) f1)))))
(assert (forall ((?v0 S31) (?v1 S12)) (let ((?v_0 (f46 f47 ?v0))) (=> (= (f45 ?v_0 f34) f12) (= (f42 (f43 f44 (f38 f39 (f45 ?v_0 ?v1))) (f45 ?v_0 (f18 f37 ?v1))) f1)))))
(assert (forall ((?v0 S34) (?v1 S3)) (let ((?v_0 (f49 f50 ?v0))) (=> (= (f48 ?v_0 f33) f12) (= (f42 (f43 f44 (f38 f39 (f48 ?v_0 ?v1))) (f48 ?v_0 (f6 f7 ?v1))) f1)))))
(assert (forall ((?v0 S37) (?v1 S8)) (let ((?v_0 (f52 f53 ?v0))) (=> (= (f51 ?v_0 f12) f34) (= (f13 (f35 f36 (f18 f37 (f51 ?v_0 ?v1))) (f51 ?v_0 (f38 f39 ?v1))) f1)))))
(assert (forall ((?v0 S40) (?v1 S3)) (let ((?v_0 (f54 f55 ?v0))) (=> (= (f6 ?v_0 f33) f33) (= (f3 (f4 f5 (f6 f7 (f6 ?v_0 ?v1))) (f6 ?v_0 (f6 f7 ?v1))) f1)))))
(assert (forall ((?v0 S42) (?v1 S12)) (let ((?v_0 (f57 f58 ?v0))) (=> (= (f56 ?v_0 f34) f33) (= (f3 (f4 f5 (f6 f7 (f56 ?v_0 ?v1))) (f56 ?v_0 (f18 f37 ?v1))) f1)))))
(assert (forall ((?v0 S45) (?v1 S12)) (let ((?v_0 (f59 f60 ?v0))) (=> (= (f18 ?v_0 f34) f34) (= (f13 (f35 f36 (f18 f37 (f18 ?v_0 ?v1))) (f18 ?v_0 (f18 f37 ?v1))) f1)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f22 (f23 f24 f17) ?v0))) (= (f18 f19 ?v_0) ?v_0))))
(assert (forall ((?v0 S14) (?v1 S21) (?v2 S1)) (let ((?v_0 (=> (not (= (f13 (f14 f15 ?v0) (f18 f19 (f25 (f26 f27 f28) ?v1))) f1)) (= ?v2 f1)))) (=> ?v_0 ?v_0))))
(assert (forall ((?v0 S8)) (= (f38 (f61 f62 ?v0) (f38 f39 ?v0)) f12)))
(assert (forall ((?v0 S3)) (= (f6 (f63 f64 ?v0) (f6 f7 ?v0)) f33)))
(assert (forall ((?v0 S12)) (= (f18 (f20 f21 ?v0) (f18 f37 ?v0)) f34)))
(assert (forall ((?v0 S8)) (= (f38 (f61 f62 (f38 f39 ?v0)) ?v0) f12)))
(assert (forall ((?v0 S3)) (= (f6 (f63 f64 (f6 f7 ?v0)) ?v0) f33)))
(assert (forall ((?v0 S12)) (= (f18 (f20 f21 (f18 f37 ?v0)) ?v0) f34)))
(assert (forall ((?v0 S8)) (= (f38 (f61 f62 ?v0) (f38 f39 ?v0)) f12)))
(assert (forall ((?v0 S3)) (= (f6 (f63 f64 ?v0) (f6 f7 ?v0)) f33)))
(assert (forall ((?v0 S12)) (= (f18 (f20 f21 ?v0) (f18 f37 ?v0)) f34)))
(assert (forall ((?v0 S8)) (= (f38 (f61 f62 (f38 f39 ?v0)) ?v0) f12)))
(assert (forall ((?v0 S3)) (= (f6 (f63 f64 (f6 f7 ?v0)) ?v0) f33)))
(assert (forall ((?v0 S12)) (= (f18 (f20 f21 (f18 f37 ?v0)) ?v0) f34)))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f30 f31 ?v0))) (=> (=> (= (f3 ?v_0 ?v1) f1) false) (= (f3 ?v_0 (f6 f7 ?v1)) f1)))))
(assert (forall ((?v0 S14) (?v1 S12)) (let ((?v_0 (f14 f15 ?v0))) (=> (=> (= (f13 ?v_0 ?v1) f1) false) (= (f13 ?v_0 (f18 f37 ?v1)) f1)))))
(assert (forall ((?v0 S23) (?v1 S8)) (let ((?v_0 (f65 f66 ?v0))) (=> (=> (= (f42 ?v_0 ?v1) f1) false) (= (f42 ?v_0 (f38 f39 ?v1)) f1)))))
(assert (forall ((?v0 S14) (?v1 S12)) (let ((?v_0 (f14 f15 ?v0))) (=> (= (f13 ?v_0 ?v1) f1) (= (f13 ?v_0 (f18 f19 ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f30 f31 ?v0))) (=> (= (f3 ?v_0 (f6 (f63 f64 ?v1) ?v2)) f1) (=> (=> (= (f3 ?v_0 ?v1) f1) false) (=> (=> (= (f3 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S14) (?v1 S12) (?v2 S12)) (let ((?v_0 (f14 f15 ?v0))) (=> (= (f13 ?v_0 (f18 (f20 f21 ?v1) ?v2)) f1) (=> (=> (= (f13 ?v_0 ?v1) f1) false) (=> (=> (= (f13 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S23) (?v1 S8) (?v2 S8)) (let ((?v_0 (f65 f66 ?v0))) (=> (= (f42 ?v_0 (f38 (f61 f62 ?v1) ?v2)) f1) (=> (=> (= (f42 ?v_0 ?v1) f1) false) (=> (=> (= (f42 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f13 (f35 f36 ?v0) ?v1) f1) (=> (= (f13 (f35 f36 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f42 (f43 f44 ?v0) ?v1) f1) (=> (= (f42 (f43 f44 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f30 f31 ?v2))) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S14)) (let ((?v_0 (f14 f15 ?v2))) (=> (= (f13 (f35 f36 ?v0) ?v1) f1) (=> (= (f13 ?v_0 ?v0) f1) (= (f13 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S23)) (let ((?v_0 (f65 f66 ?v2))) (=> (= (f42 (f43 f44 ?v0) ?v1) f1) (=> (= (f42 ?v_0 ?v0) f1) (= (f42 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S14) (?v1 S15) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f16 ?v1 ?v2)) (=> (= (f3 (f30 f31 ?v2) ?v3) f1) (= (f13 (f14 f15 ?v0) (f22 (f23 f24 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S10) (?v2 S23) (?v3 S8)) (=> (= ?v0 (f32 ?v1 ?v2)) (=> (= (f42 (f65 f66 ?v2) ?v3) f1) (= (f3 (f30 f31 ?v0) (f8 (f9 f10 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S14) (?v1 S37) (?v2 S23) (?v3 S8)) (=> (= ?v0 (f67 ?v1 ?v2)) (=> (= (f42 (f65 f66 ?v2) ?v3) f1) (= (f13 (f14 f15 ?v0) (f51 (f52 f53 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S23) (?v1 S34) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f68 ?v1 ?v2)) (=> (= (f3 (f30 f31 ?v2) ?v3) f1) (= (f42 (f65 f66 ?v0) (f48 (f49 f50 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S23) (?v1 S31) (?v2 S14) (?v3 S12)) (=> (= ?v0 (f69 ?v1 ?v2)) (=> (= (f13 (f14 f15 ?v2) ?v3) f1) (= (f42 (f65 f66 ?v0) (f45 (f46 f47 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S14) (?v1 S45) (?v2 S14) (?v3 S12)) (=> (= ?v0 (f70 ?v1 ?v2)) (=> (= (f13 (f14 f15 ?v2) ?v3) f1) (= (f13 (f14 f15 ?v0) (f18 (f59 f60 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S42) (?v2 S14) (?v3 S12)) (=> (= ?v0 (f71 ?v1 ?v2)) (=> (= (f13 (f14 f15 ?v2) ?v3) f1) (= (f3 (f30 f31 ?v0) (f56 (f57 f58 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S40) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f72 ?v1 ?v2)) (=> (= (f3 (f30 f31 ?v2) ?v3) f1) (= (f3 (f30 f31 ?v0) (f6 (f54 f55 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S23) (?v1 S27) (?v2 S23) (?v3 S8)) (=> (= ?v0 (f73 ?v1 ?v2)) (=> (= (f42 (f65 f66 ?v2) ?v3) f1) (= (f42 (f65 f66 ?v0) (f38 (f40 f41 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2)) (= (f3 (f30 f31 ?v0) f33) f1)))
(assert (forall ((?v0 S14)) (= (f13 (f14 f15 ?v0) f34) f1)))
(assert (forall ((?v0 S23)) (= (f42 (f65 f66 ?v0) f12) f1)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f30 f31 ?v0))) (=> (=> (not (= (f3 ?v_0 ?v1) f1)) (= (f3 ?v_0 ?v2) f1)) (= (f3 ?v_0 (f6 (f63 f64 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S14) (?v1 S12) (?v2 S12)) (let ((?v_0 (f14 f15 ?v0))) (=> (=> (not (= (f13 ?v_0 ?v1) f1)) (= (f13 ?v_0 ?v2) f1)) (= (f13 ?v_0 (f18 (f20 f21 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S23) (?v1 S8) (?v2 S8)) (let ((?v_0 (f65 f66 ?v0))) (=> (=> (not (= (f42 ?v_0 ?v1) f1)) (= (f42 ?v_0 ?v2) f1)) (= (f42 ?v_0 (f38 (f61 f62 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S14) (?v1 S12) (?v2 S12)) (let ((?v_0 (f14 f15 ?v0)) (?v_1 (f18 f19 ?v2))) (=> (= (f13 ?v_0 (f18 f19 ?v1)) f1) (=> (= (f13 (f35 f36 ?v1) ?v_1) f1) (= (f13 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f13 (f35 f36 ?v0) ?v1) f1) (= (f13 (f35 f36 (f18 f19 ?v0)) (f18 f19 ?v1)) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f18 f19 ?v1))) (= (= (f13 (f35 f36 (f18 f19 ?v0)) ?v_0) f1) (= (f13 (f35 f36 ?v0) ?v_0) f1)))))
(assert (forall ((?v0 S12)) (= (f13 (f35 f36 ?v0) (f18 f19 ?v0)) f1)))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (=> (= (f13 (f35 f36 (f18 f19 ?v0)) (f18 f19 ?v1)) f1) (=> (= (f13 (f35 f36 (f18 f19 ?v2)) (f18 f19 ?v3)) f1) (= (f13 (f35 f36 (f18 f19 (f18 (f20 f21 ?v0) ?v2))) (f18 f19 (f18 (f20 f21 ?v1) ?v3))) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (f13 (f35 f36 (f18 (f20 f21 (f18 f19 ?v0)) (f18 f19 ?v1))) (f18 f19 (f18 (f20 f21 ?v0) ?v1))) f1)))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f20 f21 ?v0))) (= (f18 (f20 f21 (f18 ?v_0 ?v1)) ?v2) (f18 ?v_0 (f18 (f20 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f61 f62 ?v0))) (= (f38 (f61 f62 (f38 ?v_0 ?v1)) ?v2) (f38 ?v_0 (f38 (f61 f62 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f63 f64 ?v0))) (= (f6 (f63 f64 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f63 f64 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f20 f21 ?v0))) (= (f18 (f20 f21 (f18 ?v_0 ?v1)) ?v2) (f18 ?v_0 (f18 (f20 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f61 f62 ?v0))) (= (f38 (f61 f62 (f38 ?v_0 ?v1)) ?v2) (f38 ?v_0 (f38 (f61 f62 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f63 f64 ?v0))) (= (f6 (f63 f64 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f63 f64 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f20 f21 ?v0))) (= (f18 (f20 f21 (f18 ?v_0 ?v1)) ?v2) (f18 ?v_0 (f18 (f20 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f61 f62 ?v0))) (= (f38 (f61 f62 (f38 ?v_0 ?v1)) ?v2) (f38 ?v_0 (f38 (f61 f62 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f63 f64 ?v0))) (= (f6 (f63 f64 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f63 f64 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_1 (f20 f21 ?v0)) (?v_0 (f20 f21 ?v1))) (= (f18 ?v_1 (f18 ?v_0 ?v2)) (f18 ?v_0 (f18 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f61 f62 ?v0)) (?v_0 (f61 f62 ?v1))) (= (f38 ?v_1 (f38 ?v_0 ?v2)) (f38 ?v_0 (f38 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f63 f64 ?v0)) (?v_0 (f63 f64 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_1 (f20 f21 ?v0)) (?v_0 (f20 f21 ?v1))) (= (f18 ?v_1 (f18 ?v_0 ?v2)) (f18 ?v_0 (f18 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f61 f62 ?v0)) (?v_0 (f61 f62 ?v1))) (= (f38 ?v_1 (f38 ?v_0 ?v2)) (f38 ?v_0 (f38 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f63 f64 ?v0)) (?v_0 (f63 f64 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_1 (f20 f21 ?v0)) (?v_0 (f20 f21 ?v1))) (= (f18 ?v_1 (f18 ?v_0 ?v2)) (f18 ?v_0 (f18 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f61 f62 ?v0)) (?v_0 (f61 f62 ?v1))) (= (f38 ?v_1 (f38 ?v_0 ?v2)) (f38 ?v_0 (f38 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f63 f64 ?v0)) (?v_0 (f63 f64 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f20 f21 ?v0))) (let ((?v_1 (f18 ?v_0 ?v1))) (= (f18 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f61 f62 ?v0))) (let ((?v_1 (f38 ?v_0 ?v1))) (= (f38 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f63 f64 ?v0))) (let ((?v_1 (f6 ?v_0 ?v1))) (= (f6 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f20 f21 ?v0))) (let ((?v_1 (f18 ?v_0 ?v1))) (= (f18 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f61 f62 ?v0))) (let ((?v_1 (f38 ?v_0 ?v1))) (= (f38 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f63 f64 ?v0))) (let ((?v_1 (f6 ?v_0 ?v1))) (= (f6 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f20 f21 ?v0))) (let ((?v_1 (f18 ?v_0 ?v1))) (= (f18 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f61 f62 ?v0))) (let ((?v_1 (f38 ?v_0 ?v1))) (= (f38 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f63 f64 ?v0))) (let ((?v_1 (f6 ?v_0 ?v1))) (= (f6 ?v_0 ?v_1) ?v_1)))))
(check-sat)
(exit)