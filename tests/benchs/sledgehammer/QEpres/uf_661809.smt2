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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S2 S3) S1)
(declare-fun f6 (S4 S5) S3)
(declare-fun f7 () S4)
(declare-fun f8 () S5)
(declare-fun f9 (S6 S7) S3)
(declare-fun f10 (S8 S7) S6)
(declare-fun f11 (S9) S8)
(declare-fun f12 () S9)
(declare-fun f13 () S7)
(declare-fun f14 (S2) S3)
(declare-fun f15 (S11 S10) S1)
(declare-fun f16 (S10) S11)
(declare-fun f17 (S2) S3)
(declare-fun f18 (S10) S11)
(declare-fun f19 (S12 S3) S3)
(declare-fun f20 (S2) S12)
(declare-fun f21 (S13 S11) S11)
(declare-fun f22 (S10) S13)
(declare-fun f23 (S15 S14) S1)
(declare-fun f24 (S9 S10) S15)
(declare-fun f25 (S2) S9)
(declare-fun f26 (S10 S11) S1)
(declare-fun f27 (S16 S2) S10)
(declare-fun f28 () S16)
(declare-fun f29 (S10) S13)
(declare-fun f30 () S10)
(declare-fun f31 (S17 S10) S10)
(declare-fun f32 () S17)
(declare-fun f33 () S10)
(declare-fun f34 () S11)
(declare-fun f35 (S7 S10) S9)
(declare-fun f36 (S2) S7)
(declare-fun f37 (S18 S14) S10)
(declare-fun f38 (S19 S10) S18)
(declare-fun f39 () S19)
(declare-fun f40 () S17)
(declare-fun f41 (S3) S3)
(declare-fun f42 () S16)
(declare-fun f43 () S10)
(declare-fun f44 (S11 S14) S1)
(declare-fun f45 (S20 S14) S11)
(declare-fun f46 () S20)
(declare-fun f47 (S3 S5) S1)
(declare-fun f48 () S17)
(declare-fun f49 (S21 S14) S14)
(declare-fun f50 (S22 S10) S21)
(declare-fun f51 (S23 S17) S22)
(declare-fun f52 () S23)
(declare-fun f53 (S11 S14) S1)
(declare-fun f54 (S3 S5) S1)
(declare-fun f55 (S24 S14) S2)
(declare-fun f56 (S25 S10) S24)
(declare-fun f57 () S25)
(declare-fun f58 (S26 S10) S25)
(declare-fun f59 () S26)
(declare-fun f60 () S26)
(declare-fun f61 (S11 S14) S1)
(declare-fun f62 (S3 S5) S1)
(declare-fun f63 () S20)
(declare-fun f64 () S4)
(declare-fun f65 (S27 S19) S18)
(declare-fun f66 (S28 S10) S27)
(declare-fun f67 () S28)
(declare-fun f68 (S2) S12)
(declare-fun f69 () S3)
(declare-fun f70 (S11) S11)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (and (= (f5 ?v0 (f6 f7 f8)) f1) (= (f3 (f9 (f10 (f11 f12) f13) f13) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f14 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f15 (f16 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f17 ?v0) ?v1) f1) (= ?v1 ?v0))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f15 (f18 ?v0) ?v1) f1) (= ?v1 ?v0))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f19 (f20 ?v0) ?v1) ?v2) f1) (and (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S11) (?v2 S10)) (= (= (f15 (f21 (f22 ?v0) ?v1) ?v2) f1) (and (= ?v0 ?v2) (= (f15 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S10) (?v2 S14)) (= (= (f23 (f24 (f25 ?v0) ?v1) ?v2) f1) (= (f26 (f27 f28 ?v0) (f21 (f29 f30) (f21 (f29 (f31 f32 f33)) f34))) f1))))
(assert (forall ((?v0 S2) (?v1 S10) (?v2 S10) (?v3 S14)) (= (= (f23 (f24 (f35 (f36 ?v0) ?v1) ?v2) ?v3) f1) (= (f27 f28 ?v0) f30))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S14)) (= (= (f23 (f24 (f35 f13 ?v0) ?v1) ?v2) f1) true)))
(assert (forall ((?v0 S10) (?v1 S14)) (= (f37 (f38 f39 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S10) (?v1 S14)) (= (= (f23 (f24 f12 ?v0) ?v1) f1) false)))
(assert (forall ((?v0 S10)) (= (f31 f40 ?v0) ?v0)))
(assert (not (forall ((?v0 S2)) (=> (= (f5 ?v0 (f41 f4)) f1) (= (f27 f28 ?v0) f30)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f36 ?v0))) (=> (= (f5 ?v0 (f6 f7 f8)) f1) (= (f3 (f9 (f10 (f11 (f25 ?v0)) ?v_0) ?v_0) ?v0) f1)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f36 ?v0))) (=> (= (f5 ?v0 (f6 f7 f8)) f1) (= (f3 (f9 (f10 (f11 (f25 ?v0)) ?v_0) ?v_0) ?v0) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 (f6 f7 f8)) f1) (not (= (f27 f42 ?v0) f43)))))
(assert (forall ((?v0 S10)) (= (= f30 ?v0) (= ?v0 f30))))
(assert (forall ((?v0 S11) (?v1 S14)) (= (= (f44 ?v0 ?v1) f1) (exists ((?v2 S10)) (and (and (= (f26 ?v2 (f45 f46 ?v1)) f1) (= (f15 ?v0 ?v2) f1)) (forall ((?v3 S10)) (=> (and (= (f26 ?v3 (f45 f46 ?v1)) f1) (= (f15 ?v0 ?v3) f1)) (= ?v3 ?v2))))))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f47 ?v0 ?v1) f1) (exists ((?v2 S2)) (and (and (= (f5 ?v2 (f6 f7 ?v1)) f1) (= (f3 ?v0 ?v2) f1)) (forall ((?v3 S2)) (=> (and (= (f5 ?v3 (f6 f7 ?v1)) f1) (= (f3 ?v0 ?v3) f1)) (= ?v3 ?v2))))))))
(assert (= (f31 f48 f30) f30))
(assert (forall ((?v0 S10) (?v1 S14)) (=> (= (f26 ?v0 (f45 f46 ?v1)) f1) (= (f49 (f50 (f51 f52 f40) ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S11) (?v1 S14)) (= (= (f53 ?v0 ?v1) f1) (exists ((?v2 S10)) (and (= (f26 ?v2 (f45 f46 ?v1)) f1) (= (f15 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f54 ?v0 ?v1) f1) (exists ((?v2 S2)) (and (= (f5 ?v2 (f6 f7 ?v1)) f1) (= (f3 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S9) (?v1 S7) (?v2 S7) (?v3 S10) (?v4 S14)) (= (= (f3 (f9 (f10 (f11 ?v0) ?v1) ?v2) (f55 (f56 f57 ?v3) ?v4)) f1) (= (f23 (f24 ?v0 ?v3) ?v4) f1))))
(assert (forall ((?v0 S9) (?v1 S7) (?v2 S7) (?v3 S10) (?v4 S10) (?v5 S14)) (= (= (f3 (f9 (f10 (f11 ?v0) ?v1) ?v2) (f55 (f56 (f58 f59 ?v3) ?v4) ?v5)) f1) (= (f23 (f24 (f35 ?v2 ?v3) ?v4) ?v5) f1))))
(assert (forall ((?v0 S9) (?v1 S7) (?v2 S7) (?v3 S10) (?v4 S10) (?v5 S14)) (= (= (f3 (f9 (f10 (f11 ?v0) ?v1) ?v2) (f55 (f56 (f58 f60 ?v3) ?v4) ?v5)) f1) (= (f23 (f24 (f35 ?v1 ?v3) ?v4) ?v5) f1))))
(assert (forall ((?v0 S11) (?v1 S14)) (= (= (f61 ?v0 ?v1) f1) (forall ((?v2 S10)) (=> (= (f26 ?v2 (f45 f46 ?v1)) f1) (= (f15 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f62 ?v0 ?v1) f1) (forall ((?v2 S2)) (=> (= (f5 ?v2 (f6 f7 ?v1)) f1) (= (f3 ?v0 ?v2) f1))))))
(assert (= f63 f46))
(assert (= f64 f7))
(assert (forall ((?v0 S11) (?v1 S14)) (= (= (f44 ?v0 ?v1) f1) (exists ((?v2 S10)) (and (and (= (f26 ?v2 (f45 f46 ?v1)) f1) (= (f15 ?v0 ?v2) f1)) (forall ((?v3 S10)) (=> (and (= (f26 ?v3 (f45 f46 ?v1)) f1) (= (f15 ?v0 ?v3) f1)) (= ?v3 ?v2))))))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f47 ?v0 ?v1) f1) (exists ((?v2 S2)) (and (and (= (f5 ?v2 (f6 f7 ?v1)) f1) (= (f3 ?v0 ?v2) f1)) (forall ((?v3 S2)) (=> (and (= (f5 ?v3 (f6 f7 ?v1)) f1) (= (f3 ?v0 ?v3) f1)) (= ?v3 ?v2))))))))
(assert (forall ((?v0 S10) (?v1 S14) (?v2 S10) (?v3 S10) (?v4 S14)) (not (= (f55 (f56 f57 ?v0) ?v1) (f55 (f56 (f58 f60 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S10) (?v1 S14) (?v2 S10) (?v3 S10) (?v4 S14)) (not (= (f55 (f56 f57 ?v0) ?v1) (f55 (f56 (f58 f59 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S14) (?v3 S10) (?v4 S14)) (not (= (f55 (f56 (f58 f60 ?v0) ?v1) ?v2) (f55 (f56 f57 ?v3) ?v4)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S14) (?v3 S10) (?v4 S14)) (not (= (f55 (f56 (f58 f59 ?v0) ?v1) ?v2) (f55 (f56 f57 ?v3) ?v4)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S14) (?v3 S10) (?v4 S10) (?v5 S14)) (not (= (f55 (f56 (f58 f60 ?v0) ?v1) ?v2) (f55 (f56 (f58 f59 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S14) (?v3 S10) (?v4 S10) (?v5 S14)) (not (= (f55 (f56 (f58 f59 ?v0) ?v1) ?v2) (f55 (f56 (f58 f60 ?v3) ?v4) ?v5)))))
(assert (= (f31 f48 f43) f43))
(assert (forall ((?v0 S10)) (= (f31 f32 ?v0) ?v0)))
(assert (forall ((?v0 S10)) (= (f31 f32 ?v0) (f31 f48 ?v0))))
(assert (forall ((?v0 S10)) (= (f31 f32 ?v0) (f31 f48 ?v0))))
(assert (let ((?v_0 (f31 f32 f33))) (= (f31 f48 ?v_0) ?v_0)))
(assert (forall ((?v0 S10)) (let ((?v_0 (f31 f32 ?v0))) (= (f31 f48 ?v_0) ?v_0))))
(assert (forall ((?v0 S10) (?v1 S14)) (= (f27 f42 (f55 (f56 f57 ?v0) ?v1)) f30)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S14)) (= (f27 f42 (f55 (f56 (f58 f60 ?v0) ?v1) ?v2)) ?v0)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S14)) (= (f27 f42 (f55 (f56 (f58 f59 ?v0) ?v1) ?v2)) ?v0)))
(assert (= (= f33 f33) true))
(assert (forall ((?v0 S10)) (= (= f43 ?v0) (= ?v0 f43))))
(assert (forall ((?v0 S10)) (= (= f43 (f31 f48 ?v0)) (= ?v0 f43))))
(assert (forall ((?v0 S10)) (= (= (f31 f48 ?v0) f43) (= ?v0 f43))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f31 f32 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f31 f48 ?v0) (f31 f48 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f31 f32 ?v0) (f31 f32 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S14) (?v2 S10) (?v3 S14)) (= (= (f55 (f56 f57 ?v0) ?v1) (f55 (f56 f57 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S14) (?v3 S10) (?v4 S10) (?v5 S14)) (= (= (f55 (f56 (f58 f60 ?v0) ?v1) ?v2) (f55 (f56 (f58 f60 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S14) (?v3 S10) (?v4 S10) (?v5 S14)) (= (= (f55 (f56 (f58 f59 ?v0) ?v1) ?v2) (f55 (f56 (f58 f59 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (not (= f43 f30)))
(assert (forall ((?v0 S14) (?v1 S11)) (= (forall ((?v2 S10)) (=> (= (f26 ?v2 (f45 f46 ?v0)) f1) (= (f15 ?v1 ?v2) f1))) (= (f61 ?v1 ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S3)) (= (forall ((?v2 S2)) (=> (= (f5 ?v2 (f6 f7 ?v0)) f1) (= (f3 ?v1 ?v2) f1))) (= (f62 ?v1 ?v0) f1))))
(assert (forall ((?v0 S11) (?v1 S14)) (= (= (f61 ?v0 ?v1) f1) (forall ((?v2 S10)) (=> (= (f26 ?v2 (f45 f46 ?v1)) f1) (= (f15 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f62 ?v0 ?v1) f1) (forall ((?v2 S2)) (=> (= (f5 ?v2 (f6 f7 ?v1)) f1) (= (f3 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S14) (?v1 S11)) (= (exists ((?v2 S10)) (and (= (f26 ?v2 (f45 f46 ?v0)) f1) (= (f15 ?v1 ?v2) f1))) (= (f53 ?v1 ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S3)) (= (exists ((?v2 S2)) (and (= (f5 ?v2 (f6 f7 ?v0)) f1) (= (f3 ?v1 ?v2) f1))) (= (f54 ?v1 ?v0) f1))))
(assert (forall ((?v0 S11) (?v1 S14)) (= (= (f53 ?v0 ?v1) f1) (exists ((?v2 S10)) (and (= (f26 ?v2 (f45 f46 ?v1)) f1) (= (f15 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f54 ?v0 ?v1) f1) (exists ((?v2 S2)) (and (= (f5 ?v2 (f6 f7 ?v1)) f1) (= (f3 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S14)) (= (f45 f46 (f49 (f50 (f51 f52 f40) ?v0) ?v1)) (f21 (f29 ?v0) (f45 f46 ?v1)))))
(assert (forall ((?v0 S10) (?v1 S14)) (= (= (f26 ?v0 (f45 f46 ?v1)) f1) (= (f15 (f45 f63 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S5)) (= (= (f5 ?v0 (f6 f7 ?v1)) f1) (= (f3 (f6 f64 ?v1) ?v0) f1))))
(assert (forall ((?v0 S14) (?v1 S10)) (= (= (f15 (f45 f63 ?v0) ?v1) f1) (= (f26 ?v1 (f45 f46 ?v0)) f1))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (= (f3 (f6 f64 ?v0) ?v1) f1) (= (f5 ?v1 (f6 f7 ?v0)) f1))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S11) (?v3 S11)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S10)) (=> (= (f26 ?v4 (f45 f46 ?v1)) f1) (= (= (f15 ?v2 ?v4) f1) (= (f15 ?v3 ?v4) f1)))) (= (= (f53 ?v2 ?v0) f1) (= (f53 ?v3 ?v1) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3) (?v3 S3)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S2)) (=> (= (f5 ?v4 (f6 f7 ?v1)) f1) (= (= (f3 ?v2 ?v4) f1) (= (f3 ?v3 ?v4) f1)))) (= (= (f54 ?v2 ?v0) f1) (= (f54 ?v3 ?v1) f1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S11) (?v3 S11)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S10)) (=> (= (f26 ?v4 (f45 f46 ?v1)) f1) (= (= (f15 ?v2 ?v4) f1) (= (f15 ?v3 ?v4) f1)))) (= (= (f61 ?v2 ?v0) f1) (= (f61 ?v3 ?v1) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3) (?v3 S3)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S2)) (=> (= (f5 ?v4 (f6 f7 ?v1)) f1) (= (= (f3 ?v2 ?v4) f1) (= (f3 ?v3 ?v4) f1)))) (= (= (f62 ?v2 ?v0) f1) (= (f62 ?v3 ?v1) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S14)) (= (f27 f28 (f55 (f56 (f58 f59 ?v0) ?v1) ?v2)) (f37 (f65 (f66 f67 f43) f39) ?v2))))
(assert (forall ((?v0 S10) (?v1 S14)) (= (f27 f28 (f55 (f56 f57 ?v0) ?v1)) (f37 (f65 (f66 f67 f43) f39) ?v1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S14)) (= (f27 f28 (f55 (f56 (f58 f60 ?v0) ?v1) ?v2)) (f37 (f65 (f66 f67 f43) f39) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f5 ?v0 (f19 (f68 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f5 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S11)) (=> (= (f26 ?v0 (f21 (f29 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f26 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (=> (not (= (f5 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f5 ?v0 (f19 (f68 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S10) (?v1 S11) (?v2 S10)) (=> (=> (not (= (f26 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f26 ?v0 (f21 (f29 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 f69) f1) false)))
(assert (forall ((?v0 S10)) (=> (= (f26 ?v0 f34) f1) false)))
(assert (forall ((?v0 S2)) (= (f41 (f14 ?v0)) (f19 (f68 ?v0) f69))))
(assert (forall ((?v0 S10)) (= (f70 (f16 ?v0)) (f21 (f29 ?v0) f34))))
(assert (forall ((?v0 S2)) (= (f41 (f17 ?v0)) (f19 (f68 ?v0) f69))))
(assert (forall ((?v0 S10)) (= (f70 (f18 ?v0)) (f21 (f29 ?v0) f34))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f41 (f19 (f20 ?v0) ?v1)) (ite (= (f3 ?v1 ?v0) f1) (f19 (f68 ?v0) f69) f69))))
(assert (forall ((?v0 S10) (?v1 S11)) (= (f70 (f21 (f22 ?v0) ?v1)) (ite (= (f15 ?v1 ?v0) f1) (f21 (f29 ?v0) f34) f34))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f69) (not (= (f5 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S11) (?v1 S10)) (=> (= ?v0 f34) (not (= (f26 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S11)) (= (= (f70 ?v0) f34) (forall ((?v1 S10)) (not (= (f15 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (= (f41 ?v0) f69) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f5 ?v0 f69) f1) false)))
(assert (forall ((?v0 S10)) (= (= (f26 ?v0 f34) f1) false)))
(assert (forall ((?v0 S11)) (= (= f34 (f70 ?v0)) (forall ((?v1 S10)) (not (= (f15 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (= f69 (f41 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f5 ?v1 f69) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S11)) (= (forall ((?v1 S10)) (=> (= (f26 ?v1 f34) f1) (= (f15 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f5 ?v1 f69) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S11)) (= (exists ((?v1 S10)) (and (= (f26 ?v1 f34) f1) (= (f15 ?v0 ?v1) f1))) false)))
(check-sat)
(exit)