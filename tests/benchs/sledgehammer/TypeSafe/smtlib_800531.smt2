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
(declare-fun f3 (S4 S3) S5)
(declare-fun f4 (S2) S4)
(declare-fun f5 (S6) S5)
(declare-fun f6 (S2 S3) S6)
(declare-fun f7 (S8 S3) S9)
(declare-fun f8 (S10 S7) S8)
(declare-fun f9 () S10)
(declare-fun f10 (S11 S12) S9)
(declare-fun f11 () S11)
(declare-fun f12 (S7 S3) S12)
(declare-fun f13 (S14 S13) S11)
(declare-fun f14 () S14)
(declare-fun f15 (S13 S12) S12)
(declare-fun f16 (S15 S6) S1)
(declare-fun f17 (S16 S15) S15)
(declare-fun f18 (S6) S16)
(declare-fun f19 (S6 S15) S1)
(declare-fun f20 (S12 S3) S1)
(declare-fun f21 (S3) S13)
(declare-fun f22 (S17 S12) S1)
(declare-fun f23 (S3) S17)
(declare-fun f24 (S18 S17) S17)
(declare-fun f25 (S12) S18)
(declare-fun f26 (S12 S17) S1)
(declare-fun f27 (S3) S13)
(declare-fun f28 (S12) S18)
(declare-fun f29 () S12)
(declare-fun f30 () S17)
(declare-fun f31 (S19 S9) S1)
(declare-fun f32 (S20 S19) S19)
(declare-fun f33 (S21 S19) S20)
(declare-fun f34 (S22 S19) S21)
(declare-fun f35 () S22)
(declare-fun f36 () S19)
(declare-fun f37 () S21)
(declare-fun f38 () S19)
(declare-fun f39 () S21)
(declare-fun f40 (S23 S6) S19)
(declare-fun f41 () S23)
(declare-fun f42 () S6)
(declare-fun f43 (S4) S12)
(declare-fun f44 () S4)
(declare-fun f45 (S24 S6) S9)
(declare-fun f46 (S24) S15)
(declare-fun f47 (S8) S12)
(declare-fun f48 (S11) S17)
(declare-fun f49 (S25 S19 S26 S19 S26) S1)
(declare-fun f50 (S25 S19 S26 S19 S26) S1)
(declare-fun f51 (S3) S27)
(declare-fun f52 () S12)
(declare-fun f53 () S17)
(declare-fun f54 (S9 S9) S1)
(declare-fun f55 (S3) S13)
(declare-fun f56 (S12) S18)
(declare-fun f57 () S15)
(declare-fun f58 (S6) S16)
(declare-fun f59 () S1)
(declare-fun f60 (S15) S15)
(declare-fun f61 (S17) S17)
(declare-fun f62 (S12) S12)
(declare-fun f63 (S28 S1) S6)
(declare-fun f64 () S28)
(declare-fun f65 (S9) S1)
(declare-fun f66 (S27) S1)
(declare-fun f67 (S5) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f3 (f4 ?v0) ?v1) (f5 (f6 ?v0 ?v1)))))
(assert (forall ((?v0 S7) (?v1 S3)) (= (f7 (f8 f9 ?v0) ?v1) (f10 f11 (f12 ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S12)) (= (f10 (f13 f14 ?v0) ?v1) (f10 f11 (f15 ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S6)) (= (= (f16 (f17 (f18 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f19 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S12) (?v2 S3)) (= (= (f20 (f15 (f21 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f22 (f23 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S17) (?v2 S12)) (= (= (f22 (f24 (f25 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f26 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S12) (?v2 S3)) (= (= (f20 (f15 (f27 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f20 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S12) (?v1 S17) (?v2 S12)) (= (= (f22 (f24 (f28 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f22 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3)) (= (= (f20 f29 ?v0) f1) true)))
(assert (forall ((?v0 S12)) (= (= (f22 f30 ?v0) f1) true)))
(assert (not (= (f31 (f32 (f33 (f34 f35 f36) (f32 (f33 f37 f38) (f32 (f33 f39 f36) f38))) (f40 f41 f42)) (f10 f11 (f43 f44))) f1)))
(assert (= (f31 (f32 (f33 f39 f36) f38) (f10 f11 (f43 f44))) f1))
(assert (= (f31 (f32 (f33 f39 f36) f38) (f10 f11 (f43 f44))) f1))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19) (?v3 S19) (?v4 S19)) (not (= (f32 (f33 f39 ?v0) ?v1) (f32 (f33 (f34 f35 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19) (?v3 S19) (?v4 S19)) (not (= (f32 (f33 (f34 f35 ?v0) ?v1) ?v2) (f32 (f33 f39 ?v3) ?v4)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19) (?v3 S19)) (not (= (f32 (f33 f37 ?v0) ?v1) (f32 (f33 f39 ?v2) ?v3)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19) (?v3 S19)) (not (= (f32 (f33 f39 ?v0) ?v1) (f32 (f33 f37 ?v2) ?v3)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19) (?v3 S19) (?v4 S19)) (not (= (f32 (f33 f37 ?v0) ?v1) (f32 (f33 (f34 f35 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19) (?v3 S19) (?v4 S19)) (not (= (f32 (f33 (f34 f35 ?v0) ?v1) ?v2) (f32 (f33 f37 ?v3) ?v4)))))
(assert (forall ((?v0 S6) (?v1 S9)) (= (= (f31 (f40 f41 ?v0) ?v1) f1) true)))
(assert (forall ((?v0 S6) (?v1 S19) (?v2 S19)) (not (= (f40 f41 ?v0) (f32 (f33 f39 ?v1) ?v2)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S6)) (not (= (f32 (f33 f39 ?v0) ?v1) (f40 f41 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S19) (?v2 S19) (?v3 S19)) (not (= (f40 f41 ?v0) (f32 (f33 (f34 f35 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19) (?v3 S6)) (not (= (f32 (f33 (f34 f35 ?v0) ?v1) ?v2) (f40 f41 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S6)) (=> (= (f3 ?v0 ?v1) (f5 ?v2)) (= (f22 (f23 ?v1) (f43 ?v0)) f1))))
(assert (forall ((?v0 S24) (?v1 S6) (?v2 S12)) (=> (= (f45 ?v0 ?v1) (f10 f11 ?v2)) (= (f19 ?v1 (f46 ?v0)) f1))))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S12)) (=> (= (f7 ?v0 ?v1) (f10 f11 ?v2)) (= (f22 (f23 ?v1) (f47 ?v0)) f1))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S12)) (=> (= (f10 ?v0 ?v1) (f10 f11 ?v2)) (= (f26 ?v1 (f48 ?v0)) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f40 f41 ?v0) (f40 f41 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19) (?v3 S19)) (= (= (f32 (f33 f37 ?v0) ?v1) (f32 (f33 f37 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19) (?v3 S19) (?v4 S19) (?v5 S19)) (= (= (f32 (f33 (f34 f35 ?v0) ?v1) ?v2) (f32 (f33 (f34 f35 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S19) (?v3 S19)) (= (= (f32 (f33 f39 ?v0) ?v1) (f32 (f33 f39 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S6)) (not (= (f32 (f33 f37 ?v0) ?v1) (f40 f41 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S19) (?v2 S19)) (not (= (f40 f41 ?v0) (f32 (f33 f37 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S4)) (=> (= (f22 (f23 ?v0) (f43 ?v1)) f1) (exists ((?v2 S6)) (= (f3 ?v1 ?v0) (f5 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S24)) (=> (= (f19 ?v0 (f46 ?v1)) f1) (exists ((?v2 S12)) (= (f45 ?v1 ?v0) (f10 f11 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S8)) (=> (= (f22 (f23 ?v0) (f47 ?v1)) f1) (exists ((?v2 S12)) (= (f7 ?v1 ?v0) (f10 f11 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S11)) (=> (= (f26 ?v0 (f48 ?v1)) f1) (exists ((?v2 S12)) (= (f10 ?v1 ?v0) (f10 f11 ?v2))))))
(assert (forall ((?v0 S25) (?v1 S19) (?v2 S19) (?v3 S26)) (let ((?v_0 (f32 (f33 f39 ?v1) ?v2))) (= (f49 ?v0 ?v_0 ?v3 (f32 (f33 (f34 f35 ?v1) (f32 (f33 f37 ?v2) ?v_0)) (f40 f41 f42)) ?v3) f1))))
(assert (forall ((?v0 S25) (?v1 S19) (?v2 S19) (?v3 S26) (?v4 S19) (?v5 S26)) (let ((?v_0 (f32 (f33 f39 ?v1) ?v2))) (= (= (f50 ?v0 ?v_0 ?v3 ?v4 ?v5) f1) (= (f50 ?v0 (f32 (f33 (f34 f35 ?v1) (f32 (f33 f37 ?v2) ?v_0)) (f40 f41 f42)) ?v3 ?v4 ?v5) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f10 f11 ?v0) (f10 f11 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f51 ?v0) (f51 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f5 ?v0) (f5 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2)) (= (f43 (f4 ?v0)) f52)))
(assert (forall ((?v0 S7)) (= (f47 (f8 f9 ?v0)) f52)))
(assert (forall ((?v0 S13)) (= (f48 (f13 f14 ?v0)) f53)))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S19)) (=> (= (f54 ?v0 ?v1) f1) (=> (= (f31 ?v2 ?v0) f1) (= (f31 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S19) (?v1 S9) (?v2 S9)) (=> (= (f31 ?v0 ?v1) f1) (=> (= (f54 ?v1 ?v2) f1) (= (f31 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S6)) (let ((?v_0 (f43 ?v0))) (=> (= (f3 ?v0 ?v1) (f5 ?v2)) (= (f15 (f55 ?v1) ?v_0) ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S12)) (let ((?v_0 (f47 ?v0))) (=> (= (f7 ?v0 ?v1) (f10 f11 ?v2)) (= (f15 (f55 ?v1) ?v_0) ?v_0)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S12)) (let ((?v_0 (f48 ?v0))) (=> (= (f10 ?v0 ?v1) (f10 f11 ?v2)) (= (f24 (f56 ?v1) ?v_0) ?v_0)))))
(assert (forall ((?v0 S25) (?v1 S19) (?v2 S26) (?v3 S19) (?v4 S26) (?v5 S19)) (=> (= (f49 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (= (f49 ?v0 (f32 (f33 f37 ?v1) ?v5) ?v2 (f32 (f33 f37 ?v3) ?v5) ?v4) f1))))
(assert (forall ((?v0 S25) (?v1 S19) (?v2 S26) (?v3 S19) (?v4 S26) (?v5 S19) (?v6 S19)) (=> (= (f49 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (= (f49 ?v0 (f32 (f33 (f34 f35 ?v1) ?v5) ?v6) ?v2 (f32 (f33 (f34 f35 ?v3) ?v5) ?v6) ?v4) f1))))
(assert (forall ((?v0 S25) (?v1 S6) (?v2 S19) (?v3 S26)) (= (f49 ?v0 (f32 (f33 f37 (f40 f41 ?v1)) ?v2) ?v3 ?v2 ?v3) f1)))
(assert (forall ((?v0 S25) (?v1 S19) (?v2 S26) (?v3 S6) (?v4 S26) (?v5 S19) (?v6 S19) (?v7 S26)) (=> (= (f50 ?v0 ?v1 ?v2 (f40 f41 ?v3) ?v4) f1) (=> (= (f50 ?v0 ?v5 ?v4 ?v6 ?v7) f1) (= (f50 ?v0 (f32 (f33 f37 ?v1) ?v5) ?v2 ?v6 ?v7) f1)))))
(assert (forall ((?v0 S6)) (= (= (f19 ?v0 f57) f1) true)))
(assert (forall ((?v0 S3)) (= (= (f22 (f23 ?v0) f52) f1) true)))
(assert (forall ((?v0 S12)) (= (= (f26 ?v0 f53) f1) true)))
(assert (forall ((?v0 S6)) (= (f19 ?v0 f57) f1)))
(assert (forall ((?v0 S3)) (= (f22 (f23 ?v0) f52) f1)))
(assert (forall ((?v0 S12)) (= (f26 ?v0 f53) f1)))
(assert (forall ((?v0 S12)) (= (f22 f53 ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f20 f52 ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S6)) (=> (=> (not (= (f19 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f19 ?v0 (f17 (f58 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S12) (?v1 S17) (?v2 S12)) (=> (=> (not (= (f26 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f26 ?v0 (f24 (f56 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S12) (?v2 S3)) (let ((?v_0 (f23 ?v0))) (=> (=> (not (= (f22 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f22 ?v_0 (f15 (f55 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S15)) (=> (= (f19 ?v0 (f17 (f58 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f19 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S17)) (=> (= (f26 ?v0 (f24 (f56 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f26 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S12)) (let ((?v_0 (f23 ?v0))) (=> (= (f22 ?v_0 (f15 (f55 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f22 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S25) (?v1 S6) (?v2 S26)) (let ((?v_0 (f40 f41 ?v1))) (= (f50 ?v0 ?v_0 ?v2 ?v_0 ?v2) f1))))
(assert (forall ((?v0 S25) (?v1 S6) (?v2 S26) (?v3 S19) (?v4 S26)) (let ((?v_0 (f40 f41 ?v1))) (=> (= (f50 ?v0 ?v_0 ?v2 ?v3 ?v4) f1) (=> (=> (= ?v3 ?v_0) (=> (= ?v4 ?v2) false)) false)))))
(assert (forall ((?v0 S12)) (= (= (f22 f53 ?v0) f1) (= f59 f1))))
(assert (forall ((?v0 S3)) (= (= (f20 f52 ?v0) f1) (= f59 f1))))
(assert (forall ((?v0 S6) (?v1 S15)) (= (f19 ?v0 (f17 (f58 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S12) (?v1 S17)) (= (f26 ?v0 (f24 (f56 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S3) (?v1 S12)) (= (f22 (f23 ?v0) (f15 (f55 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S6) (?v1 S15)) (= (f17 (f58 ?v0) ?v1) (f60 (f17 (f18 ?v0) ?v1)))))
(assert (forall ((?v0 S12) (?v1 S17)) (= (f24 (f56 ?v0) ?v1) (f61 (f24 (f25 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S12)) (= (f15 (f55 ?v0) ?v1) (f62 (f15 (f21 ?v0) ?v1)))))
(assert (forall ((?v0 S12) (?v1 S17)) (= (f24 (f56 ?v0) (f61 ?v1)) (f61 (f24 (f28 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S12)) (= (f15 (f55 ?v0) (f62 ?v1)) (f62 (f15 (f27 ?v0) ?v1)))))
(assert (forall ((?v0 S12) (?v1 S17)) (let ((?v_0 (f56 ?v0))) (let ((?v_1 (f24 ?v_0 ?v1))) (= (f24 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S12)) (let ((?v_0 (f55 ?v0))) (let ((?v_1 (f15 ?v_0 ?v1))) (= (f15 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S17)) (let ((?v_1 (f56 ?v0)) (?v_0 (f56 ?v1))) (= (f24 ?v_1 (f24 ?v_0 ?v2)) (f24 ?v_0 (f24 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S12)) (let ((?v_1 (f55 ?v0)) (?v_0 (f55 ?v1))) (= (f15 ?v_1 (f15 ?v_0 ?v2)) (f15 ?v_0 (f15 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S15)) (= (= (f19 ?v0 (f17 (f58 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f19 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S17)) (= (= (f26 ?v0 (f24 (f56 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f26 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S12)) (let ((?v_0 (f23 ?v0))) (= (= (f22 ?v_0 (f15 (f55 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f22 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S17) (?v2 S12)) (= (= (f22 (f24 (f56 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f22 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S12) (?v2 S3)) (= (= (f20 (f15 (f55 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f20 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S15)) (let ((?v_0 (f58 ?v0))) (=> (not (= (f19 ?v0 ?v1) f1)) (=> (not (= (f19 ?v0 ?v2) f1)) (= (= (f17 ?v_0 ?v1) (f17 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S12) (?v1 S17) (?v2 S17)) (let ((?v_0 (f56 ?v0))) (=> (not (= (f26 ?v0 ?v1) f1)) (=> (not (= (f26 ?v0 ?v2) f1)) (= (= (f24 ?v_0 ?v1) (f24 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S12) (?v2 S12)) (let ((?v_0 (f23 ?v0)) (?v_1 (f55 ?v0))) (=> (not (= (f22 ?v_0 ?v1) f1)) (=> (not (= (f22 ?v_0 ?v2) f1)) (= (= (f15 ?v_1 ?v1) (f15 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S6)) (=> (= (f19 ?v0 ?v1) f1) (= (f19 ?v0 (f17 (f58 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S12) (?v1 S17) (?v2 S12)) (=> (= (f26 ?v0 ?v1) f1) (= (f26 ?v0 (f24 (f56 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S12) (?v2 S3)) (let ((?v_0 (f23 ?v0))) (=> (= (f22 ?v_0 ?v1) f1) (= (f22 ?v_0 (f15 (f55 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S15)) (=> (= (f19 ?v0 ?v1) f1) (= (f17 (f58 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S12) (?v1 S17)) (=> (= (f26 ?v0 ?v1) f1) (= (f24 (f56 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S3) (?v1 S12)) (=> (= (f22 (f23 ?v0) ?v1) f1) (= (f15 (f55 ?v0) ?v1) ?v1))))
(assert (= f53 (f61 f30)))
(assert (= f52 (f62 f29)))
(assert (forall ((?v0 S6) (?v1 S15)) (= (f17 (f58 ?v0) ?v1) (f60 (f17 (f18 ?v0) ?v1)))))
(assert (forall ((?v0 S12) (?v1 S17)) (= (f24 (f56 ?v0) ?v1) (f61 (f24 (f25 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S12)) (= (f15 (f55 ?v0) ?v1) (f62 (f15 (f21 ?v0) ?v1)))))
(assert (forall ((?v0 S25) (?v1 S19) (?v2 S26) (?v3 S26) (?v4 S19)) (=> (= (f50 ?v0 ?v1 ?v2 (f40 f41 (f63 f64 f2)) ?v3) f1) (= (f50 ?v0 (f32 (f33 f39 ?v1) ?v4) ?v2 (f40 f41 f42) ?v3) f1))))
(assert (exists ((?v0 S6)) (= (f19 ?v0 f57) f1)))
(assert (exists ((?v0 S3)) (= (f22 (f23 ?v0) f52) f1)))
(assert (exists ((?v0 S12)) (= (f26 ?v0 f53) f1)))
(assert (forall ((?v0 S15)) (=> (forall ((?v1 S6)) (= (f19 ?v1 ?v0) f1)) (= f57 ?v0))))
(assert (forall ((?v0 S12)) (=> (forall ((?v1 S3)) (= (f22 (f23 ?v1) ?v0) f1)) (= f52 ?v0))))
(assert (forall ((?v0 S17)) (=> (forall ((?v1 S12)) (= (f26 ?v1 ?v0) f1)) (= f53 ?v0))))
(assert (forall ((?v0 S6) (?v1 S15)) (=> (= (f19 ?v0 ?v1) f1) (exists ((?v2 S15)) (and (= ?v1 (f17 (f58 ?v0) ?v2)) (not (= (f19 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S12) (?v1 S17)) (=> (= (f26 ?v0 ?v1) f1) (exists ((?v2 S17)) (and (= ?v1 (f24 (f56 ?v0) ?v2)) (not (= (f26 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S3) (?v1 S12)) (=> (= (f22 (f23 ?v0) ?v1) f1) (exists ((?v2 S12)) (and (= ?v1 (f15 (f55 ?v0) ?v2)) (not (= (f22 (f23 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S6) (?v1 S15)) (=> (= (f19 ?v0 ?v1) f1) (=> (forall ((?v2 S15)) (=> (= ?v1 (f17 (f58 ?v0) ?v2)) (=> (not (= (f19 ?v0 ?v2) f1)) false))) false))))
(assert (forall ((?v0 S12) (?v1 S17)) (=> (= (f26 ?v0 ?v1) f1) (=> (forall ((?v2 S17)) (=> (= ?v1 (f24 (f56 ?v0) ?v2)) (=> (not (= (f26 ?v0 ?v2) f1)) false))) false))))
(assert (forall ((?v0 S3) (?v1 S12)) (=> (= (f22 (f23 ?v0) ?v1) f1) (=> (forall ((?v2 S12)) (=> (= ?v1 (f15 (f55 ?v0) ?v2)) (=> (not (= (f22 (f23 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S12)) (= (= (f65 (f10 f11 ?v0)) f1) false)))
(assert (forall ((?v0 S3)) (= (= (f66 (f51 ?v0)) f1) false)))
(assert (forall ((?v0 S6)) (= (= (f67 (f5 ?v0)) f1) false)))
(assert (forall ((?v0 S25) (?v1 S19) (?v2 S19) (?v3 S26)) (= (f49 ?v0 (f32 (f33 (f34 f35 (f40 f41 (f63 f64 f2))) ?v1) ?v2) ?v3 ?v2 ?v3) f1)))
(assert (forall ((?v0 S25) (?v1 S19) (?v2 S26) (?v3 S26) (?v4 S19) (?v5 S19) (?v6 S26) (?v7 S19)) (=> (= (f50 ?v0 ?v1 ?v2 (f40 f41 (f63 f64 f1)) ?v3) f1) (=> (= (f50 ?v0 ?v4 ?v3 ?v5 ?v6) f1) (= (f50 ?v0 (f32 (f33 (f34 f35 ?v1) ?v4) ?v7) ?v2 ?v5 ?v6) f1)))))
(check-sat)
(exit)