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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S3) S3)
(declare-fun f5 (S2) S4)
(declare-fun f6 (S5 S3) S1)
(declare-fun f7 (S2) S5)
(declare-fun f8 (S3) S4)
(declare-fun f9 (S2) S4)
(declare-fun f10 () S3)
(declare-fun f11 (S3) S5)
(declare-fun f12 (S2) S4)
(declare-fun f13 (S6 S7) S2)
(declare-fun f14 (S8 S9) S6)
(declare-fun f15 (S10 S7) S8)
(declare-fun f16 () S10)
(declare-fun f17 () S7)
(declare-fun f18 (S11 S12) S9)
(declare-fun f19 () S11)
(declare-fun f20 () S12)
(declare-fun f21 () S7)
(declare-fun f22 () S3)
(declare-fun f23 (S13 S14) S9)
(declare-fun f24 () S13)
(declare-fun f25 (S12) S14)
(declare-fun f26 () S3)
(declare-fun f27 (S17 S16) S1)
(declare-fun f28 (S7 S15) S17)
(declare-fun f29 (S3) S3)
(declare-fun f30 (S18 S3) S2)
(declare-fun f31 () S18)
(declare-fun f32 () S1)
(declare-fun f33 () S9)
(declare-fun f34 (S19 S9) S9)
(declare-fun f35 (S20 S9) S19)
(declare-fun f36 () S20)
(declare-fun f37 (S21 S16) S17)
(declare-fun f38 (S9) S21)
(declare-fun f39 (S22) S3)
(declare-fun f40 (S23 S22) S22)
(declare-fun f41 () S23)
(declare-fun f42 (S3) S5)
(declare-fun f43 (S24 S22) S17)
(declare-fun f44 (S25 S16) S24)
(declare-fun f45 (S9) S25)
(declare-fun f46 () S22)
(declare-fun f47 (S26) S4)
(declare-fun f48 (S26 S18) S1)
(declare-fun f49 (S28 S2) S22)
(declare-fun f50 (S29 S27) S28)
(declare-fun f51 () S29)
(declare-fun f52 () S28)
(declare-fun f53 () S22)
(declare-fun f54 (S30 S22) S1)
(declare-fun f55 (S31 S2) S4)
(declare-fun f56 (S26) S31)
(declare-fun f57 (S32 S9) S22)
(declare-fun f58 () S32)
(declare-fun f59 (S3) S1)
(declare-fun f60 (S33 S2) S2)
(declare-fun f61 (S26 S2) S33)
(declare-fun f62 () S32)
(declare-fun f63 (S26 S18) S1)
(declare-fun f64 (S34 S22) S23)
(declare-fun f65 () S34)
(declare-fun f66 (S36 S35) S35)
(declare-fun f67 (S37 S35) S36)
(declare-fun f68 () S37)
(declare-fun f69 () S35)
(declare-fun f70 (S38 S17) S20)
(declare-fun f71 () S38)
(declare-fun f72 (S41 S40) S19)
(declare-fun f73 (S42 S39) S41)
(declare-fun f74 () S42)
(declare-fun f75 (S43 S17) S19)
(declare-fun f76 () S43)
(declare-fun f77 () S23)
(declare-fun f78 () S23)
(declare-fun f79 (S44 S1) S22)
(declare-fun f80 () S44)
(declare-fun f81 (S45 S2) S3)
(declare-fun f82 (S46 S3) S5)
(declare-fun f83 (S45) S46)
(declare-fun f84 (S3) S4)
(declare-fun f85 () S37)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f6 (f7 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v2))) (= (= (f3 (f4 (f8 ?v0) ?v1) ?v2) f1) (and (= (f6 ?v_0 ?v0) f1) (not (= (f6 ?v_0 ?v1) f1)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f9 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f10 ?v0) f1) false)))
(assert (let ((?v_0 (f15 f16 f17))) (not (= (f6 (f11 (f4 (f12 (f13 (f14 ?v_0 (f18 f19 f20)) f21)) f22)) (f4 (f12 (f13 (f14 ?v_0 (f23 f24 (f25 f20))) f21)) f26)) f1))))
(assert (= (f6 (f11 f22) (f4 (f12 (f13 (f14 (f15 f16 f17) (f23 f24 (f25 f20))) f21)) f26)) f1))
(assert (forall ((?v0 S3)) (= (f6 (f11 ?v0) f26) f1)))
(assert (forall ((?v0 S7) (?v1 S9) (?v2 S7) (?v3 S7) (?v4 S9) (?v5 S7)) (= (= (f13 (f14 (f15 f16 ?v0) ?v1) ?v2) (f13 (f14 (f15 f16 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f11 ?v2))) (=> (= (f6 (f11 ?v0) ?v1) f1) (=> (= (f6 ?v_0 ?v0) f1) (= (f6 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f11 ?v0)) (?v_1 (f12 ?v1))) (=> (= (f6 ?v_0 (f4 ?v_1 f26)) f1) (=> (= (f6 ?v_0 ?v2) f1) (= (f6 ?v_0 (f4 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S7) (?v1 S12) (?v2 S7) (?v3 S3)) (let ((?v_0 (f15 f16 ?v0))) (let ((?v_1 (f12 (f13 (f14 ?v_0 (f18 f19 ?v1)) ?v2)))) (=> (= (f6 (f11 (f4 ?v_1 ?v3)) (f4 (f12 (f13 (f14 ?v_0 (f23 f24 (f25 ?v1))) ?v2)) f26)) f1) (= (f6 (f11 ?v3) (f4 ?v_1 f26)) f1))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S7)) (let ((?v_0 (f11 ?v0)) (?v_1 (f14 (f15 f16 ?v1) ?v2))) (=> (= (f6 ?v_0 (f4 (f12 (f13 ?v_1 ?v3)) f26)) f1) (=> (forall ((?v5 S15) (?v6 S16)) (=> (= (f27 (f28 ?v3 ?v5) ?v6) f1) (= (f27 (f28 ?v4 ?v5) ?v6) f1))) (= (f6 ?v_0 (f4 (f12 (f13 ?v_1 ?v4)) f26)) f1))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S7)) (let ((?v_0 (f11 ?v0))) (=> (= (f6 ?v_0 (f4 (f12 (f13 (f14 (f15 f16 ?v1) ?v2) ?v3)) f26)) f1) (=> (forall ((?v5 S15) (?v6 S16)) (=> (= (f27 (f28 ?v4 ?v5) ?v6) f1) (= (f27 (f28 ?v1 ?v5) ?v6) f1))) (= (f6 ?v_0 (f4 (f12 (f13 (f14 (f15 f16 ?v4) ?v2) ?v3)) f26)) f1))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S7) (?v5 S7)) (let ((?v_0 (f11 ?v0))) (=> (= (f6 ?v_0 (f4 (f12 (f13 (f14 (f15 f16 ?v1) ?v2) ?v3)) f26)) f1) (=> (forall ((?v6 S15) (?v7 S16)) (=> (= (f27 (f28 ?v4 ?v6) ?v7) f1) (forall ((?v8 S16)) (=> (forall ((?v9 S15)) (=> (= (f27 (f28 ?v1 ?v9) ?v7) f1) (= (f27 (f28 ?v3 ?v9) ?v8) f1))) (= (f27 (f28 ?v5 ?v6) ?v8) f1))))) (= (f6 ?v_0 (f4 (f12 (f13 (f14 (f15 f16 ?v4) ?v2) ?v5)) f26)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f12 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f6 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v0))) (=> (=> (not (= (f6 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f6 ?v_0 (f4 (f12 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f6 (f7 ?v0) f26) f1) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f26 (f4 (f12 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f4 (f12 ?v0) ?v1) f26))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f6 (f7 ?v0) (f4 (f12 ?v1) f26)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f4 (f12 ?v0) (f4 (f12 ?v1) f26)) (f4 (f12 ?v2) (f4 (f12 ?v3) f26))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f26) (not (= (f6 (f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f29 ?v0) f26) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f6 (f7 ?v0) f26) f1) false)))
(assert (forall ((?v0 S3)) (= (= f26 (f29 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f6 (f7 ?v1) f26) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f6 (f7 ?v1) f26) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f6 (f7 ?v1) ?v0) f1)) (not (= ?v0 f26)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f6 (f7 ?v1) ?v0) f1))) (= ?v0 f26))))
(assert (= f26 (f29 f10)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (= (f4 (f12 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 ?v1) f1) (= (f6 ?v_0 (f4 (f12 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0)) (?v_1 (f12 ?v0))) (=> (not (= (f6 ?v_0 ?v1) f1)) (=> (not (= (f6 ?v_0 ?v2) f1)) (= (= (f4 ?v_1 ?v1) (f4 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f12 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (= (= (f6 ?v_0 (f4 (f12 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f6 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f12 ?v0)) (?v_0 (f12 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f12 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f12 ?v0) (f29 ?v1)) (f29 (f4 (f9 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f12 ?v0) ?v1) (f29 (f4 (f5 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f6 (f7 ?v0) (f4 (f12 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f12 ?v0) f26) (f4 (f12 ?v1) f26)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f6 (f7 ?v0) (f4 (f12 ?v1) f26)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2)) (= (f30 f31 (f4 (f12 ?v0) f26)) ?v0)))
(assert (forall ((?v0 S2)) (= (= (f3 f26 ?v0) f1) (= f32 f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f26 ?v0) f1) (= f32 f1))))
(assert (forall ((?v0 S3) (?v1 S7)) (= (f6 (f11 ?v0) (f4 (f12 (f13 (f14 (f15 f16 ?v1) f33) ?v1)) f26)) f1)))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S9) (?v5 S7)) (let ((?v_0 (f11 ?v0)) (?v_1 (f15 f16 ?v1))) (=> (= (f6 ?v_0 (f4 (f12 (f13 (f14 ?v_1 ?v2) ?v3)) f26)) f1) (=> (= (f6 ?v_0 (f4 (f12 (f13 (f14 (f15 f16 ?v3) ?v4) ?v5)) f26)) f1) (= (f6 ?v_0 (f4 (f12 (f13 (f14 ?v_1 (f34 (f35 f36 ?v2) ?v4)) ?v5)) f26)) f1))))))
(assert (forall ((?v0 S2)) (=> (forall ((?v1 S7) (?v2 S9) (?v3 S7)) (=> (= ?v0 (f13 (f14 (f15 f16 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (=> (forall ((?v2 S3)) (=> (= ?v1 (f4 (f12 ?v0) ?v2)) (=> (not (= (f6 (f7 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (exists ((?v2 S3)) (and (= ?v1 (f4 (f12 ?v0) ?v2)) (not (= (f6 (f7 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2)) (=> (= (f6 (f7 ?v1) ?v0) f1) false)) (= ?v0 f26))))
(assert (forall ((?v0 S7) (?v1 S3) (?v2 S9) (?v3 S7)) (=> (forall ((?v4 S15) (?v5 S16)) (=> (= (f27 (f28 ?v0 ?v4) ?v5) f1) (exists ((?v6 S7) (?v7 S7)) (and (= (f6 (f11 ?v1) (f4 (f12 (f13 (f14 (f15 f16 ?v6) ?v2) ?v7)) f26)) f1) (forall ((?v8 S16)) (=> (forall ((?v9 S15)) (=> (= (f27 (f28 ?v6 ?v9) ?v5) f1) (= (f27 (f28 ?v7 ?v9) ?v8) f1))) (= (f27 (f28 ?v3 ?v4) ?v8) f1))))))) (= (f6 (f11 ?v1) (f4 (f12 (f13 (f14 (f15 f16 ?v0) ?v2) ?v3)) f26)) f1))))
(assert (forall ((?v0 S9) (?v1 S9)) (not (= (f34 (f35 f36 ?v0) ?v1) f33))))
(assert (forall ((?v0 S9) (?v1 S9)) (not (= f33 (f34 (f35 f36 ?v0) ?v1)))))
(assert (forall ((?v0 S12)) (not (= f33 (f18 f19 ?v0)))))
(assert (forall ((?v0 S12)) (not (= (f18 f19 ?v0) f33))))
(assert (forall ((?v0 S12) (?v1 S9) (?v2 S9)) (not (= (f18 f19 ?v0) (f34 (f35 f36 ?v1) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S12)) (not (= (f34 (f35 f36 ?v0) ?v1) (f18 f19 ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (= (= (f34 (f35 f36 ?v0) ?v1) (f34 (f35 f36 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f18 f19 ?v0) (f18 f19 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S16) (?v2 S16)) (=> (= (f27 (f37 (f38 (f23 f24 (f25 ?v0))) ?v1) ?v2) f1) (= (f27 (f37 (f38 (f18 f19 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S12) (?v1 S16) (?v2 S16)) (=> (= (f27 (f37 (f38 (f18 f19 ?v0)) ?v1) ?v2) f1) (=> (=> (= (f27 (f37 (f38 (f23 f24 (f25 ?v0))) ?v1) ?v2) f1) false) false))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f26)) (exists ((?v1 S2) (?v2 S3)) (and (= ?v0 (f4 (f12 ?v1) ?v2)) (not (= (f6 (f7 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S2)) (= (= (f3 f26 ?v0) f1) (= (f6 (f7 ?v0) f26) f1))))
(assert (forall ((?v0 S22) (?v1 S7) (?v2 S12) (?v3 S7)) (let ((?v_0 (f15 f16 ?v1))) (= (= (f3 (f39 ?v0) (f13 (f14 ?v_0 (f23 f24 (f25 ?v2))) ?v3)) f1) (= (f3 (f39 (f40 f41 ?v0)) (f13 (f14 ?v_0 (f18 f19 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S9) (?v1 S16) (?v2 S16) (?v3 S9) (?v4 S16)) (=> (= (f27 (f37 (f38 ?v0) ?v1) ?v2) f1) (=> (= (f27 (f37 (f38 ?v3) ?v2) ?v4) f1) (= (f27 (f37 (f38 (f34 (f35 f36 ?v0) ?v3)) ?v1) ?v4) f1)))))
(assert (forall ((?v0 S16) (?v1 S16)) (=> (= (f27 (f37 (f38 f33) ?v0) ?v1) f1) (=> (=> (= ?v1 ?v0) false) false))))
(assert (forall ((?v0 S16)) (= (f27 (f37 (f38 f33) ?v0) ?v0) f1)))
(assert (forall ((?v0 S9) (?v1 S16) (?v2 S16) (?v3 S16)) (let ((?v_0 (f37 (f38 ?v0) ?v1))) (=> (= (f27 ?v_0 ?v2) f1) (=> (= (f27 ?v_0 ?v3) f1) (= ?v3 ?v2))))))
(assert (forall ((?v0 S22) (?v1 S2)) (=> (= (f3 (f39 (f40 f41 ?v0)) ?v1) f1) (= (f3 (f39 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S22)) (=> (forall ((?v2 S2)) (=> (= (f6 (f7 ?v2) ?v0) f1) (= (f3 (f39 (f40 f41 ?v1)) ?v2) f1))) (forall ((?v2 S2)) (=> (= (f6 (f7 ?v2) ?v0) f1) (= (f3 (f39 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S16) (?v3 S16)) (=> (= (f27 (f37 (f38 (f34 (f35 f36 ?v0) ?v1)) ?v2) ?v3) f1) (=> (forall ((?v4 S16)) (=> (= (f27 (f37 (f38 ?v0) ?v2) ?v4) f1) (=> (= (f27 (f37 (f38 ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 (f42 ?v0) ?v1) f1) (forall ((?v2 S22)) (=> (forall ((?v3 S2)) (=> (= (f6 (f7 ?v3) ?v0) f1) (= (f3 (f39 ?v2) ?v3) f1))) (forall ((?v3 S2)) (=> (= (f6 (f7 ?v3) ?v1) f1) (= (f3 (f39 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S12) (?v1 S16) (?v2 S22) (?v3 S16)) (=> (= (f27 (f43 (f44 (f45 (f23 f24 (f25 ?v0))) ?v1) ?v2) ?v3) f1) (= (f27 (f43 (f44 (f45 (f18 f19 ?v0)) ?v1) (f40 f41 ?v2)) ?v3) f1))))
(assert (forall ((?v0 S12) (?v1 S16) (?v2 S22) (?v3 S16)) (=> (= (f27 (f43 (f44 (f45 (f18 f19 ?v0)) ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S22)) (=> (= ?v2 (f40 f41 ?v4)) (=> (= (f27 (f43 (f44 (f45 (f23 f24 (f25 ?v0))) ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S7) (?v1 S12) (?v2 S7)) (= (f3 (f39 f46) (f13 (f14 (f15 f16 ?v0) (f18 f19 ?v1)) ?v2)) f1)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f6 (f7 ?v0) ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f29 ?v0) ?v0)))
(assert (forall ((?v0 S26) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f47 ?v0) (f4 (f12 ?v1) f26)) ?v2) f1) (= ?v1 ?v2))))
(assert (forall ((?v0 S26) (?v1 S18) (?v2 S2)) (=> (= (f48 ?v0 ?v1) f1) (= (f30 ?v1 (f4 (f12 ?v2) f26)) ?v2))))
(assert (forall ((?v0 S9) (?v1 S16) (?v2 S22) (?v3 S16) (?v4 S9) (?v5 S16)) (=> (= (f27 (f43 (f44 (f45 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f27 (f43 (f44 (f45 ?v4) ?v3) ?v2) ?v5) f1) (= (f27 (f43 (f44 (f45 (f34 (f35 f36 ?v0) ?v4)) ?v1) ?v2) ?v5) f1)))))
(assert (forall ((?v0 S16) (?v1 S22)) (= (f27 (f43 (f44 (f45 f33) ?v0) ?v1) ?v0) f1)))
(assert (forall ((?v0 S16) (?v1 S22) (?v2 S16)) (=> (= (f27 (f43 (f44 (f45 f33) ?v0) ?v1) ?v2) f1) (=> (=> (= ?v2 ?v0) false) false))))
(assert (forall ((?v0 S9) (?v1 S16) (?v2 S22) (?v3 S16)) (let ((?v_0 (f44 (f45 ?v0) ?v1))) (=> (= (f27 (f43 ?v_0 ?v2) ?v3) f1) (= (f27 (f43 ?v_0 (f40 f41 ?v2)) ?v3) f1)))))
(assert (forall ((?v0 S9) (?v1 S16) (?v2 S16)) (= (= (f27 (f37 (f38 ?v0) ?v1) ?v2) f1) (exists ((?v3 S22)) (= (f27 (f43 (f44 (f45 ?v0) ?v1) ?v3) ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S16) (?v2 S22) (?v3 S16)) (=> (= (f27 (f43 (f44 (f45 ?v0) ?v1) ?v2) ?v3) f1) (= (f27 (f37 (f38 ?v0) ?v1) ?v3) f1))))
(assert (forall ((?v0 S26) (?v1 S3) (?v2 S2)) (=> (= (f3 (f4 (f47 ?v0) ?v1) ?v2) f1) (not (= ?v1 f26)))))
(assert (forall ((?v0 S26) (?v1 S2)) (=> (= (f3 (f4 (f47 ?v0) f26) ?v1) f1) false)))
(assert (forall ((?v0 S22) (?v1 S7) (?v2 S9) (?v3 S7)) (= (= (f3 (f39 ?v0) (f13 (f14 (f15 f16 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S15) (?v5 S16)) (=> (= (f27 (f28 ?v1 ?v4) ?v5) f1) (forall ((?v6 S16)) (=> (= (f27 (f43 (f44 (f45 ?v2) ?v5) ?v0) ?v6) f1) (= (f27 (f28 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S16) (?v3 S22) (?v4 S16)) (=> (= (f27 (f43 (f44 (f45 (f34 (f35 f36 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (forall ((?v5 S16)) (=> (= (f27 (f43 (f44 (f45 ?v0) ?v2) ?v3) ?v5) f1) (=> (= (f27 (f43 (f44 (f45 ?v1) ?v5) ?v3) ?v4) f1) false))) false))))
(assert (forall ((?v0 S27) (?v1 S7) (?v2 S9) (?v3 S7)) (= (f49 (f50 f51 ?v0) (f13 (f14 (f15 f16 ?v1) ?v2) ?v3)) f46)))
(assert (forall ((?v0 S9) (?v1 S16) (?v2 S16)) (=> (= (f27 (f37 (f38 ?v0) ?v1) ?v2) f1) (exists ((?v3 S22)) (= (f27 (f43 (f44 (f45 ?v0) ?v1) ?v3) ?v2) f1)))))
(assert (forall ((?v0 S7) (?v1 S9) (?v2 S7)) (= (f49 f52 (f13 (f14 (f15 f16 ?v0) ?v1) ?v2)) f46)))
(assert (forall ((?v0 S22)) (=> (= (f40 f41 ?v0) f46) false)))
(assert (forall ((?v0 S22)) (=> (= f46 (f40 f41 ?v0)) false)))
(assert (= f53 f46))
(assert (forall ((?v0 S22) (?v1 S22)) (=> (= (f40 f41 ?v0) (f40 f41 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S22) (?v1 S22)) (= (= (f40 f41 ?v0) (f40 f41 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S22)) (not (= (f40 f41 ?v0) ?v0))))
(assert (forall ((?v0 S22)) (not (= ?v0 (f40 f41 ?v0)))))
(assert (forall ((?v0 S22)) (not (= f46 (f40 f41 ?v0)))))
(assert (forall ((?v0 S22)) (not (= f46 (f40 f41 ?v0)))))
(assert (forall ((?v0 S22)) (not (= (f40 f41 ?v0) f46))))
(assert (forall ((?v0 S22)) (not (= (f40 f41 ?v0) f46))))
(assert (forall ((?v0 S22)) (=> (not (= ?v0 f46)) (exists ((?v1 S22)) (= ?v0 (f40 f41 ?v1))))))
(assert (forall ((?v0 S30) (?v1 S22)) (=> (= (f54 ?v0 f46) f1) (=> (forall ((?v2 S22)) (=> (= (f54 ?v0 ?v2) f1) (= (f54 ?v0 (f40 f41 ?v2)) f1))) (= (f54 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S30) (?v1 S22)) (=> (= (f54 ?v0 ?v1) f1) (=> (forall ((?v2 S22)) (=> (= (f54 ?v0 (f40 f41 ?v2)) f1) (= (f54 ?v0 ?v2) f1))) (= (f54 ?v0 f46) f1)))))
(assert (forall ((?v0 S22)) (=> (=> (= ?v0 f46) false) (=> (forall ((?v1 S22)) (=> (= ?v0 (f40 f41 ?v1)) false)) false))))
(assert (forall ((?v0 S9) (?v1 S16) (?v2 S22) (?v3 S16) (?v4 S9) (?v5 S16) (?v6 S22) (?v7 S16)) (=> (= (f27 (f43 (f44 (f45 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f27 (f43 (f44 (f45 ?v4) ?v5) ?v6) ?v7) f1) (exists ((?v8 S22)) (and (= (f27 (f43 (f44 (f45 ?v0) ?v1) ?v8) ?v3) f1) (= (f27 (f43 (f44 (f45 ?v4) ?v5) ?v8) ?v7) f1)))))))
(assert (forall ((?v0 S26) (?v1 S2) (?v2 S3) (?v3 S2)) (=> (= (f3 (f4 (f55 (f56 ?v0) ?v1) ?v2) ?v3) f1) (=> (not (= (f6 (f7 ?v1) ?v2) f1)) (= (f3 (f4 (f47 ?v0) (f4 (f12 ?v1) ?v2)) ?v3) f1)))))
(assert (= (f57 f58 f33) f46))
(assert (forall ((?v0 S26) (?v1 S18) (?v2 S3) (?v3 S2)) (=> (= (f48 ?v0 ?v1) f1) (=> (= (f59 ?v2) f1) (=> (not (= (f6 (f7 ?v3) ?v2) f1)) (=> (not (= ?v2 f26)) (= (f30 ?v1 (f4 (f12 ?v3) ?v2)) (f60 (f61 ?v0 ?v3) (f30 ?v1 ?v2)))))))))
(assert (forall ((?v0 S12)) (= (f57 f58 (f18 f19 ?v0)) f46)))
(assert (= (f57 f62 f33) f46))
(assert (= (f59 f26) f1))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f59 ?v0) f1) (= (f59 (f4 (f12 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f59 (f4 (f12 ?v0) ?v1)) f1) (= (f59 ?v1) f1))))
(assert (forall ((?v0 S26) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 (f55 (f56 ?v0) ?v1) f26) ?v2) f1) (=> (=> (= ?v2 ?v1) false) false))))
(assert (forall ((?v0 S26) (?v1 S2)) (= (f3 (f4 (f55 (f56 ?v0) ?v1) f26) ?v1) f1)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S26) (?v3 S2) (?v4 S2)) (let ((?v_0 (f55 (f56 ?v2) ?v3))) (=> (not (= (f6 (f7 ?v0) ?v1) f1)) (=> (= (f3 (f4 ?v_0 ?v1) ?v4) f1) (= (f3 (f4 ?v_0 (f4 (f12 ?v0) ?v1)) (f60 (f61 ?v2 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S12)) (= (f57 f62 (f18 f19 ?v0)) f46)))
(assert (forall ((?v0 S26) (?v1 S18) (?v2 S3)) (=> (= (f48 ?v0 ?v1) f1) (=> (= (f59 ?v2) f1) (=> (not (= ?v2 f26)) (=> (forall ((?v3 S2) (?v4 S2)) (= (f6 (f7 (f60 (f61 ?v0 ?v3) ?v4)) (f4 (f12 ?v3) (f4 (f12 ?v4) f26))) f1)) (= (f6 (f7 (f30 ?v1 ?v2)) ?v2) f1)))))))
(assert (forall ((?v0 S26) (?v1 S2) (?v2 S3) (?v3 S2)) (=> (= (f3 (f4 (f47 ?v0) (f4 (f12 ?v1) ?v2)) ?v3) f1) (=> (forall ((?v4 S2) (?v5 S3)) (=> (= (f4 (f12 ?v1) ?v2) (f4 (f12 ?v4) ?v5)) (=> (= (f3 (f4 (f55 (f56 ?v0) ?v4) ?v5) ?v3) f1) (=> (not (= (f6 (f7 ?v4) ?v5) f1)) false)))) false))))
(assert (forall ((?v0 S3) (?v1 S26)) (=> (= (f59 ?v0) f1) (=> (not (= ?v0 f26)) (exists ((?v2 S2)) (= (f3 (f4 (f47 ?v1) ?v0) ?v2) f1))))))
(assert (forall ((?v0 S3)) (= (= (f59 ?v0) f1) (or (= ?v0 f26) (exists ((?v1 S3) (?v2 S2)) (and (= ?v0 (f4 (f12 ?v2) ?v1)) (= (f59 ?v1) f1)))))))
(assert (forall ((?v0 S3) (?v1 S5)) (=> (= (f59 ?v0) f1) (=> (= (f6 ?v1 f26) f1) (=> (forall ((?v2 S2) (?v3 S3)) (=> (= (f59 ?v3) f1) (=> (not (= (f6 (f7 ?v2) ?v3) f1)) (=> (= (f6 ?v1 ?v3) f1) (= (f6 ?v1 (f4 (f12 ?v2) ?v3)) f1))))) (= (f6 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S26) (?v2 S2)) (=> (= (f59 ?v0) f1) (exists ((?v3 S2)) (= (f3 (f4 (f55 (f56 ?v1) ?v2) ?v0) ?v3) f1)))))
(assert (forall ((?v0 S26) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f47 ?v0) ?v1) ?v2) f1) (exists ((?v3 S2) (?v4 S3) (?v5 S2)) (and (= ?v1 (f4 (f12 ?v3) ?v4)) (and (= ?v2 ?v5) (and (= (f3 (f4 (f55 (f56 ?v0) ?v3) ?v4) ?v5) f1) (not (= (f6 (f7 ?v3) ?v4) f1)))))))))
(assert (forall ((?v0 S26) (?v1 S2) (?v2 S3) (?v3 S2)) (= (= (f3 (f4 (f55 (f56 ?v0) ?v1) ?v2) ?v3) f1) (or (and (= ?v2 f26) (= ?v3 ?v1)) (exists ((?v4 S2) (?v5 S3) (?v6 S2)) (and (= ?v2 (f4 (f12 ?v4) ?v5)) (and (= ?v3 (f60 (f61 ?v0 ?v4) ?v6)) (and (not (= (f6 (f7 ?v4) ?v5) f1)) (= (f3 (f4 (f55 (f56 ?v0) ?v1) ?v5) ?v6) f1)))))))))
(assert (forall ((?v0 S26) (?v1 S18) (?v2 S3) (?v3 S2)) (=> (= (f63 ?v0 ?v1) f1) (=> (= (f59 ?v2) f1) (=> (not (= ?v2 f26)) (= (f30 ?v1 (f4 (f12 ?v3) ?v2)) (f60 (f61 ?v0 ?v3) (f30 ?v1 ?v2))))))))
(assert (forall ((?v0 S3) (?v1 S5)) (=> (= (f59 ?v0) f1) (=> (not (= ?v0 f26)) (=> (forall ((?v2 S2)) (= (f6 ?v1 (f4 (f12 ?v2) f26)) f1)) (=> (forall ((?v2 S2) (?v3 S3)) (=> (= (f59 ?v3) f1) (=> (not (= ?v3 f26)) (=> (not (= (f6 (f7 ?v2) ?v3) f1)) (=> (= (f6 ?v1 ?v3) f1) (= (f6 ?v1 (f4 (f12 ?v2) ?v3)) f1)))))) (= (f6 ?v1 ?v0) f1)))))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f57 f62 (f34 (f35 f36 ?v0) ?v1)) (f40 (f64 f65 (f40 (f64 f65 (f57 f62 ?v0)) (f57 f62 ?v1))) (f40 f41 f46)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (= (= (f40 (f64 f65 ?v0) ?v1) (f40 (f64 f65 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (let ((?v_0 (f64 f65 ?v0))) (= (= (f40 ?v_0 ?v1) (f40 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (let ((?v_0 (f64 f65 ?v0))) (= (f40 (f64 f65 (f40 ?v_0 ?v1)) ?v2) (f40 ?v_0 (f40 (f64 f65 ?v1) ?v2))))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (let ((?v_1 (f64 f65 ?v0)) (?v_0 (f64 f65 ?v1))) (= (f40 ?v_1 (f40 ?v_0 ?v2)) (f40 ?v_0 (f40 ?v_1 ?v2))))))
(assert (forall ((?v0 S22) (?v1 S22)) (= (f40 (f64 f65 ?v0) ?v1) (f40 (f64 f65 ?v1) ?v0))))
(assert (forall ((?v0 S26) (?v1 S18) (?v2 S2)) (=> (= (f63 ?v0 ?v1) f1) (= (f60 (f61 ?v0 ?v2) ?v2) ?v2))))
(assert (forall ((?v0 S22) (?v1 S22)) (let ((?v_0 (f64 f65 ?v0))) (= (f40 ?v_0 (f40 f41 ?v1)) (f40 f41 (f40 ?v_0 ?v1))))))
(assert (forall ((?v0 S22) (?v1 S22)) (= (f40 (f64 f65 (f40 f41 ?v0)) ?v1) (f40 f41 (f40 (f64 f65 ?v0) ?v1)))))
(assert (forall ((?v0 S22) (?v1 S22)) (= (f40 (f64 f65 (f40 f41 ?v0)) ?v1) (f40 (f64 f65 ?v0) (f40 f41 ?v1)))))
(assert (forall ((?v0 S22)) (= (f40 (f64 f65 f46) ?v0) ?v0)))
(assert (forall ((?v0 S22)) (= (f40 (f64 f65 ?v0) f46) ?v0)))
(assert (forall ((?v0 S22) (?v1 S22)) (= (= (f40 (f64 f65 ?v0) ?v1) f46) (and (= ?v0 f46) (= ?v1 f46)))))
(assert (forall ((?v0 S22) (?v1 S22)) (=> (= (f40 (f64 f65 ?v0) ?v1) ?v0) (= ?v1 f46))))
(assert (forall ((?v0 S22) (?v1 S22)) (let ((?v_0 (f40 f41 f46))) (= (= (f40 (f64 f65 ?v0) ?v1) ?v_0) (or (and (= ?v0 ?v_0) (= ?v1 f46)) (and (= ?v0 f46) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S22) (?v1 S22)) (let ((?v_0 (f40 f41 f46))) (= (= ?v_0 (f40 (f64 f65 ?v0) ?v1)) (or (and (= ?v0 ?v_0) (= ?v1 f46)) (and (= ?v0 f46) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S26) (?v1 S18) (?v2 S3) (?v3 S2)) (let ((?v_0 (f30 ?v1 ?v2))) (=> (= (f63 ?v0 ?v1) f1) (=> (= (f59 ?v2) f1) (=> (= (f6 (f7 ?v3) ?v2) f1) (= (f60 (f61 ?v0 ?v3) ?v_0) ?v_0)))))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f57 f58 (f34 (f35 f36 ?v0) ?v1)) (f40 (f64 f65 (f40 (f64 f65 (f57 f58 ?v0)) (f57 f58 ?v1))) (f40 f41 f46)))))
(assert (forall ((?v0 S35)) (= (= (f66 (f67 f68 ?v0) ?v0) f69) (= ?v0 f69))))
(assert (forall ((?v0 S22) (?v1 S22)) (= (= ?v0 (f40 (f64 f65 ?v0) ?v1)) (= ?v1 f46))))
(assert (forall ((?v0 S35) (?v1 S35)) (= (= ?v0 (f66 (f67 f68 ?v0) ?v1)) (= ?v1 f69))))
(assert (forall ((?v0 S22)) (= (f40 (f64 f65 ?v0) f46) ?v0)))
(assert (forall ((?v0 S35)) (= (f66 (f67 f68 ?v0) f69) ?v0)))
(assert (forall ((?v0 S22)) (= (f40 (f64 f65 ?v0) f46) ?v0)))
(assert (forall ((?v0 S35)) (= (f66 (f67 f68 ?v0) f69) ?v0)))
(assert (forall ((?v0 S35)) (= (= f69 ?v0) (= ?v0 f69))))
(assert (forall ((?v0 S22)) (= (= f46 ?v0) (= ?v0 f46))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (=> (= (f40 (f64 f65 ?v0) ?v1) (f40 (f64 f65 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35)) (=> (= (f66 (f67 f68 ?v0) ?v1) (f66 (f67 f68 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (let ((?v_0 (f64 f65 ?v0))) (=> (= (f40 ?v_0 ?v1) (f40 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35)) (let ((?v_0 (f67 f68 ?v0))) (=> (= (f66 ?v_0 ?v1) (f66 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (let ((?v_0 (f64 f65 ?v0))) (=> (= (f40 ?v_0 ?v1) (f40 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35)) (let ((?v_0 (f67 f68 ?v0))) (=> (= (f66 ?v_0 ?v1) (f66 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22) (?v3 S22)) (let ((?v_0 (f64 f65 ?v0))) (= (f40 (f64 f65 (f40 ?v_0 ?v1)) (f40 (f64 f65 ?v2) ?v3)) (f40 (f64 f65 (f40 ?v_0 ?v2)) (f40 (f64 f65 ?v1) ?v3))))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35) (?v3 S35)) (let ((?v_0 (f67 f68 ?v0))) (= (f66 (f67 f68 (f66 ?v_0 ?v1)) (f66 (f67 f68 ?v2) ?v3)) (f66 (f67 f68 (f66 ?v_0 ?v2)) (f66 (f67 f68 ?v1) ?v3))))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (= (= (f40 (f64 f65 ?v0) ?v1) (f40 (f64 f65 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35)) (= (= (f66 (f67 f68 ?v0) ?v1) (f66 (f67 f68 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (let ((?v_0 (f64 f65 ?v0))) (= (= (f40 ?v_0 ?v1) (f40 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35)) (let ((?v_0 (f67 f68 ?v0))) (= (= (f66 ?v_0 ?v1) (f66 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (let ((?v_0 (f64 f65 ?v0))) (= (f40 (f64 f65 (f40 ?v_0 ?v1)) ?v2) (f40 (f64 f65 (f40 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35)) (let ((?v_0 (f67 f68 ?v0))) (= (f66 (f67 f68 (f66 ?v_0 ?v1)) ?v2) (f66 (f67 f68 (f66 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (let ((?v_0 (f64 f65 ?v0))) (= (f40 (f64 f65 (f40 ?v_0 ?v1)) ?v2) (f40 ?v_0 (f40 (f64 f65 ?v1) ?v2))))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35)) (let ((?v_0 (f67 f68 ?v0))) (= (f66 (f67 f68 (f66 ?v_0 ?v1)) ?v2) (f66 ?v_0 (f66 (f67 f68 ?v1) ?v2))))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (let ((?v_0 (f64 f65 ?v0))) (= (f40 (f64 f65 (f40 ?v_0 ?v1)) ?v2) (f40 ?v_0 (f40 (f64 f65 ?v1) ?v2))))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35)) (let ((?v_0 (f67 f68 ?v0))) (= (f66 (f67 f68 (f66 ?v_0 ?v1)) ?v2) (f66 ?v_0 (f66 (f67 f68 ?v1) ?v2))))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (let ((?v_0 (f64 f65 ?v0))) (= (f40 ?v_0 (f40 (f64 f65 ?v1) ?v2)) (f40 (f64 f65 (f40 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35)) (let ((?v_0 (f67 f68 ?v0))) (= (f66 ?v_0 (f66 (f67 f68 ?v1) ?v2)) (f66 (f67 f68 (f66 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22)) (let ((?v_1 (f64 f65 ?v0)) (?v_0 (f64 f65 ?v1))) (= (f40 ?v_1 (f40 ?v_0 ?v2)) (f40 ?v_0 (f40 ?v_1 ?v2))))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35)) (let ((?v_1 (f67 f68 ?v0)) (?v_0 (f67 f68 ?v1))) (= (f66 ?v_1 (f66 ?v_0 ?v2)) (f66 ?v_0 (f66 ?v_1 ?v2))))))
(assert (forall ((?v0 S22) (?v1 S22)) (= (f40 (f64 f65 ?v0) ?v1) (f40 (f64 f65 ?v1) ?v0))))
(assert (forall ((?v0 S35) (?v1 S35)) (= (f66 (f67 f68 ?v0) ?v1) (f66 (f67 f68 ?v1) ?v0))))
(assert (forall ((?v0 S22)) (= (f40 (f64 f65 f46) ?v0) ?v0)))
(assert (forall ((?v0 S35)) (= (f66 (f67 f68 f69) ?v0) ?v0)))
(assert (forall ((?v0 S22)) (= (f40 (f64 f65 f46) ?v0) ?v0)))
(assert (forall ((?v0 S35)) (= (f66 (f67 f68 f69) ?v0) ?v0)))
(assert (forall ((?v0 S22)) (= (f40 (f64 f65 f46) ?v0) ?v0)))
(assert (forall ((?v0 S35)) (= (f66 (f67 f68 f69) ?v0) ?v0)))
(assert (forall ((?v0 S35)) (= (= f69 (f66 (f67 f68 ?v0) ?v0)) (= ?v0 f69))))
(assert (forall ((?v0 S22)) (= (f40 (f64 f65 ?v0) f46) ?v0)))
(assert (forall ((?v0 S35)) (= (f66 (f67 f68 ?v0) f69) ?v0)))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S9)) (= (f57 f58 (f34 (f35 (f70 f71 ?v0) ?v1) ?v2)) (f40 (f64 f65 (f40 (f64 f65 (f57 f58 ?v1)) (f57 f58 ?v2))) (f40 f41 f46)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S9)) (= (f57 f62 (f34 (f35 (f70 f71 ?v0) ?v1) ?v2)) (f40 (f64 f65 (f40 (f64 f65 (f57 f62 ?v1)) (f57 f62 ?v2))) (f40 f41 f46)))))
(assert (forall ((?v0 S39) (?v1 S40) (?v2 S9)) (= (f57 f58 (f34 (f72 (f73 f74 ?v0) ?v1) ?v2)) (f40 (f64 f65 (f57 f58 ?v2)) (f40 f41 f46)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S9) (?v3 S16) (?v4 S22) (?v5 S16)) (let ((?v_0 (= (f27 ?v0 ?v3) f1))) (=> (= (f27 (f43 (f44 (f45 (f34 (f35 (f70 f71 ?v0) ?v1) ?v2)) ?v3) ?v4) ?v5) f1) (=> (=> ?v_0 (=> (= (f27 (f43 (f44 (f45 ?v1) ?v3) ?v4) ?v5) f1) false)) (=> (=> (not ?v_0) (=> (= (f27 (f43 (f44 (f45 ?v2) ?v3) ?v4) ?v5) f1) false)) false))))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S9) (?v3 S22) (?v4 S16) (?v5 S9)) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f27 (f43 (f44 (f45 ?v2) ?v1) ?v3) ?v4) f1) (= (f27 (f43 (f44 (f45 (f34 (f35 (f70 f71 ?v0) ?v2) ?v5)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S9) (?v3 S22) (?v4 S16) (?v5 S9)) (=> (not (= (f27 ?v0 ?v1) f1)) (=> (= (f27 (f43 (f44 (f45 ?v2) ?v1) ?v3) ?v4) f1) (= (f27 (f43 (f44 (f45 (f34 (f35 (f70 f71 ?v0) ?v5) ?v2)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S9) (?v3 S16) (?v4 S9)) (=> (not (= (f27 ?v0 ?v1) f1)) (=> (= (f27 (f37 (f38 ?v2) ?v1) ?v3) f1) (= (f27 (f37 (f38 (f34 (f35 (f70 f71 ?v0) ?v4) ?v2)) ?v1) ?v3) f1)))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S9) (?v3 S16) (?v4 S9)) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f27 (f37 (f38 ?v2) ?v1) ?v3) f1) (= (f27 (f37 (f38 (f34 (f35 (f70 f71 ?v0) ?v2) ?v4)) ?v1) ?v3) f1)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S9) (?v3 S16) (?v4 S16)) (let ((?v_0 (= (f27 ?v0 ?v3) f1))) (=> (= (f27 (f37 (f38 (f34 (f35 (f70 f71 ?v0) ?v1) ?v2)) ?v3) ?v4) f1) (=> (=> ?v_0 (=> (= (f27 (f37 (f38 ?v1) ?v3) ?v4) f1) false)) (=> (=> (not ?v_0) (=> (= (f27 (f37 (f38 ?v2) ?v3) ?v4) f1) false)) false))))))
(assert (forall ((?v0 S12) (?v1 S39) (?v2 S40) (?v3 S9)) (not (= (f18 f19 ?v0) (f34 (f72 (f73 f74 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S39) (?v1 S40) (?v2 S9) (?v3 S12)) (not (= (f34 (f72 (f73 f74 ?v0) ?v1) ?v2) (f18 f19 ?v3)))))
(assert (forall ((?v0 S12) (?v1 S17) (?v2 S9) (?v3 S9)) (not (= (f18 f19 ?v0) (f34 (f35 (f70 f71 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S9) (?v3 S12)) (not (= (f34 (f35 (f70 f71 ?v0) ?v1) ?v2) (f18 f19 ?v3)))))
(assert (forall ((?v0 S39) (?v1 S40) (?v2 S9) (?v3 S9) (?v4 S9)) (not (= (f34 (f72 (f73 f74 ?v0) ?v1) ?v2) (f34 (f35 f36 ?v3) ?v4)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S39) (?v3 S40) (?v4 S9)) (not (= (f34 (f35 f36 ?v0) ?v1) (f34 (f72 (f73 f74 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S39) (?v1 S40) (?v2 S9)) (not (= (f34 (f72 (f73 f74 ?v0) ?v1) ?v2) f33))))
(assert (forall ((?v0 S39) (?v1 S40) (?v2 S9)) (not (= f33 (f34 (f72 (f73 f74 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S9) (?v3 S9) (?v4 S9)) (not (= (f34 (f35 (f70 f71 ?v0) ?v1) ?v2) (f34 (f35 f36 ?v3) ?v4)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S17) (?v3 S9) (?v4 S9)) (not (= (f34 (f35 f36 ?v0) ?v1) (f34 (f35 (f70 f71 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S9)) (not (= (f34 (f35 (f70 f71 ?v0) ?v1) ?v2) f33))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S9)) (not (= f33 (f34 (f35 (f70 f71 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S39) (?v1 S40) (?v2 S9) (?v3 S39) (?v4 S40) (?v5 S9)) (= (= (f34 (f72 (f73 f74 ?v0) ?v1) ?v2) (f34 (f72 (f73 f74 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S9) (?v3 S17) (?v4 S9) (?v5 S9)) (= (= (f34 (f35 (f70 f71 ?v0) ?v1) ?v2) (f34 (f35 (f70 f71 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S39) (?v1 S40) (?v2 S9) (?v3 S17) (?v4 S9) (?v5 S9)) (not (= (f34 (f72 (f73 f74 ?v0) ?v1) ?v2) (f34 (f35 (f70 f71 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S9) (?v3 S39) (?v4 S40) (?v5 S9)) (not (= (f34 (f35 (f70 f71 ?v0) ?v1) ?v2) (f34 (f72 (f73 f74 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S39) (?v1 S40) (?v2 S9)) (= (f57 f62 (f34 (f72 (f73 f74 ?v0) ?v1) ?v2)) (f40 (f64 f65 (f57 f62 ?v2)) (f40 f41 f46)))))
(assert (forall ((?v0 S17) (?v1 S9)) (= (f57 f62 (f34 (f75 f76 ?v0) ?v1)) (f40 (f64 f65 (f57 f62 ?v1)) (f40 f41 f46)))))
(assert (forall ((?v0 S17) (?v1 S9)) (= (f57 f58 (f34 (f75 f76 ?v0) ?v1)) (f40 (f64 f65 (f57 f58 ?v1)) (f40 f41 f46)))))
(assert (forall ((?v0 S22)) (= (f40 f77 (f40 f41 ?v0)) (f40 (f64 f65 (f40 f77 ?v0)) (f40 f41 f46)))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S9) (?v3 S22) (?v4 S16) (?v5 S16)) (let ((?v_0 (f45 (f34 (f75 f76 ?v0) ?v2)))) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f27 (f43 (f44 (f45 ?v2) ?v1) ?v3) ?v4) f1) (=> (= (f27 (f43 (f44 ?v_0 ?v4) ?v3) ?v5) f1) (= (f27 (f43 (f44 ?v_0 ?v1) ?v3) ?v5) f1)))))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S9) (?v3 S22)) (=> (not (= (f27 ?v0 ?v1) f1)) (= (f27 (f43 (f44 (f45 (f34 (f75 f76 ?v0) ?v2)) ?v1) ?v3) ?v1) f1))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S9)) (=> (not (= (f27 ?v0 ?v1) f1)) (= (f27 (f37 (f38 (f34 (f75 f76 ?v0) ?v2)) ?v1) ?v1) f1))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S9) (?v3 S16) (?v4 S16)) (let ((?v_0 (f38 (f34 (f75 f76 ?v0) ?v2)))) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f27 (f37 (f38 ?v2) ?v1) ?v3) f1) (=> (= (f27 (f37 ?v_0 ?v3) ?v4) f1) (= (f27 (f37 ?v_0 ?v1) ?v4) f1)))))))
(assert (forall ((?v0 S39) (?v1 S40) (?v2 S9) (?v3 S17) (?v4 S9)) (not (= (f34 (f72 (f73 f74 ?v0) ?v1) ?v2) (f34 (f75 f76 ?v3) ?v4)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S9) (?v3 S17) (?v4 S9)) (not (= (f34 (f35 (f70 f71 ?v0) ?v1) ?v2) (f34 (f75 f76 ?v3) ?v4)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S39) (?v3 S40) (?v4 S9)) (not (= (f34 (f75 f76 ?v0) ?v1) (f34 (f72 (f73 f74 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S17) (?v3 S9) (?v4 S9)) (not (= (f34 (f75 f76 ?v0) ?v1) (f34 (f35 (f70 f71 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S12)) (not (= (f34 (f75 f76 ?v0) ?v1) (f18 f19 ?v2)))))
(assert (forall ((?v0 S12) (?v1 S17) (?v2 S9)) (not (= (f18 f19 ?v0) (f34 (f75 f76 ?v1) ?v2)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S17) (?v3 S9)) (= (= (f34 (f75 f76 ?v0) ?v1) (f34 (f75 f76 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S17) (?v1 S9)) (not (= f33 (f34 (f75 f76 ?v0) ?v1)))))
(assert (forall ((?v0 S17) (?v1 S9)) (not (= (f34 (f75 f76 ?v0) ?v1) f33))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S17) (?v3 S9)) (not (= (f34 (f35 f36 ?v0) ?v1) (f34 (f75 f76 ?v2) ?v3)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S9) (?v3 S9)) (not (= (f34 (f75 f76 ?v0) ?v1) (f34 (f35 f36 ?v2) ?v3)))))
(assert (= (f40 f77 f46) f46))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S16) (?v3 S16)) (=> (= (f27 (f37 (f38 (f34 (f75 f76 ?v0) ?v1)) ?v2) ?v3) f1) (=> (=> (= ?v3 ?v2) (=> (not (= (f27 ?v0 ?v2) f1)) false)) (=> (forall ((?v4 S16)) (=> (= (f27 ?v0 ?v2) f1) (=> (= (f27 (f37 (f38 ?v1) ?v2) ?v4) f1) (=> (= (f27 (f37 (f38 (f34 (f75 f76 ?v0) ?v1)) ?v4) ?v3) f1) false)))) false)))))
(assert (forall ((?v0 S17) (?v1 S9) (?v2 S16) (?v3 S22) (?v4 S16)) (=> (= (f27 (f43 (f44 (f45 (f34 (f75 f76 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (=> (= ?v4 ?v2) (=> (not (= (f27 ?v0 ?v2) f1)) false)) (=> (forall ((?v5 S16)) (=> (= (f27 ?v0 ?v2) f1) (=> (= (f27 (f43 (f44 (f45 ?v1) ?v2) ?v3) ?v5) f1) (=> (= (f27 (f43 (f44 (f45 (f34 (f75 f76 ?v0) ?v1)) ?v5) ?v3) ?v4) f1) false)))) false)))))
(assert (forall ((?v0 S22)) (= (f40 f78 (f40 f41 ?v0)) (f40 (f64 f65 (f40 f78 ?v0)) (f40 f41 f46)))))
(assert (= (f79 f80 f2) f46))
(assert (= (f40 f78 f46) f46))
(assert (forall ((?v0 S22)) (= (f40 f78 ?v0) ?v0)))
(assert (= (f79 f80 f1) f46))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S45)) (=> (= (f59 ?v0) f1) (=> (= (f59 ?v1) f1) (=> (not (= ?v1 f26)) (=> (forall ((?v3 S2)) (=> (= (f6 (f7 ?v3) ?v0) f1) (exists ((?v4 S2)) (and (= (f6 (f7 ?v4) ?v1) f1) (= (f3 (f81 ?v2 ?v3) ?v4) f1))))) (= (f6 (f82 (f83 ?v2) ?v0) ?v1) f1)))))))
(assert (forall ((?v0 S26) (?v1 S18) (?v2 S3) (?v3 S2)) (let ((?v_0 (f12 ?v3))) (let ((?v_1 (f4 (f84 ?v2) (f4 ?v_0 f26)))) (=> (= (f48 ?v0 ?v1) f1) (=> (= (f59 ?v2) f1) (= (f30 ?v1 (f4 ?v_0 ?v2)) (ite (= ?v_1 f26) ?v3 (f60 (f61 ?v0 ?v3) (f30 ?v1 ?v_1))))))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f84 ?v1) ?v2)) f1) (=> (=> (= (f6 ?v_0 ?v1) f1) (=> (not (= (f6 ?v_0 ?v2) f1)) false)) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 ?v1) f1) (=> (not (= (f6 ?v_0 ?v2) f1)) (= (f6 ?v_0 (f4 (f84 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f59 ?v0) f1) (= (f59 (f4 (f84 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S35) (?v1 S35)) (= (f66 (f67 f68 (f66 (f67 f85 ?v0) ?v1)) ?v1) ?v0)))
(assert (forall ((?v0 S35) (?v1 S35)) (= (f66 (f67 f85 (f66 (f67 f68 ?v0) ?v1)) ?v1) ?v0)))
(assert (forall ((?v0 S35)) (= (f66 (f67 f85 ?v0) f69) ?v0)))
(assert (forall ((?v0 S35)) (= (f66 (f67 f85 ?v0) ?v0) f69)))
(assert (forall ((?v0 S35) (?v1 S35)) (= (= ?v0 ?v1) (= (f66 (f67 f85 ?v0) ?v1) f69))))
(assert (forall ((?v0 S35) (?v1 S35)) (= (= (f66 (f67 f85 ?v0) ?v1) f69) (= ?v0 ?v1))))
(assert (forall ((?v0 S35) (?v1 S35) (?v2 S35) (?v3 S35)) (=> (= (f66 (f67 f85 ?v0) ?v1) (f66 (f67 f85 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f59 ?v0) f1) (= (= (f59 (f4 (f84 ?v1) ?v0)) f1) (= (f59 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f84 ?v1) ?v2)) f1) (=> (= (f6 ?v_0 ?v2) f1) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f84 ?v1) ?v2)) f1) (= (f6 ?v_0 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 (f84 ?v0) ?v1))) (= (f4 (f84 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (= (= (f6 ?v_0 (f4 (f84 ?v1) ?v2)) f1) (and (= (f6 ?v_0 ?v1) f1) (not (= (f6 ?v_0 ?v2) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f4 (f84 ?v0) ?v1) (f29 (f4 (f8 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 ?v0)) (?v_1 (f4 (f84 ?v1) ?v2))) (= (f4 (f84 (f4 ?v_0 ?v1)) ?v2) (ite (= (f6 (f7 ?v0) ?v2) f1) ?v_1 (f4 ?v_0 ?v_1))))))
(check-sat)
(exit)