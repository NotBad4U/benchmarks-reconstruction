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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S4 S5 S6 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 () S4)
(declare-fun f6 () S5)
(declare-fun f7 (S7 S6) S6)
(declare-fun f8 () S7)
(declare-fun f9 (S8 S9) S6)
(declare-fun f10 () S8)
(declare-fun f11 (S10 S11) S9)
(declare-fun f12 () S10)
(declare-fun f13 (S12 S13) S11)
(declare-fun f14 () S12)
(declare-fun f15 () S13)
(declare-fun f16 (S3 S2 S2) S1)
(declare-fun f17 () S2)
(declare-fun f18 (S4 S11) S14)
(declare-fun f19 (S15) S4)
(declare-fun f20 (S16 S17) S15)
(declare-fun f21 (S18 S4) S16)
(declare-fun f22 () S18)
(declare-fun f23 () S17)
(declare-fun f24 () S11)
(declare-fun f25 (S19) S14)
(declare-fun f26 (S13 S20) S19)
(declare-fun f27 () S13)
(declare-fun f28 () S20)
(declare-fun f29 (S21 S22) S1)
(declare-fun f30 (S23 S13) S21)
(declare-fun f31 (S24 S13) S23)
(declare-fun f32 () S24)
(declare-fun f33 () S13)
(declare-fun f34 (S22) S22)
(declare-fun f35 (S3) S22)
(declare-fun f36 (S3 S5 S15) S1)
(declare-fun f37 (S25 S13) S7)
(declare-fun f38 () S25)
(declare-fun f39 (S26 S3) S1)
(declare-fun f40 () S26)
(declare-fun f41 (S6) S1)
(declare-fun f42 (S2) S1)
(declare-fun f43 (S29 S28) S1)
(declare-fun f44 (S30 S27) S29)
(declare-fun f45 (S31 S27) S30)
(declare-fun f46 () S31)
(declare-fun f47 (S28) S28)
(declare-fun f48 (S3 S6 S15 S6 S15) S1)
(declare-fun f49 (S32 S13) S1)
(declare-fun f50 (S33 S13) S32)
(declare-fun f51 (S3) S33)
(declare-fun f52 (S34 S2) S32)
(declare-fun f53 (S35 S13) S34)
(declare-fun f54 (S36 S13) S35)
(declare-fun f55 (S3) S36)
(declare-fun f56 (S3) S36)
(declare-fun f57 (S37 S13) S25)
(declare-fun f58 (S38 S6) S37)
(declare-fun f59 () S38)
(declare-fun f60 (S39 S15) S27)
(declare-fun f61 (S40 S6) S39)
(declare-fun f62 () S40)
(declare-fun f63 (S3) S28)
(declare-fun f64 (S41 S27) S1)
(assert (not (= f1 f2)))
(assert (not (exists ((?v0 S2)) (and (= (f3 f4 f5 f6 (f7 f8 (f9 f10 (f11 f12 (f13 f14 f15)))) ?v0) f1) (= (f16 f4 ?v0 f17) f1)))))
(assert (= (f18 (f19 (f20 (f21 f22 f5) f23)) f24) (f25 (f26 f27 f28))))
(assert (not (= (f29 (f30 (f31 f32 f27) f33) (f34 (f35 f4))) f1)))
(assert (= (f36 f4 f6 (f20 (f21 f22 f5) f23)) f1))
(assert (= (f3 f4 f5 f6 (f7 (f37 f38 f33) (f9 f10 (f11 f12 f24))) f17) f1))
(assert (not (= (f29 (f30 (f31 f32 f27) f33) (f34 (f35 f4))) f1)))
(assert (= (f36 f4 f6 (f20 (f21 f22 f5) f23)) f1))
(assert (= (f18 (f19 (f20 (f21 f22 f5) f23)) f24) (f25 (f26 f27 f28))))
(assert (= (f3 f4 f5 f6 (f7 (f37 f38 f33) (f9 f10 (f11 f12 f24))) f17) f1))
(assert (= (f39 f40 f4) f1))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f16 ?v0 ?v1 ?v1) f1)))
(assert (forall ((?v0 S9) (?v1 S6)) (not (= (f9 f10 ?v0) (f7 f8 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S9)) (not (= (f7 f8 ?v0) (f9 f10 ?v1)))))
(assert (forall ((?v0 S6)) (= (= (f41 ?v0) f1) (or (exists ((?v1 S9)) (= ?v0 (f9 f10 ?v1))) (exists ((?v1 S11)) (= ?v0 (f7 f8 (f9 f10 (f11 f12 ?v1)))))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f16 ?v0 ?v1 ?v2) f1) (=> (= (f16 ?v0 ?v2 ?v3) f1) (= (f16 ?v0 ?v1 ?v3) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f11 f12 ?v0) (f11 f12 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f7 f8 ?v0) (f7 f8 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f9 f10 ?v0) (f9 f10 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S5) (?v3 S6) (?v4 S2) (?v5 S2)) (=> (= (f3 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f42 ?v4) f1) (= (f3 ?v0 ?v1 ?v2 (f7 f8 ?v3) ?v5) f1)))))
(assert (forall ((?v0 S6)) (=> (= (f41 ?v0) f1) (=> (forall ((?v1 S9)) (=> (= ?v0 (f9 f10 ?v1)) false)) (=> (forall ((?v1 S11)) (=> (= ?v0 (f7 f8 (f9 f10 (f11 f12 ?v1)))) false)) false)))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S5) (?v3 S6) (?v4 S2)) (=> (= (f3 ?v0 ?v1 ?v2 (f7 f8 ?v3) ?v4) f1) (=> (forall ((?v5 S2)) (=> (= (f3 ?v0 ?v1 ?v2 ?v3 ?v5) f1) (=> (= (f42 ?v5) f1) false))) false))))
(assert (forall ((?v0 S13) (?v1 S6) (?v2 S13) (?v3 S6)) (= (= (f7 (f37 f38 ?v0) ?v1) (f7 (f37 f38 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S13) (?v1 S6) (?v2 S9)) (not (= (f7 (f37 f38 ?v0) ?v1) (f9 f10 ?v2)))))
(assert (forall ((?v0 S9) (?v1 S13) (?v2 S6)) (not (= (f9 f10 ?v0) (f7 (f37 f38 ?v1) ?v2)))))
(assert (forall ((?v0 S13) (?v1 S6) (?v2 S6)) (not (= (f7 (f37 f38 ?v0) ?v1) (f7 f8 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S13) (?v2 S6)) (not (= (f7 f8 ?v0) (f7 (f37 f38 ?v1) ?v2)))))
(assert (forall ((?v0 S13) (?v1 S22)) (= (f29 (f30 (f31 f32 ?v0) ?v0) (f34 ?v1)) f1)))
(assert (forall ((?v0 S27) (?v1 S28)) (= (f43 (f44 (f45 f46 ?v0) ?v0) (f47 ?v1)) f1)))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S15) (?v3 S11) (?v4 S4) (?v5 S17) (?v6 S13) (?v7 S20) (?v8 S13)) (let ((?v_0 (f20 (f21 f22 ?v4) ?v5))) (=> (= (f48 ?v0 ?v1 ?v2 (f9 f10 (f11 f12 ?v3)) ?v_0) f1) (=> (= (f18 ?v4 ?v3) (f25 (f26 ?v6 ?v7))) (=> (not (= (f29 (f30 (f31 f32 ?v6) ?v8) (f34 (f35 ?v0))) f1)) (= (f48 ?v0 (f7 (f37 f38 ?v8) ?v1) ?v2 (f7 f8 (f9 f10 (f11 f12 (f13 f14 f15)))) ?v_0) f1)))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S15) (?v3 S11) (?v4 S4) (?v5 S17) (?v6 S13) (?v7 S20) (?v8 S13)) (let ((?v_0 (f9 f10 (f11 f12 ?v3))) (?v_1 (f20 (f21 f22 ?v4) ?v5))) (=> (= (f48 ?v0 ?v1 ?v2 ?v_0 ?v_1) f1) (=> (= (f18 ?v4 ?v3) (f25 (f26 ?v6 ?v7))) (=> (= (f29 (f30 (f31 f32 ?v6) ?v8) (f34 (f35 ?v0))) f1) (= (f48 ?v0 (f7 (f37 f38 ?v8) ?v1) ?v2 ?v_0 ?v_1) f1)))))))
(assert (forall ((?v0 S21) (?v1 S22)) (=> (= (f29 ?v0 ?v1) f1) (= (f29 ?v0 (f34 ?v1)) f1))))
(assert (forall ((?v0 S29) (?v1 S28)) (=> (= (f43 ?v0 ?v1) f1) (= (f43 ?v0 (f47 ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S13) (?v2 S13)) (= (= (f49 (f50 (f51 ?v0) ?v1) ?v2) f1) (= (f29 (f30 (f31 f32 ?v1) ?v2) (f35 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S13) (?v2 S13) (?v3 S2) (?v4 S13) (?v5 S13)) (let ((?v_0 (f55 ?v0))) (=> (= (f49 (f52 (f53 (f54 ?v_0 ?v1) ?v2) ?v3) ?v4) f1) (=> (= (f29 (f30 (f31 f32 ?v5) ?v1) (f34 (f35 ?v0))) f1) (= (f49 (f52 (f53 (f54 ?v_0 ?v5) ?v2) ?v3) ?v4) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S22) (?v3 S13)) (let ((?v_0 (f31 f32 ?v0)) (?v_1 (f34 ?v2))) (=> (= (f29 (f30 ?v_0 ?v1) ?v2) f1) (=> (= (f29 (f30 (f31 f32 ?v1) ?v3) ?v_1) f1) (= (f29 (f30 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S28) (?v3 S27)) (let ((?v_0 (f45 f46 ?v0)) (?v_1 (f47 ?v2))) (=> (= (f43 (f44 ?v_0 ?v1) ?v2) f1) (=> (= (f43 (f44 (f45 f46 ?v1) ?v3) ?v_1) f1) (= (f43 (f44 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S22) (?v3 S13)) (let ((?v_0 (f31 f32 ?v0)) (?v_1 (f34 ?v2))) (=> (= (f29 (f30 ?v_0 ?v1) ?v_1) f1) (=> (= (f29 (f30 (f31 f32 ?v1) ?v3) ?v2) f1) (= (f29 (f30 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S28) (?v3 S27)) (let ((?v_0 (f45 f46 ?v0)) (?v_1 (f47 ?v2))) (=> (= (f43 (f44 ?v_0 ?v1) ?v_1) f1) (=> (= (f43 (f44 (f45 f46 ?v1) ?v3) ?v2) f1) (= (f43 (f44 ?v_0 ?v3) ?v_1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S22) (?v3 S13)) (let ((?v_1 (f31 f32 ?v0)) (?v_0 (f34 ?v2))) (=> (= (f29 (f30 ?v_1 ?v1) ?v_0) f1) (=> (= (f29 (f30 (f31 f32 ?v1) ?v3) ?v_0) f1) (= (f29 (f30 ?v_1 ?v3) ?v_0) f1))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S28) (?v3 S27)) (let ((?v_1 (f45 f46 ?v0)) (?v_0 (f47 ?v2))) (=> (= (f43 (f44 ?v_1 ?v1) ?v_0) f1) (=> (= (f43 (f44 (f45 f46 ?v1) ?v3) ?v_0) f1) (= (f43 (f44 ?v_1 ?v3) ?v_0) f1))))))
(assert (forall ((?v0 S3) (?v1 S13) (?v2 S13) (?v3 S2) (?v4 S13)) (=> (= (f49 (f52 (f53 (f54 (f56 ?v0) ?v1) ?v2) ?v3) ?v4) f1) (= (f29 (f30 (f31 f32 ?v1) ?v4) (f34 (f35 ?v0))) f1))))
(assert (forall ((?v0 S6) (?v1 S3) (?v2 S15)) (=> (= (f41 ?v0) f1) (= (f48 ?v1 ?v0 ?v2 ?v0 ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S15) (?v3 S6) (?v4 S15)) (=> (= (f48 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (= (f41 ?v3) f1))))
(assert (forall ((?v0 S3) (?v1 S13) (?v2 S13) (?v3 S2) (?v4 S13)) (=> (= (f49 (f52 (f53 (f54 (f56 ?v0) ?v1) ?v2) ?v3) ?v4) f1) (= (f49 (f52 (f53 (f54 (f55 ?v0) ?v1) ?v2) ?v3) ?v4) f1))))
(assert (forall ((?v0 S3) (?v1 S13) (?v2 S13) (?v3 S2) (?v4 S13)) (let ((?v_0 (f56 ?v0))) (=> (= (f49 (f52 (f53 (f54 ?v_0 ?v1) ?v2) ?v3) ?v4) f1) (= (f49 (f52 (f53 (f54 ?v_0 ?v4) ?v2) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S3) (?v1 S13) (?v2 S13) (?v3 S2) (?v4 S13) (?v5 S2) (?v6 S13)) (let ((?v_0 (f53 (f54 (f56 ?v0) ?v1) ?v2))) (=> (= (f49 (f52 ?v_0 ?v3) ?v4) f1) (=> (= (f49 (f52 ?v_0 ?v5) ?v6) f1) (and (= ?v5 ?v3) (= ?v6 ?v4)))))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S15)) (let ((?v_0 (f9 f10 ?v1))) (= (f48 ?v0 ?v_0 ?v2 ?v_0 ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S15) (?v3 S6) (?v4 S15)) (let ((?v_0 (f9 f10 ?v1))) (=> (= (f48 ?v0 ?v_0 ?v2 ?v3 ?v4) f1) (=> (=> (= ?v3 ?v_0) (=> (= ?v4 ?v2) false)) false)))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S15) (?v3 S6) (?v4 S15)) (let ((?v_0 (f7 f8 ?v3))) (=> (= (f48 ?v0 ?v1 ?v2 ?v_0 ?v4) f1) (= (f48 ?v0 (f7 f8 ?v1) ?v2 ?v_0 ?v4) f1)))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S15) (?v3 S6) (?v4 S15) (?v5 S13)) (let ((?v_0 (f7 f8 ?v3))) (=> (= (f48 ?v0 ?v1 ?v2 ?v_0 ?v4) f1) (= (f48 ?v0 (f7 (f37 f38 ?v5) ?v1) ?v2 ?v_0 ?v4) f1)))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S15) (?v3 S11) (?v4 S15)) (let ((?v_0 (f9 f10 (f11 f12 ?v3)))) (=> (= (f48 ?v0 ?v1 ?v2 ?v_0 ?v4) f1) (= (f48 ?v0 (f7 f8 ?v1) ?v2 (f7 f8 ?v_0) ?v4) f1)))))
(assert (forall ((?v0 S22)) (let ((?v_0 (f34 ?v0))) (= (f34 ?v_0) ?v_0))))
(assert (forall ((?v0 S28)) (let ((?v_0 (f47 ?v0))) (= (f47 ?v_0) ?v_0))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S15) (?v3 S11) (?v4 S4) (?v5 S17) (?v6 S13) (?v7 S20) (?v8 S13) (?v9 S13) (?v10 S6)) (let ((?v_0 (f7 f8 (f9 f10 (f11 f12 ?v3)))) (?v_1 (f20 (f21 f22 ?v4) ?v5))) (=> (= (f48 ?v0 ?v1 ?v2 ?v_0 ?v_1) f1) (=> (= (f18 ?v4 ?v3) (f25 (f26 ?v6 ?v7))) (=> (not (= (f29 (f30 (f31 f32 ?v6) ?v8) (f34 (f35 ?v0))) f1)) (= (f48 ?v0 (f7 (f37 (f57 (f58 f59 ?v1) ?v8) ?v9) ?v10) ?v2 ?v_0 ?v_1) f1)))))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S11) (?v3 S15) (?v4 S3) (?v5 S13) (?v6 S20) (?v7 S13)) (let ((?v_0 (f47 (f63 ?v4)))) (=> (= (f43 (f44 (f45 f46 (f60 (f61 f62 ?v0) ?v1)) (f60 (f61 f62 (f9 f10 (f11 f12 ?v2))) ?v3)) ?v_0) f1) (=> (= (f18 (f19 ?v3) ?v2) (f25 (f26 ?v5 ?v6))) (=> (not (= (f29 (f30 (f31 f32 ?v5) ?v7) (f34 (f35 ?v4))) f1)) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 (f37 f38 ?v7) ?v0)) ?v1)) (f60 (f61 f62 (f7 f8 (f9 f10 (f11 f12 (f13 f14 f15))))) ?v3)) ?v_0) f1)))))))
(assert (forall ((?v0 S15) (?v1 S11) (?v2 S13) (?v3 S20) (?v4 S13) (?v5 S3)) (=> (= (f18 (f19 ?v0) ?v1) (f25 (f26 ?v2 ?v3))) (=> (not (= (f29 (f30 (f31 f32 ?v2) ?v4) (f34 (f35 ?v5))) f1)) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 (f37 f38 ?v4) (f9 f10 (f11 f12 ?v1)))) ?v0)) (f60 (f61 f62 (f7 f8 (f9 f10 (f11 f12 (f13 f14 f15))))) ?v0)) (f63 ?v5)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S22)) (=> (= (f29 (f30 (f31 f32 ?v0) ?v1) (f34 ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (forall ((?v3 S13)) (=> (= (f29 (f30 (f31 f32 ?v0) ?v3) (f34 ?v2)) f1) (=> (= (f29 (f30 (f31 f32 ?v3) ?v1) ?v2) f1) false))) false)))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S28)) (=> (= (f43 (f44 (f45 f46 ?v0) ?v1) (f47 ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (forall ((?v3 S27)) (=> (= (f43 (f44 (f45 f46 ?v0) ?v3) (f47 ?v2)) f1) (=> (= (f43 (f44 (f45 f46 ?v3) ?v1) ?v2) f1) false))) false)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S22)) (=> (= (f29 (f30 (f31 f32 ?v0) ?v1) (f34 ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (forall ((?v3 S13)) (=> (= (f29 (f30 (f31 f32 ?v0) ?v3) ?v2) f1) (=> (= (f29 (f30 (f31 f32 ?v3) ?v1) (f34 ?v2)) f1) false))) false)))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S28)) (=> (= (f43 (f44 (f45 f46 ?v0) ?v1) (f47 ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (forall ((?v3 S27)) (=> (= (f43 (f44 (f45 f46 ?v0) ?v3) ?v2) f1) (=> (= (f43 (f44 (f45 f46 ?v3) ?v1) (f47 ?v2)) f1) false))) false)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S22) (?v3 S32)) (=> (= (f29 (f30 (f31 f32 ?v0) ?v1) (f34 ?v2)) f1) (=> (= (f49 ?v3 ?v1) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f29 (f30 (f31 f32 ?v4) ?v5) ?v2) f1) (=> (= (f29 (f30 (f31 f32 ?v5) ?v1) (f34 ?v2)) f1) (=> (= (f49 ?v3 ?v5) f1) (= (f49 ?v3 ?v4) f1))))) (= (f49 ?v3 ?v0) f1))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S28) (?v3 S41)) (=> (= (f43 (f44 (f45 f46 ?v0) ?v1) (f47 ?v2)) f1) (=> (= (f64 ?v3 ?v1) f1) (=> (forall ((?v4 S27) (?v5 S27)) (=> (= (f43 (f44 (f45 f46 ?v4) ?v5) ?v2) f1) (=> (= (f43 (f44 (f45 f46 ?v5) ?v1) (f47 ?v2)) f1) (=> (= (f64 ?v3 ?v5) f1) (= (f64 ?v3 ?v4) f1))))) (= (f64 ?v3 ?v0) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S22) (?v3 S32)) (=> (= (f29 (f30 (f31 f32 ?v0) ?v1) (f34 ?v2)) f1) (=> (= (f49 ?v3 ?v0) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f29 (f30 (f31 f32 ?v0) ?v4) (f34 ?v2)) f1) (=> (= (f29 (f30 (f31 f32 ?v4) ?v5) ?v2) f1) (=> (= (f49 ?v3 ?v4) f1) (= (f49 ?v3 ?v5) f1))))) (= (f49 ?v3 ?v1) f1))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S28) (?v3 S41)) (=> (= (f43 (f44 (f45 f46 ?v0) ?v1) (f47 ?v2)) f1) (=> (= (f64 ?v3 ?v0) f1) (=> (forall ((?v4 S27) (?v5 S27)) (=> (= (f43 (f44 (f45 f46 ?v0) ?v4) (f47 ?v2)) f1) (=> (= (f43 (f44 (f45 f46 ?v4) ?v5) ?v2) f1) (=> (= (f64 ?v3 ?v4) f1) (= (f64 ?v3 ?v5) f1))))) (= (f64 ?v3 ?v1) f1))))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S11) (?v3 S15) (?v4 S3) (?v5 S13) (?v6 S20) (?v7 S13)) (let ((?v_0 (f60 (f61 f62 (f9 f10 (f11 f12 ?v2))) ?v3)) (?v_1 (f47 (f63 ?v4)))) (=> (= (f43 (f44 (f45 f46 (f60 (f61 f62 ?v0) ?v1)) ?v_0) ?v_1) f1) (=> (= (f18 (f19 ?v3) ?v2) (f25 (f26 ?v5 ?v6))) (=> (= (f29 (f30 (f31 f32 ?v5) ?v7) (f34 (f35 ?v4))) f1) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 (f37 f38 ?v7) ?v0)) ?v1)) ?v_0) ?v_1) f1)))))))
(assert (forall ((?v0 S15) (?v1 S11) (?v2 S13) (?v3 S20) (?v4 S13) (?v5 S3)) (let ((?v_0 (f9 f10 (f11 f12 ?v1)))) (=> (= (f18 (f19 ?v0) ?v1) (f25 (f26 ?v2 ?v3))) (=> (= (f29 (f30 (f31 f32 ?v2) ?v4) (f34 (f35 ?v5))) f1) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 (f37 f38 ?v4) ?v_0)) ?v0)) (f60 (f61 f62 ?v_0) ?v0)) (f63 ?v5)) f1))))))
(assert (forall ((?v0 S9) (?v1 S13) (?v2 S13) (?v3 S6) (?v4 S15) (?v5 S3)) (let ((?v_0 (f9 f10 ?v0))) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 (f37 (f57 (f58 f59 ?v_0) ?v1) ?v2) ?v3)) ?v4)) (f60 (f61 f62 ?v_0) ?v4)) (f63 ?v5)) f1))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S6) (?v3 S15) (?v4 S3) (?v5 S13) (?v6 S13) (?v7 S6)) (let ((?v_0 (f63 ?v4))) (=> (= (f43 (f44 (f45 f46 (f60 (f61 f62 ?v0) ?v1)) (f60 (f61 f62 ?v2) ?v3)) ?v_0) f1) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 (f37 (f57 (f58 f59 ?v0) ?v5) ?v6) ?v7)) ?v1)) (f60 (f61 f62 (f7 (f37 (f57 (f58 f59 ?v2) ?v5) ?v6) ?v7)) ?v3)) ?v_0) f1)))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S6) (?v3 S15) (?v4 S3) (?v5 S13) (?v6 S13) (?v7 S6)) (let ((?v_0 (f47 (f63 ?v4)))) (=> (= (f43 (f44 (f45 f46 (f60 (f61 f62 ?v0) ?v1)) (f60 (f61 f62 ?v2) ?v3)) ?v_0) f1) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 (f37 (f57 (f58 f59 ?v0) ?v5) ?v6) ?v7)) ?v1)) (f60 (f61 f62 (f7 (f37 (f57 (f58 f59 ?v2) ?v5) ?v6) ?v7)) ?v3)) ?v_0) f1)))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S9) (?v3 S15) (?v4 S3) (?v5 S13) (?v6 S13) (?v7 S6)) (let ((?v_0 (f60 (f61 f62 (f9 f10 ?v2)) ?v3)) (?v_1 (f47 (f63 ?v4)))) (=> (= (f43 (f44 (f45 f46 (f60 (f61 f62 ?v0) ?v1)) ?v_0) ?v_1) f1) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 (f37 (f57 (f58 f59 ?v0) ?v5) ?v6) ?v7)) ?v1)) ?v_0) ?v_1) f1)))))
(assert (forall ((?v0 S6) (?v1 S13) (?v2 S13) (?v3 S6) (?v4 S6) (?v5 S13) (?v6 S13) (?v7 S6)) (= (= (f7 (f37 (f57 (f58 f59 ?v0) ?v1) ?v2) ?v3) (f7 (f37 (f57 (f58 f59 ?v4) ?v5) ?v6) ?v7)) (and (= ?v0 ?v4) (and (= ?v1 ?v5) (and (= ?v2 ?v6) (= ?v3 ?v7)))))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S6) (?v3 S15) (?v4 S3)) (let ((?v_0 (f60 (f61 f62 (f7 f8 ?v2)) ?v3)) (?v_1 (f47 (f63 ?v4)))) (=> (= (f43 (f44 (f45 f46 (f60 (f61 f62 ?v0) ?v1)) ?v_0) ?v_1) f1) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 f8 ?v0)) ?v1)) ?v_0) ?v_1) f1)))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S6) (?v3 S15) (?v4 S3)) (let ((?v_0 (f47 (f63 ?v4)))) (=> (= (f43 (f44 (f45 f46 (f60 (f61 f62 ?v0) ?v1)) (f60 (f61 f62 ?v2) ?v3)) ?v_0) f1) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 f8 ?v0)) ?v1)) (f60 (f61 f62 (f7 f8 ?v2)) ?v3)) ?v_0) f1)))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S6) (?v3 S15) (?v4 S3)) (let ((?v_0 (f63 ?v4))) (=> (= (f43 (f44 (f45 f46 (f60 (f61 f62 ?v0) ?v1)) (f60 (f61 f62 ?v2) ?v3)) ?v_0) f1) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 f8 ?v0)) ?v1)) (f60 (f61 f62 (f7 f8 ?v2)) ?v3)) ?v_0) f1)))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 f8 ?v_0)) ?v1)) (f60 (f61 f62 ?v_0) ?v1)) (f63 ?v2)) f1))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S6) (?v3 S15) (?v4 S3) (?v5 S13)) (let ((?v_1 (f47 (f63 ?v4))) (?v_0 (f37 f38 ?v5))) (=> (= (f43 (f44 (f45 f46 (f60 (f61 f62 ?v0) ?v1)) (f60 (f61 f62 ?v2) ?v3)) ?v_1) f1) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 ?v_0 ?v0)) ?v1)) (f60 (f61 f62 (f7 ?v_0 ?v2)) ?v3)) ?v_1) f1)))))
(assert (forall ((?v0 S6) (?v1 S15) (?v2 S6) (?v3 S15) (?v4 S3) (?v5 S13)) (let ((?v_1 (f63 ?v4)) (?v_0 (f37 f38 ?v5))) (=> (= (f43 (f44 (f45 f46 (f60 (f61 f62 ?v0) ?v1)) (f60 (f61 f62 ?v2) ?v3)) ?v_1) f1) (= (f43 (f44 (f45 f46 (f60 (f61 f62 (f7 ?v_0 ?v0)) ?v1)) (f60 (f61 f62 (f7 ?v_0 ?v2)) ?v3)) ?v_1) f1)))))
(assert (forall ((?v0 S6) (?v1 S13) (?v2 S13) (?v3 S6) (?v4 S9)) (not (= (f7 (f37 (f57 (f58 f59 ?v0) ?v1) ?v2) ?v3) (f9 f10 ?v4)))))
(check-sat)
(exit)