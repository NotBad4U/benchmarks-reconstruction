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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S3) S1)
(declare-fun f4 (S5 S3) S4)
(declare-fun f5 (S2) S5)
(declare-fun f6 (S6 S2) S1)
(declare-fun f7 (S7 S3) S6)
(declare-fun f8 (S8 S3) S7)
(declare-fun f9 () S8)
(declare-fun f10 (S11 S10) S1)
(declare-fun f11 (S12 S3) S11)
(declare-fun f12 (S9) S12)
(declare-fun f13 (S13 S9) S1)
(declare-fun f14 (S14 S10) S13)
(declare-fun f15 (S15 S3) S14)
(declare-fun f16 () S15)
(declare-fun f17 (S17 S16) S18)
(declare-fun f18 () S17)
(declare-fun f19 () S18)
(declare-fun f20 () S1)
(declare-fun f21 (S20 S21) S22)
(declare-fun f22 (S23 S17) S20)
(declare-fun f23 () S23)
(declare-fun f24 () S17)
(declare-fun f25 () S21)
(declare-fun f26 (S24 S19) S22)
(declare-fun f27 () S24)
(declare-fun f28 (S25 S3 S3 S19 S3) S1)
(declare-fun f29 () S25)
(declare-fun f30 () S3)
(declare-fun f31 () S3)
(declare-fun f32 () S3)
(declare-fun f33 (S25 S19 S19) S1)
(declare-fun f34 (S25 S17 S26 S27 S19) S1)
(declare-fun f35 () S26)
(declare-fun f36 (S28 S27) S27)
(declare-fun f37 (S29 S3) S28)
(declare-fun f38 (S30 S3) S29)
(declare-fun f39 (S31 S27) S30)
(declare-fun f40 () S31)
(declare-fun f41 (S32 S21) S27)
(declare-fun f42 () S32)
(declare-fun f43 (S33 S16) S21)
(declare-fun f44 () S33)
(declare-fun f45 () S16)
(declare-fun f46 () S19)
(declare-fun f47 (S34 S13) S18)
(declare-fun f48 () S34)
(declare-fun f49 () S10)
(declare-fun f50 (S25 S17) S1)
(declare-fun f51 (S35 S21) S36)
(declare-fun f52 () S35)
(declare-fun f53 (S25 S17 S21 S19) S1)
(declare-fun f54 (S17 S17) S1)
(declare-fun f55 (S25 S17 S26 S27 S19) S1)
(declare-fun f56 (S22) S1)
(declare-fun f57 (S18) S1)
(declare-fun f58 (S36) S1)
(declare-fun f59 (S9 S13) S1)
(declare-fun f60 (S37 S17) S9)
(declare-fun f61 (S25) S37)
(declare-fun f62 () S22)
(declare-fun f63 () S36)
(declare-fun f64 (S2 S6) S1)
(declare-fun f65 (S17) S1)
(declare-fun f66 (S38 S36) S10)
(declare-fun f67 (S39 S6) S38)
(declare-fun f68 (S40 S10) S39)
(declare-fun f69 () S40)
(declare-fun f70 (S41 S18) S17)
(declare-fun f71 (S42 S16) S41)
(declare-fun f72 (S43 S17) S42)
(declare-fun f73 () S43)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (= (f6 (f7 (f8 f9 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S10)) (= (= (f10 (f11 (f12 ?v0) ?v1) ?v2) f1) (= (f13 (f14 (f15 f16 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S16)) (= (f17 f18 ?v0) f19)))
(assert (not (= f20 f1)))
(assert (forall ((?v0 S19) (?v1 S19)) (=> (= (f21 (f22 f23 f24) f25) (f26 f27 ?v0)) (=> (= (f28 f29 f30 f31 ?v1 f32) f1) (=> (= (f33 f29 ?v0 ?v1) f1) (= f20 f1))))))
(assert (= (f34 f29 f24 f35 (f36 (f37 (f38 (f39 f40 (f41 f42 (f43 f44 f45))) f31) f32) (f41 f42 f25)) f46) f1))
(assert (= (f17 f24 f45) (f47 f48 (f14 (f15 f16 f30) f49))))
(assert (= (f17 f24 f45) (f47 f48 (f14 (f15 f16 f30) f49))))
(assert (= (f34 f29 f24 f35 (f36 (f37 (f38 (f39 f40 (f41 f42 (f43 f44 f45))) f31) f32) (f41 f42 f25)) f46) f1))
(assert (= (f50 f29 f24) f1))
(assert (forall ((?v0 S25) (?v1 S19)) (= (f33 ?v0 ?v1 ?v1) f1)))
(assert (= (f34 f29 f24 f35 (f36 (f37 (f38 (f39 f40 (f41 f42 (f43 f44 f45))) f31) f32) (f41 f42 f25)) f46) f1))
(assert (forall ((?v0 S25) (?v1 S19) (?v2 S19) (?v3 S19)) (=> (= (f33 ?v0 ?v1 ?v2) f1) (=> (= (f33 ?v0 ?v2 ?v3) f1) (= (f33 ?v0 ?v1 ?v3) f1)))))
(assert (forall ((?v0 S19) (?v1 S19)) (= (= (f26 f27 ?v0) (f26 f27 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f47 f48 ?v0) (f47 f48 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S21) (?v1 S21)) (= (= (f51 f52 ?v0) (f51 f52 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S17) (?v1 S21) (?v2 S19) (?v3 S25) (?v4 S26)) (=> (= (f21 (f22 f23 ?v0) ?v1) (f26 f27 ?v2)) (= (f34 ?v3 ?v0 ?v4 (f41 f42 ?v1) ?v2) f1))))
(assert (= (f50 f29 f24) f1))
(assert (forall ((?v0 S25) (?v1 S17) (?v2 S21) (?v3 S19)) (= (= (f53 ?v0 ?v1 ?v2 ?v3) f1) (exists ((?v4 S19)) (and (= (f21 (f22 f23 ?v1) ?v2) (f26 f27 ?v4)) (= (f33 ?v0 ?v4 ?v3) f1))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S21) (?v3 S19)) (let ((?v_0 (f26 f27 ?v3))) (=> (= (f54 ?v0 ?v1) f1) (=> (= (f21 (f22 f23 ?v0) ?v2) ?v_0) (= (f21 (f22 f23 ?v1) ?v2) ?v_0))))))
(assert (forall ((?v0 S17) (?v1 S21) (?v2 S19) (?v3 S25)) (=> (= (f21 (f22 f23 ?v0) ?v1) (f26 f27 ?v2)) (= (f53 ?v3 ?v0 ?v1 ?v2) f1))))
(assert (forall ((?v0 S17) (?v1 S21) (?v2 S19) (?v3 S25) (?v4 S26)) (=> (= (f21 (f22 f23 ?v0) ?v1) (f26 f27 ?v2)) (= (f55 ?v3 ?v0 ?v4 (f41 f42 ?v1) ?v2) f1))))
(assert (forall ((?v0 S19)) (= (= (f56 (f26 f27 ?v0)) f1) false)))
(assert (forall ((?v0 S13)) (= (= (f57 (f47 f48 ?v0)) f1) false)))
(assert (forall ((?v0 S21)) (= (= (f58 (f51 f52 ?v0)) f1) false)))
(assert (forall ((?v0 S17)) (= (f54 ?v0 ?v0) f1)))
(assert (forall ((?v0 S25) (?v1 S17) (?v2 S26) (?v3 S27) (?v4 S19)) (= (= (f55 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (= (f34 ?v0 ?v1 ?v2 ?v3 ?v4) f1))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17)) (=> (= (f54 ?v0 ?v1) f1) (=> (= (f54 ?v1 ?v2) f1) (= (f54 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S25) (?v3 S21) (?v4 S19)) (=> (= (f54 ?v0 ?v1) f1) (=> (= (f53 ?v2 ?v0 ?v3 ?v4) f1) (= (f53 ?v2 ?v1 ?v3 ?v4) f1)))))
(assert (forall ((?v0 S25) (?v1 S17) (?v2 S26) (?v3 S27) (?v4 S19)) (=> (= (f55 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (= (f34 ?v0 ?v1 ?v2 ?v3 ?v4) f1))))
(assert (forall ((?v0 S25) (?v1 S17) (?v2 S26) (?v3 S27) (?v4 S19)) (=> (= (f34 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (= (f55 ?v0 ?v1 ?v2 ?v3 ?v4) f1))))
(assert (forall ((?v0 S25) (?v1 S17) (?v2 S26) (?v3 S27) (?v4 S19) (?v5 S17)) (=> (= (f34 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f54 ?v1 ?v5) f1) (= (f34 ?v0 ?v5 ?v2 ?v3 ?v4) f1)))))
(assert (forall ((?v0 S25) (?v1 S17) (?v2 S21) (?v3 S19) (?v4 S19)) (=> (= (f53 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f33 ?v0 ?v3 ?v4) f1) (= (f53 ?v0 ?v1 ?v2 ?v4) f1)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S16) (?v3 S3) (?v4 S10)) (=> (= (f54 ?v0 ?v1) f1) (=> (= (f17 ?v0 ?v2) (f47 f48 (f14 (f15 f16 ?v3) ?v4))) (exists ((?v5 S10)) (= (f17 ?v1 ?v2) (f47 f48 (f14 (f15 f16 ?v3) ?v5))))))))
(assert (forall ((?v0 S17) (?v1 S17)) (= (= (f54 ?v0 ?v1) f1) (forall ((?v2 S16) (?v3 S3) (?v4 S10)) (=> (= (f17 ?v0 ?v2) (f47 f48 (f14 (f15 f16 ?v3) ?v4))) (exists ((?v5 S10)) (= (f17 ?v1 ?v2) (f47 f48 (f14 (f15 f16 ?v3) ?v5)))))))))
(assert (forall ((?v0 S21) (?v1 S27) (?v2 S3) (?v3 S3) (?v4 S27)) (not (= (f41 f42 ?v0) (f36 (f37 (f38 (f39 f40 ?v1) ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S27) (?v1 S3) (?v2 S3) (?v3 S27) (?v4 S21)) (not (= (f36 (f37 (f38 (f39 f40 ?v0) ?v1) ?v2) ?v3) (f41 f42 ?v4)))))
(assert (forall ((?v0 S17) (?v1 S17)) (=> (forall ((?v2 S16) (?v3 S3) (?v4 S10)) (=> (= (f17 ?v0 ?v2) (f47 f48 (f14 (f15 f16 ?v3) ?v4))) (exists ((?v5 S10)) (= (f17 ?v1 ?v2) (f47 f48 (f14 (f15 f16 ?v3) ?v5)))))) (= (f54 ?v0 ?v1) f1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f12 ?v0) (f12 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f5 ?v0) (f5 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S25) (?v1 S17) (?v2 S16) (?v3 S13)) (=> (= (f50 ?v0 ?v1) f1) (=> (= (f17 ?v1 ?v2) (f47 f48 ?v3)) (= (f59 (f60 (f61 ?v0) ?v1) ?v3) f1)))))
(assert (forall ((?v0 S21) (?v1 S19) (?v2 S25) (?v3 S17)) (=> (= (f21 (f22 f23 f18) ?v0) (f26 f27 ?v1)) (= (f53 ?v2 ?v3 ?v0 ?v1) f1))))
(assert (forall ((?v0 S27) (?v1 S3) (?v2 S3) (?v3 S27) (?v4 S27) (?v5 S3) (?v6 S3) (?v7 S27)) (= (= (f36 (f37 (f38 (f39 f40 ?v0) ?v1) ?v2) ?v3) (f36 (f37 (f38 (f39 f40 ?v4) ?v5) ?v6) ?v7)) (and (= ?v0 ?v4) (and (= ?v1 ?v5) (and (= ?v2 ?v6) (= ?v3 ?v7)))))))
(assert (forall ((?v0 S19)) (not (= f62 (f26 f27 ?v0)))))
(assert (forall ((?v0 S21)) (not (= f63 (f51 f52 ?v0)))))
(assert (forall ((?v0 S13)) (not (= f19 (f47 f48 ?v0)))))
(assert (forall ((?v0 S19)) (not (= (f26 f27 ?v0) f62))))
(assert (forall ((?v0 S21)) (not (= (f51 f52 ?v0) f63))))
(assert (forall ((?v0 S13)) (not (= (f47 f48 ?v0) f19))))
(assert (forall ((?v0 S22)) (= (forall ((?v1 S19)) (not (= ?v0 (f26 f27 ?v1)))) (= ?v0 f62))))
(assert (forall ((?v0 S36)) (= (forall ((?v1 S21)) (not (= ?v0 (f51 f52 ?v1)))) (= ?v0 f63))))
(assert (forall ((?v0 S18)) (= (forall ((?v1 S13)) (not (= ?v0 (f47 f48 ?v1)))) (= ?v0 f19))))
(assert (forall ((?v0 S22)) (= (not (= ?v0 f62)) (exists ((?v1 S19)) (= ?v0 (f26 f27 ?v1))))))
(assert (forall ((?v0 S36)) (= (not (= ?v0 f63)) (exists ((?v1 S21)) (= ?v0 (f51 f52 ?v1))))))
(assert (forall ((?v0 S18)) (= (not (= ?v0 f19)) (exists ((?v1 S13)) (= ?v0 (f47 f48 ?v1))))))
(assert (forall ((?v0 S36)) (= (= (f58 ?v0) f1) (= ?v0 f63))))
(assert (forall ((?v0 S22)) (= (= (f56 ?v0) f1) (= ?v0 f62))))
(assert (forall ((?v0 S18)) (= (= (f57 ?v0) f1) (= ?v0 f19))))
(assert (= (= (f58 f63) f1) true))
(assert (= (= (f56 f62) f1) true))
(assert (= (= (f57 f19) f1) true))
(assert (forall ((?v0 S25) (?v1 S17) (?v2 S13) (?v3 S17)) (let ((?v_0 (f61 ?v0))) (=> (= (f59 (f60 ?v_0 ?v1) ?v2) f1) (=> (= (f54 ?v1 ?v3) f1) (= (f59 (f60 ?v_0 ?v3) ?v2) f1))))))
(assert (forall ((?v0 S21) (?v1 S19) (?v2 S17)) (let ((?v_0 (f26 f27 ?v1))) (=> (= (f21 (f22 f23 f18) ?v0) ?v_0) (= (f21 (f22 f23 ?v2) ?v0) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S10) (?v2 S3) (?v3 S10)) (=> (= (f14 (f15 f16 ?v0) ?v1) (f14 (f15 f16 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S3) (?v1 S10) (?v2 S3) (?v3 S10)) (= (= (f14 (f15 f16 ?v0) ?v1) (f14 (f15 f16 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S9)) (= (forall ((?v1 S13)) (= (f59 ?v0 ?v1) f1)) (forall ((?v1 S3) (?v2 S10)) (= (f59 ?v0 (f14 (f15 f16 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2)) (= (forall ((?v1 S6)) (= (f64 ?v0 ?v1) f1)) (forall ((?v1 S3) (?v2 S3)) (= (f64 ?v0 (f7 (f8 f9 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S21) (?v1 S21)) (= (= (f41 f42 ?v0) (f41 f42 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S22)) (=> (=> (= ?v0 f62) false) (=> (forall ((?v1 S19)) (=> (= ?v0 (f26 f27 ?v1)) false)) false))))
(assert (forall ((?v0 S36)) (=> (=> (= ?v0 f63) false) (=> (forall ((?v1 S21)) (=> (= ?v0 (f51 f52 ?v1)) false)) false))))
(assert (forall ((?v0 S18)) (=> (=> (= ?v0 f19) false) (=> (forall ((?v1 S13)) (=> (= ?v0 (f47 f48 ?v1)) false)) false))))
(assert (forall ((?v0 S25) (?v1 S17)) (= (= (f50 ?v0 ?v1) f1) (and (forall ((?v2 S16) (?v3 S13)) (=> (= (f17 ?v1 ?v2) (f47 f48 ?v3)) (= (f59 (f60 (f61 ?v0) ?v1) ?v3) f1))) (= (f65 ?v1) f1)))))
(assert (forall ((?v0 S25) (?v1 S3) (?v2 S3) (?v3 S19) (?v4 S3) (?v5 S17) (?v6 S21) (?v7 S10)) (let ((?v_0 (f60 (f61 ?v0) ?v5)) (?v_1 (f15 f16 ?v1))) (=> (= (f28 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f53 ?v0 ?v5 ?v6 ?v3) f1) (=> (= (f59 ?v_0 (f14 ?v_1 ?v7)) f1) (= (f59 ?v_0 (f14 ?v_1 (f66 (f67 (f68 f69 ?v7) (f7 (f8 f9 ?v2) ?v4)) (f51 f52 ?v6)))) f1)))))))
(assert (forall ((?v0 S25) (?v1 S17) (?v2 S16) (?v3 S13)) (=> (= (f50 ?v0 ?v1) f1) (=> (= (f17 ?v1 ?v2) f19) (=> (= (f59 (f60 (f61 ?v0) ?v1) ?v3) f1) (= (f50 ?v0 (f70 (f71 (f72 f73 ?v1) ?v2) (f47 f48 ?v3))) f1))))))
(assert (forall ((?v0 S13)) (=> (forall ((?v1 S3) (?v2 S10)) (=> (= ?v0 (f14 (f15 f16 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S3) (?v2 S3)) (=> (= ?v0 (f7 (f8 f9 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S13)) (=> (forall ((?v1 S3) (?v2 S10)) (=> (= ?v0 (f14 (f15 f16 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S3) (?v2 S3)) (=> (= ?v0 (f7 (f8 f9 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S3) (?v3 S10) (?v4 S25) (?v5 S10) (?v6 S21) (?v7 S19)) (let ((?v_0 (f15 f16 ?v2))) (=> (= (f17 ?v0 ?v1) (f47 f48 (f14 ?v_0 ?v3))) (= (= (f53 ?v4 (f70 (f71 (f72 f73 ?v0) ?v1) (f47 f48 (f14 ?v_0 ?v5))) ?v6 ?v7) f1) (= (f53 ?v4 ?v0 ?v6 ?v7) f1))))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S3) (?v3 S10) (?v4 S10)) (let ((?v_0 (f15 f16 ?v2))) (=> (= (f17 ?v0 ?v1) (f47 f48 (f14 ?v_0 ?v3))) (= (f54 ?v0 (f70 (f71 (f72 f73 ?v0) ?v1) (f47 f48 (f14 ?v_0 ?v4)))) f1)))))
(assert (forall ((?v0 S25) (?v1 S17) (?v2 S13) (?v3 S16) (?v4 S3) (?v5 S10) (?v6 S10)) (let ((?v_0 (f61 ?v0)) (?v_1 (f15 f16 ?v4))) (=> (= (f59 (f60 ?v_0 ?v1) ?v2) f1) (=> (= (f17 ?v1 ?v3) (f47 f48 (f14 ?v_1 ?v5))) (= (f59 (f60 ?v_0 (f70 (f71 (f72 f73 ?v1) ?v3) (f47 f48 (f14 ?v_1 ?v6)))) ?v2) f1))))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S13)) (=> (= (f17 ?v0 ?v1) f19) (= (f54 ?v0 (f70 (f71 (f72 f73 ?v0) ?v1) (f47 f48 ?v2))) f1))))
(assert (forall ((?v0 S25) (?v1 S17) (?v2 S13) (?v3 S16) (?v4 S13)) (let ((?v_0 (f61 ?v0))) (=> (= (f59 (f60 ?v_0 ?v1) ?v2) f1) (=> (= (f17 ?v1 ?v3) f19) (= (f59 (f60 ?v_0 (f70 (f71 (f72 f73 ?v1) ?v3) (f47 f48 ?v4))) ?v2) f1))))))
(assert (forall ((?v0 S25) (?v1 S17) (?v2 S16) (?v3 S3) (?v4 S10) (?v5 S10)) (let ((?v_0 (f15 f16 ?v3))) (let ((?v_1 (f14 ?v_0 ?v5))) (=> (= (f50 ?v0 ?v1) f1) (=> (= (f17 ?v1 ?v2) (f47 f48 (f14 ?v_0 ?v4))) (=> (= (f59 (f60 (f61 ?v0) ?v1) ?v_1) f1) (= (f50 ?v0 (f70 (f71 (f72 f73 ?v1) ?v2) (f47 f48 ?v_1))) f1))))))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S13)) (=> (= (f65 ?v0) f1) (=> (= (f17 ?v0 ?v1) f19) (= (f65 (f70 (f71 (f72 f73 ?v0) ?v1) (f47 f48 ?v2))) f1)))))
(assert (forall ((?v0 S17) (?v1 S16) (?v2 S3) (?v3 S10) (?v4 S10)) (let ((?v_0 (f15 f16 ?v2))) (=> (= (f65 ?v0) f1) (=> (= (f17 ?v0 ?v1) (f47 f48 (f14 ?v_0 ?v3))) (= (f65 (f70 (f71 (f72 f73 ?v0) ?v1) (f47 f48 (f14 ?v_0 ?v4)))) f1))))))
(check-sat)
(exit)