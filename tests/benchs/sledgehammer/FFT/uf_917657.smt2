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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 (S5 S6) S2)
(declare-fun f5 () S5)
(declare-fun f6 (S7 S6) S6)
(declare-fun f7 (S8 S9) S7)
(declare-fun f8 () S8)
(declare-fun f9 (S10 S9) S9)
(declare-fun f10 () S10)
(declare-fun f11 () S9)
(declare-fun f12 () S6)
(declare-fun f13 (S11 S3) S3)
(declare-fun f14 (S12 S9) S11)
(declare-fun f15 () S12)
(declare-fun f16 () S9)
(declare-fun f17 (S13 S14) S9)
(declare-fun f18 () S13)
(declare-fun f19 (S15 S14) S14)
(declare-fun f20 () S15)
(declare-fun f21 () S15)
(declare-fun f22 () S14)
(declare-fun f23 () S3)
(declare-fun f24 () S4)
(declare-fun f25 () S14)
(declare-fun f26 () S15)
(declare-fun f27 (S17 S14) S16)
(declare-fun f28 () S17)
(declare-fun f29 (S19 S14) S18)
(declare-fun f30 () S19)
(declare-fun f31 () S14)
(declare-fun f32 (S20 S9) S1)
(declare-fun f33 () S4)
(declare-fun f34 (S23 S22) S4)
(declare-fun f35 (S24 S21) S23)
(declare-fun f36 () S24)
(declare-fun f37 () S22)
(declare-fun f38 (S27 S26) S4)
(declare-fun f39 (S28 S25) S27)
(declare-fun f40 () S28)
(declare-fun f41 () S26)
(declare-fun f42 (S30 S4) S22)
(declare-fun f43 (S31 S29) S30)
(declare-fun f44 () S31)
(declare-fun f45 (S33 S4) S26)
(declare-fun f46 (S34 S32) S33)
(declare-fun f47 () S34)
(declare-fun f48 (S36 S4) S3)
(declare-fun f49 (S37 S35) S36)
(declare-fun f50 () S37)
(declare-fun f51 (S38 S4) S4)
(declare-fun f52 (S39 S40) S38)
(declare-fun f53 () S39)
(declare-fun f54 (S6 S9) S40)
(declare-fun f55 (S41 S26) S26)
(declare-fun f56 (S42 S43) S41)
(declare-fun f57 () S42)
(declare-fun f58 (S32 S40) S43)
(declare-fun f59 (S44 S22) S22)
(declare-fun f60 (S45 S26) S44)
(declare-fun f61 () S45)
(declare-fun f62 (S29 S40) S26)
(declare-fun f63 (S35 S40) S9)
(declare-fun f64 (S25 S43) S40)
(declare-fun f65 (S21 S26) S40)
(declare-fun f66 () S18)
(declare-fun f67 () S18)
(declare-fun f68 () S16)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f19 f21 f22))) (not (= (f3 (f4 f5 (f6 (f7 f8 (f9 f10 (f9 f10 f11))) f12)) (f13 (f14 f15 f11) (f13 (f14 f15 f16) (f13 (f14 f15 (f17 f18 (f19 f20 ?v_0))) (f13 (f14 f15 (f17 f18 (f19 f21 ?v_0))) f23))))) f24))))
(assert (forall ((?v0 S6)) (= (f6 (f7 f8 f11) ?v0) ?v0)))
(assert (= (f9 f10 (f9 f10 f11)) (f17 f18 (f19 f20 (f19 f21 f22)))))
(assert (= (f17 f18 (f19 f20 (f19 f21 f22))) (f9 f10 (f9 f10 f11))))
(assert (= (f17 f18 (f19 f21 f22)) (f9 f10 f11)))
(assert (= (f17 f18 (f19 f21 (f19 f21 f22))) (f9 f10 (f9 f10 (f9 f10 f11)))))
(assert (= f16 (f17 f18 (f19 f21 f22))))
(assert (= (f17 f18 (f19 f21 f22)) f16))
(assert (= f25 (f19 f26 (f19 f21 f22))))
(assert (= (f19 f26 (f19 f21 f22)) f25))
(assert (= (f19 f26 (f19 f21 f22)) f25))
(assert (= (f17 f18 (f19 f21 f22)) f16))
(assert (= f16 (f9 f10 f11)))
(assert (= f11 (f17 f18 f22)))
(assert (= (f17 f18 f22) f11))
(assert (= f25 (f19 f26 (f19 f21 f22))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f19 f26 ?v0) (f19 f26 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S14) (?v1 S16)) (let ((?v_0 (f27 f28 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S14) (?v1 S18)) (let ((?v_0 (f29 f30 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S14) (?v1 S14)) (let ((?v_0 (f19 f26 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S14) (?v1 S9)) (let ((?v_0 (f17 f18 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f19 f21 ?v0) (f19 f21 ?v1)) (= ?v0 ?v1))))
(assert (= (= f22 f22) true))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f19 f20 ?v0) (f19 f20 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f9 f10 ?v0) (f9 f10 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f9 f10 ?v0) (f9 f10 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9)) (not (= (f9 f10 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (not (= ?v0 (f9 f10 ?v0)))))
(assert (forall ((?v0 S9)) (=> (= (f9 f10 ?v0) f11) false)))
(assert (forall ((?v0 S9)) (=> (= f11 (f9 f10 ?v0)) false)))
(assert (forall ((?v0 S9)) (not (= (f9 f10 ?v0) f11))))
(assert (forall ((?v0 S9)) (not (= (f9 f10 ?v0) f11))))
(assert (forall ((?v0 S9)) (not (= f11 (f9 f10 ?v0)))))
(assert (forall ((?v0 S9)) (not (= f11 (f9 f10 ?v0)))))
(assert (forall ((?v0 S14)) (= (= (f19 f21 ?v0) f22) false)))
(assert (forall ((?v0 S14)) (= (= f22 (f19 f21 ?v0)) false)))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f19 f21 ?v0) (f19 f20 ?v1)) false)))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f19 f20 ?v0) (f19 f21 ?v1)) false)))
(assert (forall ((?v0 S14)) (= (= (f19 f20 ?v0) f22) (= ?v0 f22))))
(assert (forall ((?v0 S14)) (= (= f22 (f19 f20 ?v0)) (= f22 ?v0))))
(assert (= (f19 f20 f22) f22))
(assert (= (f19 f26 f22) f31))
(assert (= (f17 f18 f22) f11))
(assert (= (f19 f26 f22) f31))
(assert (= f31 (f19 f26 f22)))
(assert (forall ((?v0 S9)) (=> (=> (= ?v0 f11) false) (=> (forall ((?v1 S9)) (=> (= ?v0 (f9 f10 ?v1)) false)) false))))
(assert (forall ((?v0 S20) (?v1 S9)) (=> (= (f32 ?v0 ?v1) f1) (=> (forall ((?v2 S9)) (=> (= (f32 ?v0 (f9 f10 ?v2)) f1) (= (f32 ?v0 ?v2) f1))) (= (f32 ?v0 f11) f1)))))
(assert (forall ((?v0 S20) (?v1 S9)) (=> (= (f32 ?v0 f11) f1) (=> (forall ((?v2 S9)) (=> (= (f32 ?v0 ?v2) f1) (= (f32 ?v0 (f9 f10 ?v2)) f1))) (= (f32 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S9)) (=> (not (= ?v0 f11)) (exists ((?v1 S9)) (= ?v0 (f9 f10 ?v1))))))
(assert (forall ((?v0 S6) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f33) (= ?v1 f23))))
(assert (forall ((?v0 S21) (?v1 S22)) (= (= (f34 (f35 f36 ?v0) ?v1) f33) (= ?v1 f37))))
(assert (forall ((?v0 S25) (?v1 S26)) (= (= (f38 (f39 f40 ?v0) ?v1) f33) (= ?v1 f41))))
(assert (forall ((?v0 S29) (?v1 S4)) (= (= (f42 (f43 f44 ?v0) ?v1) f37) (= ?v1 f33))))
(assert (forall ((?v0 S32) (?v1 S4)) (= (= (f45 (f46 f47 ?v0) ?v1) f41) (= ?v1 f33))))
(assert (forall ((?v0 S35) (?v1 S4)) (= (= (f48 (f49 f50 ?v0) ?v1) f23) (= ?v1 f33))))
(assert (forall ((?v0 S6)) (= (f3 (f4 f5 ?v0) f23) f33)))
(assert (forall ((?v0 S29)) (= (f42 (f43 f44 ?v0) f33) f37)))
(assert (forall ((?v0 S32)) (= (f45 (f46 f47 ?v0) f33) f41)))
(assert (forall ((?v0 S35)) (= (f48 (f49 f50 ?v0) f33) f23)))
(assert (forall ((?v0 S21)) (= (f34 (f35 f36 ?v0) f37) f33)))
(assert (forall ((?v0 S25)) (= (f38 (f39 f40 ?v0) f41) f33)))
(assert (forall ((?v0 S6) (?v1 S3)) (= (= f33 (f3 (f4 f5 ?v0) ?v1)) (= ?v1 f23))))
(assert (forall ((?v0 S21) (?v1 S22)) (= (= f33 (f34 (f35 f36 ?v0) ?v1)) (= ?v1 f37))))
(assert (forall ((?v0 S25) (?v1 S26)) (= (= f33 (f38 (f39 f40 ?v0) ?v1)) (= ?v1 f41))))
(assert (forall ((?v0 S29) (?v1 S4)) (= (= f37 (f42 (f43 f44 ?v0) ?v1)) (= ?v1 f33))))
(assert (forall ((?v0 S32) (?v1 S4)) (= (= f41 (f45 (f46 f47 ?v0) ?v1)) (= ?v1 f33))))
(assert (forall ((?v0 S35) (?v1 S4)) (= (= f23 (f48 (f49 f50 ?v0) ?v1)) (= ?v1 f33))))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f13 (f14 f15 ?v1) ?v2)) (f51 (f52 f53 (f54 ?v0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S32) (?v1 S40) (?v2 S4)) (let ((?v_0 (f46 f47 ?v0))) (= (f45 ?v_0 (f51 (f52 f53 ?v1) ?v2)) (f55 (f56 f57 (f58 ?v0 ?v1)) (f45 ?v_0 ?v2))))))
(assert (forall ((?v0 S29) (?v1 S40) (?v2 S4)) (let ((?v_0 (f43 f44 ?v0))) (= (f42 ?v_0 (f51 (f52 f53 ?v1) ?v2)) (f59 (f60 f61 (f62 ?v0 ?v1)) (f42 ?v_0 ?v2))))))
(assert (forall ((?v0 S35) (?v1 S40) (?v2 S4)) (let ((?v_0 (f49 f50 ?v0))) (= (f48 ?v_0 (f51 (f52 f53 ?v1) ?v2)) (f13 (f14 f15 (f63 ?v0 ?v1)) (f48 ?v_0 ?v2))))))
(assert (forall ((?v0 S25) (?v1 S43) (?v2 S26)) (let ((?v_0 (f39 f40 ?v0))) (= (f38 ?v_0 (f55 (f56 f57 ?v1) ?v2)) (f51 (f52 f53 (f64 ?v0 ?v1)) (f38 ?v_0 ?v2))))))
(assert (forall ((?v0 S21) (?v1 S26) (?v2 S22)) (let ((?v_0 (f35 f36 ?v0))) (= (f34 ?v_0 (f59 (f60 f61 ?v1) ?v2)) (f51 (f52 f53 (f65 ?v0 ?v1)) (f34 ?v_0 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S22)) (not (= (f59 (f60 f61 ?v0) ?v1) f37))))
(assert (forall ((?v0 S43) (?v1 S26)) (not (= (f55 (f56 f57 ?v0) ?v1) f41))))
(assert (forall ((?v0 S9) (?v1 S3)) (not (= (f13 (f14 f15 ?v0) ?v1) f23))))
(assert (forall ((?v0 S40) (?v1 S4)) (not (= (f51 (f52 f53 ?v0) ?v1) f33))))
(assert (forall ((?v0 S26) (?v1 S22)) (not (= f37 (f59 (f60 f61 ?v0) ?v1)))))
(assert (forall ((?v0 S43) (?v1 S26)) (not (= f41 (f55 (f56 f57 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S3)) (not (= f23 (f13 (f14 f15 ?v0) ?v1)))))
(assert (forall ((?v0 S40) (?v1 S4)) (not (= f33 (f51 (f52 f53 ?v0) ?v1)))))
(assert (= f66 (f29 f30 (f19 f21 f22))))
(assert (not (= f31 f25)))
(assert (forall ((?v0 S14)) (= (f19 f26 ?v0) ?v0)))
(assert (= f67 (f29 f30 f22)))
(assert (= f22 f31))
(assert (= f31 (f19 f26 f22)))
(assert (forall ((?v0 S26) (?v1 S43)) (not (= ?v0 (f55 (f56 f57 ?v1) ?v0)))))
(assert (forall ((?v0 S22) (?v1 S26)) (not (= ?v0 (f59 (f60 f61 ?v1) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S9)) (not (= ?v0 (f13 (f14 f15 ?v1) ?v0)))))
(assert (forall ((?v0 S4) (?v1 S40)) (not (= ?v0 (f51 (f52 f53 ?v1) ?v0)))))
(assert (forall ((?v0 S43) (?v1 S26)) (not (= (f55 (f56 f57 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S26) (?v1 S22)) (not (= (f59 (f60 f61 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S9) (?v1 S3)) (not (= (f13 (f14 f15 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S40) (?v1 S4)) (not (= (f51 (f52 f53 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S43) (?v1 S26) (?v2 S43) (?v3 S26)) (= (= (f55 (f56 f57 ?v0) ?v1) (f55 (f56 f57 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S26) (?v1 S22) (?v2 S26) (?v3 S22)) (= (= (f59 (f60 f61 ?v0) ?v1) (f59 (f60 f61 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S9) (?v3 S3)) (= (= (f13 (f14 f15 ?v0) ?v1) (f13 (f14 f15 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S40) (?v1 S4) (?v2 S40) (?v3 S4)) (= (= (f51 (f52 f53 ?v0) ?v1) (f51 (f52 f53 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S40) (?v1 S4) (?v2 S6) (?v3 S3)) (= (= (f51 (f52 f53 ?v0) ?v1) (f3 (f4 f5 ?v2) ?v3)) (exists ((?v4 S9) (?v5 S3)) (and (= ?v3 (f13 (f14 f15 ?v4) ?v5)) (and (= ?v0 (f54 ?v2 ?v4)) (= ?v1 (f3 (f4 f5 ?v2) ?v5))))))))
(assert (forall ((?v0 S40) (?v1 S4) (?v2 S25) (?v3 S26)) (= (= (f51 (f52 f53 ?v0) ?v1) (f38 (f39 f40 ?v2) ?v3)) (exists ((?v4 S43) (?v5 S26)) (and (= ?v3 (f55 (f56 f57 ?v4) ?v5)) (and (= ?v0 (f64 ?v2 ?v4)) (= ?v1 (f38 (f39 f40 ?v2) ?v5))))))))
(assert (forall ((?v0 S40) (?v1 S4) (?v2 S21) (?v3 S22)) (= (= (f51 (f52 f53 ?v0) ?v1) (f34 (f35 f36 ?v2) ?v3)) (exists ((?v4 S26) (?v5 S22)) (and (= ?v3 (f59 (f60 f61 ?v4) ?v5)) (and (= ?v0 (f65 ?v2 ?v4)) (= ?v1 (f34 (f35 f36 ?v2) ?v5))))))))
(assert (forall ((?v0 S43) (?v1 S26) (?v2 S32) (?v3 S4)) (= (= (f55 (f56 f57 ?v0) ?v1) (f45 (f46 f47 ?v2) ?v3)) (exists ((?v4 S40) (?v5 S4)) (and (= ?v3 (f51 (f52 f53 ?v4) ?v5)) (and (= ?v0 (f58 ?v2 ?v4)) (= ?v1 (f45 (f46 f47 ?v2) ?v5))))))))
(assert (forall ((?v0 S26) (?v1 S22) (?v2 S29) (?v3 S4)) (= (= (f59 (f60 f61 ?v0) ?v1) (f42 (f43 f44 ?v2) ?v3)) (exists ((?v4 S40) (?v5 S4)) (and (= ?v3 (f51 (f52 f53 ?v4) ?v5)) (and (= ?v0 (f62 ?v2 ?v4)) (= ?v1 (f42 (f43 f44 ?v2) ?v5))))))))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S35) (?v3 S4)) (= (= (f13 (f14 f15 ?v0) ?v1) (f48 (f49 f50 ?v2) ?v3)) (exists ((?v4 S40) (?v5 S4)) (and (= ?v3 (f51 (f52 f53 ?v4) ?v5)) (and (= ?v0 (f63 ?v2 ?v4)) (= ?v1 (f48 (f49 f50 ?v2) ?v5))))))))
(assert (forall ((?v0 S6) (?v1 S3) (?v2 S40) (?v3 S4)) (= (= (f3 (f4 f5 ?v0) ?v1) (f51 (f52 f53 ?v2) ?v3)) (exists ((?v4 S9) (?v5 S3)) (and (= ?v1 (f13 (f14 f15 ?v4) ?v5)) (and (= (f54 ?v0 ?v4) ?v2) (= (f3 (f4 f5 ?v0) ?v5) ?v3)))))))
(assert (forall ((?v0 S25) (?v1 S26) (?v2 S40) (?v3 S4)) (= (= (f38 (f39 f40 ?v0) ?v1) (f51 (f52 f53 ?v2) ?v3)) (exists ((?v4 S43) (?v5 S26)) (and (= ?v1 (f55 (f56 f57 ?v4) ?v5)) (and (= (f64 ?v0 ?v4) ?v2) (= (f38 (f39 f40 ?v0) ?v5) ?v3)))))))
(assert (forall ((?v0 S21) (?v1 S22) (?v2 S40) (?v3 S4)) (= (= (f34 (f35 f36 ?v0) ?v1) (f51 (f52 f53 ?v2) ?v3)) (exists ((?v4 S26) (?v5 S22)) (and (= ?v1 (f59 (f60 f61 ?v4) ?v5)) (and (= (f65 ?v0 ?v4) ?v2) (= (f34 (f35 f36 ?v0) ?v5) ?v3)))))))
(assert (forall ((?v0 S32) (?v1 S4) (?v2 S43) (?v3 S26)) (= (= (f45 (f46 f47 ?v0) ?v1) (f55 (f56 f57 ?v2) ?v3)) (exists ((?v4 S40) (?v5 S4)) (and (= ?v1 (f51 (f52 f53 ?v4) ?v5)) (and (= (f58 ?v0 ?v4) ?v2) (= (f45 (f46 f47 ?v0) ?v5) ?v3)))))))
(assert (forall ((?v0 S29) (?v1 S4) (?v2 S26) (?v3 S22)) (= (= (f42 (f43 f44 ?v0) ?v1) (f59 (f60 f61 ?v2) ?v3)) (exists ((?v4 S40) (?v5 S4)) (and (= ?v1 (f51 (f52 f53 ?v4) ?v5)) (and (= (f62 ?v0 ?v4) ?v2) (= (f42 (f43 f44 ?v0) ?v5) ?v3)))))))
(assert (forall ((?v0 S35) (?v1 S4) (?v2 S9) (?v3 S3)) (= (= (f48 (f49 f50 ?v0) ?v1) (f13 (f14 f15 ?v2) ?v3)) (exists ((?v4 S40) (?v5 S4)) (and (= ?v1 (f51 (f52 f53 ?v4) ?v5)) (and (= (f63 ?v0 ?v4) ?v2) (= (f48 (f49 f50 ?v0) ?v5) ?v3)))))))
(assert (forall ((?v0 S22)) (= (not (= ?v0 f37)) (exists ((?v1 S26) (?v2 S22)) (= ?v0 (f59 (f60 f61 ?v1) ?v2))))))
(assert (forall ((?v0 S26)) (= (not (= ?v0 f41)) (exists ((?v1 S43) (?v2 S26)) (= ?v0 (f55 (f56 f57 ?v1) ?v2))))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f23)) (exists ((?v1 S9) (?v2 S3)) (= ?v0 (f13 (f14 f15 ?v1) ?v2))))))
(assert (forall ((?v0 S4)) (= (not (= ?v0 f33)) (exists ((?v1 S40) (?v2 S4)) (= ?v0 (f51 (f52 f53 ?v1) ?v2))))))
(assert (forall ((?v0 S22)) (=> (=> (= ?v0 f37) false) (=> (forall ((?v1 S26) (?v2 S22)) (=> (= ?v0 (f59 (f60 f61 ?v1) ?v2)) false)) false))))
(assert (forall ((?v0 S26)) (=> (=> (= ?v0 f41) false) (=> (forall ((?v1 S43) (?v2 S26)) (=> (= ?v0 (f55 (f56 f57 ?v1) ?v2)) false)) false))))
(assert (forall ((?v0 S3)) (=> (=> (= ?v0 f23) false) (=> (forall ((?v1 S9) (?v2 S3)) (=> (= ?v0 (f13 (f14 f15 ?v1) ?v2)) false)) false))))
(assert (forall ((?v0 S4)) (=> (=> (= ?v0 f33) false) (=> (forall ((?v1 S40) (?v2 S4)) (=> (= ?v0 (f51 (f52 f53 ?v1) ?v2)) false)) false))))
(assert (= f68 (f27 f28 (f19 f21 f22))))
(check-sat)
(exit)