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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S3) S1)
(declare-fun f4 (S5 S6) S4)
(declare-fun f5 (S7 S3) S5)
(declare-fun f6 (S8 S2) S7)
(declare-fun f7 () S8)
(declare-fun f8 () S6)
(declare-fun f9 (S9 S2) S2)
(declare-fun f10 (S10 S4) S9)
(declare-fun f11 () S10)
(declare-fun f12 () S4)
(declare-fun f13 () S2)
(declare-fun f14 (S12 S13) S1)
(declare-fun f15 (S14 S11) S12)
(declare-fun f16 () S14)
(declare-fun f17 () S13)
(declare-fun f18 (S13 S11) S1)
(declare-fun f19 (S15 S6) S13)
(declare-fun f20 () S15)
(declare-fun f21 (S17 S16) S4)
(declare-fun f22 () S17)
(declare-fun f23 (S18 S13) S12)
(declare-fun f24 () S18)
(declare-fun f25 (S19 S17) S11)
(declare-fun f26 (S20 S2) S19)
(declare-fun f27 (S21 S17) S20)
(declare-fun f28 () S21)
(declare-fun f29 (S22 S6) S6)
(declare-fun f30 () S22)
(declare-fun f31 () S2)
(declare-fun f32 (S23 S2) S9)
(declare-fun f33 () S23)
(declare-fun f34 (S24 S2) S1)
(declare-fun f35 () S24)
(declare-fun f36 (S25 S4) S23)
(declare-fun f37 () S25)
(declare-fun f38 (S28 S27) S2)
(declare-fun f39 (S29 S26) S28)
(declare-fun f40 () S29)
(declare-fun f41 (S31 S27) S9)
(declare-fun f42 (S32 S30) S31)
(declare-fun f43 () S32)
(declare-fun f44 (S33 S6) S3)
(declare-fun f45 (S34 S26) S33)
(declare-fun f46 (S35 S3) S34)
(declare-fun f47 () S35)
(declare-fun f48 (S27 S3) S6)
(declare-fun f49 (S36 S3) S4)
(declare-fun f50 (S37 S2) S36)
(declare-fun f51 () S37)
(declare-fun f52 () S6)
(declare-fun f53 (S39 S11) S6)
(declare-fun f54 (S40 S38) S39)
(declare-fun f55 () S40)
(declare-fun f56 () S39)
(declare-fun f57 (S41 S6) S1)
(declare-fun f58 (S43 S42) S2)
(declare-fun f59 () S43)
(declare-fun f60 (S44 S2) S6)
(declare-fun f61 () S44)
(declare-fun f62 (S45 S6) S22)
(declare-fun f63 () S45)
(declare-fun f64 (S47 S46) S46)
(declare-fun f65 (S48 S46) S47)
(declare-fun f66 () S48)
(declare-fun f67 () S46)
(declare-fun f68 () S44)
(declare-fun f69 () S22)
(declare-fun f70 () S22)
(declare-fun f71 (S49 S1) S6)
(declare-fun f72 () S49)
(declare-fun f73 (S50 S42) S28)
(declare-fun f74 (S51 S26) S50)
(declare-fun f75 () S51)
(declare-fun f76 (S52 S53) S2)
(declare-fun f77 () S52)
(declare-fun f78 (S54 S42) S53)
(declare-fun f79 () S54)
(declare-fun f80 () S53)
(declare-fun f81 () S49)
(declare-fun f82 (S55 S44) S56)
(declare-fun f83 () S55)
(declare-fun f84 (S56 S53) S6)
(declare-fun f85 () S56)
(declare-fun f86 (S57 S2) S53)
(declare-fun f87 () S57)
(declare-fun f88 () S1)
(declare-fun f89 (S58 S53) S1)
(declare-fun f90 () S58)
(assert (not (= f1 f2)))
(assert (not (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 (f5 (f6 f7 ?v0) ?v1) f8) ?v2) f1) (=> (= ?v0 (f9 (f10 f11 f12) f13)) (=> (forall ((?v3 S11)) (=> (= (f14 (f15 f16 ?v3) f17) f1) (= (f18 (f19 f20 f8) ?v3) f1))) (forall ((?v3 S16)) (let ((?v_0 (f21 f22 ?v3))) (=> (= (f3 ?v_0 ?v1) f1) (and (= (f3 ?v_0 ?v2) f1) (not (= (f3 f12 ?v2) f1))))))))))))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S11)) (=> (= (f14 (f15 f16 ?v1) f17) f1) (= (f18 (f19 f20 ?v0) ?v1) f1))) (forall ((?v1 S16) (?v2 S3)) (=> (and (= (f3 (f21 f22 ?v1) ?v2) f1) (= (f3 f12 ?v2) f1)) (forall ((?v3 S3)) (=> (= (f3 (f4 (f5 (f6 f7 f13) ?v2) ?v0) ?v3) f1) (= (f3 (f21 f22 ?v1) ?v3) f1))))))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S6)) (=> (not (= (f3 ?v0 ?v1) f1)) (= (f3 (f4 (f5 (f6 f7 (f9 (f10 f11 ?v0) ?v2)) ?v1) ?v3) ?v1) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S6) (?v4 S3) (?v5 S3)) (let ((?v_0 (f6 f7 (f9 (f10 f11 ?v0) ?v2)))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 (f4 (f5 (f6 f7 ?v2) ?v1) ?v3) ?v4) f1) (=> (= (f3 (f4 (f5 ?v_0 ?v4) ?v3) ?v5) f1) (= (f3 (f4 (f5 ?v_0 ?v1) ?v3) ?v5) f1)))))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f14 (f23 f24 ?v0) ?v1) f1) (forall ((?v2 S6)) (=> (forall ((?v3 S11)) (=> (= (f14 (f15 f16 ?v3) ?v0) f1) (= (f18 (f19 f20 ?v2) ?v3) f1))) (forall ((?v3 S11)) (=> (= (f14 (f15 f16 ?v3) ?v1) f1) (= (f18 (f19 f20 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S4) (?v3 S2)) (= (= (f9 (f10 f11 ?v0) ?v1) (f9 (f10 f11 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S3) (?v3 S6) (?v4 S3)) (=> (= (f3 (f4 (f5 (f6 f7 (f9 (f10 f11 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (=> (= ?v4 ?v2) (=> (not (= (f3 ?v0 ?v2) f1)) false)) (=> (forall ((?v5 S3)) (=> (= (f3 ?v0 ?v2) f1) (=> (= (f3 (f4 (f5 (f6 f7 ?v1) ?v2) ?v3) ?v5) f1) (=> (= (f3 (f4 (f5 (f6 f7 (f9 (f10 f11 ?v0) ?v1)) ?v5) ?v3) ?v4) f1) false)))) false)))))
(assert (forall ((?v0 S6) (?v1 S17) (?v2 S2) (?v3 S17)) (= (= (f18 (f19 f20 ?v0) (f25 (f26 (f27 f28 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S16) (?v5 S3)) (=> (= (f3 (f21 ?v1 ?v4) ?v5) f1) (forall ((?v6 S3)) (=> (= (f3 (f4 (f5 (f6 f7 ?v2) ?v5) ?v0) ?v6) f1) (= (f3 (f21 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S6) (?v3 S3) (?v4 S2) (?v5 S3) (?v6 S6) (?v7 S3)) (=> (= (f3 (f4 (f5 (f6 f7 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f3 (f4 (f5 (f6 f7 ?v4) ?v5) ?v6) ?v7) f1) (exists ((?v8 S6)) (and (= (f3 (f4 (f5 (f6 f7 ?v0) ?v1) ?v8) ?v3) f1) (= (f3 (f4 (f5 (f6 f7 ?v4) ?v5) ?v8) ?v7) f1)))))))
(assert (forall ((?v0 S13) (?v1 S6)) (=> (forall ((?v2 S11)) (=> (= (f14 (f15 f16 ?v2) ?v0) f1) (= (f18 (f19 f20 (f29 f30 ?v1)) ?v2) f1))) (forall ((?v2 S11)) (=> (= (f14 (f15 f16 ?v2) ?v0) f1) (= (f18 (f19 f20 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S11)) (=> (= (f18 (f19 f20 (f29 f30 ?v0)) ?v1) f1) (= (f18 (f19 f20 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S6)) (= (f3 (f4 (f5 (f6 f7 f31) ?v0) ?v1) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S3)) (=> (= (f3 (f4 (f5 (f6 f7 f31) ?v0) ?v1) ?v2) f1) (=> (=> (= ?v2 ?v0) false) false))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S17) (?v3 S17) (?v4 S2) (?v5 S17)) (= (= (f25 (f26 (f27 f28 ?v0) ?v1) ?v2) (f25 (f26 (f27 f28 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S6) (?v3 S3)) (let ((?v_0 (f5 (f6 f7 ?v0) ?v1))) (=> (= (f3 (f4 ?v_0 ?v2) ?v3) f1) (= (f3 (f4 ?v_0 (f29 f30 ?v2)) ?v3) f1)))))
(assert (forall ((?v0 S4) (?v1 S2)) (not (= (f9 (f10 f11 ?v0) ?v1) f31))))
(assert (forall ((?v0 S4) (?v1 S2)) (not (= f31 (f9 (f10 f11 ?v0) ?v1)))))
(assert (forall ((?v0 S11)) (=> (forall ((?v1 S17) (?v2 S2) (?v3 S17)) (=> (= ?v0 (f25 (f26 (f27 f28 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S6)) (not (= ?v0 (f29 f30 ?v0)))))
(assert (forall ((?v0 S6)) (not (= (f29 f30 ?v0) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f29 f30 ?v0) (f29 f30 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f29 f30 ?v0) (f29 f30 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S6) (?v3 S3) (?v4 S2) (?v5 S3)) (=> (= (f3 (f4 (f5 (f6 f7 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f3 (f4 (f5 (f6 f7 ?v4) ?v3) ?v2) ?v5) f1) (= (f3 (f4 (f5 (f6 f7 (f9 (f32 f33 ?v0) ?v4)) ?v1) ?v2) ?v5) f1)))))
(assert (=> (= (f34 f35 f31) f1) (=> false false)))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S3) (?v4 S6) (?v5 S3)) (let ((?v_0 (= (f3 ?v0 ?v3) f1))) (=> (= (f3 (f4 (f5 (f6 f7 (f9 (f32 (f36 f37 ?v0) ?v1) ?v2)) ?v3) ?v4) ?v5) f1) (=> (=> ?v_0 (=> (= (f3 (f4 (f5 (f6 f7 ?v1) ?v3) ?v4) ?v5) f1) false)) (=> (=> (not ?v_0) (=> (= (f3 (f4 (f5 (f6 f7 ?v2) ?v3) ?v4) ?v5) f1) false)) false))))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S6) (?v4 S3) (?v5 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 (f4 (f5 (f6 f7 ?v2) ?v1) ?v3) ?v4) f1) (= (f3 (f4 (f5 (f6 f7 (f9 (f32 (f36 f37 ?v0) ?v2) ?v5)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S6) (?v4 S3) (?v5 S2)) (=> (not (= (f3 ?v0 ?v1) f1)) (=> (= (f3 (f4 (f5 (f6 f7 ?v2) ?v1) ?v3) ?v4) f1) (= (f3 (f4 (f5 (f6 f7 (f9 (f32 (f36 f37 ?v0) ?v5) ?v2)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S4) (?v1 S2)) (=> (= (f34 f35 (f9 (f10 f11 ?v0) ?v1)) f1) (=> (=> (= (f34 f35 ?v1) f1) false) false))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (=> (= (f34 f35 (f9 (f32 (f36 f37 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f34 f35 ?v1) f1) (=> (= (f34 f35 ?v2) f1) false)) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f34 f35 (f9 (f32 f33 ?v0) ?v1)) f1) (=> (=> (= (f34 f35 ?v0) f1) (=> (= (f34 f35 ?v1) f1) false)) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S4) (?v3 S2) (?v4 S2)) (not (= (f9 (f32 f33 ?v0) ?v1) (f9 (f32 (f36 f37 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (not (= (f9 (f32 (f36 f37 ?v0) ?v1) ?v2) (f9 (f32 f33 ?v3) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f9 (f32 f33 ?v0) ?v1) (f9 (f32 f33 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S4) (?v4 S2) (?v5 S2)) (= (= (f9 (f32 (f36 f37 ?v0) ?v1) ?v2) (f9 (f32 (f36 f37 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f34 f35 ?v0) f1) (=> (= (f34 f35 ?v1) f1) (= (f34 f35 (f9 (f32 f33 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S4)) (=> (= (f34 f35 ?v0) f1) (=> (= (f34 f35 ?v1) f1) (= (f34 f35 (f9 (f32 (f36 f37 ?v2) ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S4)) (=> (= (f34 f35 ?v0) f1) (= (f34 f35 (f9 (f10 f11 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S4) (?v3 S2) (?v4 S2)) (not (= (f9 (f10 f11 ?v0) ?v1) (f9 (f32 (f36 f37 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S4) (?v4 S2)) (not (= (f9 (f32 (f36 f37 ?v0) ?v1) ?v2) (f9 (f10 f11 ?v3) ?v4)))))
(assert (= (f34 f35 f31) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S4) (?v3 S2)) (not (= (f9 (f32 f33 ?v0) ?v1) (f9 (f10 f11 ?v2) ?v3)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S2)) (not (= (f9 (f10 f11 ?v0) ?v1) (f9 (f32 f33 ?v2) ?v3)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (not (= (f9 (f32 (f36 f37 ?v0) ?v1) ?v2) f31))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (not (= f31 (f9 (f32 (f36 f37 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2)) (not (= (f9 (f32 f33 ?v0) ?v1) f31))))
(assert (forall ((?v0 S2) (?v1 S2)) (not (= f31 (f9 (f32 f33 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S6) (?v4 S3)) (=> (= (f3 (f4 (f5 (f6 f7 (f9 (f32 f33 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (forall ((?v5 S3)) (=> (= (f3 (f4 (f5 (f6 f7 ?v0) ?v2) ?v3) ?v5) f1) (=> (= (f3 (f4 (f5 (f6 f7 ?v1) ?v5) ?v3) ?v4) f1) false))) false))))
(assert (forall ((?v0 S26) (?v1 S27)) (=> (= (f34 f35 (f38 (f39 f40 ?v0) ?v1)) f1) (=> false false))))
(assert (forall ((?v0 S30) (?v1 S27) (?v2 S2)) (=> (= (f34 f35 (f9 (f41 (f42 f43 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f34 f35 ?v2) f1) false) false))))
(assert (forall ((?v0 S30) (?v1 S27) (?v2 S2) (?v3 S30) (?v4 S27) (?v5 S2)) (= (= (f9 (f41 (f42 f43 ?v0) ?v1) ?v2) (f9 (f41 (f42 f43 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S26) (?v1 S27) (?v2 S26) (?v3 S27)) (= (= (f38 (f39 f40 ?v0) ?v1) (f38 (f39 f40 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S30) (?v1 S27) (?v2 S2) (?v3 S26) (?v4 S27)) (not (= (f9 (f41 (f42 f43 ?v0) ?v1) ?v2) (f38 (f39 f40 ?v3) ?v4)))))
(assert (forall ((?v0 S26) (?v1 S27) (?v2 S30) (?v3 S27) (?v4 S2)) (not (= (f38 (f39 f40 ?v0) ?v1) (f9 (f41 (f42 f43 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S30) (?v2 S27)) (=> (= (f34 f35 ?v0) f1) (= (f34 f35 (f9 (f41 (f42 f43 ?v1) ?v2) ?v0)) f1))))
(assert (forall ((?v0 S26) (?v1 S27)) (= (f34 f35 (f38 (f39 f40 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S30) (?v1 S27) (?v2 S2) (?v3 S4) (?v4 S2)) (not (= (f9 (f41 (f42 f43 ?v0) ?v1) ?v2) (f9 (f10 f11 ?v3) ?v4)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S30) (?v3 S27) (?v4 S2)) (not (= (f9 (f10 f11 ?v0) ?v1) (f9 (f41 (f42 f43 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S26) (?v3 S27)) (not (= (f9 (f10 f11 ?v0) ?v1) (f38 (f39 f40 ?v2) ?v3)))))
(assert (forall ((?v0 S26) (?v1 S27) (?v2 S4) (?v3 S2)) (not (= (f38 (f39 f40 ?v0) ?v1) (f9 (f10 f11 ?v2) ?v3)))))
(assert (forall ((?v0 S30) (?v1 S27) (?v2 S2) (?v3 S4) (?v4 S2) (?v5 S2)) (not (= (f9 (f41 (f42 f43 ?v0) ?v1) ?v2) (f9 (f32 (f36 f37 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S30) (?v4 S27) (?v5 S2)) (not (= (f9 (f32 (f36 f37 ?v0) ?v1) ?v2) (f9 (f41 (f42 f43 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S26) (?v4 S27)) (not (= (f9 (f32 (f36 f37 ?v0) ?v1) ?v2) (f38 (f39 f40 ?v3) ?v4)))))
(assert (forall ((?v0 S26) (?v1 S27) (?v2 S4) (?v3 S2) (?v4 S2)) (not (= (f38 (f39 f40 ?v0) ?v1) (f9 (f32 (f36 f37 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S30) (?v1 S27) (?v2 S2) (?v3 S2) (?v4 S2)) (not (= (f9 (f41 (f42 f43 ?v0) ?v1) ?v2) (f9 (f32 f33 ?v3) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S30) (?v3 S27) (?v4 S2)) (not (= (f9 (f32 f33 ?v0) ?v1) (f9 (f41 (f42 f43 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S26) (?v3 S27)) (not (= (f9 (f32 f33 ?v0) ?v1) (f38 (f39 f40 ?v2) ?v3)))))
(assert (forall ((?v0 S26) (?v1 S27) (?v2 S2) (?v3 S2)) (not (= (f38 (f39 f40 ?v0) ?v1) (f9 (f32 f33 ?v2) ?v3)))))
(assert (forall ((?v0 S26) (?v1 S27)) (not (= f31 (f38 (f39 f40 ?v0) ?v1)))))
(assert (forall ((?v0 S30) (?v1 S27) (?v2 S2)) (not (= f31 (f9 (f41 (f42 f43 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S27)) (not (= (f38 (f39 f40 ?v0) ?v1) f31))))
(assert (forall ((?v0 S30) (?v1 S27) (?v2 S2)) (not (= (f9 (f41 (f42 f43 ?v0) ?v1) ?v2) f31))))
(assert (forall ((?v0 S26) (?v1 S27) (?v2 S3) (?v3 S6) (?v4 S3)) (=> (= (f3 (f4 (f5 (f6 f7 (f38 (f39 f40 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (=> (= ?v4 (f44 (f45 (f46 f47 ?v2) ?v0) (f48 ?v1 ?v2))) false) false))))
(assert (forall ((?v0 S26) (?v1 S27) (?v2 S3) (?v3 S6)) (= (f3 (f4 (f5 (f6 f7 (f38 (f39 f40 ?v0) ?v1)) ?v2) ?v3) (f44 (f45 (f46 f47 ?v2) ?v0) (f48 ?v1 ?v2))) f1)))
(assert (forall ((?v0 S3)) (= (f3 (f49 (f50 f51 f31) ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f49 (f50 f51 f31) ?v0) ?v1) f1) (=> (=> (= ?v1 ?v0) false) false))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3) (?v3 S2) (?v4 S3)) (=> (= (f3 (f49 (f50 f51 ?v0) ?v1) ?v2) f1) (=> (= (f3 (f49 (f50 f51 ?v3) ?v2) ?v4) f1) (= (f3 (f49 (f50 f51 (f9 (f32 f33 ?v0) ?v3)) ?v1) ?v4) f1)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2)) (=> (not (= (f3 ?v0 ?v1) f1)) (= (f3 (f49 (f50 f51 (f9 (f10 f11 ?v0) ?v2)) ?v1) ?v1) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S3) (?v4 S3)) (let ((?v_0 (f50 f51 (f9 (f10 f11 ?v0) ?v2)))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 (f49 (f50 f51 ?v2) ?v1) ?v3) f1) (=> (= (f3 (f49 ?v_0 ?v3) ?v4) f1) (= (f3 (f49 ?v_0 ?v1) ?v4) f1)))))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S3) (?v4 S2)) (=> (not (= (f3 ?v0 ?v1) f1)) (=> (= (f3 (f49 (f50 f51 ?v2) ?v1) ?v3) f1) (= (f3 (f49 (f50 f51 (f9 (f32 (f36 f37 ?v0) ?v4) ?v2)) ?v1) ?v3) f1)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S3) (?v4 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 (f49 (f50 f51 ?v2) ?v1) ?v3) f1) (= (f3 (f49 (f50 f51 (f9 (f32 (f36 f37 ?v0) ?v2) ?v4)) ?v1) ?v3) f1)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S3) (?v4 S3)) (let ((?v_0 (= (f3 ?v0 ?v3) f1))) (=> (= (f3 (f49 (f50 f51 (f9 (f32 (f36 f37 ?v0) ?v1) ?v2)) ?v3) ?v4) f1) (=> (=> ?v_0 (=> (= (f3 (f49 (f50 f51 ?v1) ?v3) ?v4) f1) false)) (=> (=> (not ?v_0) (=> (= (f3 (f49 (f50 f51 ?v2) ?v3) ?v4) f1) false)) false))))))
(assert (forall ((?v0 S26) (?v1 S27) (?v2 S3)) (= (f3 (f49 (f50 f51 (f38 (f39 f40 ?v0) ?v1)) ?v2) (f44 (f45 (f46 f47 ?v2) ?v0) (f48 ?v1 ?v2))) f1)))
(assert (forall ((?v0 S26) (?v1 S27) (?v2 S3) (?v3 S3)) (=> (= (f3 (f49 (f50 f51 (f38 (f39 f40 ?v0) ?v1)) ?v2) ?v3) f1) (=> (=> (= ?v3 (f44 (f45 (f46 f47 ?v2) ?v0) (f48 ?v1 ?v2))) false) false))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f49 (f50 f51 ?v0) ?v1))) (=> (= (f3 ?v_0 ?v2) f1) (=> (= (f3 ?v_0 ?v3) f1) (= ?v3 ?v2))))))
(assert (forall ((?v0 S6)) (=> (= (f29 f30 ?v0) f52) false)))
(assert (forall ((?v0 S6)) (=> (= f52 (f29 f30 ?v0)) false)))
(assert (forall ((?v0 S6)) (not (= (f29 f30 ?v0) f52))))
(assert (forall ((?v0 S6)) (not (= (f29 f30 ?v0) f52))))
(assert (forall ((?v0 S6)) (not (= f52 (f29 f30 ?v0)))))
(assert (forall ((?v0 S6)) (not (= f52 (f29 f30 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (= (= (f3 (f49 (f50 f51 ?v0) ?v1) ?v2) f1) (exists ((?v3 S6)) (= (f3 (f4 (f5 (f6 f7 ?v0) ?v1) ?v3) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S6) (?v3 S3)) (=> (= (f3 (f4 (f5 (f6 f7 ?v0) ?v1) ?v2) ?v3) f1) (= (f3 (f49 (f50 f51 ?v0) ?v1) ?v3) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S3)) (=> (= (f3 (f49 (f50 f51 (f9 (f32 f33 ?v0) ?v1)) ?v2) ?v3) f1) (=> (forall ((?v4 S3)) (=> (= (f3 (f49 (f50 f51 ?v0) ?v2) ?v4) f1) (=> (= (f3 (f49 (f50 f51 ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S38) (?v1 S17) (?v2 S2) (?v3 S17)) (= (f53 (f54 f55 ?v0) (f25 (f26 (f27 f28 ?v1) ?v2) ?v3)) f52)))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S3) (?v3 S3)) (=> (= (f3 (f49 (f50 f51 (f9 (f10 f11 ?v0) ?v1)) ?v2) ?v3) f1) (=> (=> (= ?v3 ?v2) (=> (not (= (f3 ?v0 ?v2) f1)) false)) (=> (forall ((?v4 S3)) (=> (= (f3 ?v0 ?v2) f1) (=> (= (f3 (f49 (f50 f51 ?v1) ?v2) ?v4) f1) (=> (= (f3 (f49 (f50 f51 (f9 (f10 f11 ?v0) ?v1)) ?v4) ?v3) f1) false)))) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (=> (= (f3 (f49 (f50 f51 ?v0) ?v1) ?v2) f1) (exists ((?v3 S6)) (= (f3 (f4 (f5 (f6 f7 ?v0) ?v1) ?v3) ?v2) f1)))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S17)) (= (f53 f56 (f25 (f26 (f27 f28 ?v0) ?v1) ?v2)) f52)))
(assert (forall ((?v0 S6)) (=> (not (= ?v0 f52)) (exists ((?v1 S6)) (= ?v0 (f29 f30 ?v1))))))
(assert (forall ((?v0 S41) (?v1 S6)) (=> (= (f57 ?v0 f52) f1) (=> (forall ((?v2 S6)) (=> (= (f57 ?v0 ?v2) f1) (= (f57 ?v0 (f29 f30 ?v2)) f1))) (= (f57 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S41) (?v1 S6)) (=> (= (f57 ?v0 ?v1) f1) (=> (forall ((?v2 S6)) (=> (= (f57 ?v0 (f29 f30 ?v2)) f1) (= (f57 ?v0 ?v2) f1))) (= (f57 ?v0 f52) f1)))))
(assert (forall ((?v0 S6)) (=> (=> (= ?v0 f52) false) (=> (forall ((?v1 S6)) (=> (= ?v0 (f29 f30 ?v1)) false)) false))))
(assert (forall ((?v0 S17) (?v1 S42) (?v2 S17)) (= (f18 (f19 f20 f52) (f25 (f26 (f27 f28 ?v0) (f58 f59 ?v1)) ?v2)) f1)))
(assert (= (f60 f61 f31) f52))
(assert (forall ((?v0 S26) (?v1 S27)) (= (f60 f61 (f38 (f39 f40 ?v0) ?v1)) f52)))
(assert (forall ((?v0 S42)) (= (f60 f61 (f58 f59 ?v0)) f52)))
(assert (forall ((?v0 S42) (?v1 S42)) (= (= (f58 f59 ?v0) (f58 f59 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S42)) (not (= (f9 (f10 f11 ?v0) ?v1) (f58 f59 ?v2)))))
(assert (forall ((?v0 S42) (?v1 S4) (?v2 S2)) (not (= (f58 f59 ?v0) (f9 (f10 f11 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S42)) (not (= (f9 (f32 (f36 f37 ?v0) ?v1) ?v2) (f58 f59 ?v3)))))
(assert (forall ((?v0 S42) (?v1 S4) (?v2 S2) (?v3 S2)) (not (= (f58 f59 ?v0) (f9 (f32 (f36 f37 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S30) (?v1 S27) (?v2 S2) (?v3 S42)) (not (= (f9 (f41 (f42 f43 ?v0) ?v1) ?v2) (f58 f59 ?v3)))))
(assert (forall ((?v0 S26) (?v1 S27) (?v2 S42)) (not (= (f38 (f39 f40 ?v0) ?v1) (f58 f59 ?v2)))))
(assert (forall ((?v0 S42) (?v1 S30) (?v2 S27) (?v3 S2)) (not (= (f58 f59 ?v0) (f9 (f41 (f42 f43 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S42) (?v1 S26) (?v2 S27)) (not (= (f58 f59 ?v0) (f38 (f39 f40 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S42)) (not (= (f9 (f32 f33 ?v0) ?v1) (f58 f59 ?v2)))))
(assert (forall ((?v0 S42) (?v1 S2) (?v2 S2)) (not (= (f58 f59 ?v0) (f9 (f32 f33 ?v1) ?v2)))))
(assert (forall ((?v0 S42)) (not (= f31 (f58 f59 ?v0)))))
(assert (forall ((?v0 S42)) (not (= (f58 f59 ?v0) f31))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f60 f61 (f9 (f32 f33 ?v0) ?v1)) (f29 (f62 f63 (f29 (f62 f63 (f60 f61 ?v0)) (f60 f61 ?v1))) (f29 f30 f52)))))
(assert (forall ((?v0 S30) (?v1 S27) (?v2 S2)) (= (f60 f61 (f9 (f41 (f42 f43 ?v0) ?v1) ?v2)) (f29 (f62 f63 (f60 f61 ?v2)) (f29 f30 f52)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (= (f60 f61 (f9 (f32 (f36 f37 ?v0) ?v1) ?v2)) (f29 (f62 f63 (f29 (f62 f63 (f60 f61 ?v1)) (f60 f61 ?v2))) (f29 f30 f52)))))
(assert (forall ((?v0 S4) (?v1 S2)) (= (f60 f61 (f9 (f10 f11 ?v0) ?v1)) (f29 (f62 f63 (f60 f61 ?v1)) (f29 f30 f52)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f29 (f62 f63 ?v0) ?v1) ?v0) (= ?v1 f52))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f29 (f62 f63 ?v0) ?v1) f52) (and (= ?v0 f52) (= ?v1 f52)))))
(assert (forall ((?v0 S6)) (= (f29 (f62 f63 ?v0) f52) ?v0)))
(assert (forall ((?v0 S6)) (= (f29 (f62 f63 f52) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f62 f63 ?v0))) (= (f29 ?v_0 (f29 f30 ?v1)) (f29 f30 (f29 ?v_0 ?v1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f29 (f62 f63 (f29 f30 ?v0)) ?v1) (f29 f30 (f29 (f62 f63 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f29 (f62 f63 (f29 f30 ?v0)) ?v1) (f29 (f62 f63 ?v0) (f29 f30 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f29 (f62 f63 ?v0) ?v1) (f29 (f62 f63 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f62 f63 ?v0)) (?v_0 (f62 f63 ?v1))) (= (f29 ?v_1 (f29 ?v_0 ?v2)) (f29 ?v_0 (f29 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f62 f63 ?v0))) (= (f29 (f62 f63 (f29 ?v_0 ?v1)) ?v2) (f29 ?v_0 (f29 (f62 f63 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f62 f63 ?v0))) (= (= (f29 ?v_0 ?v1) (f29 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f29 (f62 f63 ?v0) ?v1) (f29 (f62 f63 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f29 f30 f52))) (= (= (f29 (f62 f63 ?v0) ?v1) ?v_0) (or (and (= ?v0 ?v_0) (= ?v1 f52)) (and (= ?v0 f52) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f29 f30 f52))) (= (= ?v_0 (f29 (f62 f63 ?v0) ?v1)) (or (and (= ?v0 ?v_0) (= ?v1 f52)) (and (= ?v0 f52) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S6)) (= (f29 (f62 f63 f52) ?v0) ?v0)))
(assert (forall ((?v0 S46)) (= (f64 (f65 f66 f67) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f29 (f62 f63 f52) ?v0) ?v0)))
(assert (forall ((?v0 S46)) (= (f64 (f65 f66 f67) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f29 (f62 f63 f52) ?v0) ?v0)))
(assert (forall ((?v0 S46)) (= (f64 (f65 f66 f67) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (= f52 ?v0) (= ?v0 f52))))
(assert (forall ((?v0 S46)) (= (= f67 ?v0) (= ?v0 f67))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f29 (f62 f63 ?v0) ?v1) (f29 (f62 f63 ?v1) ?v0))))
(assert (forall ((?v0 S46) (?v1 S46)) (= (f64 (f65 f66 ?v0) ?v1) (f64 (f65 f66 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f62 f63 ?v0)) (?v_0 (f62 f63 ?v1))) (= (f29 ?v_1 (f29 ?v_0 ?v2)) (f29 ?v_0 (f29 ?v_1 ?v2))))))
(assert (forall ((?v0 S46) (?v1 S46) (?v2 S46)) (let ((?v_1 (f65 f66 ?v0)) (?v_0 (f65 f66 ?v1))) (= (f64 ?v_1 (f64 ?v_0 ?v2)) (f64 ?v_0 (f64 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f62 f63 ?v0))) (= (f29 ?v_0 (f29 (f62 f63 ?v1) ?v2)) (f29 (f62 f63 (f29 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S46) (?v1 S46) (?v2 S46)) (let ((?v_0 (f65 f66 ?v0))) (= (f64 ?v_0 (f64 (f65 f66 ?v1) ?v2)) (f64 (f65 f66 (f64 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f62 f63 ?v0))) (= (f29 (f62 f63 (f29 ?v_0 ?v1)) ?v2) (f29 ?v_0 (f29 (f62 f63 ?v1) ?v2))))))
(assert (forall ((?v0 S46) (?v1 S46) (?v2 S46)) (let ((?v_0 (f65 f66 ?v0))) (= (f64 (f65 f66 (f64 ?v_0 ?v1)) ?v2) (f64 ?v_0 (f64 (f65 f66 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f62 f63 ?v0))) (= (f29 (f62 f63 (f29 ?v_0 ?v1)) ?v2) (f29 ?v_0 (f29 (f62 f63 ?v1) ?v2))))))
(assert (forall ((?v0 S46) (?v1 S46) (?v2 S46)) (let ((?v_0 (f65 f66 ?v0))) (= (f64 (f65 f66 (f64 ?v_0 ?v1)) ?v2) (f64 ?v_0 (f64 (f65 f66 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f62 f63 ?v0))) (= (f29 (f62 f63 (f29 ?v_0 ?v1)) ?v2) (f29 (f62 f63 (f29 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S46) (?v1 S46) (?v2 S46)) (let ((?v_0 (f65 f66 ?v0))) (= (f64 (f65 f66 (f64 ?v_0 ?v1)) ?v2) (f64 (f65 f66 (f64 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f62 f63 ?v0))) (= (= (f29 ?v_0 ?v1) (f29 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S46) (?v1 S46) (?v2 S46)) (let ((?v_0 (f65 f66 ?v0))) (= (= (f64 ?v_0 ?v1) (f64 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f29 (f62 f63 ?v0) ?v1) (f29 (f62 f63 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S46) (?v1 S46) (?v2 S46)) (= (= (f64 (f65 f66 ?v0) ?v1) (f64 (f65 f66 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f62 f63 ?v0))) (= (f29 (f62 f63 (f29 ?v_0 ?v1)) (f29 (f62 f63 ?v2) ?v3)) (f29 (f62 f63 (f29 ?v_0 ?v2)) (f29 (f62 f63 ?v1) ?v3))))))
(assert (forall ((?v0 S46) (?v1 S46) (?v2 S46) (?v3 S46)) (let ((?v_0 (f65 f66 ?v0))) (= (f64 (f65 f66 (f64 ?v_0 ?v1)) (f64 (f65 f66 ?v2) ?v3)) (f64 (f65 f66 (f64 ?v_0 ?v2)) (f64 (f65 f66 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f29 ?v_0 ?v1) (f29 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S46) (?v1 S46) (?v2 S46)) (let ((?v_0 (f65 f66 ?v0))) (=> (= (f64 ?v_0 ?v1) (f64 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f29 ?v_0 ?v1) (f29 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S46) (?v1 S46) (?v2 S46)) (let ((?v_0 (f65 f66 ?v0))) (=> (= (f64 ?v_0 ?v1) (f64 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f29 (f62 f63 ?v0) ?v1) (f29 (f62 f63 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S46) (?v1 S46) (?v2 S46)) (=> (= (f64 (f65 f66 ?v0) ?v1) (f64 (f65 f66 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= ?v0 (f29 (f62 f63 ?v0) ?v1)) (= ?v1 f52))))
(assert (forall ((?v0 S46) (?v1 S46)) (= (= ?v0 (f64 (f65 f66 ?v0) ?v1)) (= ?v1 f67))))
(assert (forall ((?v0 S6)) (= (f29 (f62 f63 ?v0) f52) ?v0)))
(assert (forall ((?v0 S46)) (= (f64 (f65 f66 ?v0) f67) ?v0)))
(assert (forall ((?v0 S6)) (= (f29 (f62 f63 ?v0) f52) ?v0)))
(assert (forall ((?v0 S46)) (= (f64 (f65 f66 ?v0) f67) ?v0)))
(assert (forall ((?v0 S6)) (= (f29 (f62 f63 ?v0) f52) ?v0)))
(assert (forall ((?v0 S46)) (= (f64 (f65 f66 ?v0) f67) ?v0)))
(assert (forall ((?v0 S46)) (= (= f67 (f64 (f65 f66 ?v0) ?v0)) (= ?v0 f67))))
(assert (forall ((?v0 S46)) (= (= (f64 (f65 f66 ?v0) ?v0) f67) (= ?v0 f67))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f60 f68 (f9 (f32 f33 ?v0) ?v1)) (f29 (f62 f63 (f29 (f62 f63 (f60 f68 ?v0)) (f60 f68 ?v1))) (f29 f30 f52)))))
(assert (forall ((?v0 S30) (?v1 S27) (?v2 S2)) (= (f60 f68 (f9 (f41 (f42 f43 ?v0) ?v1) ?v2)) (f29 (f62 f63 (f60 f68 ?v2)) (f29 f30 f52)))))
(assert (forall ((?v0 S42)) (= (f60 f68 (f58 f59 ?v0)) f52)))
(assert (forall ((?v0 S26) (?v1 S27)) (= (f60 f68 (f38 (f39 f40 ?v0) ?v1)) f52)))
(assert (= (f60 f68 f31) f52))
(assert (forall ((?v0 S4) (?v1 S2)) (= (f60 f68 (f9 (f10 f11 ?v0) ?v1)) (f29 (f62 f63 (f60 f68 ?v1)) (f29 f30 f52)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (= (f60 f68 (f9 (f32 (f36 f37 ?v0) ?v1) ?v2)) (f29 (f62 f63 (f29 (f62 f63 (f60 f68 ?v1)) (f60 f68 ?v2))) (f29 f30 f52)))))
(assert (forall ((?v0 S6)) (= (f29 f69 (f29 f30 ?v0)) (f29 (f62 f63 (f29 f69 ?v0)) (f29 f30 f52)))))
(assert (forall ((?v0 S6)) (= (f29 f70 (f29 f30 ?v0)) (f29 (f62 f63 (f29 f70 ?v0)) (f29 f30 f52)))))
(assert (= (f29 f70 f52) f52))
(assert (forall ((?v0 S6)) (= (f29 f70 ?v0) ?v0)))
(assert (= (f29 f69 f52) f52))
(assert (= (f71 f72 f1) f52))
(assert (= (f71 f72 f2) f52))
(assert (forall ((?v0 S26) (?v1 S42) (?v2 S27)) (=> (= (f34 f35 (f38 (f73 (f74 f75 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f34 f35 (f58 f59 ?v1)) f1) false) false))))
(assert (forall ((?v0 S6) (?v1 S17) (?v2 S42) (?v3 S17)) (let ((?v_0 (f27 f28 ?v1))) (= (= (f18 (f19 f20 ?v0) (f25 (f26 ?v_0 (f76 f77 (f78 f79 ?v2))) ?v3)) f1) (= (f18 (f19 f20 (f29 f30 ?v0)) (f25 (f26 ?v_0 (f58 f59 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S42) (?v1 S3) (?v2 S3)) (=> (= (f3 (f49 (f50 f51 (f76 f77 (f78 f79 ?v0))) ?v1) ?v2) f1) (= (f3 (f49 (f50 f51 (f58 f59 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S42) (?v1 S3) (?v2 S3)) (=> (= (f3 (f49 (f50 f51 (f58 f59 ?v0)) ?v1) ?v2) f1) (=> (=> (= (f3 (f49 (f50 f51 (f76 f77 (f78 f79 ?v0))) ?v1) ?v2) f1) false) false))))
(assert (forall ((?v0 S42) (?v1 S3) (?v2 S6) (?v3 S3)) (=> (= (f3 (f4 (f5 (f6 f7 (f76 f77 (f78 f79 ?v0))) ?v1) ?v2) ?v3) f1) (= (f3 (f4 (f5 (f6 f7 (f58 f59 ?v0)) ?v1) (f29 f30 ?v2)) ?v3) f1))))
(assert (forall ((?v0 S42) (?v1 S26) (?v2 S42) (?v3 S27)) (not (= (f58 f59 ?v0) (f38 (f73 (f74 f75 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S26) (?v1 S42) (?v2 S27) (?v3 S42)) (not (= (f38 (f73 (f74 f75 ?v0) ?v1) ?v2) (f58 f59 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S26) (?v3 S42) (?v4 S27)) (not (= (f9 (f10 f11 ?v0) ?v1) (f38 (f73 (f74 f75 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S26) (?v1 S42) (?v2 S27) (?v3 S4) (?v4 S2)) (not (= (f38 (f73 (f74 f75 ?v0) ?v1) ?v2) (f9 (f10 f11 ?v3) ?v4)))))
(assert (forall ((?v0 S26) (?v1 S42) (?v2 S27) (?v3 S4) (?v4 S2) (?v5 S2)) (not (= (f38 (f73 (f74 f75 ?v0) ?v1) ?v2) (f9 (f32 (f36 f37 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S26) (?v4 S42) (?v5 S27)) (not (= (f9 (f32 (f36 f37 ?v0) ?v1) ?v2) (f38 (f73 (f74 f75 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S26) (?v3 S42) (?v4 S27)) (not (= (f9 (f32 f33 ?v0) ?v1) (f38 (f73 (f74 f75 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S26) (?v1 S42) (?v2 S27) (?v3 S2) (?v4 S2)) (not (= (f38 (f73 (f74 f75 ?v0) ?v1) ?v2) (f9 (f32 f33 ?v3) ?v4)))))
(assert (forall ((?v0 S26) (?v1 S27) (?v2 S26) (?v3 S42) (?v4 S27)) (not (= (f38 (f39 f40 ?v0) ?v1) (f38 (f73 (f74 f75 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S26) (?v1 S42) (?v2 S27) (?v3 S26) (?v4 S27)) (not (= (f38 (f73 (f74 f75 ?v0) ?v1) ?v2) (f38 (f39 f40 ?v3) ?v4)))))
(assert (forall ((?v0 S26) (?v1 S42) (?v2 S27) (?v3 S30) (?v4 S27) (?v5 S2)) (not (= (f38 (f73 (f74 f75 ?v0) ?v1) ?v2) (f9 (f41 (f42 f43 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S30) (?v1 S27) (?v2 S2) (?v3 S26) (?v4 S42) (?v5 S27)) (not (= (f9 (f41 (f42 f43 ?v0) ?v1) ?v2) (f38 (f73 (f74 f75 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S26) (?v1 S42) (?v2 S27)) (not (= (f38 (f73 (f74 f75 ?v0) ?v1) ?v2) f31))))
(assert (forall ((?v0 S26) (?v1 S42) (?v2 S27)) (not (= f31 (f38 (f73 (f74 f75 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S42) (?v2 S27) (?v3 S26) (?v4 S42) (?v5 S27)) (= (= (f38 (f73 (f74 f75 ?v0) ?v1) ?v2) (f38 (f73 (f74 f75 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S26) (?v1 S42) (?v2 S27)) (= (f60 f61 (f38 (f73 (f74 f75 ?v0) ?v1) ?v2)) f52)))
(assert (forall ((?v0 S26) (?v1 S42) (?v2 S27)) (= (f60 f68 (f38 (f73 (f74 f75 ?v0) ?v1) ?v2)) f52)))
(assert (forall ((?v0 S42) (?v1 S26) (?v2 S27)) (=> (= (f34 f35 (f58 f59 ?v0)) f1) (= (f34 f35 (f38 (f73 (f74 f75 ?v1) ?v0) ?v2)) f1))))
(assert (forall ((?v0 S42) (?v1 S3) (?v2 S6) (?v3 S3)) (=> (= (f3 (f4 (f5 (f6 f7 (f58 f59 ?v0)) ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S6)) (=> (= ?v2 (f29 f30 ?v4)) (=> (= (f3 (f4 (f5 (f6 f7 (f76 f77 (f78 f79 ?v0))) ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S2)) (=> (=> (= ?v0 f31) false) (=> (forall ((?v1 S26) (?v2 S27)) (=> (= ?v0 (f38 (f39 f40 ?v1) ?v2)) false)) (=> (forall ((?v1 S30) (?v2 S27) (?v3 S2)) (=> (= ?v0 (f9 (f41 (f42 f43 ?v1) ?v2) ?v3)) false)) (=> (forall ((?v1 S2) (?v2 S2)) (=> (= ?v0 (f9 (f32 f33 ?v1) ?v2)) false)) (=> (forall ((?v1 S4) (?v2 S2) (?v3 S2)) (=> (= ?v0 (f9 (f32 (f36 f37 ?v1) ?v2) ?v3)) false)) (=> (forall ((?v1 S4) (?v2 S2)) (=> (= ?v0 (f9 (f10 f11 ?v1) ?v2)) false)) (=> (forall ((?v1 S42)) (=> (= ?v0 (f58 f59 ?v1)) false)) (=> (forall ((?v1 S26) (?v2 S42) (?v3 S27)) (=> (= ?v0 (f38 (f73 (f74 f75 ?v1) ?v2) ?v3)) false)) false))))))))))
(assert (forall ((?v0 S42)) (=> (not (= (f78 f79 ?v0) f80)) (= (f34 f35 (f58 f59 ?v0)) f1))))
(assert (forall ((?v0 S1)) (= (f71 f81 ?v0) f52)))
(assert (= (f71 f81 f1) f52))
(assert (= (f71 f81 f2) f52))
(assert (forall ((?v0 S44)) (= (f84 (f82 f83 ?v0) f80) f52)))
(assert (= (f84 f85 f80) f52))
(assert (forall ((?v0 S2)) (= (= (f34 f35 ?v0) f1) (or (= ?v0 f31) (or (exists ((?v1 S26) (?v2 S27)) (= ?v0 (f38 (f39 f40 ?v1) ?v2))) (or (exists ((?v1 S2) (?v2 S30) (?v3 S27)) (and (= ?v0 (f9 (f41 (f42 f43 ?v2) ?v3) ?v1)) (= (f34 f35 ?v1) f1))) (or (exists ((?v1 S2) (?v2 S2)) (and (= ?v0 (f9 (f32 f33 ?v1) ?v2)) (and (= (f34 f35 ?v1) f1) (= (f34 f35 ?v2) f1)))) (or (exists ((?v1 S2) (?v2 S2) (?v3 S4)) (and (= ?v0 (f9 (f32 (f36 f37 ?v3) ?v1) ?v2)) (and (= (f34 f35 ?v1) f1) (= (f34 f35 ?v2) f1)))) (or (exists ((?v1 S2) (?v2 S4)) (and (= ?v0 (f9 (f10 f11 ?v2) ?v1)) (= (f34 f35 ?v1) f1))) (or (exists ((?v1 S42)) (and (= ?v0 (f58 f59 ?v1)) (not (= (f78 f79 ?v1) f80)))) (exists ((?v1 S42) (?v2 S26) (?v3 S27)) (and (= ?v0 (f38 (f73 (f74 f75 ?v2) ?v1) ?v3)) (= (f34 f35 (f58 f59 ?v1)) f1)))))))))))))
(assert (forall ((?v0 S44) (?v1 S2)) (= (f84 (f82 f83 ?v0) (f86 f87 ?v1)) (f29 (f62 f63 (f60 ?v0 ?v1)) (f29 f30 f52)))))
(assert (forall ((?v0 S2)) (= (f84 f85 (f86 f87 ?v0)) f52)))
(assert (forall ((?v0 S42)) (=> (= (f34 f35 (f58 f59 ?v0)) f1) (=> (forall ((?v1 S2)) (=> (= (f78 f79 ?v0) (f86 f87 ?v1)) false)) false))))
(assert (forall ((?v0 S42) (?v1 S2)) (=> (= f88 f1) (=> (= (f78 f79 ?v0) (f86 f87 ?v1)) (= (f34 f35 ?v1) f1)))))
(assert (forall ((?v0 S2)) (= (f76 f77 (f86 f87 ?v0)) ?v0)))
(assert (forall ((?v0 S53)) (= (not (= ?v0 f80)) (exists ((?v1 S2)) (= ?v0 (f86 f87 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f86 f87 ?v0) (f86 f87 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2)) (not (= f80 (f86 f87 ?v0)))))
(assert (forall ((?v0 S2)) (not (= (f86 f87 ?v0) f80))))
(assert (forall ((?v0 S53)) (= (forall ((?v1 S2)) (not (= ?v0 (f86 f87 ?v1)))) (= ?v0 f80))))
(assert (forall ((?v0 S53)) (=> (=> (= ?v0 f80) false) (=> (forall ((?v1 S2)) (=> (= ?v0 (f86 f87 ?v1)) false)) false))))
(assert (forall ((?v0 S2)) (= (= (f89 f90 (f86 f87 ?v0)) f1) false)))
(assert (forall ((?v0 S53)) (= (= (f89 f90 ?v0) f1) (= ?v0 f80))))
(assert (= (= (f89 f90 f80) f1) true))
(check-sat)
(exit)