(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unsat)
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
(declare-sort S59 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S6) S1)
(declare-fun f7 (S5) S5)
(declare-fun f8 (S7 S6) S6)
(declare-fun f9 () S7)
(declare-fun f10 () S8)
(declare-fun f11 (S9 S8) S8)
(declare-fun f12 (S10 S3) S9)
(declare-fun f13 () S10)
(declare-fun f14 () S3)
(declare-fun f15 () S8)
(declare-fun f16 (S11 S12) S1)
(declare-fun f17 () S12)
(declare-fun f18 (S12 S11) S1)
(declare-fun f19 (S6) S12)
(declare-fun f20 () S6)
(declare-fun f21 (S13) S3)
(declare-fun f22 () S2)
(declare-fun f23 (S14 S6) S3)
(declare-fun f24 (S15 S2) S14)
(declare-fun f25 (S8) S15)
(declare-fun f26 (S12 S12) S1)
(declare-fun f27 (S16 S16) S1)
(declare-fun f28 (S17 S16) S1)
(declare-fun f29 (S16 S17) S1)
(declare-fun f30 (S6) S16)
(declare-fun f31 (S19 S18) S11)
(declare-fun f32 (S20 S8) S19)
(declare-fun f33 (S21 S18) S20)
(declare-fun f34 () S21)
(declare-fun f35 (S18 S13) S3)
(declare-fun f36 (S22 S4) S17)
(declare-fun f37 (S23 S8) S22)
(declare-fun f38 (S24 S4) S23)
(declare-fun f39 () S24)
(declare-fun f40 (S25 S8) S9)
(declare-fun f41 () S25)
(declare-fun f42 (S8) S1)
(declare-fun f43 (S26 S3) S25)
(declare-fun f44 () S26)
(declare-fun f45 (S29 S28) S8)
(declare-fun f46 (S30 S27) S29)
(declare-fun f47 () S30)
(declare-fun f48 (S31 S6) S2)
(declare-fun f49 (S32 S27) S31)
(declare-fun f50 (S33 S2) S32)
(declare-fun f51 () S33)
(declare-fun f52 (S28 S2) S6)
(declare-fun f53 (S35 S28) S9)
(declare-fun f54 (S36 S34) S35)
(declare-fun f55 () S36)
(declare-fun f56 () S6)
(declare-fun f57 (S37 S17) S6)
(declare-fun f58 (S38 S28) S37)
(declare-fun f59 () S38)
(declare-fun f60 (S40 S11) S6)
(declare-fun f61 (S41 S39) S40)
(declare-fun f62 () S41)
(declare-fun f63 () S37)
(declare-fun f64 () S40)
(declare-fun f65 (S43 S42) S8)
(declare-fun f66 () S43)
(declare-fun f67 (S44 S8) S6)
(declare-fun f68 () S44)
(declare-fun f69 (S45 S5) S6)
(declare-fun f70 () S45)
(declare-fun f71 (S46 S6) S7)
(declare-fun f72 () S46)
(declare-fun f73 (S48 S47) S47)
(declare-fun f74 (S49 S47) S48)
(declare-fun f75 () S49)
(declare-fun f76 () S47)
(declare-fun f77 () S44)
(declare-fun f78 () S7)
(declare-fun f79 () S7)
(declare-fun f80 (S50 S1) S6)
(declare-fun f81 () S50)
(declare-fun f82 (S51 S42) S29)
(declare-fun f83 (S52 S27) S51)
(declare-fun f84 () S52)
(declare-fun f85 (S8) S4)
(declare-fun f86 (S53 S8) S17)
(declare-fun f87 () S53)
(declare-fun f88 (S54 S55) S8)
(declare-fun f89 () S54)
(declare-fun f90 (S56 S42) S55)
(declare-fun f91 () S56)
(declare-fun f92 () S55)
(declare-fun f93 (S57 S44) S58)
(declare-fun f94 () S57)
(declare-fun f95 (S58 S55) S6)
(declare-fun f96 () S58)
(declare-fun f97 (S59 S8) S55)
(declare-fun f98 () S59)
(declare-fun f99 () S1)
(declare-fun f100 (S55) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S6)) (= (= (f6 (f7 ?v0) ?v1) f1) (= (f6 ?v0 (f8 f9 ?v1)) f1))))
(assert (not (=> (= f10 (f11 (f12 f13 f14) f15)) (=> (forall ((?v0 S11)) (=> (= (f16 ?v0 f17) f1) (= (f18 (f19 f20) ?v0) f1))) (forall ((?v0 S13)) (let ((?v_0 (= (f3 (f21 ?v0) f22) f1))) (=> ?v_0 (and ?v_0 (not (= (f3 f14 f22) f1))))))))))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S11)) (=> (= (f16 ?v1 f17) f1) (= (f18 (f19 ?v0) ?v1) f1))) (forall ((?v1 S13) (?v2 S2)) (=> (and (= (f3 (f21 ?v1) ?v2) f1) (= (f3 f14 ?v2) f1)) (forall ((?v3 S2)) (=> (= (f3 (f23 (f24 (f25 f15) ?v2) ?v0) ?v3) f1) (= (f3 (f21 ?v1) ?v3) f1))))))))
(assert (forall ((?v0 S2) (?v1 S6)) (= (f3 (f23 (f24 (f25 f10) ?v0) ?v1) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S2)) (=> (= (f3 (f23 (f24 (f25 f10) ?v0) ?v1) ?v2) f1) (=> (=> (= ?v2 ?v0) false) false))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S8) (?v3 S6)) (=> (not (= (f3 ?v0 ?v1) f1)) (= (f3 (f23 (f24 (f25 (f11 (f12 f13 ?v0) ?v2)) ?v1) ?v3) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S8) (?v3 S6) (?v4 S2) (?v5 S2)) (let ((?v_0 (f25 (f11 (f12 f13 ?v0) ?v2)))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 (f23 (f24 (f25 ?v2) ?v1) ?v3) ?v4) f1) (=> (= (f3 (f23 (f24 ?v_0 ?v4) ?v3) ?v5) f1) (= (f3 (f23 (f24 ?v_0 ?v1) ?v3) ?v5) f1)))))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f26 ?v0 ?v1) f1) (forall ((?v2 S6)) (=> (forall ((?v3 S11)) (=> (= (f16 ?v3 ?v0) f1) (= (f18 (f19 ?v2) ?v3) f1))) (forall ((?v3 S11)) (=> (= (f16 ?v3 ?v1) f1) (= (f18 (f19 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S16) (?v1 S16)) (= (= (f27 ?v0 ?v1) f1) (forall ((?v2 S6)) (=> (forall ((?v3 S17)) (=> (= (f28 ?v3 ?v0) f1) (= (f29 (f30 ?v2) ?v3) f1))) (forall ((?v3 S17)) (=> (= (f28 ?v3 ?v1) f1) (= (f29 (f30 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S3) (?v1 S8)) (not (= f10 (f11 (f12 f13 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S8)) (not (= (f11 (f12 f13 ?v0) ?v1) f10))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S3) (?v3 S8)) (= (= (f11 (f12 f13 ?v0) ?v1) (f11 (f12 f13 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S2) (?v3 S6) (?v4 S2)) (=> (= (f3 (f23 (f24 (f25 (f11 (f12 f13 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (=> (= ?v4 ?v2) (=> (not (= (f3 ?v0 ?v2) f1)) false)) (=> (forall ((?v5 S2)) (=> (= (f3 ?v0 ?v2) f1) (=> (= (f3 (f23 (f24 (f25 ?v1) ?v2) ?v3) ?v5) f1) (=> (= (f3 (f23 (f24 (f25 (f11 (f12 f13 ?v0) ?v1)) ?v5) ?v3) ?v4) f1) false)))) false)))))
(assert (forall ((?v0 S6) (?v1 S18) (?v2 S8) (?v3 S18)) (= (= (f18 (f19 ?v0) (f31 (f32 (f33 f34 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S13) (?v5 S2)) (=> (= (f3 (f35 ?v1 ?v4) ?v5) f1) (forall ((?v6 S2)) (=> (= (f3 (f23 (f24 (f25 ?v2) ?v5) ?v0) ?v6) f1) (= (f3 (f35 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S8) (?v3 S4)) (= (= (f29 (f30 ?v0) (f36 (f37 (f38 f39 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f4 ?v1 ?v4) ?v5) f1) (forall ((?v6 S2)) (=> (= (f3 (f23 (f24 (f25 ?v2) ?v5) ?v0) ?v6) f1) (= (f3 (f4 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S6) (?v3 S2) (?v4 S8) (?v5 S2) (?v6 S6) (?v7 S2)) (=> (= (f3 (f23 (f24 (f25 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f3 (f23 (f24 (f25 ?v4) ?v5) ?v6) ?v7) f1) (exists ((?v8 S6)) (and (= (f3 (f23 (f24 (f25 ?v0) ?v1) ?v8) ?v3) f1) (= (f3 (f23 (f24 (f25 ?v4) ?v5) ?v8) ?v7) f1)))))))
(assert (forall ((?v0 S12) (?v1 S6)) (=> (forall ((?v2 S11)) (=> (= (f16 ?v2 ?v0) f1) (= (f18 (f19 (f8 f9 ?v1)) ?v2) f1))) (forall ((?v2 S11)) (=> (= (f16 ?v2 ?v0) f1) (= (f18 (f19 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S16) (?v1 S6)) (=> (forall ((?v2 S17)) (=> (= (f28 ?v2 ?v0) f1) (= (f29 (f30 (f8 f9 ?v1)) ?v2) f1))) (forall ((?v2 S17)) (=> (= (f28 ?v2 ?v0) f1) (= (f29 (f30 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S4) (?v1 S8) (?v2 S4) (?v3 S4) (?v4 S8) (?v5 S4)) (= (= (f36 (f37 (f38 f39 ?v0) ?v1) ?v2) (f36 (f37 (f38 f39 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S18) (?v1 S8) (?v2 S18) (?v3 S18) (?v4 S8) (?v5 S18)) (= (= (f31 (f32 (f33 f34 ?v0) ?v1) ?v2) (f31 (f32 (f33 f34 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S6) (?v3 S2)) (let ((?v_0 (f24 (f25 ?v0) ?v1))) (=> (= (f3 (f23 ?v_0 ?v2) ?v3) f1) (= (f3 (f23 ?v_0 (f8 f9 ?v2)) ?v3) f1)))))
(assert (forall ((?v0 S6) (?v1 S11)) (=> (= (f18 (f19 (f8 f9 ?v0)) ?v1) f1) (= (f18 (f19 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S17)) (=> (= (f29 (f30 (f8 f9 ?v0)) ?v1) f1) (= (f29 (f30 ?v0) ?v1) f1))))
(assert (forall ((?v0 S17)) (=> (forall ((?v1 S4) (?v2 S8) (?v3 S4)) (=> (= ?v0 (f36 (f37 (f38 f39 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S11)) (=> (forall ((?v1 S18) (?v2 S8) (?v3 S18)) (=> (= ?v0 (f31 (f32 (f33 f34 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S6)) (not (= ?v0 (f8 f9 ?v0)))))
(assert (forall ((?v0 S6)) (not (= (f8 f9 ?v0) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f8 f9 ?v0) (f8 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f8 f9 ?v0) (f8 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S6) (?v3 S2) (?v4 S8) (?v5 S2)) (=> (= (f3 (f23 (f24 (f25 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f3 (f23 (f24 (f25 ?v4) ?v3) ?v2) ?v5) f1) (= (f3 (f23 (f24 (f25 (f11 (f40 f41 ?v0) ?v4)) ?v1) ?v2) ?v5) f1)))))
(assert (=> (= (f42 f10) f1) (=> false false)))
(assert (forall ((?v0 S3) (?v1 S8)) (=> (= (f42 (f11 (f12 f13 ?v0) ?v1)) f1) (=> (=> (= (f42 ?v1) f1) false) false))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f42 (f11 (f40 f41 ?v0) ?v1)) f1) (=> (=> (= (f42 ?v0) f1) (=> (= (f42 ?v1) f1) false)) false))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (= (= (f11 (f40 f41 ?v0) ?v1) (f11 (f40 f41 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f42 ?v0) f1) (=> (= (f42 ?v1) f1) (= (f42 (f11 (f40 f41 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S8) (?v1 S3)) (=> (= (f42 ?v0) f1) (= (f42 (f11 (f12 f13 ?v1) ?v0)) f1))))
(assert (= (f42 f10) f1))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S3) (?v3 S8)) (not (= (f11 (f40 f41 ?v0) ?v1) (f11 (f12 f13 ?v2) ?v3)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8) (?v3 S8)) (not (= (f11 (f12 f13 ?v0) ?v1) (f11 (f40 f41 ?v2) ?v3)))))
(assert (forall ((?v0 S8) (?v1 S8)) (not (= f10 (f11 (f40 f41 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (not (= (f11 (f40 f41 ?v0) ?v1) f10))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S2) (?v3 S6) (?v4 S2)) (=> (= (f3 (f23 (f24 (f25 (f11 (f40 f41 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (forall ((?v5 S2)) (=> (= (f3 (f23 (f24 (f25 ?v0) ?v2) ?v3) ?v5) f1) (=> (= (f3 (f23 (f24 (f25 ?v1) ?v5) ?v3) ?v4) f1) false))) false))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8)) (=> (= (f42 (f11 (f40 (f43 f44 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f42 ?v1) f1) (=> (= (f42 ?v2) f1) false)) false))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S8) (?v3 S6) (?v4 S2) (?v5 S8)) (=> (not (= (f3 ?v0 ?v1) f1)) (=> (= (f3 (f23 (f24 (f25 ?v2) ?v1) ?v3) ?v4) f1) (= (f3 (f23 (f24 (f25 (f11 (f40 (f43 f44 ?v0) ?v5) ?v2)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S8) (?v3 S6) (?v4 S2) (?v5 S8)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 (f23 (f24 (f25 ?v2) ?v1) ?v3) ?v4) f1) (= (f3 (f23 (f24 (f25 (f11 (f40 (f43 f44 ?v0) ?v2) ?v5)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8) (?v3 S2) (?v4 S6) (?v5 S2)) (let ((?v_0 (= (f3 ?v0 ?v3) f1))) (=> (= (f3 (f23 (f24 (f25 (f11 (f40 (f43 f44 ?v0) ?v1) ?v2)) ?v3) ?v4) ?v5) f1) (=> (=> ?v_0 (=> (= (f3 (f23 (f24 (f25 ?v1) ?v3) ?v4) ?v5) f1) false)) (=> (=> (not ?v_0) (=> (= (f3 (f23 (f24 (f25 ?v2) ?v3) ?v4) ?v5) f1) false)) false))))))
(assert (forall ((?v0 S27) (?v1 S28)) (=> (= (f42 (f45 (f46 f47 ?v0) ?v1)) f1) (=> false false))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8) (?v3 S3) (?v4 S8) (?v5 S8)) (= (= (f11 (f40 (f43 f44 ?v0) ?v1) ?v2) (f11 (f40 (f43 f44 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S27) (?v3 S28)) (= (= (f45 (f46 f47 ?v0) ?v1) (f45 (f46 f47 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8) (?v3 S27) (?v4 S28)) (not (= (f11 (f40 (f43 f44 ?v0) ?v1) ?v2) (f45 (f46 f47 ?v3) ?v4)))))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S3) (?v3 S8) (?v4 S8)) (not (= (f45 (f46 f47 ?v0) ?v1) (f11 (f40 (f43 f44 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S27) (?v1 S28)) (= (f42 (f45 (f46 f47 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S27) (?v3 S28)) (not (= (f11 (f12 f13 ?v0) ?v1) (f45 (f46 f47 ?v2) ?v3)))))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S3) (?v3 S8)) (not (= (f45 (f46 f47 ?v0) ?v1) (f11 (f12 f13 ?v2) ?v3)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S27) (?v3 S28)) (not (= (f11 (f40 f41 ?v0) ?v1) (f45 (f46 f47 ?v2) ?v3)))))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S8) (?v3 S8)) (not (= (f45 (f46 f47 ?v0) ?v1) (f11 (f40 f41 ?v2) ?v3)))))
(assert (forall ((?v0 S27) (?v1 S28)) (not (= (f45 (f46 f47 ?v0) ?v1) f10))))
(assert (forall ((?v0 S27) (?v1 S28)) (not (= f10 (f45 (f46 f47 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S3)) (=> (= (f42 ?v0) f1) (=> (= (f42 ?v1) f1) (= (f42 (f11 (f40 (f43 f44 ?v2) ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8) (?v3 S3) (?v4 S8)) (not (= (f11 (f40 (f43 f44 ?v0) ?v1) ?v2) (f11 (f12 f13 ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S3) (?v3 S8) (?v4 S8)) (not (= (f11 (f12 f13 ?v0) ?v1) (f11 (f40 (f43 f44 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8) (?v3 S8) (?v4 S8)) (not (= (f11 (f40 (f43 f44 ?v0) ?v1) ?v2) (f11 (f40 f41 ?v3) ?v4)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S3) (?v3 S8) (?v4 S8)) (not (= (f11 (f40 f41 ?v0) ?v1) (f11 (f40 (f43 f44 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8)) (not (= (f11 (f40 (f43 f44 ?v0) ?v1) ?v2) f10))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8)) (not (= f10 (f11 (f40 (f43 f44 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S2) (?v3 S6) (?v4 S2)) (=> (= (f3 (f23 (f24 (f25 (f45 (f46 f47 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (=> (= ?v4 (f48 (f49 (f50 f51 ?v2) ?v0) (f52 ?v1 ?v2))) false) false))))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S2) (?v3 S6)) (= (f3 (f23 (f24 (f25 (f45 (f46 f47 ?v0) ?v1)) ?v2) ?v3) (f48 (f49 (f50 f51 ?v2) ?v0) (f52 ?v1 ?v2))) f1)))
(assert (forall ((?v0 S34) (?v1 S28) (?v2 S8)) (=> (= (f42 (f11 (f53 (f54 f55 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f42 ?v2) f1) false) false))))
(assert (forall ((?v0 S34) (?v1 S28) (?v2 S8) (?v3 S34) (?v4 S28) (?v5 S8)) (= (= (f11 (f53 (f54 f55 ?v0) ?v1) ?v2) (f11 (f53 (f54 f55 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S6)) (=> (= (f8 f9 ?v0) f56) false)))
(assert (forall ((?v0 S6)) (=> (= f56 (f8 f9 ?v0)) false)))
(assert (forall ((?v0 S6)) (not (= (f8 f9 ?v0) f56))))
(assert (forall ((?v0 S6)) (not (= (f8 f9 ?v0) f56))))
(assert (forall ((?v0 S6)) (not (= f56 (f8 f9 ?v0)))))
(assert (forall ((?v0 S6)) (not (= f56 (f8 f9 ?v0)))))
(assert (forall ((?v0 S8) (?v1 S34) (?v2 S28)) (=> (= (f42 ?v0) f1) (= (f42 (f11 (f53 (f54 f55 ?v1) ?v2) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S34) (?v3 S28) (?v4 S8)) (not (= (f11 (f12 f13 ?v0) ?v1) (f11 (f53 (f54 f55 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S34) (?v1 S28) (?v2 S8) (?v3 S3) (?v4 S8)) (not (= (f11 (f53 (f54 f55 ?v0) ?v1) ?v2) (f11 (f12 f13 ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8) (?v3 S34) (?v4 S28) (?v5 S8)) (not (= (f11 (f40 (f43 f44 ?v0) ?v1) ?v2) (f11 (f53 (f54 f55 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S34) (?v1 S28) (?v2 S8) (?v3 S3) (?v4 S8) (?v5 S8)) (not (= (f11 (f53 (f54 f55 ?v0) ?v1) ?v2) (f11 (f40 (f43 f44 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S34) (?v3 S28) (?v4 S8)) (not (= (f11 (f40 f41 ?v0) ?v1) (f11 (f53 (f54 f55 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S34) (?v1 S28) (?v2 S8) (?v3 S8) (?v4 S8)) (not (= (f11 (f53 (f54 f55 ?v0) ?v1) ?v2) (f11 (f40 f41 ?v3) ?v4)))))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S34) (?v3 S28) (?v4 S8)) (not (= (f45 (f46 f47 ?v0) ?v1) (f11 (f53 (f54 f55 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S34) (?v1 S28) (?v2 S8) (?v3 S27) (?v4 S28)) (not (= (f11 (f53 (f54 f55 ?v0) ?v1) ?v2) (f45 (f46 f47 ?v3) ?v4)))))
(assert (forall ((?v0 S34) (?v1 S28) (?v2 S8)) (not (= f10 (f11 (f53 (f54 f55 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S34) (?v1 S28) (?v2 S8)) (not (= (f11 (f53 (f54 f55 ?v0) ?v1) ?v2) f10))))
(assert (forall ((?v0 S28) (?v1 S4) (?v2 S8) (?v3 S4)) (= (f57 (f58 f59 ?v0) (f36 (f37 (f38 f39 ?v1) ?v2) ?v3)) f56)))
(assert (forall ((?v0 S39) (?v1 S18) (?v2 S8) (?v3 S18)) (= (f60 (f61 f62 ?v0) (f31 (f32 (f33 f34 ?v1) ?v2) ?v3)) f56)))
(assert (forall ((?v0 S4) (?v1 S8) (?v2 S4)) (= (f57 f63 (f36 (f37 (f38 f39 ?v0) ?v1) ?v2)) f56)))
(assert (forall ((?v0 S18) (?v1 S8) (?v2 S18)) (= (f60 f64 (f31 (f32 (f33 f34 ?v0) ?v1) ?v2)) f56)))
(assert (forall ((?v0 S6)) (=> (=> (= ?v0 f56) false) (=> (forall ((?v1 S6)) (=> (= ?v0 (f8 f9 ?v1)) false)) false))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f6 ?v0 ?v1) f1) (=> (forall ((?v2 S6)) (=> (= (f6 ?v0 (f8 f9 ?v2)) f1) (= (f6 ?v0 ?v2) f1))) (= (f6 ?v0 f56) f1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f6 ?v0 f56) f1) (=> (forall ((?v2 S6)) (=> (= (f6 ?v0 ?v2) f1) (= (f6 ?v0 (f8 f9 ?v2)) f1))) (= (f6 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S6)) (=> (not (= ?v0 f56)) (exists ((?v1 S6)) (= ?v0 (f8 f9 ?v1))))))
(assert (forall ((?v0 S18) (?v1 S42) (?v2 S18)) (= (f18 (f19 f56) (f31 (f32 (f33 f34 ?v0) (f65 f66 ?v1)) ?v2)) f1)))
(assert (forall ((?v0 S4) (?v1 S42) (?v2 S4)) (= (f29 (f30 f56) (f36 (f37 (f38 f39 ?v0) (f65 f66 ?v1)) ?v2)) f1)))
(assert (= (f67 f68 f10) f56))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f6 ?v0 ?v1) f1) (=> (not (= (f6 ?v0 f56) f1)) (= (f69 f70 ?v0) (f8 f9 (f69 f70 (f7 ?v0))))))))
(assert (forall ((?v0 S27) (?v1 S28)) (= (f67 f68 (f45 (f46 f47 ?v0) ?v1)) f56)))
(assert (forall ((?v0 S42) (?v1 S42)) (= (= (f65 f66 ?v0) (f65 f66 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S42)) (= (f67 f68 (f65 f66 ?v0)) f56)))
(assert (forall ((?v0 S42) (?v1 S3) (?v2 S8)) (not (= (f65 f66 ?v0) (f11 (f12 f13 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S42)) (not (= (f11 (f12 f13 ?v0) ?v1) (f65 f66 ?v2)))))
(assert (forall ((?v0 S42) (?v1 S3) (?v2 S8) (?v3 S8)) (not (= (f65 f66 ?v0) (f11 (f40 (f43 f44 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8) (?v3 S42)) (not (= (f11 (f40 (f43 f44 ?v0) ?v1) ?v2) (f65 f66 ?v3)))))
(assert (forall ((?v0 S42) (?v1 S34) (?v2 S28) (?v3 S8)) (not (= (f65 f66 ?v0) (f11 (f53 (f54 f55 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S34) (?v1 S28) (?v2 S8) (?v3 S42)) (not (= (f11 (f53 (f54 f55 ?v0) ?v1) ?v2) (f65 f66 ?v3)))))
(assert (forall ((?v0 S42) (?v1 S8) (?v2 S8)) (not (= (f65 f66 ?v0) (f11 (f40 f41 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S42)) (not (= (f11 (f40 f41 ?v0) ?v1) (f65 f66 ?v2)))))
(assert (forall ((?v0 S42) (?v1 S27) (?v2 S28)) (not (= (f65 f66 ?v0) (f45 (f46 f47 ?v1) ?v2)))))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S42)) (not (= (f45 (f46 f47 ?v0) ?v1) (f65 f66 ?v2)))))
(assert (forall ((?v0 S42)) (not (= f10 (f65 f66 ?v0)))))
(assert (forall ((?v0 S42)) (not (= (f65 f66 ?v0) f10))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5) (?v3 S6)) (=> (= (f6 ?v0 ?v1) f1) (=> (= (f6 ?v2 ?v3) f1) (=> (not (= (f6 ?v0 f56) f1)) (=> (forall ((?v4 S6)) (= (= (f6 ?v0 (f8 f9 ?v4)) f1) (= (f6 ?v2 ?v4) f1))) (= (f69 f70 ?v0) (f8 f9 (f69 f70 ?v2)))))))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f6 ?v0 ?v1) f1) (= (f6 ?v0 (f69 f70 ?v0)) f1))))
(assert (forall ((?v0 S34) (?v1 S28) (?v2 S8)) (= (f67 f68 (f11 (f53 (f54 f55 ?v0) ?v1) ?v2)) (f8 (f71 f72 (f67 f68 ?v2)) (f8 f9 f56)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f67 f68 (f11 (f40 f41 ?v0) ?v1)) (f8 (f71 f72 (f8 (f71 f72 (f67 f68 ?v0)) (f67 f68 ?v1))) (f8 f9 f56)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f8 (f71 f72 ?v0) ?v1) (f8 (f71 f72 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f71 f72 ?v0))) (= (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f71 f72 ?v0))) (= (f8 (f71 f72 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f71 f72 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f71 f72 ?v0)) (?v_0 (f71 f72 ?v1))) (= (f8 ?v_1 (f8 ?v_0 ?v2)) (f8 ?v_0 (f8 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f8 (f71 f72 ?v0) ?v1) (f8 (f71 f72 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f8 (f71 f72 (f8 f9 ?v0)) ?v1) (f8 (f71 f72 ?v0) (f8 f9 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f8 (f71 f72 (f8 f9 ?v0)) ?v1) (f8 f9 (f8 (f71 f72 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f71 f72 ?v0))) (= (f8 ?v_0 (f8 f9 ?v1)) (f8 f9 (f8 ?v_0 ?v1))))))
(assert (forall ((?v0 S6)) (= (f8 (f71 f72 f56) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f8 (f71 f72 ?v0) f56) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f8 (f71 f72 ?v0) ?v1) f56) (and (= ?v0 f56) (= ?v1 f56)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f8 (f71 f72 ?v0) ?v1) ?v0) (= ?v1 f56))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f8 f9 f56))) (= (= ?v_0 (f8 (f71 f72 ?v0) ?v1)) (or (and (= ?v0 ?v_0) (= ?v1 f56)) (and (= ?v0 f56) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f8 f9 f56))) (= (= (f8 (f71 f72 ?v0) ?v1) ?v_0) (or (and (= ?v0 ?v_0) (= ?v1 f56)) (and (= ?v0 f56) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S5)) (=> (exists ((?v1 S6)) (= (f6 ?v0 ?v1) f1)) (= (f6 ?v0 (f69 f70 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S8)) (= (f67 f68 (f11 (f12 f13 ?v0) ?v1)) (f8 (f71 f72 (f67 f68 ?v1)) (f8 f9 f56)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8)) (= (f67 f68 (f11 (f40 (f43 f44 ?v0) ?v1) ?v2)) (f8 (f71 f72 (f8 (f71 f72 (f67 f68 ?v1)) (f67 f68 ?v2))) (f8 f9 f56)))))
(assert (forall ((?v0 S47)) (= (= (f73 (f74 f75 ?v0) ?v0) f76) (= ?v0 f76))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= ?v0 (f8 (f71 f72 ?v0) ?v1)) (= ?v1 f56))))
(assert (forall ((?v0 S47) (?v1 S47)) (= (= ?v0 (f73 (f74 f75 ?v0) ?v1)) (= ?v1 f76))))
(assert (forall ((?v0 S6)) (= (f8 (f71 f72 ?v0) f56) ?v0)))
(assert (forall ((?v0 S47)) (= (f73 (f74 f75 ?v0) f76) ?v0)))
(assert (forall ((?v0 S6)) (= (f8 (f71 f72 ?v0) f56) ?v0)))
(assert (forall ((?v0 S47)) (= (f73 (f74 f75 ?v0) f76) ?v0)))
(assert (forall ((?v0 S6)) (= (= f56 ?v0) (= ?v0 f56))))
(assert (forall ((?v0 S47)) (= (= f76 ?v0) (= ?v0 f76))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f8 (f71 f72 ?v0) ?v1) (f8 (f71 f72 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S47) (?v1 S47) (?v2 S47)) (=> (= (f73 (f74 f75 ?v0) ?v1) (f73 (f74 f75 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f71 f72 ?v0))) (=> (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S47) (?v1 S47) (?v2 S47)) (let ((?v_0 (f74 f75 ?v0))) (=> (= (f73 ?v_0 ?v1) (f73 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f71 f72 ?v0))) (=> (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S47) (?v1 S47) (?v2 S47)) (let ((?v_0 (f74 f75 ?v0))) (=> (= (f73 ?v_0 ?v1) (f73 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f71 f72 ?v0))) (= (f8 (f71 f72 (f8 ?v_0 ?v1)) (f8 (f71 f72 ?v2) ?v3)) (f8 (f71 f72 (f8 ?v_0 ?v2)) (f8 (f71 f72 ?v1) ?v3))))))
(assert (forall ((?v0 S47) (?v1 S47) (?v2 S47) (?v3 S47)) (let ((?v_0 (f74 f75 ?v0))) (= (f73 (f74 f75 (f73 ?v_0 ?v1)) (f73 (f74 f75 ?v2) ?v3)) (f73 (f74 f75 (f73 ?v_0 ?v2)) (f73 (f74 f75 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f8 (f71 f72 ?v0) ?v1) (f8 (f71 f72 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S47) (?v1 S47) (?v2 S47)) (= (= (f73 (f74 f75 ?v0) ?v1) (f73 (f74 f75 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f71 f72 ?v0))) (= (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S47) (?v1 S47) (?v2 S47)) (let ((?v_0 (f74 f75 ?v0))) (= (= (f73 ?v_0 ?v1) (f73 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f71 f72 ?v0))) (= (f8 (f71 f72 (f8 ?v_0 ?v1)) ?v2) (f8 (f71 f72 (f8 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S47) (?v1 S47) (?v2 S47)) (let ((?v_0 (f74 f75 ?v0))) (= (f73 (f74 f75 (f73 ?v_0 ?v1)) ?v2) (f73 (f74 f75 (f73 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f71 f72 ?v0))) (= (f8 (f71 f72 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f71 f72 ?v1) ?v2))))))
(assert (forall ((?v0 S47) (?v1 S47) (?v2 S47)) (let ((?v_0 (f74 f75 ?v0))) (= (f73 (f74 f75 (f73 ?v_0 ?v1)) ?v2) (f73 ?v_0 (f73 (f74 f75 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f71 f72 ?v0))) (= (f8 (f71 f72 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f71 f72 ?v1) ?v2))))))
(assert (forall ((?v0 S47) (?v1 S47) (?v2 S47)) (let ((?v_0 (f74 f75 ?v0))) (= (f73 (f74 f75 (f73 ?v_0 ?v1)) ?v2) (f73 ?v_0 (f73 (f74 f75 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f71 f72 ?v0))) (= (f8 ?v_0 (f8 (f71 f72 ?v1) ?v2)) (f8 (f71 f72 (f8 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S47) (?v1 S47) (?v2 S47)) (let ((?v_0 (f74 f75 ?v0))) (= (f73 ?v_0 (f73 (f74 f75 ?v1) ?v2)) (f73 (f74 f75 (f73 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f71 f72 ?v0)) (?v_0 (f71 f72 ?v1))) (= (f8 ?v_1 (f8 ?v_0 ?v2)) (f8 ?v_0 (f8 ?v_1 ?v2))))))
(assert (forall ((?v0 S47) (?v1 S47) (?v2 S47)) (let ((?v_1 (f74 f75 ?v0)) (?v_0 (f74 f75 ?v1))) (= (f73 ?v_1 (f73 ?v_0 ?v2)) (f73 ?v_0 (f73 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f8 (f71 f72 ?v0) ?v1) (f8 (f71 f72 ?v1) ?v0))))
(assert (forall ((?v0 S47) (?v1 S47)) (= (f73 (f74 f75 ?v0) ?v1) (f73 (f74 f75 ?v1) ?v0))))
(assert (forall ((?v0 S6)) (= (f8 (f71 f72 f56) ?v0) ?v0)))
(assert (forall ((?v0 S47)) (= (f73 (f74 f75 f76) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f8 (f71 f72 f56) ?v0) ?v0)))
(assert (forall ((?v0 S47)) (= (f73 (f74 f75 f76) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f8 (f71 f72 f56) ?v0) ?v0)))
(assert (forall ((?v0 S47)) (= (f73 (f74 f75 f76) ?v0) ?v0)))
(assert (forall ((?v0 S47)) (= (= f76 (f73 (f74 f75 ?v0) ?v0)) (= ?v0 f76))))
(assert (forall ((?v0 S6)) (= (f8 (f71 f72 ?v0) f56) ?v0)))
(assert (forall ((?v0 S47)) (= (f73 (f74 f75 ?v0) f76) ?v0)))
(assert (forall ((?v0 S34) (?v1 S28) (?v2 S8)) (= (f67 f77 (f11 (f53 (f54 f55 ?v0) ?v1) ?v2)) (f8 (f71 f72 (f67 f77 ?v2)) (f8 f9 f56)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f67 f77 (f11 (f40 f41 ?v0) ?v1)) (f8 (f71 f72 (f8 (f71 f72 (f67 f77 ?v0)) (f67 f77 ?v1))) (f8 f9 f56)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8)) (= (f67 f77 (f11 (f40 (f43 f44 ?v0) ?v1) ?v2)) (f8 (f71 f72 (f8 (f71 f72 (f67 f77 ?v1)) (f67 f77 ?v2))) (f8 f9 f56)))))
(assert (forall ((?v0 S42)) (= (f67 f77 (f65 f66 ?v0)) f56)))
(assert (forall ((?v0 S27) (?v1 S28)) (= (f67 f77 (f45 (f46 f47 ?v0) ?v1)) f56)))
(assert (= (f67 f77 f10) f56))
(assert (forall ((?v0 S3) (?v1 S8)) (= (f67 f77 (f11 (f12 f13 ?v0) ?v1)) (f8 (f71 f72 (f67 f77 ?v1)) (f8 f9 f56)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (exists ((?v2 S6)) (= (f6 ?v0 ?v2) f1)) (=> (forall ((?v2 S6)) (=> (= (f6 ?v0 ?v2) f1) (= (f6 ?v1 ?v2) f1))) (= (f6 ?v1 (f69 f70 ?v0)) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (=> (= (f6 ?v0 ?v1) f1) (=> (forall ((?v3 S6)) (=> (= (f6 ?v0 ?v3) f1) (= (f6 ?v2 ?v3) f1))) (= (f6 ?v2 (f69 f70 ?v0)) f1)))))
(assert (forall ((?v0 S6)) (= (f8 f78 (f8 f9 ?v0)) (f8 (f71 f72 (f8 f78 ?v0)) (f8 f9 f56)))))
(assert (= (f8 f78 f56) f56))
(assert (forall ((?v0 S6)) (= (f8 f79 (f8 f9 ?v0)) (f8 (f71 f72 (f8 f79 ?v0)) (f8 f9 f56)))))
(assert (= (f80 f81 f1) f56))
(assert (= (f80 f81 f2) f56))
(assert (forall ((?v0 S6)) (= (f8 f79 ?v0) ?v0)))
(assert (= (f8 f79 f56) f56))
(assert (forall ((?v0 S27) (?v1 S42) (?v2 S28)) (=> (= (f42 (f45 (f82 (f83 f84 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f42 (f65 f66 ?v1)) f1) false) false))))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S2) (?v3 S2)) (=> (= (f3 (f4 (f85 (f45 (f46 f47 ?v0) ?v1)) ?v2) ?v3) f1) (=> (=> (= ?v3 (f48 (f49 (f50 f51 ?v2) ?v0) (f52 ?v1 ?v2))) false) false))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S8) (?v3 S2) (?v4 S2)) (let ((?v_0 (f85 (f11 (f12 f13 ?v0) ?v2)))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 (f4 (f85 ?v2) ?v1) ?v3) f1) (=> (= (f3 (f4 ?v_0 ?v3) ?v4) f1) (= (f3 (f4 ?v_0 ?v1) ?v4) f1)))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S8)) (=> (not (= (f3 ?v0 ?v1) f1)) (= (f3 (f4 (f85 (f11 (f12 f13 ?v0) ?v2)) ?v1) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8) (?v3 S2) (?v4 S2)) (let ((?v_0 (= (f3 ?v0 ?v3) f1))) (=> (= (f3 (f4 (f85 (f11 (f40 (f43 f44 ?v0) ?v1) ?v2)) ?v3) ?v4) f1) (=> (=> ?v_0 (=> (= (f3 (f4 (f85 ?v1) ?v3) ?v4) f1) false)) (=> (=> (not ?v_0) (=> (= (f3 (f4 (f85 ?v2) ?v3) ?v4) f1) false)) false))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S8) (?v3 S2) (?v4 S8)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 (f4 (f85 ?v2) ?v1) ?v3) f1) (= (f3 (f4 (f85 (f11 (f40 (f43 f44 ?v0) ?v2) ?v4)) ?v1) ?v3) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S8) (?v3 S2) (?v4 S8)) (=> (not (= (f3 ?v0 ?v1) f1)) (=> (= (f3 (f4 (f85 ?v2) ?v1) ?v3) f1) (= (f3 (f4 (f85 (f11 (f40 (f43 f44 ?v0) ?v4) ?v2)) ?v1) ?v3) f1)))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2) (?v3 S8) (?v4 S2)) (=> (= (f3 (f4 (f85 ?v0) ?v1) ?v2) f1) (=> (= (f3 (f4 (f85 ?v3) ?v2) ?v4) f1) (= (f3 (f4 (f85 (f11 (f40 f41 ?v0) ?v3)) ?v1) ?v4) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 (f85 f10) ?v0) ?v1) f1) (=> (=> (= ?v1 ?v0) false) false))))
(assert (forall ((?v0 S2)) (= (f3 (f4 (f85 f10) ?v0) ?v0) f1)))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S2)) (= (f3 (f4 (f85 (f45 (f46 f47 ?v0) ?v1)) ?v2) (f48 (f49 (f50 f51 ?v2) ?v0) (f52 ?v1 ?v2))) f1)))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S6) (?v3 S2)) (=> (= (f3 (f23 (f24 (f25 ?v0) ?v1) ?v2) ?v3) f1) (= (f3 (f4 (f85 ?v0) ?v1) ?v3) f1))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f85 ?v0) ?v1) ?v2) f1) (exists ((?v3 S6)) (= (f3 (f23 (f24 (f25 ?v0) ?v1) ?v3) ?v2) f1)))))
(assert (forall ((?v0 S27) (?v1 S42) (?v2 S28) (?v3 S27) (?v4 S42) (?v5 S28)) (= (= (f45 (f82 (f83 f84 ?v0) ?v1) ?v2) (f45 (f82 (f83 f84 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f4 (f85 ?v0) ?v1))) (=> (= (f3 ?v_0 ?v2) f1) (=> (= (f3 ?v_0 ?v3) f1) (= ?v3 ?v2))))))
(assert (forall ((?v0 S27) (?v1 S42) (?v2 S28)) (not (= (f45 (f82 (f83 f84 ?v0) ?v1) ?v2) f10))))
(assert (forall ((?v0 S27) (?v1 S42) (?v2 S28)) (not (= f10 (f45 (f82 (f83 f84 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S27) (?v1 S42) (?v2 S28) (?v3 S27) (?v4 S28)) (not (= (f45 (f82 (f83 f84 ?v0) ?v1) ?v2) (f45 (f46 f47 ?v3) ?v4)))))
(assert (forall ((?v0 S27) (?v1 S28) (?v2 S27) (?v3 S42) (?v4 S28)) (not (= (f45 (f46 f47 ?v0) ?v1) (f45 (f82 (f83 f84 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S27) (?v1 S42) (?v2 S28) (?v3 S8) (?v4 S8)) (not (= (f45 (f82 (f83 f84 ?v0) ?v1) ?v2) (f11 (f40 f41 ?v3) ?v4)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S27) (?v3 S42) (?v4 S28)) (not (= (f11 (f40 f41 ?v0) ?v1) (f45 (f82 (f83 f84 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S34) (?v1 S28) (?v2 S8) (?v3 S27) (?v4 S42) (?v5 S28)) (not (= (f11 (f53 (f54 f55 ?v0) ?v1) ?v2) (f45 (f82 (f83 f84 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S27) (?v1 S42) (?v2 S28) (?v3 S34) (?v4 S28) (?v5 S8)) (not (= (f45 (f82 (f83 f84 ?v0) ?v1) ?v2) (f11 (f53 (f54 f55 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8) (?v3 S27) (?v4 S42) (?v5 S28)) (not (= (f11 (f40 (f43 f44 ?v0) ?v1) ?v2) (f45 (f82 (f83 f84 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S27) (?v1 S42) (?v2 S28) (?v3 S3) (?v4 S8) (?v5 S8)) (not (= (f45 (f82 (f83 f84 ?v0) ?v1) ?v2) (f11 (f40 (f43 f44 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S27) (?v1 S42) (?v2 S28) (?v3 S3) (?v4 S8)) (not (= (f45 (f82 (f83 f84 ?v0) ?v1) ?v2) (f11 (f12 f13 ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S27) (?v3 S42) (?v4 S28)) (not (= (f11 (f12 f13 ?v0) ?v1) (f45 (f82 (f83 f84 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S27) (?v1 S42) (?v2 S28) (?v3 S42)) (not (= (f45 (f82 (f83 f84 ?v0) ?v1) ?v2) (f65 f66 ?v3)))))
(assert (forall ((?v0 S42) (?v1 S27) (?v2 S42) (?v3 S28)) (not (= (f65 f66 ?v0) (f45 (f82 (f83 f84 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S27) (?v1 S42) (?v2 S28)) (= (f67 f68 (f45 (f82 (f83 f84 ?v0) ?v1) ?v2)) f56)))
(assert (forall ((?v0 S27) (?v1 S42) (?v2 S28)) (= (f67 f77 (f45 (f82 (f83 f84 ?v0) ?v1) ?v2)) f56)))
(assert (forall ((?v0 S42) (?v1 S27) (?v2 S28)) (=> (= (f42 (f65 f66 ?v0)) f1) (= (f42 (f45 (f82 (f83 f84 ?v1) ?v0) ?v2)) f1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S2) (?v3 S2)) (=> (= (f3 (f4 (f85 (f11 (f40 f41 ?v0) ?v1)) ?v2) ?v3) f1) (=> (forall ((?v4 S2)) (=> (= (f3 (f4 (f85 ?v0) ?v2) ?v4) f1) (=> (= (f3 (f4 (f85 ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S8)) (= (f86 f87 ?v0) (f36 (f37 (f38 f39 f5) ?v0) (f85 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S2) (?v3 S2)) (=> (= (f3 (f4 (f85 (f11 (f12 f13 ?v0) ?v1)) ?v2) ?v3) f1) (=> (=> (= ?v3 ?v2) (=> (not (= (f3 ?v0 ?v2) f1)) false)) (=> (forall ((?v4 S2)) (=> (= (f3 ?v0 ?v2) f1) (=> (= (f3 (f4 (f85 ?v1) ?v2) ?v4) f1) (=> (= (f3 (f4 (f85 (f11 (f12 f13 ?v0) ?v1)) ?v4) ?v3) f1) false)))) false)))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 (f85 ?v0) ?v1) ?v2) f1) (exists ((?v3 S6)) (= (f3 (f23 (f24 (f25 ?v0) ?v1) ?v3) ?v2) f1)))))
(assert (forall ((?v0 S8)) (=> (=> (= ?v0 f10) false) (=> (forall ((?v1 S27) (?v2 S28)) (=> (= ?v0 (f45 (f46 f47 ?v1) ?v2)) false)) (=> (forall ((?v1 S34) (?v2 S28) (?v3 S8)) (=> (= ?v0 (f11 (f53 (f54 f55 ?v1) ?v2) ?v3)) false)) (=> (forall ((?v1 S8) (?v2 S8)) (=> (= ?v0 (f11 (f40 f41 ?v1) ?v2)) false)) (=> (forall ((?v1 S3) (?v2 S8) (?v3 S8)) (=> (= ?v0 (f11 (f40 (f43 f44 ?v1) ?v2) ?v3)) false)) (=> (forall ((?v1 S3) (?v2 S8)) (=> (= ?v0 (f11 (f12 f13 ?v1) ?v2)) false)) (=> (forall ((?v1 S42)) (=> (= ?v0 (f65 f66 ?v1)) false)) (=> (forall ((?v1 S27) (?v2 S42) (?v3 S28)) (=> (= ?v0 (f45 (f82 (f83 f84 ?v1) ?v2) ?v3)) false)) false))))))))))
(assert (forall ((?v0 S6) (?v1 S18) (?v2 S42) (?v3 S18)) (let ((?v_0 (f33 f34 ?v1))) (= (= (f18 (f19 ?v0) (f31 (f32 ?v_0 (f88 f89 (f90 f91 ?v2))) ?v3)) f1) (= (f18 (f19 (f8 f9 ?v0)) (f31 (f32 ?v_0 (f65 f66 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S42) (?v3 S4)) (let ((?v_0 (f38 f39 ?v1))) (= (= (f29 (f30 ?v0) (f36 (f37 ?v_0 (f88 f89 (f90 f91 ?v2))) ?v3)) f1) (= (f29 (f30 (f8 f9 ?v0)) (f36 (f37 ?v_0 (f65 f66 ?v2)) ?v3)) f1)))))
(assert (forall ((?v0 S42) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 (f85 (f88 f89 (f90 f91 ?v0))) ?v1) ?v2) f1) (= (f3 (f4 (f85 (f65 f66 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S42) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 (f85 (f65 f66 ?v0)) ?v1) ?v2) f1) (=> (=> (= (f3 (f4 (f85 (f88 f89 (f90 f91 ?v0))) ?v1) ?v2) f1) false) false))))
(assert (forall ((?v0 S42) (?v1 S2) (?v2 S6) (?v3 S2)) (=> (= (f3 (f23 (f24 (f25 (f88 f89 (f90 f91 ?v0))) ?v1) ?v2) ?v3) f1) (= (f3 (f23 (f24 (f25 (f65 f66 ?v0)) ?v1) (f8 f9 ?v2)) ?v3) f1))))
(assert (forall ((?v0 S42) (?v1 S2) (?v2 S6) (?v3 S2)) (=> (= (f3 (f23 (f24 (f25 (f65 f66 ?v0)) ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S6)) (=> (= ?v2 (f8 f9 ?v4)) (=> (= (f3 (f23 (f24 (f25 (f88 f89 (f90 f91 ?v0))) ?v1) ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S42)) (=> (not (= (f90 f91 ?v0) f92)) (= (f42 (f65 f66 ?v0)) f1))))
(assert (forall ((?v0 S44)) (= (f95 (f93 f94 ?v0) f92) f56)))
(assert (= (f95 f96 f92) f56))
(assert (forall ((?v0 S8)) (= (= (f42 ?v0) f1) (or (= ?v0 f10) (or (exists ((?v1 S27) (?v2 S28)) (= ?v0 (f45 (f46 f47 ?v1) ?v2))) (or (exists ((?v1 S8) (?v2 S34) (?v3 S28)) (and (= ?v0 (f11 (f53 (f54 f55 ?v2) ?v3) ?v1)) (= (f42 ?v1) f1))) (or (exists ((?v1 S8) (?v2 S8)) (and (= ?v0 (f11 (f40 f41 ?v1) ?v2)) (and (= (f42 ?v1) f1) (= (f42 ?v2) f1)))) (or (exists ((?v1 S8) (?v2 S8) (?v3 S3)) (and (= ?v0 (f11 (f40 (f43 f44 ?v3) ?v1) ?v2)) (and (= (f42 ?v1) f1) (= (f42 ?v2) f1)))) (or (exists ((?v1 S8) (?v2 S3)) (and (= ?v0 (f11 (f12 f13 ?v2) ?v1)) (= (f42 ?v1) f1))) (or (exists ((?v1 S42)) (and (= ?v0 (f65 f66 ?v1)) (not (= (f90 f91 ?v1) f92)))) (exists ((?v1 S42) (?v2 S27) (?v3 S28)) (and (= ?v0 (f45 (f82 (f83 f84 ?v2) ?v1) ?v3)) (= (f42 (f65 f66 ?v1)) f1)))))))))))))
(assert (forall ((?v0 S44) (?v1 S8)) (= (f95 (f93 f94 ?v0) (f97 f98 ?v1)) (f8 (f71 f72 (f67 ?v0 ?v1)) (f8 f9 f56)))))
(assert (forall ((?v0 S8)) (= (f95 f96 (f97 f98 ?v0)) f56)))
(assert (forall ((?v0 S42)) (=> (= (f42 (f65 f66 ?v0)) f1) (=> (forall ((?v1 S8)) (=> (= (f90 f91 ?v0) (f97 f98 ?v1)) false)) false))))
(assert (forall ((?v0 S42) (?v1 S8)) (=> (= f99 f1) (=> (= (f90 f91 ?v0) (f97 f98 ?v1)) (= (f42 ?v1) f1)))))
(assert (forall ((?v0 S8)) (= (f88 f89 (f97 f98 ?v0)) ?v0)))
(assert (forall ((?v0 S8)) (not (= f92 (f97 f98 ?v0)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f97 f98 ?v0) (f97 f98 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S55)) (= (not (= ?v0 f92)) (exists ((?v1 S8)) (= ?v0 (f97 f98 ?v1))))))
(assert (forall ((?v0 S55)) (= (forall ((?v1 S8)) (not (= ?v0 (f97 f98 ?v1)))) (= ?v0 f92))))
(assert (forall ((?v0 S8)) (not (= (f97 f98 ?v0) f92))))
(assert (forall ((?v0 S55)) (=> (=> (= ?v0 f92) false) (=> (forall ((?v1 S8)) (=> (= ?v0 (f97 f98 ?v1)) false)) false))))
(assert (forall ((?v0 S8)) (= (= (f100 (f97 f98 ?v0)) f1) false)))
(assert (= (= (f100 f92) f1) true))
(assert (forall ((?v0 S55)) (= (= (f100 ?v0) f1) (= ?v0 f92))))
(check-sat)
(exit)
