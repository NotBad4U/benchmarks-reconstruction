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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S4) S1)
(declare-fun f6 () S5)
(declare-fun f7 (S4) S1)
(declare-fun f8 (S6) S5)
(declare-fun f9 (S7 S2) S6)
(declare-fun f10 (S8 S2) S7)
(declare-fun f11 () S8)
(declare-fun f12 (S9) S1)
(declare-fun f13 (S11 S9) S1)
(declare-fun f14 (S12 S10) S11)
(declare-fun f15 (S13 S10) S12)
(declare-fun f16 () S13)
(declare-fun f17 (S14) S1)
(declare-fun f18 (S16 S14) S1)
(declare-fun f19 (S17 S15) S16)
(declare-fun f20 (S18 S15) S17)
(declare-fun f21 () S18)
(declare-fun f22 (S19) S1)
(declare-fun f23 (S21 S19) S1)
(declare-fun f24 (S22 S20) S21)
(declare-fun f25 (S23 S20) S22)
(declare-fun f26 () S23)
(declare-fun f27 (S24) S1)
(declare-fun f28 (S26 S24) S1)
(declare-fun f29 (S27 S25) S26)
(declare-fun f30 (S28 S25) S27)
(declare-fun f31 () S28)
(declare-fun f32 (S29) S1)
(declare-fun f33 (S25 S29) S1)
(declare-fun f34 (S30 S16) S25)
(declare-fun f35 (S31 S16) S30)
(declare-fun f36 () S31)
(declare-fun f37 (S32) S1)
(declare-fun f38 (S20 S32) S1)
(declare-fun f39 (S33 S11) S20)
(declare-fun f40 (S34 S11) S33)
(declare-fun f41 () S34)
(declare-fun f42 (S35) S1)
(declare-fun f43 (S15 S35) S1)
(declare-fun f44 (S36 S4) S15)
(declare-fun f45 (S37 S4) S36)
(declare-fun f46 () S37)
(declare-fun f47 (S38) S1)
(declare-fun f48 (S10 S38) S1)
(declare-fun f49 (S39 S6) S10)
(declare-fun f50 (S40 S6) S39)
(declare-fun f51 () S40)
(declare-fun f52 (S4) S1)
(declare-fun f53 (S9) S1)
(declare-fun f54 (S14) S1)
(declare-fun f55 (S19) S1)
(declare-fun f56 (S24) S1)
(declare-fun f57 (S29) S1)
(declare-fun f58 (S32) S1)
(declare-fun f59 (S35) S1)
(declare-fun f60 (S38) S1)
(declare-fun f61 () S5)
(declare-fun f62 (S5) S5)
(declare-fun f63 (S3) S5)
(declare-fun f64 () S3)
(declare-fun f65 (S4 S6) S1)
(declare-fun f66 (S4 S5) S1)
(declare-fun f67 (S9 S11) S1)
(declare-fun f68 (S14 S16) S1)
(declare-fun f69 (S19 S21) S1)
(declare-fun f70 (S24 S26) S1)
(declare-fun f71 (S29 S25) S1)
(declare-fun f72 (S32 S20) S1)
(declare-fun f73 (S35 S15) S1)
(declare-fun f74 (S38 S10) S1)
(declare-fun f75 (S2 S3) S1)
(declare-fun f76 () S5)
(declare-fun f77 (S3) S3)
(declare-fun f78 (S3) S5)
(declare-fun f79 (S4 S38) S1)
(declare-fun f80 (S5 S35) S1)
(declare-fun f81 (S9 S32) S1)
(declare-fun f82 (S14 S29) S1)
(declare-fun f83 (S19 S41) S1)
(declare-fun f84 (S42 S41) S1)
(declare-fun f85 (S21 S21) S42)
(declare-fun f86 (S24 S43) S1)
(declare-fun f87 (S44 S43) S1)
(declare-fun f88 (S26 S26) S44)
(declare-fun f89 (S29 S24) S1)
(declare-fun f90 (S32 S19) S1)
(declare-fun f91 (S35 S14) S1)
(declare-fun f92 (S38 S9) S1)
(declare-fun f93 (S45 S2) S4)
(declare-fun f94 (S4) S45)
(declare-fun f95 (S38 S9) S1)
(declare-fun f96 (S35 S14) S1)
(declare-fun f97 (S32 S19) S1)
(declare-fun f98 (S29 S24) S1)
(declare-fun f99 (S14 S29) S1)
(declare-fun f100 (S9 S32) S1)
(declare-fun f101 (S5 S35) S1)
(declare-fun f102 (S4 S38) S1)
(declare-fun f103 () S4)
(declare-fun f104 () S2)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) true)))
(assert (forall ((?v0 S4)) (= (= (f5 f6 ?v0) f1) true)))
(assert (forall ((?v0 S4)) (= (= (f7 ?v0) f1) (forall ((?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f10 f11 ?v1))) (=> (= (f5 (f8 (f9 ?v_0 ?v2)) ?v0) f1) (=> (= (f5 (f8 (f9 (f10 f11 ?v2) ?v3)) ?v0) f1) (= (f5 (f8 (f9 ?v_0 ?v3)) ?v0) f1))))))))
(assert (forall ((?v0 S9)) (= (= (f12 ?v0) f1) (forall ((?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f15 f16 ?v1))) (=> (= (f13 (f14 ?v_0 ?v2) ?v0) f1) (=> (= (f13 (f14 (f15 f16 ?v2) ?v3) ?v0) f1) (= (f13 (f14 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S14)) (= (= (f17 ?v0) f1) (forall ((?v1 S15) (?v2 S15) (?v3 S15)) (let ((?v_0 (f20 f21 ?v1))) (=> (= (f18 (f19 ?v_0 ?v2) ?v0) f1) (=> (= (f18 (f19 (f20 f21 ?v2) ?v3) ?v0) f1) (= (f18 (f19 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S19)) (= (= (f22 ?v0) f1) (forall ((?v1 S20) (?v2 S20) (?v3 S20)) (let ((?v_0 (f25 f26 ?v1))) (=> (= (f23 (f24 ?v_0 ?v2) ?v0) f1) (=> (= (f23 (f24 (f25 f26 ?v2) ?v3) ?v0) f1) (= (f23 (f24 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S24)) (= (= (f27 ?v0) f1) (forall ((?v1 S25) (?v2 S25) (?v3 S25)) (let ((?v_0 (f30 f31 ?v1))) (=> (= (f28 (f29 ?v_0 ?v2) ?v0) f1) (=> (= (f28 (f29 (f30 f31 ?v2) ?v3) ?v0) f1) (= (f28 (f29 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S29)) (= (= (f32 ?v0) f1) (forall ((?v1 S16) (?v2 S16) (?v3 S16)) (let ((?v_0 (f35 f36 ?v1))) (=> (= (f33 (f34 ?v_0 ?v2) ?v0) f1) (=> (= (f33 (f34 (f35 f36 ?v2) ?v3) ?v0) f1) (= (f33 (f34 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S32)) (= (= (f37 ?v0) f1) (forall ((?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f40 f41 ?v1))) (=> (= (f38 (f39 ?v_0 ?v2) ?v0) f1) (=> (= (f38 (f39 (f40 f41 ?v2) ?v3) ?v0) f1) (= (f38 (f39 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S35)) (= (= (f42 ?v0) f1) (forall ((?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f45 f46 ?v1))) (=> (= (f43 (f44 ?v_0 ?v2) ?v0) f1) (=> (= (f43 (f44 (f45 f46 ?v2) ?v3) ?v0) f1) (= (f43 (f44 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S38)) (= (= (f47 ?v0) f1) (forall ((?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f50 f51 ?v1))) (=> (= (f48 (f49 ?v_0 ?v2) ?v0) f1) (=> (= (f48 (f49 (f50 f51 ?v2) ?v3) ?v0) f1) (= (f48 (f49 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f10 f11 ?v1))) (=> (= (f5 (f8 (f9 ?v_0 ?v2)) ?v0) f1) (=> (= (f5 (f8 (f9 (f10 f11 ?v2) ?v3)) ?v0) f1) (= (f5 (f8 (f9 ?v_0 ?v3)) ?v0) f1))))) (= (f7 ?v0) f1))))
(assert (forall ((?v0 S9)) (=> (forall ((?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f15 f16 ?v1))) (=> (= (f13 (f14 ?v_0 ?v2) ?v0) f1) (=> (= (f13 (f14 (f15 f16 ?v2) ?v3) ?v0) f1) (= (f13 (f14 ?v_0 ?v3) ?v0) f1))))) (= (f12 ?v0) f1))))
(assert (forall ((?v0 S14)) (=> (forall ((?v1 S15) (?v2 S15) (?v3 S15)) (let ((?v_0 (f20 f21 ?v1))) (=> (= (f18 (f19 ?v_0 ?v2) ?v0) f1) (=> (= (f18 (f19 (f20 f21 ?v2) ?v3) ?v0) f1) (= (f18 (f19 ?v_0 ?v3) ?v0) f1))))) (= (f17 ?v0) f1))))
(assert (forall ((?v0 S19)) (=> (forall ((?v1 S20) (?v2 S20) (?v3 S20)) (let ((?v_0 (f25 f26 ?v1))) (=> (= (f23 (f24 ?v_0 ?v2) ?v0) f1) (=> (= (f23 (f24 (f25 f26 ?v2) ?v3) ?v0) f1) (= (f23 (f24 ?v_0 ?v3) ?v0) f1))))) (= (f22 ?v0) f1))))
(assert (forall ((?v0 S24)) (=> (forall ((?v1 S25) (?v2 S25) (?v3 S25)) (let ((?v_0 (f30 f31 ?v1))) (=> (= (f28 (f29 ?v_0 ?v2) ?v0) f1) (=> (= (f28 (f29 (f30 f31 ?v2) ?v3) ?v0) f1) (= (f28 (f29 ?v_0 ?v3) ?v0) f1))))) (= (f27 ?v0) f1))))
(assert (forall ((?v0 S29)) (=> (forall ((?v1 S16) (?v2 S16) (?v3 S16)) (let ((?v_0 (f35 f36 ?v1))) (=> (= (f33 (f34 ?v_0 ?v2) ?v0) f1) (=> (= (f33 (f34 (f35 f36 ?v2) ?v3) ?v0) f1) (= (f33 (f34 ?v_0 ?v3) ?v0) f1))))) (= (f32 ?v0) f1))))
(assert (forall ((?v0 S32)) (=> (forall ((?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f40 f41 ?v1))) (=> (= (f38 (f39 ?v_0 ?v2) ?v0) f1) (=> (= (f38 (f39 (f40 f41 ?v2) ?v3) ?v0) f1) (= (f38 (f39 ?v_0 ?v3) ?v0) f1))))) (= (f37 ?v0) f1))))
(assert (forall ((?v0 S35)) (=> (forall ((?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f45 f46 ?v1))) (=> (= (f43 (f44 ?v_0 ?v2) ?v0) f1) (=> (= (f43 (f44 (f45 f46 ?v2) ?v3) ?v0) f1) (= (f43 (f44 ?v_0 ?v3) ?v0) f1))))) (= (f42 ?v0) f1))))
(assert (forall ((?v0 S38)) (=> (forall ((?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f50 f51 ?v1))) (=> (= (f48 (f49 ?v_0 ?v2) ?v0) f1) (=> (= (f48 (f49 (f50 f51 ?v2) ?v3) ?v0) f1) (= (f48 (f49 ?v_0 ?v3) ?v0) f1))))) (= (f47 ?v0) f1))))
(assert (forall ((?v0 S4)) (= (= (f52 ?v0) f1) (forall ((?v1 S2)) (not (= (f5 (f8 (f9 (f10 f11 ?v1) ?v1)) ?v0) f1))))))
(assert (forall ((?v0 S9)) (= (= (f53 ?v0) f1) (forall ((?v1 S10)) (not (= (f13 (f14 (f15 f16 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S14)) (= (= (f54 ?v0) f1) (forall ((?v1 S15)) (not (= (f18 (f19 (f20 f21 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S19)) (= (= (f55 ?v0) f1) (forall ((?v1 S20)) (not (= (f23 (f24 (f25 f26 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S24)) (= (= (f56 ?v0) f1) (forall ((?v1 S25)) (not (= (f28 (f29 (f30 f31 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S29)) (= (= (f57 ?v0) f1) (forall ((?v1 S16)) (not (= (f33 (f34 (f35 f36 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S32)) (= (= (f58 ?v0) f1) (forall ((?v1 S11)) (not (= (f38 (f39 (f40 f41 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S35)) (= (= (f59 ?v0) f1) (forall ((?v1 S4)) (not (= (f43 (f44 (f45 f46 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S38)) (= (= (f60 ?v0) f1) (forall ((?v1 S6)) (not (= (f48 (f49 (f50 f51 ?v1) ?v1) ?v0) f1))))))
(assert (= f61 (f62 (f63 f64))))
(assert (forall ((?v0 S6) (?v1 S4)) (= (= (f5 (f8 ?v0) ?v1) f1) (= (f65 ?v1 ?v0) f1))))
(assert (forall ((?v0 S4) (?v1 S5)) (= (= (f66 ?v0 ?v1) f1) (= (f5 ?v1 ?v0) f1))))
(assert (forall ((?v0 S11) (?v1 S9)) (= (= (f13 ?v0 ?v1) f1) (= (f67 ?v1 ?v0) f1))))
(assert (forall ((?v0 S16) (?v1 S14)) (= (= (f18 ?v0 ?v1) f1) (= (f68 ?v1 ?v0) f1))))
(assert (forall ((?v0 S21) (?v1 S19)) (= (= (f23 ?v0 ?v1) f1) (= (f69 ?v1 ?v0) f1))))
(assert (forall ((?v0 S26) (?v1 S24)) (= (= (f28 ?v0 ?v1) f1) (= (f70 ?v1 ?v0) f1))))
(assert (forall ((?v0 S25) (?v1 S29)) (= (= (f33 ?v0 ?v1) f1) (= (f71 ?v1 ?v0) f1))))
(assert (forall ((?v0 S20) (?v1 S32)) (= (= (f38 ?v0 ?v1) f1) (= (f72 ?v1 ?v0) f1))))
(assert (forall ((?v0 S15) (?v1 S35)) (= (= (f43 ?v0 ?v1) f1) (= (f73 ?v1 ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S38)) (= (= (f48 ?v0 ?v1) f1) (= (f74 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f75 ?v0 ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (= f76 (f62 f6)))
(assert (= f64 (f77 f4)))
(assert (forall ((?v0 S5)) (= (f62 ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f77 ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S4)) (= (= (f5 (f78 ?v0) ?v1) f1) (forall ((?v2 S2)) (=> (= (f75 ?v2 ?v0) f1) (forall ((?v3 S2)) (=> (= (f75 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f5 (f8 (f9 (f10 f11 ?v2) ?v3)) ?v1) f1) (= (f5 (f8 (f9 (f10 f11 ?v3) ?v2)) ?v1) f1))))))))))
(assert (forall ((?v0 S4) (?v1 S38)) (= (= (f79 ?v0 ?v1) f1) (forall ((?v2 S6)) (=> (= (f5 (f8 ?v2) ?v0) f1) (forall ((?v3 S6)) (=> (= (f5 (f8 ?v3) ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f48 (f49 (f50 f51 ?v2) ?v3) ?v1) f1) (= (f48 (f49 (f50 f51 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S5) (?v1 S35)) (= (= (f80 ?v0 ?v1) f1) (forall ((?v2 S4)) (=> (= (f66 ?v2 ?v0) f1) (forall ((?v3 S4)) (=> (= (f66 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f43 (f44 (f45 f46 ?v2) ?v3) ?v1) f1) (= (f43 (f44 (f45 f46 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S9) (?v1 S32)) (= (= (f81 ?v0 ?v1) f1) (forall ((?v2 S11)) (=> (= (f13 ?v2 ?v0) f1) (forall ((?v3 S11)) (=> (= (f13 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f38 (f39 (f40 f41 ?v2) ?v3) ?v1) f1) (= (f38 (f39 (f40 f41 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S14) (?v1 S29)) (= (= (f82 ?v0 ?v1) f1) (forall ((?v2 S16)) (=> (= (f18 ?v2 ?v0) f1) (forall ((?v3 S16)) (=> (= (f18 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f33 (f34 (f35 f36 ?v2) ?v3) ?v1) f1) (= (f33 (f34 (f35 f36 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S19) (?v1 S41)) (= (= (f83 ?v0 ?v1) f1) (forall ((?v2 S21)) (=> (= (f23 ?v2 ?v0) f1) (forall ((?v3 S21)) (=> (= (f23 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f84 (f85 ?v2 ?v3) ?v1) f1) (= (f84 (f85 ?v3 ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S24) (?v1 S43)) (= (= (f86 ?v0 ?v1) f1) (forall ((?v2 S26)) (=> (= (f28 ?v2 ?v0) f1) (forall ((?v3 S26)) (=> (= (f28 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f87 (f88 ?v2 ?v3) ?v1) f1) (= (f87 (f88 ?v3 ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S29) (?v1 S24)) (= (= (f89 ?v0 ?v1) f1) (forall ((?v2 S25)) (=> (= (f33 ?v2 ?v0) f1) (forall ((?v3 S25)) (=> (= (f33 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f28 (f29 (f30 f31 ?v2) ?v3) ?v1) f1) (= (f28 (f29 (f30 f31 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S32) (?v1 S19)) (= (= (f90 ?v0 ?v1) f1) (forall ((?v2 S20)) (=> (= (f38 ?v2 ?v0) f1) (forall ((?v3 S20)) (=> (= (f38 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f23 (f24 (f25 f26 ?v2) ?v3) ?v1) f1) (= (f23 (f24 (f25 f26 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S35) (?v1 S14)) (= (= (f91 ?v0 ?v1) f1) (forall ((?v2 S15)) (=> (= (f43 ?v2 ?v0) f1) (forall ((?v3 S15)) (=> (= (f43 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f18 (f19 (f20 f21 ?v2) ?v3) ?v1) f1) (= (f18 (f19 (f20 f21 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S38) (?v1 S9)) (= (= (f92 ?v0 ?v1) f1) (forall ((?v2 S10)) (=> (= (f48 ?v2 ?v0) f1) (forall ((?v3 S10)) (=> (= (f48 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f13 (f14 (f15 f16 ?v2) ?v3) ?v1) f1) (= (f13 (f14 (f15 f16 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (=> (= (f66 ?v0 f61) f1) (=> (not (= ?v1 ?v2)) (= (not (= (f5 (f8 (f9 (f10 f11 ?v1) ?v2)) ?v0) f1)) (= (f5 (f8 (f9 (f10 f11 ?v2) ?v1)) ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S4) (?v3 S2)) (let ((?v_0 (f8 (f9 (f10 f11 ?v0) ?v1)))) (= (= (f5 ?v_0 (f93 (f94 ?v2) ?v3)) f1) (and (not (= ?v1 ?v3)) (ite (= ?v0 ?v3) (not (= ?v0 ?v1)) (= (f5 ?v_0 ?v2) f1)))))))
(assert (forall ((?v0 S3) (?v1 S4)) (= (= (f5 (f63 ?v0) ?v1) f1) (and (= (f7 ?v1) f1) (and (= (f52 ?v1) f1) (= (f5 (f78 ?v0) ?v1) f1))))))
(assert (forall ((?v0 S38) (?v1 S9)) (= (= (f95 ?v0 ?v1) f1) (and (= (f12 ?v1) f1) (and (= (f53 ?v1) f1) (= (f92 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S35) (?v1 S14)) (= (= (f96 ?v0 ?v1) f1) (and (= (f17 ?v1) f1) (and (= (f54 ?v1) f1) (= (f91 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S32) (?v1 S19)) (= (= (f97 ?v0 ?v1) f1) (and (= (f22 ?v1) f1) (and (= (f55 ?v1) f1) (= (f90 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S29) (?v1 S24)) (= (= (f98 ?v0 ?v1) f1) (and (= (f27 ?v1) f1) (and (= (f56 ?v1) f1) (= (f89 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S14) (?v1 S29)) (= (= (f99 ?v0 ?v1) f1) (and (= (f32 ?v1) f1) (and (= (f57 ?v1) f1) (= (f82 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S9) (?v1 S32)) (= (= (f100 ?v0 ?v1) f1) (and (= (f37 ?v1) f1) (and (= (f58 ?v1) f1) (= (f81 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S5) (?v1 S35)) (= (= (f101 ?v0 ?v1) f1) (and (= (f42 ?v1) f1) (and (= (f59 ?v1) f1) (= (f80 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S4) (?v1 S38)) (= (= (f102 ?v0 ?v1) f1) (and (= (f47 ?v1) f1) (and (= (f60 ?v1) f1) (= (f79 ?v0 ?v1) f1))))))
(assert (not (=> (= (f66 f103 f61) f1) (= (f66 (f93 (f94 f103) f104) f61) f1))))
(check-sat)
(exit)
