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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 (S7 S6) S1)
(declare-fun f7 (S8 S6) S7)
(declare-fun f8 (S5) S8)
(declare-fun f9 (S9 S5) S1)
(declare-fun f10 (S10 S6) S9)
(declare-fun f11 (S11 S6) S10)
(declare-fun f12 () S11)
(declare-fun f13 (S15 S14) S1)
(declare-fun f14 (S16 S13) S15)
(declare-fun f15 (S12) S16)
(declare-fun f16 (S17 S12) S1)
(declare-fun f17 (S18 S14) S17)
(declare-fun f18 (S19 S13) S18)
(declare-fun f19 () S19)
(declare-fun f20 (S21 S20) S1)
(declare-fun f21 (S22 S14) S21)
(declare-fun f22 (S7) S22)
(declare-fun f23 (S6 S7) S1)
(declare-fun f24 (S23 S20) S6)
(declare-fun f25 (S24 S14) S23)
(declare-fun f26 () S24)
(declare-fun f27 (S27 S26) S1)
(declare-fun f28 (S28 S25) S27)
(declare-fun f29 (S21) S28)
(declare-fun f30 (S20 S21) S1)
(declare-fun f31 (S29 S26) S20)
(declare-fun f32 (S30 S25) S29)
(declare-fun f33 () S30)
(declare-fun f34 (S31 S25 S32 S14 S2) S1)
(declare-fun f35 () S31)
(declare-fun f36 () S25)
(declare-fun f37 () S32)
(declare-fun f38 (S33 S34) S14)
(declare-fun f39 (S35 S36) S33)
(declare-fun f40 (S37 S14) S35)
(declare-fun f41 () S37)
(declare-fun f42 () S14)
(declare-fun f43 () S36)
(declare-fun f44 () S34)
(declare-fun f45 (S31) S4)
(declare-fun f46 () S2)
(declare-fun f47 () S25)
(declare-fun f48 () S14)
(declare-fun f49 () S2)
(declare-fun f50 (S31 S25 S32 S34 S38) S1)
(declare-fun f51 (S39 S36) S2)
(declare-fun f52 () S39)
(declare-fun f53 (S31 S36 S36 S38 S2 S17 S36) S1)
(declare-fun f54 (S4 S38 S38) S1)
(declare-fun f55 (S40 S31) S1)
(declare-fun f56 () S40)
(declare-fun f57 (S41 S32) S21)
(declare-fun f58 (S31) S41)
(declare-fun f59 () S26)
(declare-fun f60 () S26)
(declare-fun f61 (S31) S5)
(declare-fun f62 (S42 S7) S36)
(declare-fun f63 (S43 S7) S7)
(declare-fun f64 (S6) S43)
(declare-fun f65 () S7)
(declare-fun f66 (S44 S21) S36)
(declare-fun f67 (S45 S21) S21)
(declare-fun f68 (S20) S45)
(declare-fun f69 () S21)
(declare-fun f70 (S46 S12) S36)
(declare-fun f71 (S47 S12) S12)
(declare-fun f72 (S17) S47)
(declare-fun f73 () S12)
(declare-fun f74 (S48 S5) S36)
(declare-fun f75 (S49 S5) S5)
(declare-fun f76 (S9) S49)
(declare-fun f77 () S5)
(declare-fun f78 (S31 S32 S14 S2) S1)
(declare-fun f79 (S31 S32 S34 S38) S1)
(declare-fun f80 (S5 S9) S1)
(declare-fun f81 (S12 S17) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S6)) (= (= (f6 (f7 (f8 ?v0) ?v1) ?v2) f1) (= (f9 (f10 (f11 f12 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S13) (?v2 S14)) (= (= (f13 (f14 (f15 ?v0) ?v1) ?v2) f1) (= (f16 (f17 (f18 f19 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S7) (?v1 S14) (?v2 S20)) (= (= (f20 (f21 (f22 ?v0) ?v1) ?v2) f1) (= (f23 (f24 (f25 f26 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S21) (?v1 S25) (?v2 S26)) (= (= (f27 (f28 (f29 ?v0) ?v1) ?v2) f1) (= (f30 (f31 (f32 f33 ?v1) ?v2) ?v0) f1))))
(assert (not (exists ((?v0 S2)) (and (= (f34 f35 f36 f37 (f38 (f39 (f40 f41 f42) f43) f44) ?v0) f1) (= (f3 (f4 (f45 f35) ?v0) f46) f1)))))
(assert (forall ((?v0 S38)) (=> (= (f34 f35 f47 f37 f48 f49) f1) (=> (= (f50 f35 f47 f37 f44 ?v0) f1) (exists ((?v1 S2)) (and (= (f34 f35 f36 f37 (f38 (f39 (f40 f41 f42) f43) f44) ?v1) f1) (= (f3 (f4 (f45 f35) ?v1) f46) f1)))))))
(assert (forall ((?v0 S36) (?v1 S38) (?v2 S13) (?v3 S14) (?v4 S36) (?v5 S38)) (=> (= (f34 f35 f47 f37 f48 (f51 f52 ?v0)) f1) (=> (= (f53 f35 ?v0 f43 ?v1 f46 (f17 (f18 f19 ?v2) ?v3) ?v4) f1) (=> (= (f50 f35 f47 f37 f44 ?v5) f1) (=> (= (f54 (f45 f35) ?v5 ?v1) f1) (exists ((?v6 S2)) (and (= (f34 f35 f36 f37 (f38 (f39 (f40 f41 f42) f43) f44) ?v6) f1) (= (f3 (f4 (f45 f35) ?v6) f46) f1)))))))))
(assert (= (f34 f35 f47 f37 (f38 (f39 (f40 f41 f48) f43) f44) f46) f1))
(assert (= (f34 f35 f47 f37 (f38 (f39 (f40 f41 f48) f43) f44) f46) f1))
(assert (= (f34 f35 f47 f37 (f38 (f39 (f40 f41 f48) f43) f44) f46) f1))
(assert (forall ((?v0 S38)) (=> (= (f34 f35 f47 f37 f48 f49) f1) (=> (= (f50 f35 f47 f37 f44 ?v0) f1) (exists ((?v1 S2)) (and (= (f34 f35 f36 f37 (f38 (f39 (f40 f41 f42) f43) f44) ?v1) f1) (= (f3 (f4 (f45 f35) ?v1) f46) f1)))))))
(assert (forall ((?v0 S36) (?v1 S38) (?v2 S13) (?v3 S14) (?v4 S36) (?v5 S38)) (=> (= (f34 f35 f47 f37 f48 (f51 f52 ?v0)) f1) (=> (= (f53 f35 ?v0 f43 ?v1 f46 (f17 (f18 f19 ?v2) ?v3) ?v4) f1) (=> (= (f50 f35 f47 f37 f44 ?v5) f1) (=> (= (f54 (f45 f35) ?v5 ?v1) f1) (exists ((?v6 S2)) (and (= (f34 f35 f36 f37 (f38 (f39 (f40 f41 f42) f43) f44) ?v6) f1) (= (f3 (f4 (f45 f35) ?v6) f46) f1)))))))))
(assert (forall ((?v0 S31) (?v1 S2)) (= (f3 (f4 (f45 ?v0) ?v1) ?v1) f1)))
(assert (= (f55 f56 f35) f1))
(assert (forall ((?v0 S32) (?v1 S2)) (=> (= (f20 (f57 (f58 f35) ?v0) (f31 (f32 f33 f47) f59)) f1) (=> (= (f34 f35 f47 ?v0 f48 ?v1) f1) (exists ((?v2 S2)) (and (= (f34 f35 f36 ?v0 f42 ?v2) f1) (= (f3 (f4 (f45 f35) ?v2) ?v1) f1)))))))
(assert (forall ((?v0 S14) (?v1 S36) (?v2 S34) (?v3 S14) (?v4 S36) (?v5 S34)) (= (= (f38 (f39 (f40 f41 ?v0) ?v1) ?v2) (f38 (f39 (f40 f41 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S31) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f45 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (=> (= (f3 ?v_1 ?v2) f1) (=> (= (f3 (f4 ?v_0 ?v2) ?v3) f1) (= (f3 ?v_1 ?v3) f1)))))))
(assert (forall ((?v0 S32) (?v1 S2)) (=> (= (f20 (f57 (f58 f35) ?v0) (f31 (f32 f33 f47) f59)) f1) (=> (= (f34 f35 f47 ?v0 f48 ?v1) f1) (exists ((?v2 S2)) (and (= (f34 f35 f36 ?v0 f42 ?v2) f1) (= (f3 (f4 (f45 f35) ?v2) ?v1) f1)))))))
(assert (= (f20 (f57 (f58 f35) f37) (f31 (f32 f33 f47) f59)) f1))
(assert (forall ((?v0 S31) (?v1 S25) (?v2 S32) (?v3 S14) (?v4 S34) (?v5 S38) (?v6 S36) (?v7 S2)) (=> (= (f34 ?v0 ?v1 ?v2 ?v3 f49) f1) (=> (= (f50 ?v0 ?v1 ?v2 ?v4 ?v5) f1) (= (f34 ?v0 ?v1 ?v2 (f38 (f39 (f40 f41 ?v3) ?v6) ?v4) ?v7) f1)))))
(assert (forall ((?v0 S31) (?v1 S38)) (= (f54 (f45 ?v0) ?v1 ?v1) f1)))
(assert (forall ((?v0 S31) (?v1 S25) (?v2 S32) (?v3 S14) (?v4 S36) (?v5 S36) (?v6 S38) (?v7 S2) (?v8 S13) (?v9 S14) (?v10 S36) (?v11 S34) (?v12 S38)) (=> (= (f34 ?v0 ?v1 ?v2 ?v3 (f51 f52 ?v4)) f1) (=> (= (f53 ?v0 ?v4 ?v5 ?v6 ?v7 (f17 (f18 f19 ?v8) ?v9) ?v10) f1) (=> (= (f50 ?v0 ?v1 ?v2 ?v11 ?v12) f1) (=> (= (f54 (f45 ?v0) ?v12 ?v6) f1) (= (f34 ?v0 ?v1 ?v2 (f38 (f39 (f40 f41 ?v3) ?v5) ?v11) ?v7) f1)))))))
(assert (= (f20 (f57 (f58 f35) f37) (f31 (f32 f33 f47) f59)) f1))
(assert (forall ((?v0 S31) (?v1 S36)) (= (f3 (f4 (f45 ?v0) f49) (f51 f52 ?v1)) f1)))
(assert (forall ((?v0 S31) (?v1 S36) (?v2 S36) (?v3 S38) (?v4 S2) (?v5 S17) (?v6 S36)) (=> (= (f53 ?v0 ?v1 ?v2 ?v3 ?v4 ?v5 ?v6) f1) (= (f53 ?v0 ?v6 ?v2 ?v3 ?v4 ?v5 ?v6) f1))))
(assert (forall ((?v0 S31) (?v1 S36) (?v2 S36) (?v3 S38) (?v4 S2) (?v5 S17) (?v6 S36) (?v7 S38) (?v8 S2) (?v9 S17) (?v10 S36)) (=> (= (f53 ?v0 ?v1 ?v2 ?v3 ?v4 ?v5 ?v6) f1) (=> (= (f53 ?v0 ?v1 ?v2 ?v7 ?v8 ?v9 ?v10) f1) (and (= ?v7 ?v3) (and (= ?v8 ?v4) (and (= ?v9 ?v5) (= ?v10 ?v6))))))))
(assert (forall ((?v0 S31) (?v1 S38) (?v2 S38) (?v3 S38)) (let ((?v_0 (f45 ?v0))) (=> (= (f54 ?v_0 ?v1 ?v2) f1) (=> (= (f54 ?v_0 ?v2 ?v3) f1) (= (f54 ?v_0 ?v1 ?v3) f1))))))
(assert (forall ((?v0 S31) (?v1 S36) (?v2 S2)) (=> (= (f3 (f4 (f45 ?v0) (f51 f52 ?v1)) ?v2) f1) (exists ((?v3 S36)) (= ?v2 (f51 f52 ?v3))))))
(assert (forall ((?v0 S36)) (not (= f49 (f51 f52 ?v0)))))
(assert (forall ((?v0 S36)) (not (= (f51 f52 ?v0) f49))))
(assert (= (f9 (f10 (f11 f12 (f24 (f25 f26 f48) (f31 (f32 f33 f47) f59))) (f24 (f25 f26 f42) (f31 (f32 f33 f36) f60))) (f61 f35)) f1))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f8 ?v0) (f8 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f22 ?v0) (f22 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S21) (?v1 S21)) (= (= (f29 ?v0) (f29 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f15 ?v0) (f15 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S31) (?v1 S25) (?v2 S32) (?v3 S14) (?v4 S42) (?v5 S6) (?v6 S34) (?v7 S2)) (=> (= (f34 ?v0 ?v1 ?v2 (f38 (f39 (f40 f41 ?v3) (f62 ?v4 (f63 (f64 ?v5) f65))) ?v6) ?v7) f1) (=> (forall ((?v8 S36) (?v9 S38) (?v10 S13) (?v11 S14) (?v12 S36) (?v13 S38)) (=> (= (f34 ?v0 ?v1 ?v2 ?v3 (f51 f52 ?v8)) f1) (=> (= (f53 ?v0 ?v8 (f62 ?v4 (f63 (f64 ?v5) f65)) ?v9 ?v7 (f17 (f18 f19 ?v10) ?v11) ?v12) f1) (=> (= (f50 ?v0 ?v1 ?v2 ?v6 ?v13) f1) (=> (= (f54 (f45 ?v0) ?v13 ?v9) f1) false))))) (=> (forall ((?v8 S38)) (=> (= (f34 ?v0 ?v1 ?v2 ?v3 f49) f1) (=> (= (f50 ?v0 ?v1 ?v2 ?v6 ?v8) f1) false))) false)))))
(assert (forall ((?v0 S31) (?v1 S25) (?v2 S32) (?v3 S14) (?v4 S44) (?v5 S20) (?v6 S34) (?v7 S2)) (=> (= (f34 ?v0 ?v1 ?v2 (f38 (f39 (f40 f41 ?v3) (f66 ?v4 (f67 (f68 ?v5) f69))) ?v6) ?v7) f1) (=> (forall ((?v8 S36) (?v9 S38) (?v10 S13) (?v11 S14) (?v12 S36) (?v13 S38)) (=> (= (f34 ?v0 ?v1 ?v2 ?v3 (f51 f52 ?v8)) f1) (=> (= (f53 ?v0 ?v8 (f66 ?v4 (f67 (f68 ?v5) f69)) ?v9 ?v7 (f17 (f18 f19 ?v10) ?v11) ?v12) f1) (=> (= (f50 ?v0 ?v1 ?v2 ?v6 ?v13) f1) (=> (= (f54 (f45 ?v0) ?v13 ?v9) f1) false))))) (=> (forall ((?v8 S38)) (=> (= (f34 ?v0 ?v1 ?v2 ?v3 f49) f1) (=> (= (f50 ?v0 ?v1 ?v2 ?v6 ?v8) f1) false))) false)))))
(assert (forall ((?v0 S31) (?v1 S25) (?v2 S32) (?v3 S14) (?v4 S46) (?v5 S17) (?v6 S34) (?v7 S2)) (=> (= (f34 ?v0 ?v1 ?v2 (f38 (f39 (f40 f41 ?v3) (f70 ?v4 (f71 (f72 ?v5) f73))) ?v6) ?v7) f1) (=> (forall ((?v8 S36) (?v9 S38) (?v10 S13) (?v11 S14) (?v12 S36) (?v13 S38)) (=> (= (f34 ?v0 ?v1 ?v2 ?v3 (f51 f52 ?v8)) f1) (=> (= (f53 ?v0 ?v8 (f70 ?v4 (f71 (f72 ?v5) f73)) ?v9 ?v7 (f17 (f18 f19 ?v10) ?v11) ?v12) f1) (=> (= (f50 ?v0 ?v1 ?v2 ?v6 ?v13) f1) (=> (= (f54 (f45 ?v0) ?v13 ?v9) f1) false))))) (=> (forall ((?v8 S38)) (=> (= (f34 ?v0 ?v1 ?v2 ?v3 f49) f1) (=> (= (f50 ?v0 ?v1 ?v2 ?v6 ?v8) f1) false))) false)))))
(assert (forall ((?v0 S31) (?v1 S25) (?v2 S32) (?v3 S14) (?v4 S48) (?v5 S9) (?v6 S34) (?v7 S2)) (=> (= (f34 ?v0 ?v1 ?v2 (f38 (f39 (f40 f41 ?v3) (f74 ?v4 (f75 (f76 ?v5) f77))) ?v6) ?v7) f1) (=> (forall ((?v8 S36) (?v9 S38) (?v10 S13) (?v11 S14) (?v12 S36) (?v13 S38)) (=> (= (f34 ?v0 ?v1 ?v2 ?v3 (f51 f52 ?v8)) f1) (=> (= (f53 ?v0 ?v8 (f74 ?v4 (f75 (f76 ?v5) f77)) ?v9 ?v7 (f17 (f18 f19 ?v10) ?v11) ?v12) f1) (=> (= (f50 ?v0 ?v1 ?v2 ?v6 ?v13) f1) (=> (= (f54 (f45 ?v0) ?v13 ?v9) f1) false))))) (=> (forall ((?v8 S38)) (=> (= (f34 ?v0 ?v1 ?v2 ?v3 f49) f1) (=> (= (f50 ?v0 ?v1 ?v2 ?v6 ?v8) f1) false))) false)))))
(assert (forall ((?v0 S31) (?v1 S32) (?v2 S14) (?v3 S36) (?v4 S36) (?v5 S38) (?v6 S2) (?v7 S13) (?v8 S14) (?v9 S36) (?v10 S34) (?v11 S38)) (=> (= (f78 ?v0 ?v1 ?v2 (f51 f52 ?v3)) f1) (=> (= (f53 ?v0 ?v3 ?v4 ?v5 ?v6 (f17 (f18 f19 ?v7) ?v8) ?v9) f1) (=> (= (f79 ?v0 ?v1 ?v10 ?v11) f1) (=> (= (f54 (f45 ?v0) ?v11 ?v5) f1) (= (f78 ?v0 ?v1 (f38 (f39 (f40 f41 ?v2) ?v4) ?v10) ?v6) f1)))))))
(assert (forall ((?v0 S36) (?v1 S36)) (= (= (f51 f52 ?v0) (f51 f52 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S38) (?v1 S38)) (= (= ?v0 ?v1) (= (f54 f5 ?v0 ?v1) f1))))
(assert (forall ((?v0 S9)) (= (= (f80 f77 ?v0) f1) (= (f9 ?v0 f77) f1))))
(assert (forall ((?v0 S17)) (= (= (f81 f73 ?v0) f1) (= (f16 ?v0 f73) f1))))
(assert (forall ((?v0 S20)) (= (= (f20 f69 ?v0) f1) (= (f30 ?v0 f69) f1))))
(assert (forall ((?v0 S6)) (= (= (f6 f65 ?v0) f1) (= (f23 ?v0 f65) f1))))
(assert (forall ((?v0 S31) (?v1 S32) (?v2 S14) (?v3 S2) (?v4 S25)) (=> (= (f78 ?v0 ?v1 ?v2 ?v3) f1) (= (f34 ?v0 ?v4 ?v1 ?v2 ?v3) f1))))
(assert (forall ((?v0 S31) (?v1 S32) (?v2 S34) (?v3 S38) (?v4 S25)) (=> (= (f79 ?v0 ?v1 ?v2 ?v3) f1) (= (f50 ?v0 ?v4 ?v1 ?v2 ?v3) f1))))
(check-sat)
(exit)