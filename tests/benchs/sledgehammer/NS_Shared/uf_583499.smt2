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
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S4 S2) S2)
(declare-fun f6 () S4)
(declare-fun f7 (S6 S5) S1)
(declare-fun f8 (S7 S6) S6)
(declare-fun f9 (S8 S5) S7)
(declare-fun f10 () S8)
(declare-fun f11 (S9 S6) S1)
(declare-fun f12 (S10 S5) S9)
(declare-fun f13 () S10)
(declare-fun f14 (S12 S11) S1)
(declare-fun f15 (S13 S12) S12)
(declare-fun f16 (S14 S11) S13)
(declare-fun f17 () S14)
(declare-fun f18 (S15 S12) S1)
(declare-fun f19 (S16 S11) S15)
(declare-fun f20 () S16)
(declare-fun f21 (S18 S17) S1)
(declare-fun f22 (S19 S18) S18)
(declare-fun f23 (S20 S17) S19)
(declare-fun f24 () S20)
(declare-fun f25 (S21 S18) S1)
(declare-fun f26 (S22 S17) S21)
(declare-fun f27 () S22)
(declare-fun f28 (S23 S3) S3)
(declare-fun f29 (S24 S2) S23)
(declare-fun f30 () S24)
(declare-fun f31 (S25 S3) S1)
(declare-fun f32 (S26 S2) S25)
(declare-fun f33 () S26)
(declare-fun f34 () S8)
(declare-fun f35 () S14)
(declare-fun f36 () S20)
(declare-fun f37 () S24)
(declare-fun f38 (S27 S2) S11)
(declare-fun f39 () S27)
(declare-fun f40 (S28 S5) S2)
(declare-fun f41 () S28)
(declare-fun f42 () S5)
(declare-fun f43 () S13)
(declare-fun f44 (S29 S17) S12)
(declare-fun f45 (S30 S5) S29)
(declare-fun f46 () S30)
(declare-fun f47 () S5)
(declare-fun f48 () S17)
(declare-fun f49 () S6)
(declare-fun f50 () S18)
(declare-fun f51 () S29)
(declare-fun f52 (S32 S31) S28)
(declare-fun f53 () S32)
(declare-fun f54 (S33 S5) S12)
(declare-fun f55 () S33)
(declare-fun f56 () S18)
(declare-fun f57 (S34 S12) S15)
(declare-fun f58 () S34)
(declare-fun f59 () S13)
(declare-fun f60 () S3)
(declare-fun f61 () S23)
(declare-fun f62 (S35 S3) S25)
(declare-fun f63 () S35)
(declare-fun f64 (S36 S18) S21)
(declare-fun f65 () S36)
(declare-fun f66 (S37 S6) S9)
(declare-fun f67 () S37)
(declare-fun f68 (S38 S1) S1)
(declare-fun f69 (S39 S1) S38)
(declare-fun f70 () S39)
(declare-fun f71 () S31)
(declare-fun f72 (S40 S11) S11)
(declare-fun f73 (S41 S2) S40)
(declare-fun f74 () S41)
(declare-fun f75 () S13)
(declare-fun f76 () S19)
(declare-fun f77 () S7)
(declare-fun f78 () S14)
(declare-fun f79 () S8)
(declare-fun f80 () S20)
(declare-fun f81 () S24)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (= (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f7 (f8 (f9 f10 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f11 (f12 f13 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11)) (= (= (f14 (f15 (f16 f17 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f18 (f19 f20 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S17) (?v1 S18) (?v2 S17)) (= (= (f21 (f22 (f23 f24 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f25 (f26 f27 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f28 (f29 f30 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f31 (f32 f33 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f7 (f8 (f9 f34 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f7 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11)) (= (= (f14 (f15 (f16 f35 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f14 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S17) (?v1 S18) (?v2 S17)) (= (= (f21 (f22 (f23 f36 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f21 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f28 (f29 f37 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (not (= (= (f18 (f19 f20 (f38 f39 (f40 f41 f42))) (f15 f43 (f44 (f45 f46 f47) f48))) f1) (= (f11 (f12 f13 f42) f49) f1))))
(assert (= (f25 (f26 f27 f48) f50) f1))
(assert (forall ((?v0 S5) (?v1 S17)) (=> (= (f11 (f12 f13 ?v0) f49) f1) (= (f18 (f19 f20 (f38 f39 (f40 f41 ?v0))) (f44 (f45 f46 f47) ?v1)) f1))))
(assert (forall ((?v0 S5) (?v1 S17)) (= (f18 (f19 f20 (f38 f39 (f40 f41 ?v0))) (f44 (f45 f46 ?v0) ?v1)) f1)))
(assert (= (f11 (f12 f13 f47) f49) f1))
(assert (forall ((?v0 S11) (?v1 S12)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f18 ?v_0 ?v1) f1) (= (f18 ?v_0 (f15 f43 ?v1)) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f40 f41 ?v0) (f40 f41 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f38 f39 ?v0) (f38 f39 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12)) (let ((?v_0 (f15 f43 ?v0))) (= (f15 f43 ?v_0) ?v_0))))
(assert (forall ((?v0 S11) (?v1 S12)) (let ((?v_0 (f19 f20 ?v0)) (?v_1 (f15 f43 ?v1))) (=> (= (f18 ?v_0 (f15 f43 ?v_1)) f1) (= (f18 ?v_0 ?v_1) f1)))))
(assert (forall ((?v0 S11) (?v1 S17)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f18 ?v_0 (f15 f43 (f44 (f45 f46 f47) ?v1))) f1) (= (f18 ?v_0 (f44 f51 ?v1)) f1)))))
(assert (forall ((?v0 S31) (?v1 S5) (?v2 S17)) (= (f18 (f19 f20 (f38 f39 (f40 (f52 f53 ?v0) ?v1))) (f44 (f45 f46 f47) ?v2)) f1)))
(assert (forall ((?v0 S5)) (= (f18 (f19 f20 (f38 f39 (f40 f41 ?v0))) (f54 f55 ?v0)) f1)))
(assert (forall ((?v0 S17)) (= (= (f21 f56 ?v0) f1) (= (f25 (f26 f27 ?v0) f50) f1))))
(assert (forall ((?v0 S31) (?v1 S5) (?v2 S17)) (= (f18 (f19 f20 (f38 f39 (f40 (f52 f53 ?v0) ?v1))) (f44 f51 ?v2)) f1)))
(assert (forall ((?v0 S5) (?v1 S17)) (= (f18 (f19 f20 (f38 f39 (f40 f41 ?v0))) (f44 f51 ?v1)) f1)))
(assert (forall ((?v0 S31) (?v1 S5) (?v2 S5)) (= (f18 (f19 f20 (f38 f39 (f40 (f52 f53 ?v0) ?v1))) (f54 f55 ?v2)) f1)))
(assert (forall ((?v0 S31) (?v1 S5) (?v2 S31) (?v3 S5)) (= (= (f40 (f52 f53 ?v0) ?v1) (f40 (f52 f53 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S31) (?v1 S5) (?v2 S31) (?v3 S5)) (=> (= (f40 (f52 f53 ?v0) ?v1) (f40 (f52 f53 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S17)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f18 ?v_0 (f15 f43 (f54 f55 ?v1))) f1) (= (f18 ?v_0 (f44 f51 ?v2)) f1)))))
(assert (forall ((?v0 S31) (?v1 S5) (?v2 S5)) (not (= (f40 (f52 f53 ?v0) ?v1) (f40 f41 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S31) (?v2 S5)) (not (= (f40 f41 ?v0) (f40 (f52 f53 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S17) (?v2 S5)) (=> (not (= (f18 (f19 f20 (f38 f39 ?v0)) (f44 f51 ?v1)) f1)) (not (= (f40 f41 ?v2) ?v0)))))
(assert (forall ((?v0 S2) (?v1 S17) (?v2 S5)) (=> (not (= (f18 (f19 f20 (f38 f39 ?v0)) (f44 f51 ?v1)) f1)) (not (= ?v0 (f40 f41 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S31) (?v2 S17)) (=> (= (f11 (f12 f13 ?v0) f49) f1) (= (f18 (f19 f20 (f38 f39 (f5 f6 (f40 (f52 f53 ?v1) ?v0)))) (f44 (f45 f46 f47) ?v2)) f1))))
(assert (forall ((?v0 S31) (?v1 S5)) (= (f18 (f19 f20 (f38 f39 (f5 f6 (f40 (f52 f53 ?v0) ?v1)))) (f54 f55 ?v1)) f1)))
(assert (forall ((?v0 S17)) (= (f18 (f57 f58 (f15 f43 (f44 (f45 f46 f47) ?v0))) (f44 f51 ?v0)) f1)))
(assert (forall ((?v0 S31) (?v1 S5) (?v2 S17)) (= (f18 (f19 f20 (f38 f39 (f5 f6 (f40 (f52 f53 ?v0) ?v1)))) (f44 f51 ?v2)) f1)))
(assert (forall ((?v0 S31) (?v1 S5) (?v2 S17)) (= (f18 (f19 f20 (f38 f39 (f40 (f52 f53 ?v0) ?v1))) (f15 f59 (f44 (f45 f46 f47) ?v2))) f1)))
(assert (forall ((?v0 S5)) (= (f31 (f32 f33 (f40 f41 ?v0)) f60) f1)))
(assert (forall ((?v0 S5) (?v1 S31) (?v2 S5)) (not (= (f40 f41 ?v0) (f5 f6 (f40 (f52 f53 ?v1) ?v2))))))
(assert (forall ((?v0 S31) (?v1 S5) (?v2 S5)) (not (= (f5 f6 (f40 (f52 f53 ?v0) ?v1)) (f40 f41 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S17)) (= (f18 (f57 f58 (f54 f55 ?v0)) (f44 (f45 f46 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S11) (?v1 S12)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f18 ?v_0 ?v1) f1) (= (f18 ?v_0 (f15 f59 ?v1)) f1)))))
(assert (forall ((?v0 S12)) (= (f18 (f57 f58 ?v0) (f15 f59 ?v0)) f1)))
(assert (forall ((?v0 S2)) (= (f5 f6 (f5 f6 ?v0)) ?v0)))
(assert (forall ((?v0 S12)) (let ((?v_0 (f15 f59 ?v0))) (= (f15 f59 ?v_0) ?v_0))))
(assert (forall ((?v0 S2)) (= (= (f31 (f32 f33 (f5 f6 ?v0)) f60) f1) (= (f31 (f32 f33 ?v0) f60) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f5 f6 ?v0) (f5 f6 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f15 f59 ?v1))) (= (= (f18 (f57 f58 (f15 f59 ?v0)) ?v_0) f1) (= (f18 (f57 f58 ?v0) ?v_0) f1)))))
(assert (= f60 (f28 f61 f4)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (= (f31 (f32 f33 ?v0) f60) f1) (= (f31 (f32 f33 ?v1) f60) f1))) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S2)) (=> (= (f31 (f32 f33 ?v0) f60) f1) (= (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (= (f18 (f57 f58 (f15 f59 ?v0)) (f15 f59 ?v1)) f1))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S12)) (let ((?v_0 (f19 f20 ?v0)) (?v_1 (f15 f59 ?v2))) (=> (= (f18 ?v_0 (f15 f59 ?v1)) f1) (=> (= (f18 (f57 f58 ?v1) ?v_1) f1) (= (f18 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S11) (?v1 S12)) (let ((?v_0 (f19 f20 ?v0)) (?v_1 (f15 f59 ?v1))) (=> (= (f18 ?v_0 (f15 f59 ?v_1)) f1) (= (f18 ?v_0 ?v_1) f1)))))
(assert (forall ((?v0 S12)) (= (f18 (f57 f58 (f15 f59 ?v0)) (f15 f43 ?v0)) f1)))
(assert (forall ((?v0 S31) (?v1 S5)) (not (= (f31 (f32 f33 (f5 f6 (f40 (f52 f53 ?v0) ?v1))) f60) f1))))
(assert (forall ((?v0 S12)) (let ((?v_0 (f15 f43 ?v0))) (= (f15 f59 ?v_0) ?v_0))))
(assert (forall ((?v0 S12)) (= (f15 f43 (f15 f59 ?v0)) (f15 f43 ?v0))))
(assert (forall ((?v0 S11) (?v1 S12)) (let ((?v_0 (f19 f20 ?v0))) (let ((?v_1 (= (f18 ?v_0 (f15 f59 ?v1)) f1))) (= (and ?v_1 (= (f18 ?v_0 (f15 f43 ?v1)) f1)) ?v_1)))))
(assert (forall ((?v0 S11) (?v1 S12)) (let ((?v_0 (f19 f20 ?v0))) (let ((?v_1 (= (f18 ?v_0 (f15 f43 ?v1)) f1))) (= (or (= (f18 ?v_0 (f15 f59 ?v1)) f1) ?v_1) ?v_1)))))
(assert (forall ((?v0 S11) (?v1 S12)) (let ((?v_0 (f19 f20 ?v0))) (=> (not (= (f18 ?v_0 (f15 f43 ?v1)) f1)) (not (= (f18 ?v_0 (f15 f59 ?v1)) f1))))))
(assert (forall ((?v0 S11) (?v1 S12)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f18 ?v_0 (f15 f59 ?v1)) f1) (= (f18 ?v_0 (f15 f43 ?v1)) f1)))))
(assert (forall ((?v0 S12)) (= (f18 (f57 f58 ?v0) (f15 f43 ?v0)) f1)))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f15 f43 ?v1))) (= (= (f18 (f57 f58 (f15 f43 ?v0)) ?v_0) f1) (= (f18 (f57 f58 ?v0) ?v_0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (= (f18 (f57 f58 (f15 f43 ?v0)) (f15 f43 ?v1)) f1))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S12)) (let ((?v_0 (f19 f20 ?v0)) (?v_1 (f15 f43 ?v2))) (=> (= (f18 ?v_0 (f15 f43 ?v1)) f1) (=> (= (f18 (f57 f58 ?v1) ?v_1) f1) (= (f18 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S31) (?v1 S5) (?v2 S31) (?v3 S5)) (not (= (f40 (f52 f53 ?v0) ?v1) (f5 f6 (f40 (f52 f53 ?v2) ?v3))))))
(assert (forall ((?v0 S31) (?v1 S5) (?v2 S31) (?v3 S5)) (not (= (f5 f6 (f40 (f52 f53 ?v0) ?v1)) (f40 (f52 f53 ?v2) ?v3)))))
(assert (forall ((?v0 S5)) (let ((?v_0 (f40 f41 ?v0))) (= (f5 f6 ?v_0) ?v_0))))
(assert (forall ((?v0 S31) (?v1 S5)) (not (= (f31 (f32 f33 (f40 (f52 f53 ?v0) ?v1)) f60) f1))))
(assert (forall ((?v0 S11) (?v1 S17) (?v2 S1)) (let ((?v_0 (=> (not (= (f18 (f19 f20 ?v0) (f15 f59 (f44 (f45 f46 f47) ?v1))) f1)) (= ?v2 f1)))) (=> ?v_0 ?v_0))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f31 (f62 f63 ?v0) ?v1) f1) (=> (= (f31 (f62 f63 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f25 (f64 f65 ?v0) ?v1) f1) (=> (= (f25 (f64 f65 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f11 (f66 f67 ?v0) ?v1) f1) (=> (= (f11 (f66 f67 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (=> (= (f18 (f57 f58 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S11)) (let ((?v_0 (f19 f20 ?v2))) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (=> (= (f18 ?v_0 ?v0) f1) (= (f18 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S5)) (let ((?v_0 (f12 f13 ?v2))) (=> (= (f11 (f66 f67 ?v0) ?v1) f1) (=> (= (f11 ?v_0 ?v0) f1) (= (f11 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S17)) (let ((?v_0 (f26 f27 ?v2))) (=> (= (f25 (f64 f65 ?v0) ?v1) f1) (=> (= (f25 ?v_0 ?v0) f1) (= (f25 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f32 f33 ?v2))) (=> (= (f31 (f62 f63 ?v0) ?v1) f1) (=> (= (f31 ?v_0 ?v0) f1) (= (f31 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S1)) (= (f68 (f69 f70 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f31 (f62 f63 ?v0) ?v0) f1)))
(assert (forall ((?v0 S18)) (= (f25 (f64 f65 ?v0) ?v0) f1)))
(assert (forall ((?v0 S6)) (= (f11 (f66 f67 ?v0) ?v0) f1)))
(assert (forall ((?v0 S12)) (= (f18 (f57 f58 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f31 (f62 f63 ?v0) ?v1) f1) (=> (=> (= (f68 (f69 f70 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1) false) false))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S17)) (=> (= (f25 (f64 f65 ?v0) ?v1) f1) (=> (=> (= (f68 (f69 f70 (f21 ?v0 ?v2)) (f21 ?v1 ?v2)) f1) false) false))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S5)) (=> (= (f11 (f66 f67 ?v0) ?v1) f1) (=> (=> (= (f68 (f69 f70 (f7 ?v0 ?v2)) (f7 ?v1 ?v2)) f1) false) false))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S11)) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (=> (=> (= (f68 (f69 f70 (f14 ?v0 ?v2)) (f14 ?v1 ?v2)) f1) false) false))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f31 (f62 f63 ?v0) ?v1) f1) (= (f68 (f69 f70 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S17)) (=> (= (f25 (f64 f65 ?v0) ?v1) f1) (= (f68 (f69 f70 (f21 ?v0 ?v2)) (f21 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S5)) (=> (= (f11 (f66 f67 ?v0) ?v1) f1) (= (f68 (f69 f70 (f7 ?v0 ?v2)) (f7 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S11)) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (= (f68 (f69 f70 (f14 ?v0 ?v2)) (f14 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f31 (f62 f63 ?v0) ?v1) f1) (forall ((?v2 S2)) (= (f68 (f69 f70 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (= (f25 (f64 f65 ?v0) ?v1) f1) (forall ((?v2 S17)) (= (f68 (f69 f70 (f21 ?v0 ?v2)) (f21 ?v1 ?v2)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f11 (f66 f67 ?v0) ?v1) f1) (forall ((?v2 S5)) (= (f68 (f69 f70 (f7 ?v0 ?v2)) (f7 ?v1 ?v2)) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f18 (f57 f58 ?v0) ?v1) f1) (forall ((?v2 S11)) (= (f68 (f69 f70 (f14 ?v0 ?v2)) (f14 ?v1 ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S5)) (=> (= (f31 (f32 f33 ?v0) f60) f1) (not (= ?v0 (f5 f6 (f40 (f52 f53 f71) ?v1)))))))
(assert (forall ((?v0 S5) (?v1 S5)) (not (= (f5 f6 (f40 (f52 f53 f71) ?v0)) (f40 f41 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S11) (?v2 S17)) (let ((?v_0 (f15 f59 (f44 (f45 f46 f47) ?v2)))) (=> (= (f18 (f19 f20 (f72 (f73 f74 (f40 f41 ?v0)) ?v1)) ?v_0) f1) (=> (= (f11 (f12 f13 ?v0) f49) f1) (= (f18 (f19 f20 ?v1) ?v_0) f1))))))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S2) (?v3 S11)) (= (= (f72 (f73 f74 ?v0) ?v1) (f72 (f73 f74 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S12)) (let ((?v_0 (f15 f43 ?v2))) (=> (= (f18 (f19 f20 (f72 (f73 f74 ?v0) ?v1)) ?v_0) f1) (=> (=> (= (f18 (f19 f20 ?v1) ?v_0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S12)) (let ((?v_0 (f15 f43 ?v2))) (=> (= (f18 (f19 f20 (f72 (f73 f74 ?v0) ?v1)) ?v_0) f1) (= (f18 (f19 f20 ?v1) ?v_0) f1)))))
(assert (forall ((?v0 S11) (?v1 S12)) (= (= (f18 (f19 f20 ?v0) ?v1) f1) (= (f14 ?v1 ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S6)) (= (= (f11 (f12 f13 ?v0) ?v1) f1) (= (f7 ?v1 ?v0) f1))))
(assert (forall ((?v0 S17) (?v1 S18)) (= (= (f25 (f26 f27 ?v0) ?v1) f1) (= (f21 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f31 (f32 f33 ?v0) ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S12)) (= (f15 f75 ?v0) ?v0)))
(assert (forall ((?v0 S18)) (= (f22 f76 ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f8 f77 ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f28 f61 ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S2)) (not (= (f72 (f73 f74 ?v0) ?v1) (f38 f39 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S11)) (not (= (f38 f39 ?v0) (f72 (f73 f74 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S5)) (not (= (f18 (f19 f20 (f72 (f73 f74 ?v0) ?v1)) (f15 f43 (f54 f55 ?v2))) f1))))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S12)) (let ((?v_0 (f15 f59 ?v2))) (=> (= (f18 (f19 f20 (f72 (f73 f74 ?v0) ?v1)) ?v_0) f1) (=> (= (f18 (f19 f20 (f38 f39 (f5 f6 ?v0))) ?v_0) f1) (= (f18 (f19 f20 ?v1) ?v_0) f1))))))
(assert (forall ((?v0 S5) (?v1 S11) (?v2 S12)) (let ((?v_0 (f40 f41 ?v0)) (?v_1 (f15 f59 ?v2))) (=> (= (f18 (f19 f20 (f72 (f73 f74 ?v_0) ?v1)) ?v_1) f1) (=> (= (f18 (f19 f20 (f38 f39 ?v_0)) ?v_1) f1) (= (f18 (f19 f20 ?v1) ?v_1) f1))))))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S12)) (let ((?v_0 (f15 f59 ?v2))) (=> (= (f18 (f19 f20 (f72 (f73 f74 ?v0) ?v1)) ?v_0) f1) (=> (= (f31 (f32 f33 ?v0) f60) f1) (=> (= (f18 (f19 f20 (f38 f39 ?v0)) ?v_0) f1) (= (f18 (f19 f20 ?v1) ?v_0) f1)))))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (= ?v0 f1) (= ?v1 f1)) (and (= (f68 (f69 f70 ?v0) ?v1) f1) (= (f68 (f69 f70 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (and (= (f31 (f62 f63 ?v0) ?v1) f1) (= (f31 (f62 f63 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (= ?v0 ?v1) (and (= (f25 (f64 f65 ?v0) ?v1) f1) (= (f25 (f64 f65 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= ?v0 ?v1) (and (= (f11 (f66 f67 ?v0) ?v1) f1) (= (f11 (f66 f67 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= ?v0 ?v1) (and (= (f18 (f57 f58 ?v0) ?v1) f1) (= (f18 (f57 f58 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (= ?v0 f1) (= ?v1 f1)) (= (f68 (f69 f70 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f31 (f62 f63 ?v0) ?v1) f1))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= ?v0 ?v1) (= (f25 (f64 f65 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= ?v0 ?v1) (= (f11 (f66 f67 ?v0) ?v1) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= ?v0 ?v1) (= (f18 (f57 f58 ?v0) ?v1) f1))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f68 (f69 f70 ?v0) ?v1) f1) (= (= (f68 (f69 f70 ?v1) ?v0) f1) (= (= ?v1 f1) (= ?v0 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f31 (f62 f63 ?v0) ?v1) f1) (= (= (f31 (f62 f63 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f25 (f64 f65 ?v0) ?v1) f1) (= (= (f25 (f64 f65 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f11 (f66 f67 ?v0) ?v1) f1) (= (= (f11 (f66 f67 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (= (= (f18 (f57 f58 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f68 (f69 f70 ?v1) ?v2) f1) (= (f68 (f69 f70 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= ?v0 ?v1) (=> (= (f31 (f62 f63 ?v1) ?v2) f1) (= (f31 (f62 f63 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= ?v0 ?v1) (=> (= (f25 (f64 f65 ?v1) ?v2) f1) (= (f25 (f64 f65 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= ?v0 ?v1) (=> (= (f11 (f66 f67 ?v1) ?v2) f1) (= (f11 (f66 f67 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= ?v0 ?v1) (=> (= (f18 (f57 f58 ?v1) ?v2) f1) (= (f18 (f57 f58 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f69 f70 ?v2))) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f68 ?v_0 ?v1) f1) (= (f68 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f62 f63 ?v2))) (=> (= ?v0 ?v1) (=> (= (f31 ?v_0 ?v1) f1) (= (f31 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f64 f65 ?v2))) (=> (= ?v0 ?v1) (=> (= (f25 ?v_0 ?v1) f1) (= (f25 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f66 f67 ?v2))) (=> (= ?v0 ?v1) (=> (= (f11 ?v_0 ?v1) f1) (= (f11 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f57 f58 ?v2))) (=> (= ?v0 ?v1) (=> (= (f18 ?v_0 ?v1) f1) (= (f18 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f69 f70 ?v0))) (=> (= (f68 ?v_0 ?v1) f1) (=> (= (= ?v1 f1) (= ?v2 f1)) (= (f68 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f31 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f64 f65 ?v0))) (=> (= (f25 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f25 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f66 f67 ?v0))) (=> (= (f11 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f11 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f57 f58 ?v0))) (=> (= (f18 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f18 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (f68 (f69 f70 ?v0) ?v1) f1) (=> (= (= ?v0 f1) (= ?v2 f1)) (= (f68 (f69 f70 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f31 (f62 f63 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f31 (f62 f63 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f25 (f64 f65 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f25 (f64 f65 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f11 (f66 f67 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f11 (f66 f67 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f18 (f57 f58 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f68 (f69 f70 ?v0) ?v1) f1) (=> (= (f68 (f69 f70 ?v1) ?v0) f1) (= (= ?v0 f1) (= ?v1 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f31 (f62 f63 ?v0) ?v1) f1) (=> (= (f31 (f62 f63 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f25 (f64 f65 ?v0) ?v1) f1) (=> (= (f25 (f64 f65 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f11 (f66 f67 ?v0) ?v1) f1) (=> (= (f11 (f66 f67 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (=> (= (f18 (f57 f58 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f69 f70 ?v0))) (=> (= (f68 ?v_0 ?v1) f1) (=> (= (f68 (f69 f70 ?v1) ?v2) f1) (= (f68 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (=> (= (f31 (f62 f63 ?v1) ?v2) f1) (= (f31 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f64 f65 ?v0))) (=> (= (f25 ?v_0 ?v1) f1) (=> (= (f25 (f64 f65 ?v1) ?v2) f1) (= (f25 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f66 f67 ?v0))) (=> (= (f11 ?v_0 ?v1) f1) (=> (= (f11 (f66 f67 ?v1) ?v2) f1) (= (f11 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f57 f58 ?v0))) (=> (= (f18 ?v_0 ?v1) f1) (=> (= (f18 (f57 f58 ?v1) ?v2) f1) (= (f18 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f68 (f69 f70 ?v0) ?v1) f1) (=> (= (f68 (f69 f70 ?v1) ?v0) f1) (= (= ?v1 f1) (= ?v0 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f31 (f62 f63 ?v0) ?v1) f1) (=> (= (f31 (f62 f63 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f25 (f64 f65 ?v0) ?v1) f1) (=> (= (f25 (f64 f65 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f11 (f66 f67 ?v0) ?v1) f1) (=> (= (f11 (f66 f67 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (=> (= (f18 (f57 f58 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f69 f70 ?v2))) (=> (= (f68 (f69 f70 ?v0) ?v1) f1) (=> (= (f68 ?v_0 ?v0) f1) (= (f68 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f62 f63 ?v2))) (=> (= (f31 (f62 f63 ?v0) ?v1) f1) (=> (= (f31 ?v_0 ?v0) f1) (= (f31 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f64 f65 ?v2))) (=> (= (f25 (f64 f65 ?v0) ?v1) f1) (=> (= (f25 ?v_0 ?v0) f1) (= (f25 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f66 f67 ?v2))) (=> (= (f11 (f66 f67 ?v0) ?v1) f1) (=> (= (f11 ?v_0 ?v0) f1) (= (f11 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f57 f58 ?v2))) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (=> (= (f18 ?v_0 ?v0) f1) (= (f18 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (f31 (f62 f63 ?v0) ?v0) f1)))
(assert (forall ((?v0 S18)) (= (f25 (f64 f65 ?v0) ?v0) f1)))
(assert (forall ((?v0 S6)) (= (f11 (f66 f67 ?v0) ?v0) f1)))
(assert (forall ((?v0 S12)) (= (f18 (f57 f58 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (and (= (f31 (f62 f63 ?v0) ?v1) f1) (= (f31 (f62 f63 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (= ?v0 ?v1) (and (= (f25 (f64 f65 ?v0) ?v1) f1) (= (f25 (f64 f65 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= ?v0 ?v1) (and (= (f11 (f66 f67 ?v0) ?v1) f1) (= (f11 (f66 f67 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= ?v0 ?v1) (and (= (f18 (f57 f58 ?v0) ?v1) f1) (= (f18 (f57 f58 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f31 (f62 f63 ?v0) ?v1) f1))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= ?v0 ?v1) (= (f25 (f64 f65 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= ?v0 ?v1) (= (f11 (f66 f67 ?v0) ?v1) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= ?v0 ?v1) (= (f18 (f57 f58 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f31 (f62 f63 ?v1) ?v0) f1))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= ?v0 ?v1) (= (f25 (f64 f65 ?v1) ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= ?v0 ?v1) (= (f11 (f66 f67 ?v1) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= ?v0 ?v1) (= (f18 (f57 f58 ?v1) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S11)) (let ((?v_0 (f19 f20 ?v2))) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (=> (= (f18 ?v_0 ?v0) f1) (= (f18 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S5)) (let ((?v_0 (f12 f13 ?v2))) (=> (= (f11 (f66 f67 ?v0) ?v1) f1) (=> (= (f11 ?v_0 ?v0) f1) (= (f11 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S17)) (let ((?v_0 (f26 f27 ?v2))) (=> (= (f25 (f64 f65 ?v0) ?v1) f1) (=> (= (f25 ?v_0 ?v0) f1) (= (f25 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f32 f33 ?v2))) (=> (= (f31 (f62 f63 ?v0) ?v1) f1) (=> (= (f31 ?v_0 ?v0) f1) (= (f31 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S12)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f18 ?v_0 ?v1) f1) (=> (= (f18 (f57 f58 ?v1) ?v2) f1) (= (f18 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S6)) (let ((?v_0 (f12 f13 ?v0))) (=> (= (f11 ?v_0 ?v1) f1) (=> (= (f11 (f66 f67 ?v1) ?v2) f1) (= (f11 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S17) (?v1 S18) (?v2 S18)) (let ((?v_0 (f26 f27 ?v0))) (=> (= (f25 ?v_0 ?v1) f1) (=> (= (f25 (f64 f65 ?v1) ?v2) f1) (= (f25 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f32 f33 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (=> (= (f31 (f62 f63 ?v1) ?v2) f1) (= (f31 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S11)) (let ((?v_0 (f19 f20 ?v2))) (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (=> (= (f18 ?v_0 ?v0) f1) (= (f18 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S5)) (let ((?v_0 (f12 f13 ?v2))) (=> (= (f11 (f66 f67 ?v0) ?v1) f1) (=> (= (f11 ?v_0 ?v0) f1) (= (f11 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S17)) (let ((?v_0 (f26 f27 ?v2))) (=> (= (f25 (f64 f65 ?v0) ?v1) f1) (=> (= (f25 ?v_0 ?v0) f1) (= (f25 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f32 f33 ?v2))) (=> (= (f31 (f62 f63 ?v0) ?v1) f1) (=> (= (f31 ?v_0 ?v0) f1) (= (f31 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (=> (= (f31 (f62 f63 ?v1) ?v2) f1) (= (f31 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f64 f65 ?v0))) (=> (= (f25 ?v_0 ?v1) f1) (=> (= (f25 (f64 f65 ?v1) ?v2) f1) (= (f25 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f66 f67 ?v0))) (=> (= (f11 ?v_0 ?v1) f1) (=> (= (f11 (f66 f67 ?v1) ?v2) f1) (= (f11 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f57 f58 ?v0))) (=> (= (f18 ?v_0 ?v1) f1) (=> (= (f18 (f57 f58 ?v1) ?v2) f1) (= (f18 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (=> (=> (= (f31 (f62 f63 ?v0) ?v1) f1) (=> (= (f31 (f62 f63 ?v1) ?v0) f1) false)) false))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= ?v0 ?v1) (=> (=> (= (f25 (f64 f65 ?v0) ?v1) f1) (=> (= (f25 (f64 f65 ?v1) ?v0) f1) false)) false))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= ?v0 ?v1) (=> (=> (= (f11 (f66 f67 ?v0) ?v1) f1) (=> (= (f11 (f66 f67 ?v1) ?v0) f1) false)) false))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= ?v0 ?v1) (=> (=> (= (f18 (f57 f58 ?v0) ?v1) f1) (=> (= (f18 (f57 f58 ?v1) ?v0) f1) false)) false))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (forall ((?v2 S11)) (let ((?v_0 (f19 f20 ?v2))) (=> (= (f18 ?v_0 ?v0) f1) (= (f18 ?v_0 ?v1) f1)))) (= (f18 (f57 f58 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (forall ((?v2 S5)) (let ((?v_0 (f12 f13 ?v2))) (=> (= (f11 ?v_0 ?v0) f1) (= (f11 ?v_0 ?v1) f1)))) (= (f11 (f66 f67 ?v0) ?v1) f1))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (forall ((?v2 S17)) (let ((?v_0 (f26 f27 ?v2))) (=> (= (f25 ?v_0 ?v0) f1) (= (f25 ?v_0 ?v1) f1)))) (= (f25 (f64 f65 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S2)) (let ((?v_0 (f32 f33 ?v2))) (=> (= (f31 ?v_0 ?v0) f1) (= (f31 ?v_0 ?v1) f1)))) (= (f31 (f62 f63 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S2)) (= (f68 (f69 f70 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1)) (= (f31 (f62 f63 ?v0) ?v1) f1))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (forall ((?v2 S17)) (= (f68 (f69 f70 (f21 ?v0 ?v2)) (f21 ?v1 ?v2)) f1)) (= (f25 (f64 f65 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (forall ((?v2 S5)) (= (f68 (f69 f70 (f7 ?v0 ?v2)) (f7 ?v1 ?v2)) f1)) (= (f11 (f66 f67 ?v0) ?v1) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (forall ((?v2 S11)) (= (f68 (f69 f70 (f14 ?v0 ?v2)) (f14 ?v1 ?v2)) f1)) (= (f18 (f57 f58 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S12) (?v2 S11)) (let ((?v_0 (f16 f78 (f72 (f73 f74 ?v0) ?v2)))) (=> (= (f18 (f19 f20 (f38 f39 (f5 f6 ?v0))) (f15 f59 ?v1)) f1) (= (f18 (f57 f58 (f15 ?v_0 (f15 f59 (f15 (f16 f78 ?v2) ?v1)))) (f15 f59 (f15 ?v_0 ?v1))) f1)))))
(assert (forall ((?v0 S2) (?v1 S12) (?v2 S11)) (let ((?v_0 (f16 f78 (f72 (f73 f74 ?v0) ?v2)))) (=> (= (f18 (f19 f20 (f38 f39 (f5 f6 ?v0))) (f15 f59 ?v1)) f1) (= (f18 (f57 f58 (f15 f59 (f15 ?v_0 ?v1))) (f15 ?v_0 (f15 f59 (f15 (f16 f78 ?v2) ?v1)))) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S6)) (let ((?v_0 (f12 f13 ?v0))) (=> (= (f11 ?v_0 (f8 (f9 f79 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f11 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S18)) (let ((?v_0 (f26 f27 ?v0))) (=> (= (f25 ?v_0 (f22 (f23 f80 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f25 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f32 f33 ?v0))) (=> (= (f31 ?v_0 (f28 (f29 f81 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f31 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f18 ?v_0 (f15 (f16 f78 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f18 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (let ((?v_0 (f12 f13 ?v0))) (=> (=> (not (= (f11 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f11 ?v_0 (f8 (f9 f79 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S17) (?v1 S18) (?v2 S17)) (let ((?v_0 (f26 f27 ?v0))) (=> (=> (not (= (f25 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f25 ?v_0 (f22 (f23 f80 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f32 f33 ?v0))) (=> (=> (not (= (f31 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f31 ?v_0 (f28 (f29 f81 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11)) (let ((?v_0 (f19 f20 ?v0))) (=> (=> (not (= (f18 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f18 ?v_0 (f15 (f16 f78 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (= (f11 (f12 f13 ?v0) (f8 (f9 f79 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S17) (?v1 S18)) (= (f25 (f26 f27 ?v0) (f22 (f23 f80 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f31 (f32 f33 ?v0) (f28 (f29 f81 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S11) (?v1 S12)) (= (f18 (f19 f20 ?v0) (f15 (f16 f78 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S5) (?v1 S6)) (= (f8 (f9 f79 ?v0) ?v1) (f8 f77 (f8 (f9 f10 ?v0) ?v1)))))
(assert (forall ((?v0 S17) (?v1 S18)) (= (f22 (f23 f80 ?v0) ?v1) (f22 f76 (f22 (f23 f24 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f28 (f29 f81 ?v0) ?v1) (f28 f61 (f28 (f29 f30 ?v0) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S12)) (= (f15 (f16 f78 ?v0) ?v1) (f15 f75 (f15 (f16 f17 ?v0) ?v1)))))
(assert (forall ((?v0 S17) (?v1 S18)) (= (f22 (f23 f80 ?v0) (f22 f76 ?v1)) (f22 f76 (f22 (f23 f36 ?v0) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (= (f8 (f9 f79 ?v0) (f8 f77 ?v1)) (f8 f77 (f8 (f9 f34 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f28 (f29 f81 ?v0) (f28 f61 ?v1)) (f28 f61 (f28 (f29 f37 ?v0) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S12)) (= (f15 (f16 f78 ?v0) (f15 f75 ?v1)) (f15 f75 (f15 (f16 f35 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f29 f81 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S17) (?v1 S18)) (let ((?v_0 (f23 f80 ?v0))) (let ((?v_1 (f22 ?v_0 ?v1))) (= (f22 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (let ((?v_0 (f9 f79 ?v0))) (let ((?v_1 (f8 ?v_0 ?v1))) (= (f8 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S11) (?v1 S12)) (let ((?v_0 (f16 f78 ?v0))) (let ((?v_1 (f15 ?v_0 ?v1))) (= (f15 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f29 f81 ?v0)) (?v_0 (f29 f81 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S18)) (let ((?v_1 (f23 f80 ?v0)) (?v_0 (f23 f80 ?v1))) (= (f22 ?v_1 (f22 ?v_0 ?v2)) (f22 ?v_0 (f22 ?v_1 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S6)) (let ((?v_1 (f9 f79 ?v0)) (?v_0 (f9 f79 ?v1))) (= (f8 ?v_1 (f8 ?v_0 ?v2)) (f8 ?v_0 (f8 ?v_1 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (let ((?v_1 (f16 f78 ?v0)) (?v_0 (f16 f78 ?v1))) (= (f15 ?v_1 (f15 ?v_0 ?v2)) (f15 ?v_0 (f15 ?v_1 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S6)) (let ((?v_0 (f12 f13 ?v0))) (= (= (f11 ?v_0 (f8 (f9 f79 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f11 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S18)) (let ((?v_0 (f26 f27 ?v0))) (= (= (f25 ?v_0 (f22 (f23 f80 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f25 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f32 f33 ?v0))) (= (= (f31 ?v_0 (f28 (f29 f81 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f31 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (let ((?v_0 (f19 f20 ?v0))) (= (= (f18 ?v_0 (f15 (f16 f78 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f18 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f28 (f29 f81 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S17) (?v1 S18) (?v2 S17)) (= (= (f21 (f22 (f23 f80 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f21 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f7 (f8 (f9 f79 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f7 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11)) (= (= (f14 (f15 (f16 f78 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f14 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S6)) (let ((?v_0 (f12 f13 ?v0)) (?v_1 (f9 f79 ?v0))) (=> (not (= (f11 ?v_0 ?v1) f1)) (=> (not (= (f11 ?v_0 ?v2) f1)) (= (= (f8 ?v_1 ?v1) (f8 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S17) (?v1 S18) (?v2 S18)) (let ((?v_0 (f26 f27 ?v0)) (?v_1 (f23 f80 ?v0))) (=> (not (= (f25 ?v_0 ?v1) f1)) (=> (not (= (f25 ?v_0 ?v2) f1)) (= (= (f22 ?v_1 ?v1) (f22 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f32 f33 ?v0)) (?v_1 (f29 f81 ?v0))) (=> (not (= (f31 ?v_0 ?v1) f1)) (=> (not (= (f31 ?v_0 ?v2) f1)) (= (= (f28 ?v_1 ?v1) (f28 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S12)) (let ((?v_0 (f19 f20 ?v0)) (?v_1 (f16 f78 ?v0))) (=> (not (= (f18 ?v_0 ?v1) f1)) (=> (not (= (f18 ?v_0 ?v2) f1)) (= (= (f15 ?v_1 ?v1) (f15 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (let ((?v_0 (f12 f13 ?v0))) (=> (= (f11 ?v_0 ?v1) f1) (= (f11 ?v_0 (f8 (f9 f79 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S17) (?v1 S18) (?v2 S17)) (let ((?v_0 (f26 f27 ?v0))) (=> (= (f25 ?v_0 ?v1) f1) (= (f25 ?v_0 (f22 (f23 f80 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f32 f33 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (= (f31 ?v_0 (f28 (f29 f81 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f18 ?v_0 ?v1) f1) (= (f18 ?v_0 (f15 (f16 f78 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f11 (f12 f13 ?v0) ?v1) f1) (= (f8 (f9 f79 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S17) (?v1 S18)) (=> (= (f25 (f26 f27 ?v0) ?v1) f1) (= (f22 (f23 f80 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (= (f28 (f29 f81 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S11) (?v1 S12)) (=> (= (f18 (f19 f20 ?v0) ?v1) f1) (= (f15 (f16 f78 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f31 (f62 f63 ?v0) (f28 (f29 f81 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S18) (?v1 S17)) (= (f25 (f64 f65 ?v0) (f22 (f23 f80 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S6) (?v1 S5)) (= (f11 (f66 f67 ?v0) (f8 (f9 f79 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S12) (?v1 S11)) (= (f18 (f57 f58 ?v0) (f15 (f16 f78 ?v1) ?v0)) f1)))
(check-sat)
(exit)