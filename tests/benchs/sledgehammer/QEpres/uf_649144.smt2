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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S4 S3) S1)
(declare-fun f6 (S5 S2) S4)
(declare-fun f7 () S5)
(declare-fun f8 (S6 S7) S3)
(declare-fun f9 () S6)
(declare-fun f10 () S7)
(declare-fun f11 (S8 S9) S3)
(declare-fun f12 (S10 S9) S8)
(declare-fun f13 (S11 S12) S10)
(declare-fun f14 () S11)
(declare-fun f15 () S12)
(declare-fun f16 () S9)
(declare-fun f17 () S3)
(declare-fun f18 () S12)
(declare-fun f19 () S3)
(declare-fun f20 () S12)
(declare-fun f21 () S9)
(declare-fun f22 (S12 S13) S14)
(declare-fun f23 (S15 S12) S14)
(declare-fun f24 (S16 S1) S15)
(declare-fun f25 () S16)
(declare-fun f26 () S12)
(declare-fun f27 () S12)
(declare-fun f28 (S17 S3) S3)
(declare-fun f29 () S17)
(declare-fun f30 (S14 S18) S1)
(declare-fun f31 (S19 S13) S1)
(declare-fun f32 (S20 S13) S19)
(declare-fun f33 () S20)
(declare-fun f34 () S13)
(declare-fun f35 (S21 S3) S17)
(declare-fun f36 () S21)
(declare-fun f37 () S21)
(declare-fun f38 (S9 S13) S12)
(declare-fun f39 () S21)
(declare-fun f40 () S17)
(declare-fun f41 (S22 S2) S13)
(declare-fun f42 () S22)
(declare-fun f43 (S23 S1) S1)
(declare-fun f44 (S24 S1) S23)
(declare-fun f45 () S24)
(declare-fun f46 (S25 S13) S13)
(declare-fun f47 (S26 S13) S25)
(declare-fun f48 () S26)
(declare-fun f49 (S27 S3) S4)
(declare-fun f50 () S27)
(declare-fun f51 () S24)
(declare-fun f52 (S28 S1) S13)
(declare-fun f53 (S29 S3) S13)
(declare-fun f54 (S30 S13) S3)
(declare-fun f55 () S25)
(declare-fun f56 () S25)
(declare-fun f57 (S31 S19) S1)
(declare-fun f58 () S31)
(declare-fun f59 (S32 S30) S1)
(declare-fun f60 () S32)
(declare-fun f61 (S33 S28) S1)
(declare-fun f62 () S33)
(declare-fun f63 (S34 S29) S1)
(declare-fun f64 () S34)
(declare-fun f65 () S13)
(declare-fun f66 () S25)
(declare-fun f67 () S26)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (and (= (f5 (f6 f7 ?v0) (f8 f9 f10)) f1) (= (f3 (f11 (f12 (f13 f14 f15) f16) f16) ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f17 ?v0) f1) (and (= (f5 (f6 f7 ?v0) (f8 f9 f10)) f1) (= (f3 (f11 (f12 (f13 f14 f18) f16) f16) ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f19 ?v0) f1) (and (= (f5 (f6 f7 ?v0) (f8 f9 f10)) f1) (= (f3 (f11 (f12 (f13 f14 f20) f21) f21) ?v0) f1)))))
(assert (forall ((?v0 S13)) (= (f22 f15 ?v0) (f23 (f24 f25 f2) f26))))
(assert (forall ((?v0 S13)) (= (f22 f18 ?v0) (f23 (f24 f25 f2) f27))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (= (f3 (f28 f29 ?v0) ?v1) f1) (= (f5 (f6 f7 ?v1) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S18)) (= (= (f30 (f22 f26 ?v0) ?v1) f1) (= (f31 (f32 f33 ?v0) f34) f1))))
(assert (forall ((?v0 S13) (?v1 S18)) (= (= (f30 (f22 f27 ?v0) ?v1) f1) (= (f31 (f32 f33 f34) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f6 f7 ?v2))) (= (= (f3 (f28 (f35 f36 ?v0) ?v1) ?v2) f1) (or (= (f5 ?v_0 ?v0) f1) (= (f5 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (= (= (f3 (f28 (f35 f37 ?v0) ?v1) ?v2) f1) (or (= (f3 ?v0 ?v2) f1) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S18)) (= (= (f30 (f22 (f38 f16 ?v0) ?v1) ?v2) f1) false)))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S18)) (= (= (f30 (f22 (f38 f21 ?v0) ?v1) ?v2) f1) true)))
(assert (forall ((?v0 S13) (?v1 S18)) (= (= (f30 (f22 f20 ?v0) ?v1) f1) false)))
(assert (not (= (f8 f9 f10) (f28 (f35 f39 (f28 (f35 f39 (f28 f40 f19)) (f28 f40 f17))) (f28 f40 f4)))))
(assert (forall ((?v0 S2)) (=> (= (f5 (f6 f7 ?v0) (f8 f9 f10)) f1) (not (= (f41 f42 ?v0) f34)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f5 ?v_0 (f28 (f35 f39 ?v1) ?v2)) f1) (=> (=> (= (f5 ?v_0 ?v1) f1) false) (=> (=> (= (f5 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f3 (f28 (f35 f39 ?v0) ?v1) ?v2) f1) (=> (=> (= (f3 ?v0 ?v2) f1) false) (=> (=> (= (f3 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (=> (=> (not (= (f3 ?v0 ?v1) f1)) (= (f3 ?v2 ?v1) f1)) (= (f3 (f28 (f35 f39 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v0))) (=> (=> (not (= (f5 ?v_0 ?v1) f1)) (= (f5 ?v_0 ?v2) f1)) (= (f5 ?v_0 (f28 (f35 f39 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (= (= (f3 (f28 (f35 f39 ?v0) ?v1) ?v2) f1) (= (f43 (f44 f45 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (= (= (f3 (f28 (f35 f39 ?v0) ?v1) ?v2) f1) (= (f43 (f44 f45 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f32 f33 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (= (f31 ?v_0 (f46 (f47 f48 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f49 f50 ?v0))) (=> (= (f5 ?v_0 ?v1) f1) (= (f5 ?v_0 (f28 (f35 f39 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f44 f51 ?v0))) (=> (= (f43 ?v_0 ?v1) f1) (= (f43 ?v_0 (f43 (f44 f45 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f32 f33 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (= (f31 ?v_0 (f46 (f47 f48 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f49 f50 ?v0))) (=> (= (f5 ?v_0 ?v1) f1) (= (f5 ?v_0 (f28 (f35 f39 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f44 f51 ?v0))) (=> (= (f43 ?v_0 ?v1) f1) (= (f43 ?v_0 (f43 (f44 f45 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f28 f40 (f28 (f35 f37 ?v0) ?v1)) (f28 (f35 f39 (f28 f40 ?v0)) (f28 f40 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (= (= (f3 (f28 (f35 f39 (f28 f29 ?v0)) (f28 f29 ?v1)) ?v2) f1) (= (f5 (f6 f7 ?v2) (f28 (f35 f39 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S3)) (= (f28 (f35 f39 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f28 (f35 f39 ?v0) ?v1) (f28 f40 (f28 (f35 f36 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f35 f39 ?v0))) (= (f28 (f35 f39 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f35 f39 ?v1) ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f44 f45 ?v0))) (= (= (f43 (f44 f45 (f43 ?v_0 ?v1)) ?v2) f1) (= (f43 ?v_0 (f43 (f44 f45 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f47 f48 ?v0))) (= (f46 (f47 f48 (f46 ?v_0 ?v1)) ?v2) (f46 ?v_0 (f46 (f47 f48 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f35 f39 ?v0))) (= (f28 (f35 f39 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f35 f39 ?v1) ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f44 f45 ?v0))) (= (= (f43 (f44 f45 (f43 ?v_0 ?v1)) ?v2) f1) (= (f43 ?v_0 (f43 (f44 f45 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f47 f48 ?v0))) (= (f46 (f47 f48 (f46 ?v_0 ?v1)) ?v2) (f46 ?v_0 (f46 (f47 f48 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f35 f39 ?v0))) (= (f28 (f35 f39 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f35 f39 ?v1) ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f44 f45 ?v0))) (= (= (f43 (f44 f45 (f43 ?v_0 ?v1)) ?v2) f1) (= (f43 ?v_0 (f43 (f44 f45 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f47 f48 ?v0))) (= (f46 (f47 f48 (f46 ?v_0 ?v1)) ?v2) (f46 ?v_0 (f46 (f47 f48 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f35 f39 ?v0)) (?v_0 (f35 f39 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_1 (f44 f45 ?v0)) (?v_0 (f44 f45 ?v1))) (= (= (f43 ?v_1 (f43 ?v_0 ?v2)) f1) (= (f43 ?v_0 (f43 ?v_1 ?v2)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_1 (f47 f48 ?v0)) (?v_0 (f47 f48 ?v1))) (= (f46 ?v_1 (f46 ?v_0 ?v2)) (f46 ?v_0 (f46 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f35 f39 ?v0)) (?v_0 (f35 f39 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_1 (f44 f45 ?v0)) (?v_0 (f44 f45 ?v1))) (= (= (f43 ?v_1 (f43 ?v_0 ?v2)) f1) (= (f43 ?v_0 (f43 ?v_1 ?v2)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_1 (f47 f48 ?v0)) (?v_0 (f47 f48 ?v1))) (= (f46 ?v_1 (f46 ?v_0 ?v2)) (f46 ?v_0 (f46 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f35 f39 ?v0)) (?v_0 (f35 f39 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_1 (f44 f45 ?v0)) (?v_0 (f44 f45 ?v1))) (= (= (f43 ?v_1 (f43 ?v_0 ?v2)) f1) (= (f43 ?v_0 (f43 ?v_1 ?v2)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_1 (f47 f48 ?v0)) (?v_0 (f47 f48 ?v1))) (= (f46 ?v_1 (f46 ?v_0 ?v2)) (f46 ?v_0 (f46 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f35 f39 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (let ((?v_0 (f44 f45 ?v0))) (let ((?v_1 (f43 ?v_0 ?v1))) (= (= (f43 ?v_0 ?v_1) f1) (= ?v_1 f1))))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f47 f48 ?v0))) (let ((?v_1 (f46 ?v_0 ?v1))) (= (f46 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f35 f39 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (let ((?v_0 (f44 f45 ?v0))) (let ((?v_1 (f43 ?v_0 ?v1))) (= (= (f43 ?v_0 ?v_1) f1) (= ?v_1 f1))))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f47 f48 ?v0))) (let ((?v_1 (f46 ?v_0 ?v1))) (= (f46 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f35 f39 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (let ((?v_0 (f44 f45 ?v0))) (let ((?v_1 (f43 ?v_0 ?v1))) (= (= (f43 ?v_0 ?v_1) f1) (= ?v_1 f1))))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f47 f48 ?v0))) (let ((?v_1 (f46 ?v_0 ?v1))) (= (f46 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f28 (f35 f39 ?v0) ?v1) (f28 (f35 f39 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f43 (f44 f45 ?v0) ?v1) f1) (= (f43 (f44 f45 ?v1) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 f48 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f28 (f35 f39 ?v0) ?v1) (f28 (f35 f39 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f43 (f44 f45 ?v0) ?v1) f1) (= (f43 (f44 f45 ?v1) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 f48 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f28 (f35 f39 ?v0) ?v1) (f28 (f35 f39 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f43 (f44 f45 ?v0) ?v1) f1) (= (f43 (f44 f45 ?v1) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 f48 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (= (f28 (f35 f39 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S1)) (= (= (f43 (f44 f45 ?v0) ?v0) f1) (= ?v0 f1))))
(assert (forall ((?v0 S13)) (= (f46 (f47 f48 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f28 (f35 f39 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S1)) (= (= (f43 (f44 f45 ?v0) ?v0) f1) (= ?v0 f1))))
(assert (forall ((?v0 S13)) (= (f46 (f47 f48 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f5 ?v_0 ?v1) f1) (= (f5 ?v_0 (f28 (f35 f39 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f5 ?v_0 ?v1) f1) (= (f5 ?v_0 (f28 (f35 f39 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (=> (= (f3 ?v0 ?v1) f1) (= (f3 (f28 (f35 f39 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (=> (= (f3 ?v0 ?v1) f1) (= (f3 (f28 (f35 f39 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (forall ((?v3 S2)) (=> (= (f5 (f6 f7 ?v3) (f28 (f35 f39 ?v0) ?v1)) f1) (= (f3 ?v2 ?v3) f1))) (and (forall ((?v3 S2)) (=> (= (f5 (f6 f7 ?v3) ?v0) f1) (= (f3 ?v2 ?v3) f1))) (forall ((?v3 S2)) (=> (= (f5 (f6 f7 ?v3) ?v1) f1) (= (f3 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (exists ((?v3 S2)) (and (= (f5 (f6 f7 ?v3) (f28 (f35 f39 ?v0) ?v1)) f1) (= (f3 ?v2 ?v3) f1))) (or (exists ((?v3 S2)) (and (= (f5 (f6 f7 ?v3) ?v0) f1) (= (f3 ?v2 ?v3) f1))) (exists ((?v3 S2)) (and (= (f5 (f6 f7 ?v3) ?v1) f1) (= (f3 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f35 f39 ?v0))) (= (f28 (f35 f39 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f35 f39 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v0))) (= (= (f5 ?v_0 (f28 (f35 f39 ?v1) ?v2)) f1) (or (= (f5 ?v_0 ?v1) f1) (= (f5 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f35 f39 ?v0)) (?v_0 (f35 f39 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f35 f39 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f28 (f35 f39 ?v0) ?v1) (f28 (f35 f39 ?v1) ?v0))))
(assert (forall ((?v0 S13) (?v1 S13)) (or (= (f31 (f32 f33 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f31 (f32 f33 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (f28 (f35 f39 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S1)) (= (= (f43 (f44 f45 ?v0) ?v0) f1) (= ?v0 f1))))
(assert (forall ((?v0 S13)) (= (f46 (f47 f48 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (=> (= (f31 (f32 f33 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f31 (f32 f33 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (=> (=> (not false) (= (f31 (f32 f33 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (=> (=> (not false) (= (f43 (f44 f51 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (=> (=> (not false) (= (f5 (f49 f50 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f32 f33 ?v2))) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (=> (= (f31 ?v_0 ?v0) f1) (= (f31 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f44 f51 ?v2))) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (=> (= (f43 ?v_0 ?v0) f1) (= (f43 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f49 f50 ?v2))) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (=> (= (f5 ?v_0 ?v0) f1) (= (f5 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f32 f33 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (=> (= (f31 (f32 f33 ?v1) ?v2) f1) (= (f31 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f44 f51 ?v0))) (=> (= (f43 ?v_0 ?v1) f1) (=> (= (f43 (f44 f51 ?v1) ?v2) f1) (= (f43 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f49 f50 ?v0))) (=> (= (f5 ?v_0 ?v1) f1) (=> (= (f5 (f49 f50 ?v1) ?v2) f1) (= (f5 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f31 (f32 f33 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (=> (= (= ?v0 f1) (= ?v2 f1)) (= (f43 (f44 f51 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f5 (f49 f50 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f32 f33 ?v0))) (=> (= (f31 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f31 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f44 f51 ?v0))) (=> (= (f43 ?v_0 ?v1) f1) (=> (= (= ?v1 f1) (= ?v2 f1)) (= (f43 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f49 f50 ?v0))) (=> (= (f5 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f5 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f32 f33 ?v2))) (=> (= ?v0 ?v1) (=> (= (f31 ?v_0 ?v1) f1) (= (f31 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f44 f51 ?v2))) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f43 ?v_0 ?v1) f1) (= (f43 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f49 f50 ?v2))) (=> (= ?v0 ?v1) (=> (= (f5 ?v_0 ?v1) f1) (= (f5 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= ?v0 ?v1) (=> (= (f31 (f32 f33 ?v1) ?v2) f1) (= (f31 (f32 f33 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f43 (f44 f51 ?v1) ?v2) f1) (= (f43 (f44 f51 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= ?v0 ?v1) (=> (= (f5 (f49 f50 ?v1) ?v2) f1) (= (f5 (f49 f50 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (=> (= (f31 (f32 f33 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (=> (= (f43 (f44 f51 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (=> (= (f5 (f49 f50 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S13)) (not (= (f31 (f32 f33 ?v0) ?v0) f1))))
(assert (forall ((?v0 S1)) (not (= (f43 (f44 f51 ?v0) ?v0) f1))))
(assert (forall ((?v0 S3)) (not (= (f5 (f49 f50 ?v0) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (not (= ?v0 ?v1)) (or (= (f31 (f32 f33 ?v0) ?v1) f1) (= (f31 (f32 f33 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (not (= (f31 (f32 f33 ?v0) ?v1) f1)) (or (= (f31 (f32 f33 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (or (= (f31 (f32 f33 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f31 (f32 f33 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (not (= (f31 (f32 f33 ?v0) ?v1) f1)) (= (not (= (f31 (f32 f33 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f31 (f32 f33 ?v0) ?v1) f1) false) (=> (=> (= (f31 (f32 f33 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (not (= (= ?v0 f1) (= ?v1 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (not (= (f31 (f32 f33 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (not (= (f43 (f44 f51 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (not (= (f5 (f49 f50 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (= (not (= (f31 (f32 f33 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (= (not (= (f43 (f44 f51 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (= (not (= (f5 (f49 f50 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (= (= (= ?v0 f1) (= ?v1 f1)) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (= (= (= ?v1 f1) (= ?v0 f1)) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S1)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (= (=> (= (f31 (f32 f33 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (= (=> (= (f43 (f44 f51 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S1)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (= (=> (= (f5 (f49 f50 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (=> (= (f31 (f32 f33 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (=> (= (f43 (f44 f51 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (=> (= (f5 (f49 f50 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S13) (?v3 S28)) (let ((?v_0 (f32 f33 ?v2))) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (=> (= (f31 ?v_0 (f52 ?v3 ?v0)) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f43 (f44 f51 ?v5) ?v4) f1) (= (f31 (f32 f33 (f52 ?v3 ?v5)) (f52 ?v3 ?v4)) f1))) (= (f31 ?v_0 (f52 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S13) (?v3 S29)) (let ((?v_0 (f32 f33 ?v2))) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (=> (= (f31 ?v_0 (f53 ?v3 ?v0)) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f5 (f49 f50 ?v5) ?v4) f1) (= (f31 (f32 f33 (f53 ?v3 ?v5)) (f53 ?v3 ?v4)) f1))) (= (f31 ?v_0 (f53 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S1) (?v3 S19)) (let ((?v_0 (f44 f51 ?v2))) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (=> (= (f43 ?v_0 (f31 ?v3 ?v0)) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v5) ?v4) f1) (= (f43 (f44 f51 (f31 ?v3 ?v5)) (f31 ?v3 ?v4)) f1))) (= (f43 ?v_0 (f31 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S3) (?v3 S30)) (let ((?v_0 (f49 f50 ?v2))) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (=> (= (f5 ?v_0 (f54 ?v3 ?v0)) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v5) ?v4) f1) (= (f5 (f49 f50 (f54 ?v3 ?v5)) (f54 ?v3 ?v4)) f1))) (= (f5 ?v_0 (f54 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S25) (?v3 S13)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (=> (= (f46 ?v2 ?v0) ?v3) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v5) ?v4) f1) (= (f31 (f32 f33 (f46 ?v2 ?v5)) (f46 ?v2 ?v4)) f1))) (= (f31 (f32 f33 ?v3) (f46 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S23) (?v3 S1)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (=> (= (= (f43 ?v2 ?v0) f1) (= ?v3 f1)) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f43 (f44 f51 ?v5) ?v4) f1) (= (f43 (f44 f51 (f43 ?v2 ?v5)) (f43 ?v2 ?v4)) f1))) (= (f43 (f44 f51 ?v3) (f43 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S17) (?v3 S3)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (=> (= (f28 ?v2 ?v0) ?v3) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f5 (f49 f50 ?v5) ?v4) f1) (= (f5 (f49 f50 (f28 ?v2 ?v5)) (f28 ?v2 ?v4)) f1))) (= (f5 (f49 f50 ?v3) (f28 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S28) (?v3 S13)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (=> (= (f52 ?v2 ?v1) ?v3) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f43 (f44 f51 ?v4) ?v5) f1) (= (f31 (f32 f33 (f52 ?v2 ?v4)) (f52 ?v2 ?v5)) f1))) (= (f31 (f32 f33 (f52 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S29) (?v3 S13)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (=> (= (f53 ?v2 ?v1) ?v3) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f5 (f49 f50 ?v4) ?v5) f1) (= (f31 (f32 f33 (f53 ?v2 ?v4)) (f53 ?v2 ?v5)) f1))) (= (f31 (f32 f33 (f53 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S19) (?v3 S1)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (=> (= (= (f31 ?v2 ?v1) f1) (= ?v3 f1)) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v4) ?v5) f1) (= (f43 (f44 f51 (f31 ?v2 ?v4)) (f31 ?v2 ?v5)) f1))) (= (f43 (f44 f51 (f31 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S30) (?v3 S3)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (=> (= (f54 ?v2 ?v1) ?v3) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v4) ?v5) f1) (= (f5 (f49 f50 (f54 ?v2 ?v4)) (f54 ?v2 ?v5)) f1))) (= (f5 (f49 f50 (f54 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S28) (?v3 S13)) (=> (= (f43 (f44 f51 ?v0) ?v1) f1) (=> (= (f31 (f32 f33 (f52 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f43 (f44 f51 ?v4) ?v5) f1) (= (f31 (f32 f33 (f52 ?v2 ?v4)) (f52 ?v2 ?v5)) f1))) (= (f31 (f32 f33 (f52 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S29) (?v3 S13)) (=> (= (f5 (f49 f50 ?v0) ?v1) f1) (=> (= (f31 (f32 f33 (f53 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f5 (f49 f50 ?v4) ?v5) f1) (= (f31 (f32 f33 (f53 ?v2 ?v4)) (f53 ?v2 ?v5)) f1))) (= (f31 (f32 f33 (f53 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S19) (?v3 S1)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (=> (= (f43 (f44 f51 (f31 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v4) ?v5) f1) (= (f43 (f44 f51 (f31 ?v2 ?v4)) (f31 ?v2 ?v5)) f1))) (= (f43 (f44 f51 (f31 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S30) (?v3 S3)) (=> (= (f31 (f32 f33 ?v0) ?v1) f1) (=> (= (f5 (f49 f50 (f54 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v4) ?v5) f1) (= (f5 (f49 f50 (f54 ?v2 ?v4)) (f54 ?v2 ?v5)) f1))) (= (f5 (f49 f50 (f54 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S13) (?v1 S28) (?v2 S1) (?v3 S1)) (=> (= ?v0 (f52 ?v1 ?v2)) (=> (= (f43 (f44 f51 ?v2) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f43 (f44 f51 ?v4) ?v5) f1) (= (f31 (f32 f33 (f52 ?v1 ?v4)) (f52 ?v1 ?v5)) f1))) (= (f31 (f32 f33 ?v0) (f52 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S13) (?v1 S29) (?v2 S3) (?v3 S3)) (=> (= ?v0 (f53 ?v1 ?v2)) (=> (= (f5 (f49 f50 ?v2) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f5 (f49 f50 ?v4) ?v5) f1) (= (f31 (f32 f33 (f53 ?v1 ?v4)) (f53 ?v1 ?v5)) f1))) (= (f31 (f32 f33 ?v0) (f53 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S1) (?v1 S19) (?v2 S13) (?v3 S13)) (=> (= (= ?v0 f1) (= (f31 ?v1 ?v2) f1)) (=> (= (f31 (f32 f33 ?v2) ?v3) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v4) ?v5) f1) (= (f43 (f44 f51 (f31 ?v1 ?v4)) (f31 ?v1 ?v5)) f1))) (= (f43 (f44 f51 ?v0) (f31 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S3) (?v1 S30) (?v2 S13) (?v3 S13)) (=> (= ?v0 (f54 ?v1 ?v2)) (=> (= (f31 (f32 f33 ?v2) ?v3) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v4) ?v5) f1) (= (f5 (f49 f50 (f54 ?v1 ?v4)) (f54 ?v1 ?v5)) f1))) (= (f5 (f49 f50 ?v0) (f54 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S19) (?v1 S13) (?v2 S1) (?v3 S13)) (=> (= (f43 (f44 f51 (f31 ?v0 ?v1)) ?v2) f1) (=> (= (f31 (f32 f33 ?v3) ?v1) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v5) ?v4) f1) (= (f43 (f44 f51 (f31 ?v0 ?v5)) (f31 ?v0 ?v4)) f1))) (= (f43 (f44 f51 (f31 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S30) (?v1 S13) (?v2 S3) (?v3 S13)) (=> (= (f5 (f49 f50 (f54 ?v0 ?v1)) ?v2) f1) (=> (= (f31 (f32 f33 ?v3) ?v1) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v5) ?v4) f1) (= (f5 (f49 f50 (f54 ?v0 ?v5)) (f54 ?v0 ?v4)) f1))) (= (f5 (f49 f50 (f54 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S28) (?v1 S1) (?v2 S13) (?v3 S1)) (=> (= (f31 (f32 f33 (f52 ?v0 ?v1)) ?v2) f1) (=> (= (f43 (f44 f51 ?v3) ?v1) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f43 (f44 f51 ?v5) ?v4) f1) (= (f31 (f32 f33 (f52 ?v0 ?v5)) (f52 ?v0 ?v4)) f1))) (= (f31 (f32 f33 (f52 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S29) (?v1 S3) (?v2 S13) (?v3 S3)) (=> (= (f31 (f32 f33 (f53 ?v0 ?v1)) ?v2) f1) (=> (= (f5 (f49 f50 ?v3) ?v1) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f5 (f49 f50 ?v5) ?v4) f1) (= (f31 (f32 f33 (f53 ?v0 ?v5)) (f53 ?v0 ?v4)) f1))) (= (f31 (f32 f33 (f53 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S25) (?v2 S13) (?v3 S13)) (=> (= ?v0 (f46 ?v1 ?v2)) (=> (= (f31 (f32 f33 ?v3) ?v2) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v5) ?v4) f1) (= (f31 (f32 f33 (f46 ?v1 ?v5)) (f46 ?v1 ?v4)) f1))) (= (f31 (f32 f33 (f46 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S1) (?v1 S23) (?v2 S1) (?v3 S1)) (=> (= (= ?v0 f1) (= (f43 ?v1 ?v2) f1)) (=> (= (f43 (f44 f51 ?v3) ?v2) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f43 (f44 f51 ?v5) ?v4) f1) (= (f43 (f44 f51 (f43 ?v1 ?v5)) (f43 ?v1 ?v4)) f1))) (= (f43 (f44 f51 (f43 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S17) (?v2 S3) (?v3 S3)) (=> (= ?v0 (f28 ?v1 ?v2)) (=> (= (f5 (f49 f50 ?v3) ?v2) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f5 (f49 f50 ?v5) ?v4) f1) (= (f5 (f49 f50 (f28 ?v1 ?v5)) (f28 ?v1 ?v4)) f1))) (= (f5 (f49 f50 (f28 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S1) (?v1 S19) (?v2 S13) (?v3 S13)) (let ((?v_0 (f44 f51 ?v0))) (=> (= (f43 ?v_0 (f31 ?v1 ?v2)) f1) (=> (= (f31 (f32 f33 ?v2) ?v3) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v4) ?v5) f1) (= (f43 (f44 f51 (f31 ?v1 ?v4)) (f31 ?v1 ?v5)) f1))) (= (f43 ?v_0 (f31 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S30) (?v2 S13) (?v3 S13)) (let ((?v_0 (f49 f50 ?v0))) (=> (= (f5 ?v_0 (f54 ?v1 ?v2)) f1) (=> (= (f31 (f32 f33 ?v2) ?v3) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f31 (f32 f33 ?v4) ?v5) f1) (= (f5 (f49 f50 (f54 ?v1 ?v4)) (f54 ?v1 ?v5)) f1))) (= (f5 ?v_0 (f54 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S13) (?v1 S28) (?v2 S1) (?v3 S1)) (let ((?v_0 (f32 f33 ?v0))) (=> (= (f31 ?v_0 (f52 ?v1 ?v2)) f1) (=> (= (f43 (f44 f51 ?v2) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f43 (f44 f51 ?v4) ?v5) f1) (= (f31 (f32 f33 (f52 ?v1 ?v4)) (f52 ?v1 ?v5)) f1))) (= (f31 ?v_0 (f52 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S13) (?v1 S29) (?v2 S3) (?v3 S3)) (let ((?v_0 (f32 f33 ?v0))) (=> (= (f31 ?v_0 (f53 ?v1 ?v2)) f1) (=> (= (f5 (f49 f50 ?v2) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f5 (f49 f50 ?v4) ?v5) f1) (= (f31 (f32 f33 (f53 ?v1 ?v4)) (f53 ?v1 ?v5)) f1))) (= (f31 ?v_0 (f53 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S13)) (= (= (f31 (f32 f33 (f46 f55 ?v0)) f34) f1) (= (f31 (f32 f33 ?v0) f34) f1))))
(assert (forall ((?v0 S13)) (let ((?v_0 (f32 f33 f34))) (= (= (f31 ?v_0 (f46 f55 ?v0)) f1) (= (f31 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f5 (f6 f7 ?v0) ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f28 f40 ?v0) ?v0)))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f31 (f32 f33 ?v0) ?v1) f1) false) (=> (=> (= (f31 (f32 f33 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f46 f55 ?v0) (f46 f55 ?v1)) (= ?v0 ?v1))))
(assert (= (f46 f55 f34) f34))
(assert (forall ((?v0 S13)) (= (= f34 (f46 f55 ?v0)) (= ?v0 f34))))
(assert (forall ((?v0 S13)) (= (= (f46 f55 ?v0) f34) (= ?v0 f34))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f31 (f32 f33 (f46 f55 ?v0)) (f46 f55 ?v1)) f1) (= (f31 (f32 f33 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13)) (= (= f34 ?v0) (= ?v0 f34))))
(assert (forall ((?v0 S13)) (let ((?v_0 (f32 f33 f34))) (= (= (f31 ?v_0 (f46 f56 ?v0)) f1) (= (f31 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S13)) (= (= (f31 (f32 f33 (f46 f56 ?v0)) f34) f1) (= (f31 (f32 f33 ?v0) f34) f1))))
(assert (forall ((?v0 S19) (?v1 S13) (?v2 S13)) (=> (= (f57 f58 ?v0) f1) (= (= (f43 (f44 f51 (f31 ?v0 ?v1)) (f31 ?v0 ?v2)) f1) (= (f31 (f32 f33 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S30) (?v1 S13) (?v2 S13)) (=> (= (f59 f60 ?v0) f1) (= (= (f5 (f49 f50 (f54 ?v0 ?v1)) (f54 ?v0 ?v2)) f1) (= (f31 (f32 f33 ?v1) ?v2) f1)))))
(assert (= (f46 f56 f34) f34))
(assert (forall ((?v0 S13)) (let ((?v_0 (f46 f56 ?v0))) (= (f46 f56 ?v_0) ?v_0))))
(assert (forall ((?v0 S30) (?v1 S13) (?v2 S13)) (=> (= (f59 f60 ?v0) f1) (= (= (f54 ?v0 ?v1) (f54 ?v0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S13)) (= (= (f46 f56 ?v0) f34) (= ?v0 f34))))
(assert (forall ((?v0 S28) (?v1 S1) (?v2 S1)) (=> (= (f61 f62 ?v0) f1) (=> (= (f43 (f44 f51 ?v1) ?v2) f1) (= (f31 (f32 f33 (f52 ?v0 ?v1)) (f52 ?v0 ?v2)) f1)))))
(assert (forall ((?v0 S29) (?v1 S3) (?v2 S3)) (=> (= (f63 f64 ?v0) f1) (=> (= (f5 (f49 f50 ?v1) ?v2) f1) (= (f31 (f32 f33 (f53 ?v0 ?v1)) (f53 ?v0 ?v2)) f1)))))
(assert (forall ((?v0 S19) (?v1 S13) (?v2 S13)) (=> (= (f57 f58 ?v0) f1) (=> (= (f31 (f32 f33 ?v1) ?v2) f1) (= (f43 (f44 f51 (f31 ?v0 ?v1)) (f31 ?v0 ?v2)) f1)))))
(assert (forall ((?v0 S30) (?v1 S13) (?v2 S13)) (=> (= (f59 f60 ?v0) f1) (=> (= (f31 (f32 f33 ?v1) ?v2) f1) (= (f5 (f49 f50 (f54 ?v0 ?v1)) (f54 ?v0 ?v2)) f1)))))
(assert (forall ((?v0 S28)) (=> (forall ((?v1 S1) (?v2 S1)) (=> (= (f43 (f44 f51 ?v1) ?v2) f1) (= (f31 (f32 f33 (f52 ?v0 ?v1)) (f52 ?v0 ?v2)) f1))) (= (f61 f62 ?v0) f1))))
(assert (forall ((?v0 S29)) (=> (forall ((?v1 S3) (?v2 S3)) (=> (= (f5 (f49 f50 ?v1) ?v2) f1) (= (f31 (f32 f33 (f53 ?v0 ?v1)) (f53 ?v0 ?v2)) f1))) (= (f63 f64 ?v0) f1))))
(assert (forall ((?v0 S19)) (=> (forall ((?v1 S13) (?v2 S13)) (=> (= (f31 (f32 f33 ?v1) ?v2) f1) (= (f43 (f44 f51 (f31 ?v0 ?v1)) (f31 ?v0 ?v2)) f1))) (= (f57 f58 ?v0) f1))))
(assert (forall ((?v0 S30)) (=> (forall ((?v1 S13) (?v2 S13)) (=> (= (f31 (f32 f33 ?v1) ?v2) f1) (= (f5 (f49 f50 (f54 ?v0 ?v1)) (f54 ?v0 ?v2)) f1))) (= (f59 f60 ?v0) f1))))
(assert (forall ((?v0 S13)) (= (= (f46 f56 ?v0) f65) (= (f31 (f32 f33 f34) ?v0) f1))))
(assert (forall ((?v0 S13)) (=> (= (f31 (f32 f33 f34) ?v0) f1) (= (f46 f56 ?v0) f65))))
(assert (forall ((?v0 S13)) (= (= f65 ?v0) (= ?v0 f65))))
(assert (= (f46 f55 f65) f65))
(assert (not (= f34 f65)))
(assert (not (= f65 f34)))
(assert (not (= f34 f65)))
(assert (not (= (f31 (f32 f33 f65) f34) f1)))
(assert (= (f31 (f32 f33 f34) f65) f1))
(assert (= (f31 (f32 f33 f34) f65) f1))
(assert (forall ((?v0 S13)) (= (f46 f56 ?v0) (ite (= ?v0 f34) f34 (ite (= (f31 (f32 f33 f34) ?v0) f1) f65 (f46 f66 f65))))))
(assert (forall ((?v0 S13)) (= (= (f46 f56 ?v0) (f46 f66 f65)) (= (f31 (f32 f33 ?v0) f34) f1))))
(assert (forall ((?v0 S13)) (=> (= (f31 (f32 f33 ?v0) f34) f1) (= (f46 f56 ?v0) (f46 f66 f65)))))
(assert (= (f31 (f32 f33 f34) (f46 (f47 f67 f65) f65)) f1))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f32 f33 ?v0))) (= (= (f31 ?v_0 (f46 (f47 f67 ?v1) f65)) f1) (or (= (f31 ?v_0 ?v1) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S13)) (not (= (f46 (f47 f67 (f46 (f47 f67 f65) ?v0)) ?v0) f34))))
(assert (forall ((?v0 S13)) (= (= (f46 (f47 f67 ?v0) ?v0) f34) (= ?v0 f34))))
(assert (forall ((?v0 S13)) (= (f46 (f47 f67 f34) ?v0) ?v0)))
(assert (forall ((?v0 S13)) (= (f46 (f47 f67 f34) ?v0) ?v0)))
(assert (forall ((?v0 S13)) (= (= f34 (f46 (f47 f67 ?v0) ?v0)) (= ?v0 f34))))
(assert (forall ((?v0 S13)) (= (f46 (f47 f67 ?v0) f34) ?v0)))
(assert (forall ((?v0 S13)) (= (f46 (f47 f67 ?v0) f34) ?v0)))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f47 f67 ?v0))) (=> (= (f31 (f32 f33 (f46 ?v_0 ?v1)) (f46 ?v_0 ?v2)) f1) (= (f31 (f32 f33 ?v1) ?v2) f1)))))
(check-sat)
(exit)