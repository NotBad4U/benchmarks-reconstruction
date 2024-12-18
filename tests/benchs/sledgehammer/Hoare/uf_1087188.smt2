(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status sat)
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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S6) S4)
(declare-fun f6 () S5)
(declare-fun f7 (S7) S6)
(declare-fun f8 (S8 S2) S7)
(declare-fun f9 () S8)
(declare-fun f10 () S3)
(declare-fun f11 (S2) S6)
(declare-fun f12 (S9 S4) S1)
(declare-fun f13 (S10 S9) S9)
(declare-fun f14 () S10)
(declare-fun f15 (S11 S9) S1)
(declare-fun f16 (S12 S4) S11)
(declare-fun f17 () S12)
(declare-fun f18 (S13 S2) S1)
(declare-fun f19 (S14 S13) S13)
(declare-fun f20 () S14)
(declare-fun f21 (S15 S13) S1)
(declare-fun f22 (S16 S2) S15)
(declare-fun f23 () S16)
(declare-fun f24 (S18 S3) S3)
(declare-fun f25 (S19 S17) S18)
(declare-fun f26 () S19)
(declare-fun f27 (S17 S4) S4)
(declare-fun f28 (S21 S2) S2)
(declare-fun f29 (S22 S3) S21)
(declare-fun f30 (S23 S20) S22)
(declare-fun f31 () S23)
(declare-fun f32 (S20 S4) S2)
(declare-fun f33 (S24 S20) S17)
(declare-fun f34 (S25 S3) S24)
(declare-fun f35 () S25)
(declare-fun f36 () S17)
(declare-fun f37 (S26 S9) S11)
(declare-fun f38 () S26)
(declare-fun f39 (S27 S13) S9)
(declare-fun f40 (S28 S3) S27)
(declare-fun f41 () S28)
(declare-fun f42 (S29 S8) S13)
(declare-fun f43 () S29)
(declare-fun f44 () S9)
(declare-fun f45 () S1)
(declare-fun f46 () S1)
(declare-fun f47 () S26)
(declare-fun f48 (S30 S17) S10)
(declare-fun f49 () S30)
(declare-fun f50 (S31 S9) S13)
(declare-fun f51 (S32 S20) S31)
(declare-fun f52 () S32)
(declare-fun f53 (S33 S13) S15)
(declare-fun f54 () S33)
(declare-fun f55 (S34 S1) S1)
(declare-fun f56 (S35 S1) S34)
(declare-fun f57 () S35)
(declare-fun f58 (S37 S21) S14)
(declare-fun f59 () S37)
(declare-fun f60 () S10)
(declare-fun f61 () S14)
(declare-fun f62 (S38 S1) S9)
(declare-fun f63 (S39 S9) S10)
(declare-fun f64 () S39)
(declare-fun f65 () S15)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 f6 (f7 (f8 f9 ?v0))))))
(assert (forall ((?v0 S2)) (= (f3 f10 ?v0) (f5 f6 (f11 ?v0)))))
(assert (forall ((?v0 S9) (?v1 S4)) (= (= (f12 (f13 f14 ?v0) ?v1) f1) (= (f15 (f16 f17 ?v1) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S2)) (= (= (f18 (f19 f20 ?v0) ?v1) f1) (= (f21 (f22 f23 ?v1) ?v0) f1))))
(assert (forall ((?v0 S17) (?v1 S3) (?v2 S2)) (= (f3 (f24 (f25 f26 ?v0) ?v1) ?v2) (f27 ?v0 (f3 ?v1 ?v2)))))
(assert (forall ((?v0 S20) (?v1 S3) (?v2 S2)) (= (f28 (f29 (f30 f31 ?v0) ?v1) ?v2) (f32 ?v0 (f3 ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S20) (?v2 S4)) (= (f27 (f33 (f34 f35 ?v0) ?v1) ?v2) (f3 ?v0 (f32 ?v1 ?v2)))))
(assert (forall ((?v0 S4)) (= (f27 f36 ?v0) ?v0)))
(assert (not (= (f15 (f37 f38 (f39 (f40 f41 f10) (f42 f43 f9))) f44) f1)))
(assert (= f45 f1))
(assert (= f46 f1))
(assert (= (f15 (f37 f47 f44) (f39 (f40 f41 f4) (f42 f43 f9))) f1))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (= (f15 (f37 f38 ?v1) ?v0) f1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f37 f38 ?v0))) (=> (= (f15 ?v_0 ?v1) f1) (=> (= (f15 (f37 f47 ?v2) ?v1) f1) (= (f15 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f15 (f37 f38 ?v0) ?v1) f1) (=> (= (f15 (f37 f47 ?v0) ?v2) f1) (= (f15 (f37 f38 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f37 f38 ?v2))) (=> (= (f15 (f37 f38 ?v0) ?v1) f1) (=> (= (f15 ?v_0 ?v0) f1) (= (f15 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S13)) (=> (= ?v0 (f3 ?v1 ?v2)) (=> (= (f21 (f22 f23 ?v2) ?v3) f1) (= (f15 (f16 f17 ?v0) (f39 (f40 f41 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S4) (?v1 S17) (?v2 S4) (?v3 S9)) (=> (= ?v0 (f27 ?v1 ?v2)) (=> (= (f15 (f16 f17 ?v2) ?v3) f1) (= (f15 (f16 f17 ?v0) (f13 (f48 f49 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S20) (?v2 S4) (?v3 S9)) (=> (= ?v0 (f32 ?v1 ?v2)) (=> (= (f15 (f16 f17 ?v2) ?v3) f1) (= (f21 (f22 f23 ?v0) (f50 (f51 f52 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S4)) (let ((?v_0 (f16 f17 ?v2))) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f15 ?v_0 ?v0) f1) (= (f15 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S2)) (let ((?v_0 (f22 f23 ?v2))) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f21 ?v_0 ?v0) f1) (= (f21 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f15 (f37 f47 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f21 (f53 f54 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S9)) (= (f15 (f37 f47 ?v0) ?v0) f1)))
(assert (forall ((?v0 S13)) (= (f21 (f53 f54 ?v0) ?v0) f1)))
(assert (forall ((?v0 S1)) (= (f55 (f56 f57 ?v0) ?v0) f1)))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S13)) (= (= (f15 (f37 f47 ?v0) (f39 (f40 f41 ?v1) ?v2)) f1) (exists ((?v3 S13)) (and (= (f21 (f53 f54 ?v3) ?v2) f1) (= ?v0 (f39 (f40 f41 ?v1) ?v3)))))))
(assert (forall ((?v0 S13) (?v1 S20) (?v2 S9)) (= (= (f21 (f53 f54 ?v0) (f50 (f51 f52 ?v1) ?v2)) f1) (exists ((?v3 S9)) (and (= (f15 (f37 f47 ?v3) ?v2) f1) (= ?v0 (f50 (f51 f52 ?v1) ?v3)))))))
(assert (forall ((?v0 S9) (?v1 S17) (?v2 S9)) (= (= (f15 (f37 f47 ?v0) (f13 (f48 f49 ?v1) ?v2)) f1) (exists ((?v3 S9)) (and (= (f15 (f37 f47 ?v3) ?v2) f1) (= ?v0 (f13 (f48 f49 ?v1) ?v3)))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S3)) (let ((?v_0 (f40 f41 ?v2))) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (= (f15 (f37 f47 (f39 ?v_0 ?v0)) (f39 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S20)) (let ((?v_0 (f51 f52 ?v2))) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (= (f21 (f53 f54 (f50 ?v_0 ?v0)) (f50 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S17)) (let ((?v_0 (f48 f49 ?v2))) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (= (f15 (f37 f47 (f13 ?v_0 ?v0)) (f13 ?v_0 ?v1)) f1)))))
(assert (= (= f45 f1) (exists ((?v0 S36) (?v1 S36)) (not (= ?v0 ?v1)))))
(assert (=> (= f45 f1) (forall ((?v0 S36)) (=> (forall ((?v1 S36)) (= ?v1 ?v0)) false))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f15 (f37 f47 ?v0) ?v1) f1) (forall ((?v2 S4)) (= (f55 (f56 f57 (f12 ?v0 ?v2)) (f12 ?v1 ?v2)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f21 (f53 f54 ?v0) ?v1) f1) (forall ((?v2 S2)) (= (f55 (f56 f57 (f18 ?v0 ?v2)) (f18 ?v1 ?v2)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S4)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (= (f55 (f56 f57 (f12 ?v0 ?v2)) (f12 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S2)) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (= (f55 (f56 f57 (f18 ?v0 ?v2)) (f18 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S4)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (=> (= (f55 (f56 f57 (f12 ?v0 ?v2)) (f12 ?v1 ?v2)) f1) false) false))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S2)) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (=> (= (f55 (f56 f57 (f18 ?v0 ?v2)) (f18 ?v1 ?v2)) f1) false) false))))
(assert (forall ((?v0 S17) (?v1 S3) (?v2 S13)) (= (f13 (f48 f49 ?v0) (f39 (f40 f41 ?v1) ?v2)) (f39 (f40 f41 (f24 (f25 f26 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S20) (?v1 S3) (?v2 S13)) (= (f50 (f51 f52 ?v0) (f39 (f40 f41 ?v1) ?v2)) (f19 (f58 f59 (f29 (f30 f31 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S3) (?v1 S20) (?v2 S9)) (= (f39 (f40 f41 ?v0) (f50 (f51 f52 ?v1) ?v2)) (f13 (f48 f49 (f33 (f34 f35 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f37 f47 ?v2))) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f15 ?v_0 ?v0) f1) (= (f15 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f53 f54 ?v2))) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f21 ?v_0 ?v0) f1) (= (f21 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f56 f57 ?v2))) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f55 ?v_0 ?v0) f1) (= (f55 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f15 (f37 f47 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f21 (f53 f54 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f55 (f56 f57 ?v1) ?v0) f1) (= (= ?v1 f1) (= ?v0 f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f37 f47 ?v0))) (=> (= (f15 ?v_0 ?v1) f1) (=> (= (f15 (f37 f47 ?v1) ?v2) f1) (= (f15 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f53 f54 ?v0))) (=> (= (f21 ?v_0 ?v1) f1) (=> (= (f21 (f53 f54 ?v1) ?v2) f1) (= (f21 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f56 f57 ?v0))) (=> (= (f55 ?v_0 ?v1) f1) (=> (= (f55 (f56 f57 ?v1) ?v2) f1) (= (f55 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f15 (f37 f47 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f21 (f53 f54 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f55 (f56 f57 ?v1) ?v0) f1) (= (= ?v0 f1) (= ?v1 f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f15 (f37 f47 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f21 (f53 f54 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (= ?v0 f1) (= ?v2 f1)) (= (f55 (f56 f57 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f37 f47 ?v0))) (=> (= (f15 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f15 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f53 f54 ?v0))) (=> (= (f21 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f21 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f56 f57 ?v0))) (=> (= (f55 ?v_0 ?v1) f1) (=> (= (= ?v1 f1) (= ?v2 f1)) (= (f55 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f37 f47 ?v2))) (=> (= ?v0 ?v1) (=> (= (f15 ?v_0 ?v1) f1) (= (f15 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f53 f54 ?v2))) (=> (= ?v0 ?v1) (=> (= (f21 ?v_0 ?v1) f1) (= (f21 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f56 f57 ?v2))) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f55 ?v_0 ?v1) f1) (= (f55 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= ?v0 ?v1) (=> (= (f15 (f37 f47 ?v1) ?v2) f1) (= (f15 (f37 f47 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= ?v0 ?v1) (=> (= (f21 (f53 f54 ?v1) ?v2) f1) (= (f21 (f53 f54 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f55 (f56 f57 ?v1) ?v2) f1) (= (f55 (f56 f57 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (= (= (f15 (f37 f47 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (= (= (f21 (f53 f54 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (= (= (f55 (f56 f57 ?v1) ?v0) f1) (= (= ?v1 f1) (= ?v0 f1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= ?v0 ?v1) (= (f15 (f37 f47 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= ?v0 ?v1) (= (f21 (f53 f54 ?v0) ?v1) f1))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (= ?v0 f1) (= ?v1 f1)) (= (f55 (f56 f57 ?v0) ?v1) f1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= ?v0 ?v1) (and (= (f15 (f37 f47 ?v0) ?v1) f1) (= (f15 (f37 f47 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= ?v0 ?v1) (and (= (f21 (f53 f54 ?v0) ?v1) f1) (= (f21 (f53 f54 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (= ?v0 f1) (= ?v1 f1)) (and (= (f55 (f56 f57 ?v0) ?v1) f1) (= (f55 (f56 f57 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= ?v0 ?v1) (=> (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f15 (f37 f47 ?v1) ?v0) f1) false)) false))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= ?v0 ?v1) (=> (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f21 (f53 f54 ?v1) ?v0) f1) false)) false))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f37 f47 ?v0))) (=> (= (f15 ?v_0 ?v1) f1) (=> (= (f15 (f37 f47 ?v1) ?v2) f1) (= (f15 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f53 f54 ?v0))) (=> (= (f21 ?v_0 ?v1) f1) (=> (= (f21 (f53 f54 ?v1) ?v2) f1) (= (f21 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S4)) (let ((?v_0 (f16 f17 ?v2))) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f15 ?v_0 ?v0) f1) (= (f15 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S2)) (let ((?v_0 (f22 f23 ?v2))) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f21 ?v_0 ?v0) f1) (= (f21 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S4) (?v1 S9) (?v2 S9)) (let ((?v_0 (f16 f17 ?v0))) (=> (= (f15 ?v_0 ?v1) f1) (=> (= (f15 (f37 f47 ?v1) ?v2) f1) (= (f15 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S13)) (let ((?v_0 (f22 f23 ?v0))) (=> (= (f21 ?v_0 ?v1) f1) (=> (= (f21 (f53 f54 ?v1) ?v2) f1) (= (f21 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S4)) (let ((?v_0 (f16 f17 ?v2))) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f15 ?v_0 ?v0) f1) (= (f15 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S2)) (let ((?v_0 (f22 f23 ?v2))) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f21 ?v_0 ?v0) f1) (= (f21 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= ?v0 ?v1) (= (f15 (f37 f47 ?v1) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= ?v0 ?v1) (= (f21 (f53 f54 ?v1) ?v0) f1))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= ?v0 ?v1) (= (f15 (f37 f47 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= ?v0 ?v1) (= (f21 (f53 f54 ?v0) ?v1) f1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= ?v0 ?v1) (and (= (f15 (f37 f47 ?v0) ?v1) f1) (= (f15 (f37 f47 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= ?v0 ?v1) (and (= (f21 (f53 f54 ?v0) ?v1) f1) (= (f21 (f53 f54 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S9)) (= (f15 (f37 f47 ?v0) ?v0) f1)))
(assert (forall ((?v0 S13)) (= (f21 (f53 f54 ?v0) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S4) (?v3 S3)) (=> (= (f21 (f22 f23 ?v0) ?v1) f1) (=> (= ?v2 (f3 ?v3 ?v0)) (= (f15 (f16 f17 ?v2) (f39 (f40 f41 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S9) (?v2 S4) (?v3 S17)) (=> (= (f15 (f16 f17 ?v0) ?v1) f1) (=> (= ?v2 (f27 ?v3 ?v0)) (= (f15 (f16 f17 ?v2) (f13 (f48 f49 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S9) (?v2 S2) (?v3 S20)) (=> (= (f15 (f16 f17 ?v0) ?v1) f1) (=> (= ?v2 (f32 ?v3 ?v0)) (= (f21 (f22 f23 ?v2) (f50 (f51 f52 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S3)) (=> (= (f21 (f22 f23 ?v0) ?v1) f1) (= (f15 (f16 f17 (f3 ?v2 ?v0)) (f39 (f40 f41 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S9) (?v2 S17)) (=> (= (f15 (f16 f17 ?v0) ?v1) f1) (= (f15 (f16 f17 (f27 ?v2 ?v0)) (f13 (f48 f49 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S9) (?v2 S20)) (=> (= (f15 (f16 f17 ?v0) ?v1) f1) (= (f21 (f22 f23 (f32 ?v2 ?v0)) (f50 (f51 f52 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S13)) (= (= (f15 (f16 f17 ?v0) (f39 (f40 f41 ?v1) ?v2)) f1) (exists ((?v3 S2)) (and (= (f21 (f22 f23 ?v3) ?v2) f1) (= ?v0 (f3 ?v1 ?v3)))))))
(assert (forall ((?v0 S4) (?v1 S17) (?v2 S9)) (= (= (f15 (f16 f17 ?v0) (f13 (f48 f49 ?v1) ?v2)) f1) (exists ((?v3 S4)) (and (= (f15 (f16 f17 ?v3) ?v2) f1) (= ?v0 (f27 ?v1 ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S20) (?v2 S9)) (= (= (f21 (f22 f23 ?v0) (f50 (f51 f52 ?v1) ?v2)) f1) (exists ((?v3 S4)) (and (= (f15 (f16 f17 ?v3) ?v2) f1) (= ?v0 (f32 ?v1 ?v3)))))))
(assert (forall ((?v0 S9)) (= (f13 (f48 f49 f36) ?v0) ?v0)))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S13)) (=> (= (f15 (f16 f17 ?v0) (f39 (f40 f41 ?v1) ?v2)) f1) (=> (forall ((?v3 S2)) (=> (= ?v0 (f3 ?v1 ?v3)) (=> (= (f21 (f22 f23 ?v3) ?v2) f1) false))) false))))
(assert (forall ((?v0 S4) (?v1 S17) (?v2 S9)) (=> (= (f15 (f16 f17 ?v0) (f13 (f48 f49 ?v1) ?v2)) f1) (=> (forall ((?v3 S4)) (=> (= ?v0 (f27 ?v1 ?v3)) (=> (= (f15 (f16 f17 ?v3) ?v2) f1) false))) false))))
(assert (forall ((?v0 S2) (?v1 S20) (?v2 S9)) (=> (= (f21 (f22 f23 ?v0) (f50 (f51 f52 ?v1) ?v2)) f1) (=> (forall ((?v3 S4)) (=> (= ?v0 (f32 ?v1 ?v3)) (=> (= (f15 (f16 f17 ?v3) ?v2) f1) false))) false))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (forall ((?v2 S4)) (let ((?v_0 (f16 f17 ?v2))) (=> (= (f15 ?v_0 ?v0) f1) (= (f15 ?v_0 ?v1) f1)))) (= (f15 (f37 f47 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (forall ((?v2 S2)) (let ((?v_0 (f22 f23 ?v2))) (=> (= (f21 ?v_0 ?v0) f1) (= (f21 ?v_0 ?v1) f1)))) (= (f21 (f53 f54 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S3) (?v2 S9)) (=> (forall ((?v3 S2)) (=> (= (f21 (f22 f23 ?v3) ?v0) f1) (= (f15 (f16 f17 (f3 ?v1 ?v3)) ?v2) f1))) (= (f15 (f37 f47 (f39 (f40 f41 ?v1) ?v0)) ?v2) f1))))
(assert (forall ((?v0 S9) (?v1 S17) (?v2 S9)) (=> (forall ((?v3 S4)) (=> (= (f15 (f16 f17 ?v3) ?v0) f1) (= (f15 (f16 f17 (f27 ?v1 ?v3)) ?v2) f1))) (= (f15 (f37 f47 (f13 (f48 f49 ?v1) ?v0)) ?v2) f1))))
(assert (forall ((?v0 S9) (?v1 S20) (?v2 S13)) (=> (forall ((?v3 S4)) (=> (= (f15 (f16 f17 ?v3) ?v0) f1) (= (f21 (f22 f23 (f32 ?v1 ?v3)) ?v2) f1))) (= (f21 (f53 f54 (f50 (f51 f52 ?v1) ?v0)) ?v2) f1))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (forall ((?v2 S4)) (= (f55 (f56 f57 (f12 ?v0 ?v2)) (f12 ?v1 ?v2)) f1)) (= (f15 (f37 f47 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (forall ((?v2 S2)) (= (f55 (f56 f57 (f18 ?v0 ?v2)) (f18 ?v1 ?v2)) f1)) (= (f21 (f53 f54 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S3) (?v3 S3)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S2)) (=> (= (f21 (f22 f23 ?v4) ?v1) f1) (= (f3 ?v2 ?v4) (f3 ?v3 ?v4)))) (= (f39 (f40 f41 ?v2) ?v0) (f39 (f40 f41 ?v3) ?v1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S17) (?v3 S17)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S4)) (=> (= (f15 (f16 f17 ?v4) ?v1) f1) (= (f27 ?v2 ?v4) (f27 ?v3 ?v4)))) (= (f13 (f48 f49 ?v2) ?v0) (f13 (f48 f49 ?v3) ?v1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S20) (?v3 S20)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S4)) (=> (= (f15 (f16 f17 ?v4) ?v1) f1) (= (f32 ?v2 ?v4) (f32 ?v3 ?v4)))) (= (f50 (f51 f52 ?v2) ?v0) (f50 (f51 f52 ?v3) ?v1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (forall ((?v2 S4)) (=> (= (f12 ?v0 ?v2) f1) (= (f12 ?v1 ?v2) f1))) (= (f15 (f37 f47 (f13 f60 ?v0)) (f13 f60 ?v1)) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (forall ((?v2 S2)) (=> (= (f18 ?v0 ?v2) f1) (= (f18 ?v1 ?v2) f1))) (= (f21 (f53 f54 (f19 f61 ?v0)) (f19 f61 ?v1)) f1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f15 (f37 f47 (f13 f14 ?v0)) (f13 f14 ?v1)) f1) (= (f15 (f37 f47 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f21 (f53 f54 (f19 f20 ?v0)) (f19 f20 ?v1)) f1) (= (f21 (f53 f54 ?v0) ?v1) f1))))
(assert (forall ((?v0 S31) (?v1 S9) (?v2 S13) (?v3 S9)) (=> (= (f21 (f53 f54 (f50 ?v0 ?v1)) ?v2) f1) (=> (= (f15 (f37 f47 ?v3) ?v1) f1) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v5) ?v4) f1) (= (f21 (f53 f54 (f50 ?v0 ?v5)) (f50 ?v0 ?v4)) f1))) (= (f21 (f53 f54 (f50 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S11) (?v1 S9) (?v2 S1) (?v3 S9)) (=> (= (f55 (f56 f57 (f15 ?v0 ?v1)) ?v2) f1) (=> (= (f15 (f37 f47 ?v3) ?v1) f1) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v5) ?v4) f1) (= (f55 (f56 f57 (f15 ?v0 ?v5)) (f15 ?v0 ?v4)) f1))) (= (f55 (f56 f57 (f15 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S27) (?v1 S13) (?v2 S9) (?v3 S13)) (=> (= (f15 (f37 f47 (f39 ?v0 ?v1)) ?v2) f1) (=> (= (f21 (f53 f54 ?v3) ?v1) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f21 (f53 f54 ?v5) ?v4) f1) (= (f15 (f37 f47 (f39 ?v0 ?v5)) (f39 ?v0 ?v4)) f1))) (= (f15 (f37 f47 (f39 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S38) (?v1 S1) (?v2 S9) (?v3 S1)) (=> (= (f15 (f37 f47 (f62 ?v0 ?v1)) ?v2) f1) (=> (= (f55 (f56 f57 ?v3) ?v1) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f55 (f56 f57 ?v5) ?v4) f1) (= (f15 (f37 f47 (f62 ?v0 ?v5)) (f62 ?v0 ?v4)) f1))) (= (f15 (f37 f47 (f62 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S9) (?v1 S10) (?v2 S9) (?v3 S9)) (=> (= ?v0 (f13 ?v1 ?v2)) (=> (= (f15 (f37 f47 ?v3) ?v2) f1) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v5) ?v4) f1) (= (f15 (f37 f47 (f13 ?v1 ?v5)) (f13 ?v1 ?v4)) f1))) (= (f15 (f37 f47 (f13 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S13) (?v3 S13)) (=> (= ?v0 (f19 ?v1 ?v2)) (=> (= (f21 (f53 f54 ?v3) ?v2) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f21 (f53 f54 ?v5) ?v4) f1) (= (f21 (f53 f54 (f19 ?v1 ?v5)) (f19 ?v1 ?v4)) f1))) (= (f21 (f53 f54 (f19 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S1) (?v1 S34) (?v2 S1) (?v3 S1)) (=> (= (= ?v0 f1) (= (f55 ?v1 ?v2) f1)) (=> (= (f55 (f56 f57 ?v3) ?v2) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f55 (f56 f57 ?v5) ?v4) f1) (= (f55 (f56 f57 (f55 ?v1 ?v5)) (f55 ?v1 ?v4)) f1))) (= (f55 (f56 f57 (f55 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S13) (?v1 S31) (?v2 S9) (?v3 S9)) (let ((?v_0 (f53 f54 ?v0))) (=> (= (f21 ?v_0 (f50 ?v1 ?v2)) f1) (=> (= (f15 (f37 f47 ?v2) ?v3) f1) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v4) ?v5) f1) (= (f21 (f53 f54 (f50 ?v1 ?v4)) (f50 ?v1 ?v5)) f1))) (= (f21 ?v_0 (f50 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S1) (?v1 S11) (?v2 S9) (?v3 S9)) (let ((?v_0 (f56 f57 ?v0))) (=> (= (f55 ?v_0 (f15 ?v1 ?v2)) f1) (=> (= (f15 (f37 f47 ?v2) ?v3) f1) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v4) ?v5) f1) (= (f55 (f56 f57 (f15 ?v1 ?v4)) (f15 ?v1 ?v5)) f1))) (= (f55 ?v_0 (f15 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S9) (?v1 S27) (?v2 S13) (?v3 S13)) (let ((?v_0 (f37 f47 ?v0))) (=> (= (f15 ?v_0 (f39 ?v1 ?v2)) f1) (=> (= (f21 (f53 f54 ?v2) ?v3) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f21 (f53 f54 ?v4) ?v5) f1) (= (f15 (f37 f47 (f39 ?v1 ?v4)) (f39 ?v1 ?v5)) f1))) (= (f15 ?v_0 (f39 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S9) (?v1 S38) (?v2 S1) (?v3 S1)) (let ((?v_0 (f37 f47 ?v0))) (=> (= (f15 ?v_0 (f62 ?v1 ?v2)) f1) (=> (= (f55 (f56 f57 ?v2) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f55 (f56 f57 ?v4) ?v5) f1) (= (f15 (f37 f47 (f62 ?v1 ?v4)) (f62 ?v1 ?v5)) f1))) (= (f15 ?v_0 (f62 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S9) (?v1 S4) (?v2 S9)) (=> (= (f12 ?v0 ?v1) f1) (=> (= (f15 (f37 f47 ?v0) ?v2) f1) (= (f12 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S2) (?v2 S13)) (=> (= (f18 ?v0 ?v1) f1) (=> (= (f21 (f53 f54 ?v0) ?v2) f1) (= (f18 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S4)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f12 ?v0 ?v2) f1) (= (f12 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S2)) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f18 ?v0 ?v2) f1) (= (f18 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (forall ((?v2 S4)) (=> (= (f12 ?v0 ?v2) f1) (= (f12 ?v1 ?v2) f1))) (= (f15 (f37 f47 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (forall ((?v2 S2)) (=> (= (f18 ?v0 ?v2) f1) (= (f18 ?v1 ?v2) f1))) (= (f21 (f53 f54 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S9) (?v3 S27)) (let ((?v_0 (f37 f47 ?v2))) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f15 ?v_0 (f39 ?v3 ?v0)) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f21 (f53 f54 ?v5) ?v4) f1) (= (f15 (f37 f47 (f39 ?v3 ?v5)) (f39 ?v3 ?v4)) f1))) (= (f15 ?v_0 (f39 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S9) (?v3 S38)) (let ((?v_0 (f37 f47 ?v2))) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f15 ?v_0 (f62 ?v3 ?v0)) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f55 (f56 f57 ?v5) ?v4) f1) (= (f15 (f37 f47 (f62 ?v3 ?v5)) (f62 ?v3 ?v4)) f1))) (= (f15 ?v_0 (f62 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S13) (?v3 S31)) (let ((?v_0 (f53 f54 ?v2))) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f21 ?v_0 (f50 ?v3 ?v0)) f1) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v5) ?v4) f1) (= (f21 (f53 f54 (f50 ?v3 ?v5)) (f50 ?v3 ?v4)) f1))) (= (f21 ?v_0 (f50 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S1) (?v3 S11)) (let ((?v_0 (f56 f57 ?v2))) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f55 ?v_0 (f15 ?v3 ?v0)) f1) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v5) ?v4) f1) (= (f55 (f56 f57 (f15 ?v3 ?v5)) (f15 ?v3 ?v4)) f1))) (= (f55 ?v_0 (f15 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S10) (?v3 S9)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f13 ?v2 ?v0) ?v3) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v5) ?v4) f1) (= (f15 (f37 f47 (f13 ?v2 ?v5)) (f13 ?v2 ?v4)) f1))) (= (f15 (f37 f47 ?v3) (f13 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S14) (?v3 S13)) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f19 ?v2 ?v0) ?v3) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f21 (f53 f54 ?v5) ?v4) f1) (= (f21 (f53 f54 (f19 ?v2 ?v5)) (f19 ?v2 ?v4)) f1))) (= (f21 (f53 f54 ?v3) (f19 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S34) (?v3 S1)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (= (f55 ?v2 ?v0) f1) (= ?v3 f1)) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f55 (f56 f57 ?v5) ?v4) f1) (= (f55 (f56 f57 (f55 ?v2 ?v5)) (f55 ?v2 ?v4)) f1))) (= (f55 (f56 f57 ?v3) (f55 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S27) (?v3 S9)) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f39 ?v2 ?v1) ?v3) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f21 (f53 f54 ?v4) ?v5) f1) (= (f15 (f37 f47 (f39 ?v2 ?v4)) (f39 ?v2 ?v5)) f1))) (= (f15 (f37 f47 (f39 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S38) (?v3 S9)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f62 ?v2 ?v1) ?v3) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f55 (f56 f57 ?v4) ?v5) f1) (= (f15 (f37 f47 (f62 ?v2 ?v4)) (f62 ?v2 ?v5)) f1))) (= (f15 (f37 f47 (f62 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S31) (?v3 S13)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f50 ?v2 ?v1) ?v3) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v4) ?v5) f1) (= (f21 (f53 f54 (f50 ?v2 ?v4)) (f50 ?v2 ?v5)) f1))) (= (f21 (f53 f54 (f50 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S11) (?v3 S1)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (= (f15 ?v2 ?v1) f1) (= ?v3 f1)) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v4) ?v5) f1) (= (f55 (f56 f57 (f15 ?v2 ?v4)) (f15 ?v2 ?v5)) f1))) (= (f55 (f56 f57 (f15 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S27) (?v3 S9)) (=> (= (f21 (f53 f54 ?v0) ?v1) f1) (=> (= (f15 (f37 f47 (f39 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f21 (f53 f54 ?v4) ?v5) f1) (= (f15 (f37 f47 (f39 ?v2 ?v4)) (f39 ?v2 ?v5)) f1))) (= (f15 (f37 f47 (f39 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S38) (?v3 S9)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f15 (f37 f47 (f62 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f55 (f56 f57 ?v4) ?v5) f1) (= (f15 (f37 f47 (f62 ?v2 ?v4)) (f62 ?v2 ?v5)) f1))) (= (f15 (f37 f47 (f62 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S31) (?v3 S13)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f21 (f53 f54 (f50 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v4) ?v5) f1) (= (f21 (f53 f54 (f50 ?v2 ?v4)) (f50 ?v2 ?v5)) f1))) (= (f21 (f53 f54 (f50 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S11) (?v3 S1)) (=> (= (f15 (f37 f47 ?v0) ?v1) f1) (=> (= (f55 (f56 f57 (f15 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v4) ?v5) f1) (= (f55 (f56 f57 (f15 ?v2 ?v4)) (f15 ?v2 ?v5)) f1))) (= (f55 (f56 f57 (f15 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S9) (?v1 S27) (?v2 S13) (?v3 S13)) (=> (= ?v0 (f39 ?v1 ?v2)) (=> (= (f21 (f53 f54 ?v2) ?v3) f1) (=> (forall ((?v4 S13) (?v5 S13)) (=> (= (f21 (f53 f54 ?v4) ?v5) f1) (= (f15 (f37 f47 (f39 ?v1 ?v4)) (f39 ?v1 ?v5)) f1))) (= (f15 (f37 f47 ?v0) (f39 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S9) (?v1 S38) (?v2 S1) (?v3 S1)) (=> (= ?v0 (f62 ?v1 ?v2)) (=> (= (f55 (f56 f57 ?v2) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f55 (f56 f57 ?v4) ?v5) f1) (= (f15 (f37 f47 (f62 ?v1 ?v4)) (f62 ?v1 ?v5)) f1))) (= (f15 (f37 f47 ?v0) (f62 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S13) (?v1 S31) (?v2 S9) (?v3 S9)) (=> (= ?v0 (f50 ?v1 ?v2)) (=> (= (f15 (f37 f47 ?v2) ?v3) f1) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v4) ?v5) f1) (= (f21 (f53 f54 (f50 ?v1 ?v4)) (f50 ?v1 ?v5)) f1))) (= (f21 (f53 f54 ?v0) (f50 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S1) (?v1 S11) (?v2 S9) (?v3 S9)) (=> (= (= ?v0 f1) (= (f15 ?v1 ?v2) f1)) (=> (= (f15 (f37 f47 ?v2) ?v3) f1) (=> (forall ((?v4 S9) (?v5 S9)) (=> (= (f15 (f37 f47 ?v4) ?v5) f1) (= (f55 (f56 f57 (f15 ?v1 ?v4)) (f15 ?v1 ?v5)) f1))) (= (f55 (f56 f57 ?v0) (f15 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S9) (?v1 S13)) (let ((?v_0 (f39 (f40 f41 f10) ?v1))) (=> (= (f15 (f37 f38 (f13 (f63 f64 ?v0) ?v_0)) (f39 (f40 f41 f4) ?v1)) f1) (=> (= (f21 f65 ?v1) f1) (= (f15 (f37 f38 ?v0) ?v_0) f1))))))
(assert (forall ((?v0 S9) (?v1 S4) (?v2 S9)) (=> (=> (not (= (f12 ?v0 ?v1) f1)) (= (f12 ?v2 ?v1) f1)) (= (f12 (f13 (f63 f64 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S4)) (=> (= (f12 (f13 (f63 f64 ?v0) ?v1) ?v2) f1) (=> (=> (= (f12 ?v0 ?v2) f1) false) (=> (=> (= (f12 ?v1 ?v2) f1) false) false)))))
(check-sat)
(exit)
