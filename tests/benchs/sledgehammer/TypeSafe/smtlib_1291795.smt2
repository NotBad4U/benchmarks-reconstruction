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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S3) S1)
(declare-fun f4 (S5 S3) S4)
(declare-fun f5 (S2) S5)
(declare-fun f6 (S6 S2) S1)
(declare-fun f7 (S3 S3) S6)
(declare-fun f8 (S9 S8) S1)
(declare-fun f9 (S10 S7) S9)
(declare-fun f10 (S4) S10)
(declare-fun f11 (S3 S4) S1)
(declare-fun f12 (S11 S8) S3)
(declare-fun f13 (S12 S7) S11)
(declare-fun f14 () S12)
(declare-fun f15 (S15 S14) S1)
(declare-fun f16 (S16 S13) S15)
(declare-fun f17 (S9) S16)
(declare-fun f18 (S8 S9) S1)
(declare-fun f19 (S17 S14) S8)
(declare-fun f20 (S18 S13) S17)
(declare-fun f21 () S18)
(declare-fun f22 (S14 S19) S20)
(declare-fun f23 () S14)
(declare-fun f24 () S20)
(declare-fun f25 (S21 S19) S22)
(declare-fun f26 () S21)
(declare-fun f27 () S22)
(declare-fun f28 () S1)
(declare-fun f29 (S24 S13 S21 S7 S23) S1)
(declare-fun f30 () S24)
(declare-fun f31 () S13)
(declare-fun f32 (S25 S22) S21)
(declare-fun f33 (S26 S19) S25)
(declare-fun f34 (S27 S21) S26)
(declare-fun f35 () S27)
(declare-fun f36 () S21)
(declare-fun f37 () S19)
(declare-fun f38 (S28 S23) S22)
(declare-fun f39 () S28)
(declare-fun f40 () S23)
(declare-fun f41 () S7)
(declare-fun f42 (S24 S23 S23) S1)
(declare-fun f43 () S23)
(declare-fun f44 (S29 S21) S9)
(declare-fun f45 (S24) S29)
(declare-fun f46 () S13)
(declare-fun f47 (S30 S20) S14)
(declare-fun f48 (S31 S19) S30)
(declare-fun f49 (S32 S14) S31)
(declare-fun f50 () S32)
(declare-fun f51 () S14)
(declare-fun f52 () S7)
(declare-fun f53 (S33 S7) S7)
(declare-fun f54 (S34 S23) S33)
(declare-fun f55 (S35 S19) S34)
(declare-fun f56 () S35)
(declare-fun f57 (S19 S7) S1)
(declare-fun f58 (S36 S24) S1)
(declare-fun f59 () S36)
(declare-fun f60 (S38 S37) S20)
(declare-fun f61 () S38)
(declare-fun f62 () S14)
(declare-fun f63 () S37)
(declare-fun f64 (S24) S2)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (= (f6 (f7 ?v1 ?v2) ?v0) f1))))
(assert (forall ((?v0 S4) (?v1 S7) (?v2 S8)) (= (= (f8 (f9 (f10 ?v0) ?v1) ?v2) f1) (= (f11 (f12 (f13 f14 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S9) (?v1 S13) (?v2 S14)) (= (= (f15 (f16 (f17 ?v0) ?v1) ?v2) f1) (= (f18 (f19 (f20 f21 ?v1) ?v2) ?v0) f1))))
(assert (forall ((?v0 S19)) (= (f22 f23 ?v0) f24)))
(assert (forall ((?v0 S19)) (= (f25 f26 ?v0) f27)))
(assert (not (= f28 f1)))
(assert (forall ((?v0 S23)) (=> (and (= (f29 f30 f31 (f32 (f33 (f34 f35 f36) f37) (f38 f39 f40)) f41 ?v0) f1) (= (f42 f30 ?v0 f43) f1)) (= f28 f1))))
(assert (forall ((?v0 S21) (?v1 S23)) (=> (= (f8 (f44 (f45 f30) ?v0) (f19 (f20 f21 f46) (f47 (f48 (f49 f50 f51) f37) f24))) f1) (=> (= (f29 f30 f46 ?v0 f52 ?v1) f1) (exists ((?v2 S23)) (and (= (f29 f30 f31 ?v0 f41 ?v2) f1) (= (f42 f30 ?v2 ?v1) f1)))))))
(assert (= (f8 (f44 (f45 f30) f36) (f19 (f20 f21 f46) f51)) f1))
(assert (= (f29 f30 f46 f36 (f53 (f54 (f55 f56 f37) f40) f52) f43) f1))
(assert (not (= (f57 f37 f52) f1)))
(assert (= (f8 (f44 (f45 f30) f36) (f19 (f20 f21 f46) f51)) f1))
(assert (= (f29 f30 f46 f36 (f53 (f54 (f55 f56 f37) f40) f52) f43) f1))
(assert (forall ((?v0 S21) (?v1 S23)) (=> (= (f8 (f44 (f45 f30) ?v0) (f19 (f20 f21 f46) (f47 (f48 (f49 f50 f51) f37) f24))) f1) (=> (= (f29 f30 f46 ?v0 f52 ?v1) f1) (exists ((?v2 S23)) (and (= (f29 f30 f31 ?v0 f41 ?v2) f1) (= (f42 f30 ?v2 ?v1) f1)))))))
(assert (forall ((?v0 S24) (?v1 S23)) (= (f42 ?v0 ?v1 ?v1) f1)))
(assert (forall ((?v0 S24) (?v1 S13) (?v2 S21) (?v3 S19) (?v4 S23) (?v5 S7) (?v6 S23)) (=> (= (f29 ?v0 ?v1 (f32 (f33 (f34 f35 ?v2) ?v3) (f38 f39 ?v4)) ?v5 ?v6) f1) (= (f29 ?v0 ?v1 ?v2 (f53 (f54 (f55 f56 ?v3) ?v4) ?v5) ?v6) f1))))
(assert (forall ((?v0 S21) (?v1 S19)) (= (f32 (f33 (f34 f35 ?v0) ?v1) (f25 ?v0 ?v1)) ?v0)))
(assert (forall ((?v0 S14) (?v1 S19)) (= (f47 (f48 (f49 f50 ?v0) ?v1) (f22 ?v0 ?v1)) ?v0)))
(assert (= (f29 f30 f46 f36 (f53 (f54 (f55 f56 f37) f40) f52) f43) f1))
(assert (= (f58 f59 f30) f1))
(assert (forall ((?v0 S21) (?v1 S19) (?v2 S23) (?v3 S19) (?v4 S23)) (let ((?v_1 (f38 f39 ?v4)) (?v_0 (= ?v3 ?v1))) (= (= (f25 (f32 (f33 (f34 f35 ?v0) ?v1) (f38 f39 ?v2)) ?v3) ?v_1) (or (and ?v_0 (= ?v2 ?v4)) (and (not ?v_0) (= (f25 ?v0 ?v3) ?v_1)))))))
(assert (forall ((?v0 S14) (?v1 S19) (?v2 S37) (?v3 S19) (?v4 S37)) (let ((?v_1 (f60 f61 ?v4)) (?v_0 (= ?v3 ?v1))) (= (= (f22 (f47 (f48 (f49 f50 ?v0) ?v1) (f60 f61 ?v2)) ?v3) ?v_1) (or (and ?v_0 (= ?v2 ?v4)) (and (not ?v_0) (= (f22 ?v0 ?v3) ?v_1)))))))
(assert (forall ((?v0 S21) (?v1 S19) (?v2 S23)) (let ((?v_0 (f38 f39 ?v2))) (=> (= (f25 ?v0 ?v1) ?v_0) (= (f32 (f33 (f34 f35 ?v0) ?v1) ?v_0) ?v0)))))
(assert (forall ((?v0 S14) (?v1 S19) (?v2 S37)) (let ((?v_0 (f60 f61 ?v2))) (=> (= (f22 ?v0 ?v1) ?v_0) (= (f47 (f48 (f49 f50 ?v0) ?v1) ?v_0) ?v0)))))
(assert (forall ((?v0 S21) (?v1 S19) (?v2 S23) (?v3 S21) (?v4 S23)) (=> (= (f32 (f33 (f34 f35 ?v0) ?v1) (f38 f39 ?v2)) (f32 (f33 (f34 f35 ?v3) ?v1) (f38 f39 ?v4))) (= ?v2 ?v4))))
(assert (forall ((?v0 S14) (?v1 S19) (?v2 S37) (?v3 S14) (?v4 S37)) (=> (= (f47 (f48 (f49 f50 ?v0) ?v1) (f60 f61 ?v2)) (f47 (f48 (f49 f50 ?v3) ?v1) (f60 f61 ?v4))) (= ?v2 ?v4))))
(assert (= (f22 f62 f37) (f60 f61 f63)))
(assert (forall ((?v0 S24) (?v1 S23) (?v2 S23) (?v3 S23)) (=> (= (f42 ?v0 ?v1 ?v2) f1) (=> (= (f42 ?v0 ?v2 ?v3) f1) (= (f42 ?v0 ?v1 ?v3) f1)))))
(assert (forall ((?v0 S21) (?v1 S19) (?v2 S23)) (not (= (f32 (f33 (f34 f35 ?v0) ?v1) (f38 f39 ?v2)) f26))))
(assert (forall ((?v0 S14) (?v1 S19) (?v2 S37)) (not (= (f47 (f48 (f49 f50 ?v0) ?v1) (f60 f61 ?v2)) f23))))
(assert (= (f8 (f44 (f45 f30) f36) (f19 (f20 f21 f46) f51)) f1))
(assert (forall ((?v0 S21) (?v1 S23)) (=> (= (f8 (f44 (f45 f30) ?v0) (f19 (f20 f21 f46) (f47 (f48 (f49 f50 f51) f37) f24))) f1) (=> (= (f29 f30 f46 ?v0 f52 ?v1) f1) (exists ((?v2 S23)) (and (= (f29 f30 f31 ?v0 f41 ?v2) f1) (= (f42 f30 ?v2 ?v1) f1)))))))
(assert (forall ((?v0 S19) (?v1 S19)) (= (f25 (f32 (f33 (f34 f35 f26) ?v0) f27) ?v1) f27)))
(assert (forall ((?v0 S19) (?v1 S19)) (= (f22 (f47 (f48 (f49 f50 f23) ?v0) f24) ?v1) f24)))
(assert (forall ((?v0 S21) (?v1 S19) (?v2 S22) (?v3 S19)) (= (f25 (f32 (f33 (f34 f35 ?v0) ?v1) ?v2) ?v3) (ite (= ?v3 ?v1) ?v2 (f25 ?v0 ?v3)))))
(assert (forall ((?v0 S14) (?v1 S19) (?v2 S20) (?v3 S19)) (= (f22 (f47 (f48 (f49 f50 ?v0) ?v1) ?v2) ?v3) (ite (= ?v3 ?v1) ?v2 (f22 ?v0 ?v3)))))
(assert (forall ((?v0 S21) (?v1 S19) (?v2 S22)) (=> (= (f25 ?v0 ?v1) ?v2) (= (f32 (f33 (f34 f35 ?v0) ?v1) ?v2) ?v0))))
(assert (forall ((?v0 S14) (?v1 S19) (?v2 S20)) (=> (= (f22 ?v0 ?v1) ?v2) (= (f47 (f48 (f49 f50 ?v0) ?v1) ?v2) ?v0))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S21) (?v3 S22)) (=> (not (= ?v0 ?v1)) (= (f25 (f32 (f33 (f34 f35 ?v2) ?v1) ?v3) ?v0) (f25 ?v2 ?v0)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S14) (?v3 S20)) (=> (not (= ?v0 ?v1)) (= (f22 (f47 (f48 (f49 f50 ?v2) ?v1) ?v3) ?v0) (f22 ?v2 ?v0)))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S21) (?v3 S22) (?v4 S22)) (let ((?v_0 (f34 f35 ?v2))) (=> (not (= ?v0 ?v1)) (= (f32 (f33 (f34 f35 (f32 (f33 ?v_0 ?v0) ?v3)) ?v1) ?v4) (f32 (f33 (f34 f35 (f32 (f33 ?v_0 ?v1) ?v4)) ?v0) ?v3))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S14) (?v3 S20) (?v4 S20)) (let ((?v_0 (f49 f50 ?v2))) (=> (not (= ?v0 ?v1)) (= (f47 (f48 (f49 f50 (f47 (f48 ?v_0 ?v0) ?v3)) ?v1) ?v4) (f47 (f48 (f49 f50 (f47 (f48 ?v_0 ?v1) ?v4)) ?v0) ?v3))))))
(assert (forall ((?v0 S21) (?v1 S19) (?v2 S22) (?v3 S19)) (= (f25 (f32 (f33 (f34 f35 ?v0) ?v1) ?v2) ?v3) (ite (= ?v3 ?v1) ?v2 (f25 ?v0 ?v3)))))
(assert (forall ((?v0 S14) (?v1 S19) (?v2 S20) (?v3 S19)) (= (f22 (f47 (f48 (f49 f50 ?v0) ?v1) ?v2) ?v3) (ite (= ?v3 ?v1) ?v2 (f22 ?v0 ?v3)))))
(assert (forall ((?v0 S21) (?v1 S19) (?v2 S22)) (= (f25 (f32 (f33 (f34 f35 ?v0) ?v1) ?v2) ?v1) ?v2)))
(assert (forall ((?v0 S14) (?v1 S19) (?v2 S20)) (= (f22 (f47 (f48 (f49 f50 ?v0) ?v1) ?v2) ?v1) ?v2)))
(assert (forall ((?v0 S21) (?v1 S19) (?v2 S22) (?v3 S22)) (let ((?v_0 (f33 (f34 f35 ?v0) ?v1))) (= (f32 (f33 (f34 f35 (f32 ?v_0 ?v2)) ?v1) ?v3) (f32 ?v_0 ?v3)))))
(assert (forall ((?v0 S14) (?v1 S19) (?v2 S20) (?v3 S20)) (let ((?v_0 (f48 (f49 f50 ?v0) ?v1))) (= (f47 (f48 (f49 f50 (f47 ?v_0 ?v2)) ?v1) ?v3) (f47 ?v_0 ?v3)))))
(assert (forall ((?v0 S21) (?v1 S19) (?v2 S22)) (= (= (f32 (f33 (f34 f35 ?v0) ?v1) ?v2) ?v0) (= (f25 ?v0 ?v1) ?v2))))
(assert (forall ((?v0 S14) (?v1 S19) (?v2 S20)) (= (= (f47 (f48 (f49 f50 ?v0) ?v1) ?v2) ?v0) (= (f22 ?v0 ?v1) ?v2))))
(assert (= (f6 (f7 (f12 (f13 f14 f52) (f19 (f20 f21 f46) (f47 (f48 (f49 f50 f51) f37) f24))) (f12 (f13 f14 f41) (f19 (f20 f21 f31) f62))) (f64 f30)) f1))
(assert (forall ((?v0 S22)) (= (not (= ?v0 f27)) (exists ((?v1 S23)) (= ?v0 (f38 f39 ?v1))))))
(assert (forall ((?v0 S20)) (= (not (= ?v0 f24)) (exists ((?v1 S37)) (= ?v0 (f60 f61 ?v1))))))
(assert (forall ((?v0 S22)) (= (forall ((?v1 S23)) (not (= ?v0 (f38 f39 ?v1)))) (= ?v0 f27))))
(assert (forall ((?v0 S20)) (= (forall ((?v1 S37)) (not (= ?v0 (f60 f61 ?v1)))) (= ?v0 f24))))
(assert (forall ((?v0 S23)) (not (= (f38 f39 ?v0) f27))))
(assert (forall ((?v0 S37)) (not (= (f60 f61 ?v0) f24))))
(assert (forall ((?v0 S23)) (not (= f27 (f38 f39 ?v0)))))
(assert (forall ((?v0 S37)) (not (= f24 (f60 f61 ?v0)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f17 ?v0) (f17 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f10 ?v0) (f10 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f5 ?v0) (f5 ?v1)) (= ?v0 ?v1))))
(check-sat)
(exit)