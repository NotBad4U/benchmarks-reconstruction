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
(declare-fun f6 (S7 S8) S5)
(declare-fun f7 (S9 S6) S7)
(declare-fun f8 () S9)
(declare-fun f9 () S6)
(declare-fun f10 (S10 S11) S8)
(declare-fun f11 () S10)
(declare-fun f12 (S2) S11)
(declare-fun f13 () S6)
(declare-fun f14 () S3)
(declare-fun f15 (S12 S2) S8)
(declare-fun f16 () S12)
(declare-fun f17 (S13 S4) S1)
(declare-fun f18 (S13) S13)
(declare-fun f19 (S4 S13) S1)
(declare-fun f20 (S14 S2) S1)
(declare-fun f21 (S14) S14)
(declare-fun f22 (S2 S14) S1)
(declare-fun f23 (S16 S15) S3)
(declare-fun f24 (S17 S15) S16)
(declare-fun f25 () S17)
(declare-fun f26 (S15 S2) S6)
(declare-fun f27 () S17)
(declare-fun f28 (S18 S13) S13)
(declare-fun f29 (S13) S18)
(declare-fun f30 (S19 S14) S14)
(declare-fun f31 (S14) S19)
(declare-fun f32 (S4) S18)
(declare-fun f33 (S2) S19)
(declare-fun f34 (S13) S18)
(declare-fun f35 (S14) S19)
(declare-fun f36 (S4) S18)
(declare-fun f37 (S2) S19)
(declare-fun f38 (S21 S3) S3)
(declare-fun f39 (S22 S20) S21)
(declare-fun f40 () S22)
(declare-fun f41 (S20 S4) S4)
(declare-fun f42 (S24 S2) S2)
(declare-fun f43 (S25 S3) S24)
(declare-fun f44 (S26 S23) S25)
(declare-fun f45 () S26)
(declare-fun f46 (S23 S4) S2)
(declare-fun f47 (S27 S23) S20)
(declare-fun f48 (S28 S3) S27)
(declare-fun f49 () S28)
(declare-fun f50 (S29 S24) S3)
(declare-fun f51 (S30 S3) S29)
(declare-fun f52 () S30)
(declare-fun f53 (S31 S4) S20)
(declare-fun f54 () S31)
(declare-fun f55 (S32 S4) S3)
(declare-fun f56 () S32)
(declare-fun f57 (S33 S2) S23)
(declare-fun f58 () S33)
(declare-fun f59 (S34 S2) S24)
(declare-fun f60 () S34)
(declare-fun f61 () S20)
(declare-fun f62 () S24)
(declare-fun f63 () S13)
(declare-fun f64 () S14)
(declare-fun f65 (S13 S13) S1)
(declare-fun f66 (S13) S18)
(declare-fun f67 () S13)
(declare-fun f68 (S35 S14) S13)
(declare-fun f69 (S3) S35)
(declare-fun f70 () S14)
(declare-fun f71 (S4) S18)
(declare-fun f72 () S2)
(declare-fun f73 () S13)
(declare-fun f74 (S38 S37) S1)
(declare-fun f75 (S6 S36) S38)
(declare-fun f76 () S14)
(declare-fun f77 (S39 S13) S14)
(declare-fun f78 (S23) S39)
(declare-fun f79 (S2) S19)
(declare-fun f80 (S24) S19)
(declare-fun f81 (S20) S18)
(declare-fun f82 (S14) S19)
(declare-fun f83 (S13) S13)
(declare-fun f84 (S14) S14)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 (f6 (f7 f8 f9) (f10 f11 (f12 ?v0))) f13))))
(assert (forall ((?v0 S2)) (= (f3 f14 ?v0) (f5 (f6 (f7 f8 f9) (f15 f16 ?v0)) f13))))
(assert (forall ((?v0 S13) (?v1 S4)) (= (= (f17 (f18 ?v0) ?v1) f1) (= (f19 ?v1 ?v0) f1))))
(assert (forall ((?v0 S14) (?v1 S2)) (= (= (f20 (f21 ?v0) ?v1) f1) (= (f22 ?v1 ?v0) f1))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S2)) (= (f3 (f23 (f24 f25 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f26 ?v0 ?v2)) (f10 f11 (f12 ?v2))) (f26 ?v1 ?v2)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S2)) (= (f3 (f23 (f24 f27 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f26 ?v0 ?v2)) (f15 f16 ?v2)) (f26 ?v1 ?v2)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (= (= (f17 (f28 (f29 ?v0) ?v1) ?v2) f1) (or (= (f19 ?v2 ?v0) f1) (= (f19 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (= (f20 (f30 (f31 ?v0) ?v1) ?v2) f1) (or (= (f22 ?v2 ?v0) f1) (= (f22 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S4)) (= (= (f17 (f28 (f32 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f19 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (= (= (f20 (f30 (f33 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f22 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (= (= (f17 (f28 (f34 ?v0) ?v1) ?v2) f1) (or (= (f17 ?v0 ?v2) f1) (= (f17 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (= (f20 (f30 (f35 ?v0) ?v1) ?v2) f1) (or (= (f20 ?v0 ?v2) f1) (= (f20 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S4)) (= (= (f17 (f28 (f36 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f17 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (= (= (f20 (f30 (f37 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f20 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S20) (?v1 S3) (?v2 S2)) (= (f3 (f38 (f39 f40 ?v0) ?v1) ?v2) (f41 ?v0 (f3 ?v1 ?v2)))))
(assert (forall ((?v0 S23) (?v1 S3) (?v2 S2)) (= (f42 (f43 (f44 f45 ?v0) ?v1) ?v2) (f46 ?v0 (f3 ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S23) (?v2 S4)) (= (f41 (f47 (f48 f49 ?v0) ?v1) ?v2) (f3 ?v0 (f46 ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S24) (?v2 S2)) (= (f3 (f50 (f51 f52 ?v0) ?v1) ?v2) (f3 ?v0 (f42 ?v1 ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f41 (f53 f54 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S4) (?v1 S2)) (= (f3 (f55 f56 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S2) (?v1 S4)) (= (f46 (f57 f58 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f42 (f59 f60 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S4)) (= (f41 f61 ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f42 f62 ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (= (f17 f63 ?v0) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f20 f64 ?v0) f1) false)))
(assert (not (= (f65 (f28 (f66 f67) (f68 (f69 f14) f70)) (f68 (f69 f4) f70)) f1)))
(assert (let ((?v_0 (f7 f8 f9))) (= (f65 (f28 (f71 (f5 (f6 ?v_0 (f15 f16 f72)) f13)) f67) (f28 (f71 (f5 (f6 ?v_0 (f10 f11 (f12 f72))) f13)) f73)) f1)))
(assert (forall ((?v0 S13)) (= (f65 ?v0 f73) f1)))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6) (?v3 S6) (?v4 S8) (?v5 S6)) (= (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f65 ?v0 ?v1) f1) (=> (= (f65 ?v2 ?v0) f1) (= (f65 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S4) (?v2 S13)) (let ((?v_0 (f71 ?v1))) (=> (= (f65 ?v0 (f28 ?v_0 f73)) f1) (=> (= (f65 ?v0 ?v2) f1) (= (f65 ?v0 (f28 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S13) (?v1 S15) (?v2 S15) (?v3 S14)) (let ((?v_0 (f68 (f69 (f23 (f24 f27 ?v1) ?v2)) ?v3))) (=> (= (f65 (f28 (f66 ?v0) ?v_0) (f68 (f69 (f23 (f24 f25 ?v1) ?v2)) ?v3)) f1) (= (f65 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S13) (?v1 S15) (?v2 S15) (?v3 S14) (?v4 S2)) (=> (= (f65 (f28 (f66 ?v0) (f68 (f69 (f23 (f24 f27 ?v1) ?v2)) ?v3)) (f68 (f69 (f23 (f24 f25 ?v1) ?v2)) ?v3)) f1) (=> (= (f22 ?v4 ?v3) f1) (= (f65 ?v0 (f28 (f71 (f5 (f6 (f7 f8 (f26 ?v1 ?v4)) (f15 f16 ?v4)) (f26 ?v2 ?v4))) f73)) f1)))))
(assert (forall ((?v0 S13) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6)) (let ((?v_0 (f6 (f7 f8 ?v1) ?v2))) (=> (= (f65 ?v0 (f28 (f71 (f5 ?v_0 ?v3)) f73)) f1) (=> (forall ((?v5 S36) (?v6 S37)) (=> (= (f74 (f75 ?v3 ?v5) ?v6) f1) (= (f74 (f75 ?v4 ?v5) ?v6) f1))) (= (f65 ?v0 (f28 (f71 (f5 ?v_0 ?v4)) f73)) f1))))))
(assert (forall ((?v0 S13) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6)) (=> (= (f65 ?v0 (f28 (f71 (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) f73)) f1) (=> (forall ((?v5 S36) (?v6 S37)) (=> (= (f74 (f75 ?v4 ?v5) ?v6) f1) (= (f74 (f75 ?v1 ?v5) ?v6) f1))) (= (f65 ?v0 (f28 (f71 (f5 (f6 (f7 f8 ?v4) ?v2) ?v3)) f73)) f1)))))
(assert (forall ((?v0 S4) (?v1 S14)) (= (f68 (f69 (f55 f56 ?v0)) ?v1) (ite (= ?v1 f76) f73 (f28 (f71 ?v0) f73)))))
(assert (forall ((?v0 S2) (?v1 S13)) (= (f77 (f78 (f57 f58 ?v0)) ?v1) (ite (= ?v1 f73) f76 (f30 (f79 ?v0) f76)))))
(assert (forall ((?v0 S2) (?v1 S14)) (= (f30 (f80 (f59 f60 ?v0)) ?v1) (ite (= ?v1 f76) f76 (f30 (f79 ?v0) f76)))))
(assert (forall ((?v0 S4) (?v1 S13)) (= (f28 (f81 (f53 f54 ?v0)) ?v1) (ite (= ?v1 f73) f73 (f28 (f71 ?v0) f73)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S4)) (=> (= (f22 ?v0 ?v1) f1) (= (f68 (f69 (f55 f56 ?v2)) ?v1) (f28 (f71 ?v2) f73)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S4)) (=> (= (f19 ?v0 ?v1) f1) (= (f28 (f81 (f53 f54 ?v2)) ?v1) (f28 (f71 ?v2) f73)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (=> (= (f22 ?v0 ?v1) f1) (= (f30 (f80 (f59 f60 ?v2)) ?v1) (f30 (f79 ?v2) f76)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S2)) (=> (= (f19 ?v0 ?v1) f1) (= (f77 (f78 (f57 f58 ?v2)) ?v1) (f30 (f79 ?v2) f76)))))
(assert (forall ((?v0 S4) (?v1 S13)) (let ((?v_0 (f71 ?v0))) (= (f28 ?v_0 ?v1) (f28 (f66 (f28 ?v_0 f73)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S14)) (let ((?v_0 (f79 ?v0))) (= (f30 ?v_0 ?v1) (f30 (f82 (f30 ?v_0 f76)) ?v1)))))
(assert (forall ((?v0 S13) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6) (?v5 S6)) (=> (= (f65 ?v0 (f28 (f71 (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) f73)) f1) (=> (forall ((?v6 S36) (?v7 S37)) (=> (= (f74 (f75 ?v4 ?v6) ?v7) f1) (forall ((?v8 S37)) (=> (forall ((?v9 S36)) (=> (= (f74 (f75 ?v1 ?v9) ?v7) f1) (= (f74 (f75 ?v3 ?v9) ?v8) f1))) (= (f74 (f75 ?v5 ?v6) ?v8) f1))))) (= (f65 ?v0 (f28 (f71 (f5 (f6 (f7 f8 ?v4) ?v2) ?v5)) f73)) f1)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (= (f22 ?v0 (f30 (f82 ?v1) ?v2)) f1) (=> (=> (= (f22 ?v0 ?v1) f1) false) (=> (=> (= (f22 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (= (f19 ?v0 (f28 (f66 ?v1) ?v2)) f1) (=> (=> (= (f19 ?v0 ?v1) f1) false) (=> (=> (= (f19 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (=> (= (f17 (f28 (f66 ?v0) ?v1) ?v2) f1) (=> (=> (= (f17 ?v0 ?v2) f1) false) (=> (=> (= (f17 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (=> (= (f20 (f30 (f82 ?v0) ?v1) ?v2) f1) (=> (=> (= (f20 ?v0 ?v2) f1) false) (=> (=> (= (f20 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S4) (?v2 S13)) (=> (=> (not (= (f17 ?v0 ?v1) f1)) (= (f17 ?v2 ?v1) f1)) (= (f17 (f28 (f66 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S2) (?v2 S14)) (=> (=> (not (= (f20 ?v0 ?v1) f1)) (= (f20 ?v2 ?v1) f1)) (= (f20 (f30 (f82 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (=> (not (= (f22 ?v0 ?v1) f1)) (= (f22 ?v0 ?v2) f1)) (= (f22 ?v0 (f30 (f82 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (=> (not (= (f19 ?v0 ?v1) f1)) (= (f19 ?v0 ?v2) f1)) (= (f19 ?v0 (f28 (f66 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S14)) (=> (= ?v0 (f3 ?v1 ?v2)) (=> (= (f22 ?v2 ?v3) f1) (= (f19 ?v0 (f68 (f69 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S4) (?v3 S13)) (=> (= ?v0 (f46 ?v1 ?v2)) (=> (= (f19 ?v2 ?v3) f1) (= (f22 ?v0 (f77 (f78 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S24) (?v2 S2) (?v3 S14)) (=> (= ?v0 (f42 ?v1 ?v2)) (=> (= (f22 ?v2 ?v3) f1) (= (f22 ?v0 (f30 (f80 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S4) (?v1 S20) (?v2 S4) (?v3 S13)) (=> (= ?v0 (f41 ?v1 ?v2)) (=> (= (f19 ?v2 ?v3) f1) (= (f19 ?v0 (f28 (f81 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S13)) (=> (= (f19 ?v0 (f28 (f71 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f19 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S14)) (=> (= (f22 ?v0 (f30 (f79 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f22 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2)) (=> (= (f22 ?v0 f76) f1) false)))
(assert (forall ((?v0 S4)) (=> (= (f19 ?v0 f73) f1) false)))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S4)) (=> (=> (not (= (f19 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f19 ?v0 (f28 (f71 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (=> (=> (not (= (f22 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f22 ?v0 (f30 (f79 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S14) (?v1 S2)) (=> (= ?v0 f76) (not (= (f22 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S4)) (=> (= ?v0 f73) (not (= (f19 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S13)) (= (= (f83 ?v0) f73) (forall ((?v1 S4)) (not (= (f17 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S14)) (= (= (f84 ?v0) f76) (forall ((?v1 S2)) (not (= (f20 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f22 ?v0 f76) f1) false)))
(assert (forall ((?v0 S4)) (= (= (f19 ?v0 f73) f1) false)))
(assert (forall ((?v0 S13)) (= (= f73 (f83 ?v0)) (forall ((?v1 S4)) (not (= (f17 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S14)) (= (= f76 (f84 ?v0)) (forall ((?v1 S2)) (not (= (f20 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S14)) (= (forall ((?v1 S2)) (=> (= (f22 ?v1 f76) f1) (= (f20 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S13)) (= (forall ((?v1 S4)) (=> (= (f19 ?v1 f73) f1) (= (f17 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S14)) (= (exists ((?v1 S2)) (and (= (f22 ?v1 f76) f1) (= (f20 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S13)) (= (exists ((?v1 S4)) (and (= (f19 ?v1 f73) f1) (= (f17 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S14)) (= (exists ((?v1 S2)) (= (f22 ?v1 ?v0) f1)) (not (= ?v0 f76)))))
(assert (forall ((?v0 S13)) (= (exists ((?v1 S4)) (= (f19 ?v1 ?v0) f1)) (not (= ?v0 f73)))))
(assert (forall ((?v0 S14)) (= (forall ((?v1 S2)) (not (= (f22 ?v1 ?v0) f1))) (= ?v0 f76))))
(assert (forall ((?v0 S13)) (= (forall ((?v1 S4)) (not (= (f19 ?v1 ?v0) f1))) (= ?v0 f73))))
(assert (= f73 (f83 f63)))
(assert (= f76 (f84 f64)))
(assert (forall ((?v0 S2)) (= (= (f20 f76 ?v0) f1) (= (f22 ?v0 f76) f1))))
(assert (forall ((?v0 S4)) (= (= (f17 f73 ?v0) f1) (= (f19 ?v0 f73) f1))))
(assert (forall ((?v0 S4) (?v1 S13)) (=> (= (f19 ?v0 ?v1) f1) (= (f28 (f71 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S14)) (=> (= (f22 ?v0 ?v1) f1) (= (f30 (f79 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S4)) (=> (= (f19 ?v0 ?v1) f1) (= (f19 ?v0 (f28 (f71 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (=> (= (f22 ?v0 ?v1) f1) (= (f22 ?v0 (f30 (f79 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (let ((?v_0 (f71 ?v0))) (=> (not (= (f19 ?v0 ?v1) f1)) (=> (not (= (f19 ?v0 ?v2) f1)) (= (= (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (let ((?v_0 (f79 ?v0))) (=> (not (= (f22 ?v0 ?v1) f1)) (=> (not (= (f22 ?v0 ?v2) f1)) (= (= (f30 ?v_0 ?v1) (f30 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S4)) (= (= (f17 (f28 (f71 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f17 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (= (= (f20 (f30 (f79 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f20 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S13)) (= (= (f19 ?v0 (f28 (f71 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f19 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S14)) (= (= (f22 ?v0 (f30 (f79 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f22 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S13)) (let ((?v_1 (f71 ?v0)) (?v_0 (f71 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S14)) (let ((?v_1 (f79 ?v0)) (?v_0 (f79 ?v1))) (= (f30 ?v_1 (f30 ?v_0 ?v2)) (f30 ?v_0 (f30 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S13)) (let ((?v_0 (f71 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S14)) (let ((?v_0 (f79 ?v0))) (let ((?v_1 (f30 ?v_0 ?v1))) (= (f30 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S4) (?v1 S13)) (= (f28 (f71 ?v0) (f83 ?v1)) (f83 (f28 (f36 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S14)) (= (f30 (f79 ?v0) (f84 ?v1)) (f84 (f30 (f37 ?v0) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S13)) (= (f28 (f71 ?v0) ?v1) (f83 (f28 (f32 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S14)) (= (f30 (f79 ?v0) ?v1) (f84 (f30 (f33 ?v0) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S13)) (= (f19 ?v0 (f28 (f71 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S14)) (= (f22 ?v0 (f30 (f79 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S4) (?v3 S3)) (=> (= (f22 ?v0 ?v1) f1) (=> (= ?v2 (f3 ?v3 ?v0)) (= (f19 ?v2 (f68 (f69 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S2) (?v3 S23)) (=> (= (f19 ?v0 ?v1) f1) (=> (= ?v2 (f46 ?v3 ?v0)) (= (f22 ?v2 (f77 (f78 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2) (?v3 S24)) (=> (= (f22 ?v0 ?v1) f1) (=> (= ?v2 (f42 ?v3 ?v0)) (= (f22 ?v2 (f30 (f80 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S4) (?v3 S20)) (=> (= (f19 ?v0 ?v1) f1) (=> (= ?v2 (f41 ?v3 ?v0)) (= (f19 ?v2 (f28 (f81 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S3)) (=> (= (f22 ?v0 ?v1) f1) (= (f19 (f3 ?v2 ?v0) (f68 (f69 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S23)) (=> (= (f19 ?v0 ?v1) f1) (= (f22 (f46 ?v2 ?v0) (f77 (f78 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S24)) (=> (= (f22 ?v0 ?v1) f1) (= (f22 (f42 ?v2 ?v0) (f30 (f80 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S20)) (=> (= (f19 ?v0 ?v1) f1) (= (f19 (f41 ?v2 ?v0) (f28 (f81 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S14)) (= (= (f19 ?v0 (f68 (f69 ?v1) ?v2)) f1) (exists ((?v3 S2)) (and (= (f22 ?v3 ?v2) f1) (= ?v0 (f3 ?v1 ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S13)) (= (= (f22 ?v0 (f77 (f78 ?v1) ?v2)) f1) (exists ((?v3 S4)) (and (= (f19 ?v3 ?v2) f1) (= ?v0 (f46 ?v1 ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S24) (?v2 S14)) (= (= (f22 ?v0 (f30 (f80 ?v1) ?v2)) f1) (exists ((?v3 S2)) (and (= (f22 ?v3 ?v2) f1) (= ?v0 (f42 ?v1 ?v3)))))))
(assert (forall ((?v0 S4) (?v1 S20) (?v2 S13)) (= (= (f19 ?v0 (f28 (f81 ?v1) ?v2)) f1) (exists ((?v3 S4)) (and (= (f19 ?v3 ?v2) f1) (= ?v0 (f41 ?v1 ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (= (f22 ?v0 ?v1) f1) (= (f22 ?v0 (f30 (f82 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (= (f19 ?v0 ?v1) f1) (= (f19 ?v0 (f28 (f66 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (=> (= (f22 ?v0 ?v1) f1) (= (f22 ?v0 (f30 (f82 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (=> (= (f19 ?v0 ?v1) f1) (= (f19 ?v0 (f28 (f66 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S13) (?v1 S4) (?v2 S13)) (=> (= (f17 ?v0 ?v1) f1) (= (f17 (f28 (f66 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S2) (?v2 S14)) (=> (= (f20 ?v0 ?v1) f1) (= (f20 (f30 (f82 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S4) (?v2 S13)) (=> (= (f17 ?v0 ?v1) f1) (= (f17 (f28 (f66 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S2) (?v2 S14)) (=> (= (f20 ?v0 ?v1) f1) (= (f20 (f30 (f82 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (= (forall ((?v3 S2)) (=> (= (f22 ?v3 (f30 (f82 ?v0) ?v1)) f1) (= (f20 ?v2 ?v3) f1))) (and (forall ((?v3 S2)) (=> (= (f22 ?v3 ?v0) f1) (= (f20 ?v2 ?v3) f1))) (forall ((?v3 S2)) (=> (= (f22 ?v3 ?v1) f1) (= (f20 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (= (forall ((?v3 S4)) (=> (= (f19 ?v3 (f28 (f66 ?v0) ?v1)) f1) (= (f17 ?v2 ?v3) f1))) (and (forall ((?v3 S4)) (=> (= (f19 ?v3 ?v0) f1) (= (f17 ?v2 ?v3) f1))) (forall ((?v3 S4)) (=> (= (f19 ?v3 ?v1) f1) (= (f17 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (= (exists ((?v3 S2)) (and (= (f22 ?v3 (f30 (f82 ?v0) ?v1)) f1) (= (f20 ?v2 ?v3) f1))) (or (exists ((?v3 S2)) (and (= (f22 ?v3 ?v0) f1) (= (f20 ?v2 ?v3) f1))) (exists ((?v3 S2)) (and (= (f22 ?v3 ?v1) f1) (= (f20 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (= (exists ((?v3 S4)) (and (= (f19 ?v3 (f28 (f66 ?v0) ?v1)) f1) (= (f17 ?v2 ?v3) f1))) (or (exists ((?v3 S4)) (and (= (f19 ?v3 ?v0) f1) (= (f17 ?v2 ?v3) f1))) (exists ((?v3 S4)) (and (= (f19 ?v3 ?v1) f1) (= (f17 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f66 ?v0))) (= (f28 (f66 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f66 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f82 ?v0))) (= (f30 (f82 (f30 ?v_0 ?v1)) ?v2) (f30 ?v_0 (f30 (f82 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S14)) (= (= (f22 ?v0 (f30 (f82 ?v1) ?v2)) f1) (or (= (f22 ?v0 ?v1) f1) (= (f22 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S13) (?v2 S13)) (= (= (f19 ?v0 (f28 (f66 ?v1) ?v2)) f1) (or (= (f19 ?v0 ?v1) f1) (= (f19 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_1 (f66 ?v0)) (?v_0 (f66 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_1 (f82 ?v0)) (?v_0 (f82 ?v1))) (= (f30 ?v_1 (f30 ?v_0 ?v2)) (f30 ?v_0 (f30 ?v_1 ?v2))))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f66 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (let ((?v_0 (f82 ?v0))) (let ((?v_1 (f30 ?v_0 ?v1))) (= (f30 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (f28 (f66 ?v0) ?v1) (f28 (f66 ?v1) ?v0))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f30 (f82 ?v0) ?v1) (f30 (f82 ?v1) ?v0))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f30 (f82 ?v0) ?v1) (f84 (f30 (f31 ?v0) ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (f28 (f66 ?v0) ?v1) (f83 (f28 (f29 ?v0) ?v1)))))
(assert (forall ((?v0 S13)) (= (f28 (f66 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S14)) (= (f30 (f82 ?v0) ?v0) ?v0)))
(assert (forall ((?v0 S4) (?v1 S13)) (= (f28 (f71 ?v0) ?v1) (f83 (f28 (f32 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S14)) (= (f30 (f79 ?v0) ?v1) (f84 (f30 (f33 ?v0) ?v1)))))
(assert (forall ((?v0 S14)) (= (f30 (f80 f62) ?v0) ?v0)))
(assert (forall ((?v0 S13)) (= (f28 (f81 f61) ?v0) ?v0)))
(assert (forall ((?v0 S23) (?v1 S3) (?v2 S14)) (= (f77 (f78 ?v0) (f68 (f69 ?v1) ?v2)) (f30 (f80 (f43 (f44 f45 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S20) (?v1 S3) (?v2 S14)) (= (f28 (f81 ?v0) (f68 (f69 ?v1) ?v2)) (f68 (f69 (f38 (f39 f40 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S3) (?v1 S23) (?v2 S13)) (= (f68 (f69 ?v0) (f77 (f78 ?v1) ?v2)) (f28 (f81 (f47 (f48 f49 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S3) (?v1 S24) (?v2 S14)) (= (f68 (f69 ?v0) (f30 (f80 ?v1) ?v2)) (f68 (f69 (f50 (f51 f52 ?v0) ?v1)) ?v2))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S2)) (= (= (f20 (f30 (f82 (f21 ?v0)) (f21 ?v1)) ?v2) f1) (= (f22 ?v2 (f30 (f82 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S4)) (= (= (f17 (f28 (f66 (f18 ?v0)) (f18 ?v1)) ?v2) f1) (= (f19 ?v2 (f28 (f66 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (f83 (f28 (f34 ?v0) ?v1)) (f28 (f66 (f83 ?v0)) (f83 ?v1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f84 (f30 (f35 ?v0) ?v1)) (f30 (f82 (f84 ?v0)) (f84 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (= (f28 (f71 ?v0) f73) (f28 (f71 ?v1) f73)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f30 (f79 ?v0) f76) (f30 (f79 ?v1) f76)) (= ?v0 ?v1))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (= (f19 ?v0 (f28 (f71 ?v1) f73)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f22 ?v0 (f30 (f79 ?v1) f76)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(check-sat)
(exit)