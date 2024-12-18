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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 () S2)
(declare-fun f5 (S4 S5) S3)
(declare-fun f6 (S6 S3) S4)
(declare-fun f7 () S6)
(declare-fun f8 () S3)
(declare-fun f9 () S5)
(declare-fun f10 () S3)
(declare-fun f11 (S7 S8) S1)
(declare-fun f12 (S9 S3) S7)
(declare-fun f13 (S10 S11) S9)
(declare-fun f14 () S10)
(declare-fun f15 () S11)
(declare-fun f16 () S8)
(declare-fun f17 () S12)
(declare-fun f18 (S13 S1) S5)
(declare-fun f19 () S13)
(declare-fun f20 (S15 S14) S5)
(declare-fun f21 () S15)
(declare-fun f22 (S17 S16) S5)
(declare-fun f23 () S17)
(declare-fun f24 () S4)
(declare-fun f25 (S18 S5) S5)
(declare-fun f26 () S18)
(declare-fun f27 () S17)
(declare-fun f28 () S18)
(declare-fun f29 (S19 S5) S12)
(declare-fun f30 () S19)
(declare-fun f31 () S13)
(declare-fun f32 () S11)
(declare-fun f33 () S3)
(declare-fun f34 () S8)
(declare-fun f35 (S20 S8) S8)
(declare-fun f36 (S21 S8) S20)
(declare-fun f37 () S21)
(declare-fun f38 () S8)
(declare-fun f39 (S11 S5) S8)
(declare-fun f40 (S23 S22) S16)
(declare-fun f41 (S24 S22) S23)
(declare-fun f42 () S24)
(declare-fun f43 () S18)
(declare-fun f44 (S25 S3) S5)
(declare-fun f45 () S25)
(declare-fun f46 (S26 S8) S11)
(declare-fun f47 (S27 S5) S26)
(declare-fun f48 (S28 S11) S27)
(declare-fun f49 () S28)
(declare-fun f50 () S25)
(declare-fun f51 (S29 S3) S3)
(declare-fun f52 () S29)
(declare-fun f53 (S30 S3) S6)
(declare-fun f54 () S30)
(declare-fun f55 (S31 S12) S1)
(declare-fun f56 (S32 S12) S31)
(declare-fun f57 () S32)
(declare-fun f58 (S34 S31) S1)
(declare-fun f59 (S35 S33) S34)
(declare-fun f60 () S35)
(declare-fun f61 (S36 S5) S1)
(declare-fun f62 (S37 S5) S36)
(declare-fun f63 () S37)
(declare-fun f64 () S11)
(declare-fun f65 (S38 S8) S5)
(declare-fun f66 () S38)
(declare-fun f67 () S38)
(declare-fun f68 (S39 S12) S12)
(declare-fun f69 (S40 S12) S39)
(declare-fun f70 () S40)
(declare-fun f71 () S30)
(declare-fun f72 () S39)
(declare-fun f73 (S33 S12) S5)
(declare-fun f74 () S33)
(declare-fun f75 (S41 S5) S6)
(declare-fun f76 () S41)
(declare-fun f77 (S42 S5) S18)
(declare-fun f78 () S42)
(declare-fun f79 () S32)
(declare-fun f80 () S40)
(declare-fun f81 () S37)
(assert (not (= f1 f2)))
(assert (not (= (f3 f4 (f5 (f6 f7 f8) f9)) f1)))
(assert (= (f3 f4 f8) f1))
(assert (= (f3 f4 f10) f1))
(assert (= (f3 f4 f8) f1))
(assert (forall ((?v0 S3) (?v1 S5)) (=> (= (f3 f4 ?v0) f1) (= (f3 f4 (f5 (f6 f7 ?v0) ?v1)) f1))))
(assert (= (f11 (f12 (f13 f14 f15) f8) f16) f1))
(assert (forall ((?v0 S5)) (= (= f9 ?v0) (= ?v0 f9))))
(assert (forall ((?v0 S12)) (= (= f17 ?v0) (= ?v0 f17))))
(assert (= (f18 f19 f1) f9))
(assert (= (f18 f19 f2) f9))
(assert (forall ((?v0 S14)) (= (f20 f21 ?v0) f9)))
(assert (forall ((?v0 S16)) (= (f22 f23 ?v0) f9)))
(assert (forall ((?v0 S5)) (= (f3 f4 (f5 f24 ?v0)) f1)))
(assert (= (f25 f26 f9) f9))
(assert (forall ((?v0 S16)) (= (f22 f27 ?v0) f9)))
(assert (= (f25 f28 f9) f9))
(assert (= (f29 f30 f9) f17))
(assert (= (f18 f31 f1) f9))
(assert (= (f18 f31 f2) f9))
(assert (= (f11 (f12 (f13 f14 f32) f33) f34) f1))
(assert (= (f11 (f12 (f13 f14 f15) f10) (f35 (f36 f37 f16) f38)) f1))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f25 f28 ?v0) (f25 f28 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f29 f30 ?v0) (f29 f30 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S1)) (= (f18 f31 ?v0) f9)))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S8)) (=> (= (f39 ?v0 ?v1) ?v2) (= (f11 (f12 (f13 f14 ?v0) (f5 f24 ?v1)) ?v2) f1))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S8)) (=> (= (f11 (f12 (f13 f14 ?v0) (f5 f24 ?v1)) ?v2) f1) (=> (=> (= (f39 ?v0 ?v1) ?v2) false) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f5 f24 ?v0) (f5 f24 ?v1)) (= ?v0 ?v1))))
(assert (= f17 (f29 f30 f9)))
(assert (= (f29 f30 f9) f17))
(assert (forall ((?v0 S5)) (= (= (f29 f30 ?v0) f17) (= ?v0 f9))))
(assert (forall ((?v0 S22) (?v1 S22)) (= (f22 f27 (f40 (f41 f42 ?v0) ?v1)) f9)))
(assert (forall ((?v0 S22) (?v1 S22)) (= (f22 f23 (f40 (f41 f42 ?v0) ?v1)) f9)))
(assert (= (f25 f43 f9) f9))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f29 f30 ?v0) (f29 f30 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f29 f30 ?v0) (f29 f30 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S22) (?v1 S22) (?v2 S22) (?v3 S22)) (= (= (f40 (f41 f42 ?v0) ?v1) (f40 (f41 f42 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S1) (?v1 S5) (?v2 S5)) (let ((?v_0 (= ?v0 f1))) (= (ite ?v_0 (f29 f30 ?v1) (f29 f30 ?v2)) (f29 f30 (ite ?v_0 ?v1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (= (= (f35 (f36 f37 ?v0) ?v1) (f35 (f36 f37 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5)) (= (f25 f43 ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (f44 f45 (f5 f24 ?v0)) f9)))
(assert (forall ((?v0 S16)) (=> (forall ((?v1 S22) (?v2 S22)) (=> (= ?v0 (f40 (f41 f42 ?v1) ?v2)) false)) false)))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S8) (?v3 S5) (?v4 S8)) (=> (= (f11 (f12 (f13 f14 ?v0) ?v1) ?v2) f1) (= (f11 (f12 (f13 f14 (f46 (f47 (f48 f49 ?v0) ?v3) ?v4)) (f5 (f6 f7 ?v1) ?v3)) ?v2) f1))))
(assert (forall ((?v0 S5)) (= (f44 f50 (f5 f24 ?v0)) f9)))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S11) (?v3 S8)) (=> (= ?v0 ?v1) (= (f39 (f46 (f47 (f48 f49 ?v2) ?v0) ?v3) ?v1) ?v3))))
(assert (forall ((?v0 S11) (?v1 S8) (?v2 S3) (?v3 S8)) (=> (= (f11 (f12 (f13 f14 (f46 (f47 (f48 f49 ?v0) f9) ?v1)) ?v2) ?v3) f1) (= (f11 (f12 (f13 f14 ?v0) (f51 f52 ?v2)) (f35 (f36 f37 ?v1) ?v3)) f1))))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S8)) (=> (= (f11 (f12 (f13 f14 ?v0) (f51 f52 ?v1)) ?v2) f1) (=> (forall ((?v3 S8) (?v4 S8)) (=> (= ?v2 (f35 (f36 f37 ?v3) ?v4)) (=> (= (f11 (f12 (f13 f14 (f46 (f47 (f48 f49 ?v0) f9) ?v3)) ?v1) ?v4) f1) false))) false))))
(assert (forall ((?v0 S3) (?v1 S11) (?v2 S5) (?v3 S8) (?v4 S8) (?v5 S3)) (=> (= (f3 f4 ?v0) f1) (=> (= (f11 (f12 (f13 f14 (f46 (f47 (f48 f49 ?v1) ?v2) ?v3)) ?v0) ?v4) f1) (=> (= (f3 f4 ?v5) f1) (=> (= (f11 (f12 (f13 f14 ?v1) ?v5) ?v3) f1) (= (f3 f4 (f5 (f6 (f53 f54 ?v0) ?v5) ?v2)) f1)))))))
(assert (forall ((?v0 S5)) (= (= (f55 (f56 f57 (f29 f30 ?v0)) f17) f1) (= ?v0 f9))))
(assert (forall ((?v0 S33) (?v1 S31)) (= (f58 (f59 f60 ?v0) ?v1) f1)))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S8) (?v3 S11) (?v4 S3) (?v5 S8) (?v6 S5)) (let ((?v_0 (f13 f14 ?v3))) (=> (= (f11 (f12 (f13 f14 ?v0) ?v1) ?v2) f1) (=> (= (f11 (f12 ?v_0 ?v4) ?v5) f1) (=> (= ?v0 (f46 (f47 (f48 f49 ?v3) ?v6) ?v5)) (= (f11 (f12 ?v_0 (f5 (f6 (f53 f54 ?v1) ?v4) ?v6)) ?v2) f1)))))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f61 (f62 f63 (f25 f28 ?v0)) (f25 f28 ?v1)) f1) (= (f61 (f62 f63 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f55 (f56 f57 (f29 f30 ?v0)) (f29 f30 ?v1)) f1) (= (f61 (f62 f63 ?v0) ?v1) f1))))
(assert (forall ((?v0 S12)) (= (f55 (f56 f57 ?v0) ?v0) f1)))
(assert (forall ((?v0 S12) (?v1 S12)) (or (= (f55 (f56 f57 ?v0) ?v1) f1) (= (f55 (f56 f57 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f51 f52 ?v0) (f51 f52 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f39 f64 ?v0) (f39 f64 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f56 f57 ?v0))) (=> (= (f55 ?v_0 ?v1) f1) (=> (= (f55 (f56 f57 ?v1) ?v2) f1) (= (f55 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f55 (f56 f57 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S33) (?v1 S31)) (= (= (f58 (f59 f60 ?v0) ?v1) f1) true)))
(assert (= (f55 (f56 f57 f17) f17) f1))
(assert (forall ((?v0 S5) (?v1 S3)) (not (= (f5 f24 ?v0) (f51 f52 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S5)) (not (= (f51 f52 ?v0) (f5 f24 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S3)) (= (f5 (f6 (f53 f54 (f5 f24 ?v0)) ?v1) ?v0) ?v1)))
(assert (forall ((?v0 S3) (?v1 S5) (?v2 S3)) (= (f5 (f6 (f53 f54 (f5 (f6 f7 ?v0) ?v1)) ?v2) ?v1) ?v0)))
(assert (forall ((?v0 S5)) (= (f61 (f62 f63 f9) (f25 f28 ?v0)) f1)))
(assert (forall ((?v0 S5)) (= (f55 (f56 f57 f17) (f29 f30 ?v0)) f1)))
(assert (forall ((?v0 S5)) (= (f61 (f62 f63 f9) (f25 f28 ?v0)) f1)))
(assert (forall ((?v0 S5)) (= (f55 (f56 f57 f17) (f29 f30 ?v0)) f1)))
(assert (forall ((?v0 S5)) (= (f55 (f56 f57 f17) (f29 f30 ?v0)) f1)))
(assert (forall ((?v0 S5)) (= (f55 (f56 f57 f17) (f29 f30 ?v0)) f1)))
(assert (forall ((?v0 S31)) (= (exists ((?v1 S12)) (and (= (f55 (f56 f57 f17) ?v1) f1) (= (f55 ?v0 ?v1) f1))) (exists ((?v1 S5)) (= (f55 ?v0 (f29 f30 ?v1)) f1)))))
(assert (forall ((?v0 S31)) (= (forall ((?v1 S12)) (=> (= (f55 (f56 f57 f17) ?v1) f1) (= (f55 ?v0 ?v1) f1))) (forall ((?v1 S5)) (= (f55 ?v0 (f29 f30 ?v1)) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S5)) (not (= (f35 (f36 f37 ?v0) ?v1) (f39 f64 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S8) (?v2 S8)) (not (= (f39 f64 ?v0) (f35 (f36 f37 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S5) (?v2 S5)) (=> (= (f3 f4 ?v0) f1) (= (f3 f4 (f5 (f6 (f53 f54 ?v0) (f5 f24 ?v1)) ?v2)) f1))))
(assert (forall ((?v0 S3)) (=> (= (f3 f4 ?v0) f1) (= (f3 f4 (f51 f52 ?v0)) f1))))
(assert (forall ((?v0 S11) (?v1 S3) (?v2 S8)) (=> (= (f11 (f12 (f13 f14 ?v0) (f51 f52 ?v1)) ?v2) f1) (=> (forall ((?v3 S8) (?v4 S8)) (=> (= (f11 (f12 (f13 f14 (f46 (f47 (f48 f49 ?v0) f9) ?v3)) ?v1) ?v4) f1) false)) false))))
(assert (forall ((?v0 S12)) (=> (= (f55 (f56 f57 f17) ?v0) f1) (exists ((?v1 S5)) (= ?v0 (f29 f30 ?v1))))))
(assert (forall ((?v0 S12)) (=> (= (f55 (f56 f57 f17) ?v0) f1) (=> (forall ((?v1 S5)) (=> (= ?v0 (f29 f30 ?v1)) false)) false))))
(assert (forall ((?v0 S12)) (= (f55 (f56 f57 ?v0) ?v0) f1)))
(assert (forall ((?v0 S5)) (= (f61 (f62 f63 ?v0) ?v0) f1)))
(assert (forall ((?v0 S12) (?v1 S1) (?v2 S1)) (let ((?v_0 (= (f55 (f56 f57 f17) ?v0) f1)) (?v_1 (= ?v1 f1)) (?v_2 (= ?v2 f1))) (=> (=> ?v_0 (= ?v_1 ?v_2)) (= (=> ?v_0 ?v_1) (=> ?v_0 ?v_2))))))
(assert (forall ((?v0 S12) (?v1 S1) (?v2 S1)) (let ((?v_0 (= (f55 (f56 f57 f17) ?v0) f1)) (?v_1 (= ?v1 f1)) (?v_2 (= ?v2 f1))) (=> (=> ?v_0 (= ?v_1 ?v_2)) (= (and ?v_0 ?v_1) (and ?v_0 ?v_2))))))
(assert (forall ((?v0 S5)) (= (f61 (f62 f63 f9) ?v0) f1)))
(assert (forall ((?v0 S5)) (= (f61 (f62 f63 ?v0) ?v0) f1)))
(assert (forall ((?v0 S5) (?v1 S5)) (or (= (f61 (f62 f63 ?v0) ?v1) f1) (= (f61 (f62 f63 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= ?v0 ?v1) (= (f61 (f62 f63 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f61 ?v_0 ?v1) f1) (=> (= (f61 (f62 f63 ?v1) ?v2) f1) (= (f61 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (=> (= (f61 (f62 f63 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5)) (= (= (f61 (f62 f63 ?v0) f9) f1) (= ?v0 f9))))
(assert (forall ((?v0 S5)) (= (= (f61 (f62 f63 f9) ?v0) f1) true)))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f55 (f56 f57 (f29 f30 ?v0)) (f29 f30 ?v1)) f1) (= (f61 (f62 f63 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f55 (f56 f57 (f29 f30 ?v0)) (f29 f30 ?v1)) f1) (= (f61 (f62 f63 ?v0) ?v1) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (or (= (f55 (f56 f57 ?v0) ?v1) f1) (= (f55 (f56 f57 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (or (= (f61 (f62 f63 ?v0) ?v1) f1) (= (f61 (f62 f63 ?v1) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= ?v0 ?v1) (and (= (f55 (f56 f57 ?v0) ?v1) f1) (= (f55 (f56 f57 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= ?v0 ?v1) (and (= (f61 (f62 f63 ?v0) ?v1) f1) (= (f61 (f62 f63 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= ?v0 ?v1) (= (f55 (f56 f57 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= ?v0 ?v1) (= (f61 (f62 f63 ?v0) ?v1) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (= (= (f55 (f56 f57 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (= (= (f61 (f62 f63 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= ?v0 ?v1) (=> (= (f55 (f56 f57 ?v1) ?v2) f1) (= (f55 (f56 f57 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= ?v0 ?v1) (=> (= (f61 (f62 f63 ?v1) ?v2) f1) (= (f61 (f62 f63 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f56 f57 ?v2))) (=> (= ?v0 ?v1) (=> (= (f55 ?v_0 ?v1) f1) (= (f55 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f63 ?v2))) (=> (= ?v0 ?v1) (=> (= (f61 ?v_0 ?v1) f1) (= (f61 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f56 f57 ?v0))) (=> (= (f55 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f55 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f61 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f61 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f55 (f56 f57 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f61 (f62 f63 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f55 (f56 f57 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (=> (= (f61 (f62 f63 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f56 f57 ?v0))) (=> (= (f55 ?v_0 ?v1) f1) (=> (= (f55 (f56 f57 ?v1) ?v2) f1) (= (f55 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f61 ?v_0 ?v1) f1) (=> (= (f61 (f62 f63 ?v1) ?v2) f1) (= (f61 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f55 (f56 f57 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (=> (= (f61 (f62 f63 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f56 f57 ?v2))) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f55 ?v_0 ?v0) f1) (= (f55 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f63 ?v2))) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (=> (= (f61 ?v_0 ?v0) f1) (= (f61 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (=> (= (f55 (f56 f57 ?v0) ?v1) f1) false) (=> (=> (= (f55 (f56 f57 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (=> (= (f61 (f62 f63 ?v0) ?v1) f1) false) (=> (=> (= (f61 (f62 f63 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S5)) (= (f65 f66 (f39 f64 ?v0)) f9)))
(assert (forall ((?v0 S5)) (= (f65 f67 (f39 f64 ?v0)) f9)))
(assert (forall ((?v0 S12)) (=> (= (f55 (f56 f57 f17) ?v0) f1) (=> (forall ((?v1 S5)) (=> (= ?v0 (f29 f30 ?v1)) false)) false))))
(assert (forall ((?v0 S8)) (=> (forall ((?v1 S5)) (=> (= ?v0 (f39 f64 ?v1)) false)) (=> (forall ((?v1 S8) (?v2 S8)) (=> (= ?v0 (f35 (f36 f37 ?v1) ?v2)) false)) false))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f56 f57 f17))) (=> (= (f55 ?v_0 ?v0) f1) (=> (= (f55 ?v_0 ?v1) f1) (= (f55 ?v_0 (f68 (f69 f70 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S12) (?v1 S39) (?v2 S12) (?v3 S12)) (=> (= ?v0 (f68 ?v1 ?v2)) (=> (= (f55 (f56 f57 ?v3) ?v2) f1) (=> (forall ((?v4 S12) (?v5 S12)) (=> (= (f55 (f56 f57 ?v5) ?v4) f1) (= (f55 (f56 f57 (f68 ?v1 ?v5)) (f68 ?v1 ?v4)) f1))) (= (f55 (f56 f57 (f68 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S5) (?v1 S18) (?v2 S5) (?v3 S5)) (=> (= ?v0 (f25 ?v1 ?v2)) (=> (= (f61 (f62 f63 ?v3) ?v2) f1) (=> (forall ((?v4 S5) (?v5 S5)) (=> (= (f61 (f62 f63 ?v5) ?v4) f1) (= (f61 (f62 f63 (f25 ?v1 ?v5)) (f25 ?v1 ?v4)) f1))) (= (f61 (f62 f63 (f25 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S39) (?v3 S12)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f68 ?v2 ?v0) ?v3) (=> (forall ((?v4 S12) (?v5 S12)) (=> (= (f55 (f56 f57 ?v5) ?v4) f1) (= (f55 (f56 f57 (f68 ?v2 ?v5)) (f68 ?v2 ?v4)) f1))) (= (f55 (f56 f57 ?v3) (f68 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S18) (?v3 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (=> (= (f25 ?v2 ?v0) ?v3) (=> (forall ((?v4 S5) (?v5 S5)) (=> (= (f61 (f62 f63 ?v5) ?v4) f1) (= (f61 (f62 f63 (f25 ?v2 ?v5)) (f25 ?v2 ?v4)) f1))) (= (f61 (f62 f63 ?v3) (f25 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 (f53 f71 ?v0) ?v1) f9) (f5 (f6 (f53 f54 ?v0) ?v1) f9))))
(assert (forall ((?v0 S12)) (= (= (f55 (f56 f57 (f68 f72 ?v0)) f17) f1) (= (f55 (f56 f57 ?v0) f17) f1))))
(assert (forall ((?v0 S12)) (let ((?v_0 (f56 f57 f17))) (= (= (f55 ?v_0 (f68 f72 ?v0)) f1) (= (f55 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S12)) (= (= ?v0 (f73 f74 ?v1)) (ite (= (f55 (f56 f57 f17) ?v1) f1) (= ?v1 (f29 f30 ?v0)) (= ?v0 f9)))))
(assert (forall ((?v0 S5)) (= (f73 f74 (f29 f30 ?v0)) ?v0)))
(assert (forall ((?v0 S5)) (let ((?v_0 (f29 f30 ?v0))) (= (f68 f72 ?v_0) ?v_0))))
(assert (forall ((?v0 S1) (?v1 S12) (?v2 S12)) (let ((?v_0 (= ?v0 f1))) (= (ite ?v_0 (f73 f74 ?v1) (f73 f74 ?v2)) (f73 f74 (ite ?v_0 ?v1 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f68 f72 ?v0) (f68 f72 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S12)) (=> (= (f55 (f56 f57 f17) ?v0) f1) (= (f29 f30 (f73 f74 ?v0)) (f68 f72 ?v0)))))
(assert (= f9 (f73 f74 f17)))
(assert (= (f73 f74 f17) f9))
(assert (= (f58 (f59 f60 f74) (f56 f57 f17)) f1))
(assert (forall ((?v0 S36)) (= (exists ((?v1 S5)) (= (f61 ?v0 ?v1) f1)) (exists ((?v1 S12)) (and (= (f55 (f56 f57 f17) ?v1) f1) (= (f61 ?v0 (f73 f74 ?v1)) f1))))))
(assert (forall ((?v0 S36)) (= (forall ((?v1 S5)) (= (f61 ?v0 ?v1) f1)) (forall ((?v1 S12)) (=> (= (f55 (f56 f57 f17) ?v1) f1) (= (f61 ?v0 (f73 f74 ?v1)) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f56 f57 f17))) (=> (= (f55 ?v_0 ?v0) f1) (=> (= (f55 ?v_0 ?v1) f1) (= (= (f73 f74 ?v0) (f73 f74 ?v1)) (= ?v0 ?v1)))))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f56 f57 f17))) (=> (= (f55 ?v_0 ?v0) f1) (=> (= (f55 ?v_0 ?v1) f1) (= (= (f73 f74 ?v0) (f73 f74 ?v1)) (= ?v0 ?v1)))))))
(assert (forall ((?v0 S12)) (= (= (f68 f72 ?v0) f17) (= ?v0 f17))))
(assert (forall ((?v0 S12)) (= (= f17 (f68 f72 ?v0)) (= ?v0 f17))))
(assert (= (f68 f72 f17) f17))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f55 (f56 f57 (f68 f72 ?v0)) (f68 f72 ?v1)) f1) (= (f55 (f56 f57 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5)) (let ((?v_0 (f29 f30 ?v0))) (= (f68 f72 ?v_0) ?v_0))))
(assert (forall ((?v0 S12)) (=> (= (f55 (f56 f57 ?v0) f17) f1) (= (f73 f74 ?v0) f9))))
(assert (forall ((?v0 S12)) (= (= (f73 f74 ?v0) f9) (= (f55 (f56 f57 ?v0) f17) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f56 f57 f17))) (=> (= (f55 ?v_0 ?v0) f1) (=> (= (f55 ?v_0 ?v1) f1) (= (= (f61 (f62 f63 (f73 f74 ?v0)) (f73 f74 ?v1)) f1) (= (f55 (f56 f57 ?v0) ?v1) f1)))))))
(assert (forall ((?v0 S12)) (=> (= (f55 (f56 f57 f17) ?v0) f1) (= (f29 f30 (f73 f74 ?v0)) ?v0))))
(assert (forall ((?v0 S5) (?v1 S12)) (= (= (f29 f30 ?v0) ?v1) (and (= ?v0 (f73 f74 ?v1)) (= (f55 (f56 f57 f17) ?v1) f1)))))
(assert (forall ((?v0 S12)) (= (f29 f30 (f73 f74 ?v0)) (ite (= (f55 (f56 f57 f17) ?v0) f1) ?v0 f17))))
(assert (forall ((?v0 S12) (?v1 S5)) (= (= (f73 f74 ?v0) ?v1) (ite (= (f55 (f56 f57 f17) ?v0) f1) (= ?v0 (f29 f30 ?v1)) (= ?v1 f9)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S5)) (= (f5 (f6 (f53 f71 ?v0) ?v1) ?v2) (f5 (f6 (f53 f54 ?v0) (f5 (f6 (f75 f76 ?v2) ?v1) f9)) ?v2))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f56 f57 f17))) (=> (= (f55 ?v_0 ?v0) f1) (=> (= (f55 ?v_0 ?v1) f1) (= (f25 (f77 f78 (f73 f74 ?v0)) (f73 f74 ?v1)) (f73 f74 (f68 (f69 f70 ?v0) ?v1))))))))
(assert (forall ((?v0 S36) (?v1 S12)) (= (= (f61 ?v0 (f73 f74 ?v1)) f1) (and (forall ((?v2 S5)) (=> (= ?v1 (f29 f30 ?v2)) (= (f61 ?v0 ?v2) f1))) (=> (= (f55 (f56 f79 ?v1) f17) f1) (= (f61 ?v0 f9) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (or (= (f55 (f56 f79 f17) ?v0) f1) (= (f55 (f56 f57 f17) ?v1) f1)) (= (= (f61 (f62 f63 (f73 f74 ?v0)) (f73 f74 ?v1)) f1) (= (f55 (f56 f57 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f55 (f56 f79 (f68 f72 ?v0)) (f68 f72 ?v1)) f1) (= (f55 (f56 f79 ?v0) ?v1) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (f68 f72 (f68 (f69 f80 ?v0) ?v1)) (f68 (f69 f80 (f68 f72 ?v0)) (f68 f72 ?v1)))))
(assert (forall ((?v0 S5)) (let ((?v_0 (f62 f81 f9))) (= (= (f61 ?v_0 (f25 f28 ?v0)) f1) (= (f61 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S5)) (= (= (f55 (f56 f79 f17) (f29 f30 ?v0)) f1) (= (f61 (f62 f81 f9) ?v0) f1))))
(assert (forall ((?v0 S12)) (not (= (f55 (f56 f79 ?v0) ?v0) f1))))
(assert (forall ((?v0 S5)) (not (= (f61 (f62 f81 ?v0) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (not (= ?v0 ?v1)) (or (= (f55 (f56 f79 ?v0) ?v1) f1) (= (f55 (f56 f79 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (not (= ?v0 ?v1)) (or (= (f61 (f62 f81 ?v0) ?v1) f1) (= (f61 (f62 f81 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (not (= (f55 (f56 f79 ?v0) ?v1) f1)) (or (= (f55 (f56 f79 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (not (= (f61 (f62 f81 ?v0) ?v1) f1)) (or (= (f61 (f62 f81 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (or (= (f55 (f56 f79 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f55 (f56 f79 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (or (= (f61 (f62 f81 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f61 (f62 f81 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= (f55 (f56 f79 ?v0) ?v1) f1)) (= (not (= (f55 (f56 f79 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= (f61 (f62 f81 ?v0) ?v1) f1)) (= (not (= (f61 (f62 f81 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f55 (f56 f79 ?v0) ?v1) f1) false) (=> (=> (= (f55 (f56 f79 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f61 (f62 f81 ?v0) ?v1) f1) false) (=> (=> (= (f61 (f62 f81 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (not (= (f55 (f56 f79 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (not (= (f61 (f62 f81 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (= (not (= (f55 (f56 f79 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (= (not (= (f61 (f62 f81 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S1)) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (= (=> (= (f55 (f56 f79 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S1)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (= (=> (= (f61 (f62 f81 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (=> (= (f55 (f56 f79 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (=> (= (f61 (f62 f81 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (=> (= (f55 (f56 f79 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (=> (= (f61 (f62 f81 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= ?v0 ?v1) (=> (= (f55 (f56 f79 ?v1) ?v2) f1) (= (f55 (f56 f79 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= ?v0 ?v1) (=> (= (f61 (f62 f81 ?v1) ?v2) f1) (= (f61 (f62 f81 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f56 f79 ?v2))) (=> (= ?v0 ?v1) (=> (= (f55 ?v_0 ?v1) f1) (= (f55 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f81 ?v2))) (=> (= ?v0 ?v1) (=> (= (f61 ?v_0 ?v1) f1) (= (f61 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f56 f79 ?v0))) (=> (= (f55 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f55 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f81 ?v0))) (=> (= (f61 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f61 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f55 (f56 f79 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f61 (f62 f81 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f56 f79 ?v0))) (=> (= (f55 ?v_0 ?v1) f1) (=> (= (f55 (f56 f79 ?v1) ?v2) f1) (= (f55 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f81 ?v0))) (=> (= (f61 ?v_0 ?v1) f1) (=> (= (f61 (f62 f81 ?v1) ?v2) f1) (= (f61 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f56 f79 ?v2))) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (=> (= (f55 ?v_0 ?v0) f1) (= (f55 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f81 ?v2))) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (=> (= (f61 ?v_0 ?v0) f1) (= (f61 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (=> (=> (not false) (= (f55 (f56 f79 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (=> (=> (not false) (= (f61 (f62 f81 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (=> (= (f55 (f56 f79 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f55 (f56 f79 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (=> (= (f61 (f62 f81 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f61 (f62 f81 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f68 (f69 f80 ?v0) ?v1) f17) (= ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= ?v0 ?v1) (= (f68 (f69 f80 ?v0) ?v1) f17))))
(assert (forall ((?v0 S12)) (= (f68 (f69 f80 ?v0) ?v0) f17)))
(assert (forall ((?v0 S12)) (= (f68 (f69 f80 ?v0) f17) ?v0)))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f77 f78 ?v0))) (= (f25 (f77 f78 (f25 ?v_0 ?v1)) ?v2) (f25 (f77 f78 (f25 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (=> (= (f68 (f69 f80 ?v0) ?v1) (f68 (f69 f80 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (=> (= (f68 (f69 f80 ?v0) ?v1) (f68 (f69 f80 ?v2) ?v3)) (= (= (f55 (f56 f79 ?v0) ?v1) f1) (= (f55 (f56 f79 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f55 (f56 f79 (f29 f30 ?v0)) (f29 f30 ?v1)) f1) (= (f61 (f62 f81 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f61 (f62 f81 (f25 f28 ?v0)) (f25 f28 ?v1)) f1) (= (f61 (f62 f81 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (= (f55 (f56 f79 (f29 f30 ?v0)) (f29 f30 ?v1)) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (= (f61 (f62 f81 (f25 f28 ?v0)) (f25 f28 ?v1)) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f55 (f56 f79 (f29 f30 ?v0)) (f29 f30 ?v1)) f1) (= (f61 (f62 f81 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 (f25 f28 ?v0)) (f25 f28 ?v1)) f1) (= (f61 (f62 f81 ?v0) ?v1) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (or (= (f55 (f56 f79 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f55 (f56 f79 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f55 (f56 f79 ?v0) ?v1) f1) (= (f55 (f56 f79 (f68 (f69 f80 ?v0) ?v1)) f17) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f55 (f56 f79 ?v0) ?v1) f1) (and (= (f55 (f56 f57 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f61 (f62 f63 (f25 (f77 f78 ?v0) ?v1)) ?v0) f1)))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f77 f78 ?v2))) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (= (f61 (f62 f63 (f25 ?v_0 ?v1)) (f25 ?v_0 ?v0)) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (= (f61 (f62 f63 (f25 (f77 f78 ?v0) ?v2)) (f25 (f77 f78 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (let ((?v_0 (f77 f78 ?v1))) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (= (f25 ?v_0 (f25 ?v_0 ?v0)) ?v0)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f61 ?v_0 ?v1) f1) (=> (= (f61 ?v_0 ?v2) f1) (= (= (f25 (f77 f78 ?v1) ?v0) (f25 (f77 f78 ?v2) ?v0)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f63 ?v0)) (?v_1 (f77 f78 ?v1))) (=> (= (f61 ?v_0 ?v1) f1) (=> (= (f61 ?v_0 ?v2) f1) (= (f25 (f77 f78 (f25 ?v_1 ?v0)) (f25 (f77 f78 ?v2) ?v0)) (f25 ?v_1 ?v2)))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f61 ?v_0 ?v1) f1) (=> (= (f61 ?v_0 ?v2) f1) (= (= (f61 (f62 f63 (f25 (f77 f78 ?v1) ?v0)) (f25 (f77 f78 ?v2) ?v0)) f1) (= (f61 (f62 f63 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f56 f79 ?v2))) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f55 ?v_0 ?v0) f1) (= (f55 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f81 ?v2))) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (=> (= (f61 ?v_0 ?v0) f1) (= (f61 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (= (f55 (f56 f79 ?v1) ?v2) f1) (= (f55 (f56 f79 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (=> (= (f61 (f62 f81 ?v1) ?v2) f1) (= (f61 (f62 f81 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (=> (= (f55 (f56 f57 ?v2) ?v0) f1) (= (f55 (f56 f79 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (=> (= (f61 (f62 f63 ?v2) ?v0) f1) (= (f61 (f62 f81 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f56 f79 ?v0))) (=> (= (f55 ?v_0 ?v1) f1) (=> (= (f55 (f56 f57 ?v1) ?v2) f1) (= (f55 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f81 ?v0))) (=> (= (f61 ?v_0 ?v1) f1) (=> (= (f61 (f62 f63 ?v1) ?v2) f1) (= (f61 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (not (= ?v1 ?v0)) (= (f55 (f56 f79 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (=> (not (= ?v1 ?v0)) (= (f61 (f62 f81 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f55 (f56 f79 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f61 (f62 f81 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (or (= (f55 (f56 f79 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (or (= (f61 (f62 f81 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (= (not (= (f55 (f56 f79 ?v0) ?v1) f1)) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (= (not (= (f61 (f62 f81 ?v0) ?v1) f1)) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f79 ?v0) ?v1) f1) (= (f55 (f56 f57 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (= (f61 (f62 f63 ?v0) ?v1) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (not (= (f55 (f56 f79 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (not (= (f61 (f62 f81 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= ?v0 ?v1)) (=> (= (f55 (f56 f57 ?v1) ?v0) f1) (= (f55 (f56 f79 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= ?v0 ?v1)) (=> (= (f61 (f62 f63 ?v1) ?v0) f1) (= (f61 (f62 f81 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= ?v0 ?v1)) (=> (= (f55 (f56 f57 ?v0) ?v1) f1) (= (f55 (f56 f79 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= ?v0 ?v1)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (= (f61 (f62 f81 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= (f55 (f56 f79 ?v0) ?v1) f1)) (= (= (f55 (f56 f57 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= (f61 (f62 f81 ?v0) ?v1) f1)) (= (= (f61 (f62 f63 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= (f55 (f56 f57 ?v0) ?v1) f1)) (= (f55 (f56 f79 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= (f61 (f62 f63 ?v0) ?v1) f1)) (= (f61 (f62 f81 ?v1) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= (f55 (f56 f79 ?v0) ?v1) f1)) (= (f55 (f56 f57 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= (f61 (f62 f81 ?v0) ?v1) f1)) (= (f61 (f62 f63 ?v1) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f55 (f56 f57 ?v0) ?v1) f1) (or (= (f55 (f56 f79 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f61 (f62 f63 ?v0) ?v1) f1) (or (= (f61 (f62 f81 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f55 (f56 f79 ?v0) ?v1) f1) (and (= (f55 (f56 f57 ?v0) ?v1) f1) (not (= (f55 (f56 f57 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f61 (f62 f81 ?v0) ?v1) f1) (and (= (f61 (f62 f63 ?v0) ?v1) f1) (not (= (f61 (f62 f63 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f55 (f56 f79 ?v0) ?v1) f1) (and (= (f55 (f56 f57 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f61 (f62 f81 ?v0) ?v1) f1) (and (= (f61 (f62 f63 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (or (= (f55 (f56 f57 ?v0) ?v1) f1) (= (f55 (f56 f79 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (or (= (f61 (f62 f63 ?v0) ?v1) f1) (= (f61 (f62 f81 ?v1) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (not (= (f55 (f56 f57 ?v0) ?v1) f1)) (= (f55 (f56 f79 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (not (= (f61 (f62 f63 ?v0) ?v1) f1)) (= (f61 (f62 f81 ?v1) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (not (= (f55 (f56 f79 ?v0) ?v1) f1)) (= (f55 (f56 f57 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (not (= (f61 (f62 f81 ?v0) ?v1) f1)) (= (f61 (f62 f63 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f25 (f77 f78 ?v0) ?v1) f9) (=> (= (f25 (f77 f78 ?v1) ?v0) f9) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5)) (= (f25 (f77 f78 ?v0) ?v0) f9)))
(assert (forall ((?v0 S5)) (= (f25 (f77 f78 ?v0) f9) ?v0)))
(assert (forall ((?v0 S5)) (= (f25 (f77 f78 f9) ?v0) f9)))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (=> (= (f68 (f69 f80 ?v0) ?v1) (f68 (f69 f80 ?v2) ?v3)) (= (= (f55 (f56 f57 ?v0) ?v1) f1) (= (f55 (f56 f57 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (= (f29 f30 (f25 (f77 f78 ?v1) ?v0)) (f68 (f69 f80 (f29 f30 ?v1)) (f29 f30 ?v0))))))
(assert (forall ((?v0 S12)) (= (= (f55 (f56 f79 (f68 f72 ?v0)) f17) f1) (= (f55 (f56 f79 ?v0) f17) f1))))
(assert (forall ((?v0 S12)) (let ((?v_0 (f56 f79 f17))) (= (= (f55 ?v_0 (f68 f72 ?v0)) f1) (= (f55 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f55 (f56 f57 ?v0) ?v1) f1) (= (f55 (f56 f57 (f68 (f69 f80 ?v0) ?v1)) f17) f1))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (f5 (f6 (f75 f76 f9) ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f63 ?v0) ?v1) f1) (= (f25 (f77 f78 ?v0) ?v1) f9))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f25 (f77 f78 ?v0) ?v1) f9) (= (f61 (f62 f63 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5)) (not (= (f61 (f62 f81 (f25 f28 ?v0)) f9) f1))))
(assert (forall ((?v0 S5)) (not (= (f55 (f56 f79 (f29 f30 ?v0)) f17) f1))))
(assert (forall ((?v0 S5)) (not (= (f55 (f56 f79 (f29 f30 ?v0)) f17) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f68 (f69 f70 (f29 f30 ?v0)) (f29 f30 ?v1)) (f29 f30 (f25 (f77 f78 ?v0) ?v1)))))
(assert (forall ((?v0 S12)) (exists ((?v1 S12)) (forall ((?v2 S12)) (=> (= (f55 (f56 f79 ?v2) ?v1) f1) (= (= (f55 (f56 f57 ?v0) ?v2) f1) false))))))
(assert (forall ((?v0 S5)) (exists ((?v1 S5)) (forall ((?v2 S5)) (=> (= (f61 (f62 f81 ?v2) ?v1) f1) (= (= (f61 (f62 f63 ?v0) ?v2) f1) false))))))
(assert (forall ((?v0 S12)) (exists ((?v1 S12)) (forall ((?v2 S12)) (=> (= (f55 (f56 f79 ?v1) ?v2) f1) (= (= (f55 (f56 f57 ?v0) ?v2) f1) true))))))
(assert (forall ((?v0 S5)) (exists ((?v1 S5)) (forall ((?v2 S5)) (=> (= (f61 (f62 f81 ?v1) ?v2) f1) (= (= (f61 (f62 f63 ?v0) ?v2) f1) true))))))
(assert (forall ((?v0 S12)) (exists ((?v1 S12)) (forall ((?v2 S12)) (=> (= (f55 (f56 f79 ?v2) ?v1) f1) (= (= (f55 (f56 f57 ?v2) ?v0) f1) true))))))
(assert (forall ((?v0 S5)) (exists ((?v1 S5)) (forall ((?v2 S5)) (=> (= (f61 (f62 f81 ?v2) ?v1) f1) (= (= (f61 (f62 f63 ?v2) ?v0) f1) true))))))
(assert (forall ((?v0 S5)) (=> (= (f61 (f62 f81 ?v0) f9) f1) false)))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S11) (?v3 S8)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (= (f39 (f46 (f47 (f48 f49 ?v2) ?v1) ?v3) ?v0) (f39 ?v2 ?v0)))))
(assert (forall ((?v0 S5)) (not (= (f61 (f62 f81 ?v0) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (not (= ?v0 ?v1)) (or (= (f61 (f62 f81 ?v0) ?v1) f1) (= (f61 (f62 f81 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f61 (f62 f81 ?v0) ?v1) f1) false) (=> (=> (= (f61 (f62 f81 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S5)) (=> (= (f61 (f62 f81 ?v0) ?v0) f1) false)))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (not (= ?v1 ?v0)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f61 (f62 f81 ?v0) ?v1) f1) (= (f61 (f62 f81 (f25 (f77 f78 ?v0) ?v2)) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f62 f81 ?v0)) (?v_1 (f77 f78 ?v2))) (=> (= (f61 ?v_0 ?v1) f1) (=> (= (f61 ?v_0 ?v2) f1) (= (f61 (f62 f81 (f25 ?v_1 ?v1)) (f25 ?v_1 ?v0)) f1))))))
(check-sat)
(exit)
