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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S6) S4)
(declare-fun f6 () S5)
(declare-fun f7 (S7 S2) S6)
(declare-fun f8 () S7)
(declare-fun f9 (S8 S2) S2)
(declare-fun f10 () S8)
(declare-fun f11 () S8)
(declare-fun f12 () S3)
(declare-fun f13 () S5)
(declare-fun f14 (S9 S8) S3)
(declare-fun f15 () S9)
(declare-fun f16 (S10 S3) S9)
(declare-fun f17 () S10)
(declare-fun f18 (S11 S7) S3)
(declare-fun f19 (S12 S5) S11)
(declare-fun f20 () S12)
(declare-fun f21 () S9)
(declare-fun f22 (S13 S3) S7)
(declare-fun f23 () S13)
(declare-fun f24 (S14 S4) S6)
(declare-fun f25 () S14)
(declare-fun f26 (S15 S3) S3)
(declare-fun f27 () S15)
(declare-fun f28 (S16 S4) S4)
(declare-fun f29 () S16)
(declare-fun f30 () S11)
(declare-fun f31 () S11)
(declare-fun f32 () S9)
(declare-fun f33 (S17 S7) S7)
(declare-fun f34 (S18 S3) S17)
(declare-fun f35 () S18)
(declare-fun f36 (S19 S6) S6)
(declare-fun f37 (S20 S4) S19)
(declare-fun f38 () S20)
(declare-fun f39 (S21 S3) S15)
(declare-fun f40 () S21)
(declare-fun f41 (S22 S4) S16)
(declare-fun f42 () S22)
(declare-fun f43 (S23 S6) S7)
(declare-fun f44 (S24 S3) S23)
(declare-fun f45 () S24)
(declare-fun f46 (S25 S4) S3)
(declare-fun f47 (S26 S3) S25)
(declare-fun f48 () S26)
(declare-fun f49 (S27 S4) S7)
(declare-fun f50 (S28 S7) S27)
(declare-fun f51 () S28)
(declare-fun f52 () S26)
(declare-fun f53 (S29 S19) S17)
(declare-fun f54 () S29)
(declare-fun f55 (S30 S16) S15)
(declare-fun f56 () S30)
(declare-fun f57 () S10)
(declare-fun f58 (S31 S8) S8)
(declare-fun f59 (S32 S8) S31)
(declare-fun f60 () S32)
(declare-fun f61 () S23)
(declare-fun f62 () S25)
(declare-fun f63 (S3) S1)
(declare-fun f64 (S8) S1)
(declare-fun f65 (S3) S1)
(declare-fun f66 (S7) S1)
(declare-fun f67 (S4 S4) S1)
(declare-fun f68 () S5)
(declare-fun f69 () S4)
(declare-fun f70 (S16) S1)
(declare-fun f71 (S19) S1)
(declare-fun f72 (S8) S1)
(declare-fun f73 (S2 S2) S1)
(declare-fun f74 (S33 S8) S7)
(declare-fun f75 (S34 S7) S33)
(declare-fun f76 () S34)
(declare-fun f77 () S2)
(declare-fun f78 () S4)
(declare-fun f79 () S6)
(declare-fun f80 () S16)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 f6 (f7 f8 (f9 f10 (f9 f11 ?v0)))))))
(assert (forall ((?v0 S2)) (= (f3 f12 ?v0) (f5 f13 (f7 f8 (f9 f10 ?v0))))))
(assert (forall ((?v0 S8) (?v1 S2)) (= (f3 (f14 f15 ?v0) ?v1) (f3 (f14 (f16 f17 (f18 (f19 f20 f6) f8)) f10) (f9 ?v0 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S2)) (= (f3 (f14 f21 ?v0) ?v1) (f3 (f18 (f19 f20 f13) f8) (f9 ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f7 (f22 f23 ?v0) ?v1) (f24 f25 (f3 ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f3 (f26 f27 ?v0) ?v1) (f28 f29 (f3 ?v0 ?v1)))))
(assert (forall ((?v0 S7) (?v1 S2)) (= (f3 (f18 f30 ?v0) ?v1) (f5 f13 (f7 ?v0 ?v1)))))
(assert (forall ((?v0 S7) (?v1 S2)) (= (f3 (f18 f31 ?v0) ?v1) (f5 f6 (f7 ?v0 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S2)) (= (f3 (f14 f32 ?v0) ?v1) (f5 f6 (f7 f8 (f9 f10 (f9 ?v0 ?v1)))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S2)) (= (f7 (f33 (f34 f35 ?v0) ?v1) ?v2) (f36 (f37 f38 (f3 ?v0 ?v2)) (f7 ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (= (f3 (f26 (f39 f40 ?v0) ?v1) ?v2) (f28 (f41 f42 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S2)) (= (f7 (f43 (f44 f45 ?v0) ?v1) ?v2) (f36 (f37 f38 (f3 ?v0 ?v2)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S2)) (= (f3 (f46 (f47 f48 ?v0) ?v1) ?v2) (f28 (f41 f42 (f3 ?v0 ?v2)) ?v1))))
(assert (forall ((?v0 S7) (?v1 S4) (?v2 S2)) (= (f7 (f49 (f50 f51 ?v0) ?v1) ?v2) (f36 (f37 f38 ?v1) (f7 ?v0 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S2)) (= (f3 (f46 (f47 f52 ?v0) ?v1) ?v2) (f28 (f41 f42 ?v1) (f3 ?v0 ?v2)))))
(assert (forall ((?v0 S19) (?v1 S7) (?v2 S2)) (= (f7 (f33 (f53 f54 ?v0) ?v1) ?v2) (f36 ?v0 (f7 ?v1 ?v2)))))
(assert (forall ((?v0 S16) (?v1 S3) (?v2 S2)) (= (f3 (f26 (f55 f56 ?v0) ?v1) ?v2) (f28 ?v0 (f3 ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S2)) (= (f3 (f14 (f16 f57 ?v0) ?v1) ?v2) (f3 ?v0 (f9 ?v1 ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S2)) (= (f9 (f58 (f59 f60 ?v0) ?v1) ?v2) (f9 ?v0 (f9 ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S2)) (= (f7 (f43 f61 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S4) (?v1 S2)) (= (f3 (f46 f62 ?v0) ?v1) ?v0)))
(assert (not (= (f63 f4) f1)))
(assert (= (f64 f10) f1))
(assert (= (f64 f11) f1))
(assert (= (f65 f4) f1))
(assert (= (f63 f12) f1))
(assert (= (f65 f12) f1))
(assert (=> (forall ((?v0 S8)) (=> (= (f64 ?v0) f1) (=> (= (f65 (f14 f32 ?v0)) f1) false))) false))
(assert (forall ((?v0 S4)) (= (f63 (f46 f62 ?v0)) f1)))
(assert (forall ((?v0 S6)) (= (f66 (f43 f61 ?v0)) f1)))
(assert (forall ((?v0 S7)) (=> (= (f66 ?v0) f1) (= (f63 (f18 f31 ?v0)) f1))))
(assert (forall ((?v0 S3)) (=> (= (f63 ?v0) f1) (= (f63 (f26 f27 ?v0)) f1))))
(assert (forall ((?v0 S3)) (=> (= (f63 ?v0) f1) (= (f66 (f22 f23 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S4)) (=> (= (f63 ?v0) f1) (= (f63 (f46 (f47 f48 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S6)) (=> (= (f63 ?v0) f1) (= (f66 (f43 (f44 f45 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f63 ?v0) f1) (=> (= (f63 ?v1) f1) (= (f63 (f26 (f39 f40 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S7)) (=> (= (f63 ?v0) f1) (=> (= (f66 ?v1) f1) (= (f66 (f33 (f34 f35 ?v0) ?v1)) f1)))))
(assert (exists ((?v0 S8)) (and (= (f64 ?v0) f1) (= (f65 (f14 f15 ?v0)) f1))))
(assert (forall ((?v0 S2)) (= (f67 (f5 f68 (f7 f8 ?v0)) f69) f1)))
(assert (forall ((?v0 S16) (?v1 S3)) (=> (= (f70 ?v0) f1) (=> (= (f63 ?v1) f1) (= (f63 (f26 (f55 f56 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S19) (?v1 S7)) (=> (= (f71 ?v0) f1) (=> (= (f66 ?v1) f1) (= (f66 (f33 (f53 f54 ?v0) ?v1)) f1)))))
(assert (exists ((?v0 S8)) (and (= (f64 ?v0) f1) (= (f65 (f14 f21 ?v0)) f1))))
(assert (forall ((?v0 S6)) (= (f67 (f5 f13 ?v0) (f5 f68 ?v0)) f1)))
(assert (forall ((?v0 S8)) (= (= (f72 ?v0) f1) (or (forall ((?v1 S2) (?v2 S2)) (=> (= (f73 ?v1 ?v2) f1) (= (f73 (f9 ?v0 ?v1) (f9 ?v0 ?v2)) f1))) (forall ((?v1 S2) (?v2 S2)) (=> (= (f73 ?v1 ?v2) f1) (= (f73 (f9 ?v0 ?v2) (f9 ?v0 ?v1)) f1)))))))
(assert (forall ((?v0 S3)) (= (= (f65 ?v0) f1) (or (forall ((?v1 S2) (?v2 S2)) (=> (= (f73 ?v1 ?v2) f1) (= (f67 (f3 ?v0 ?v1) (f3 ?v0 ?v2)) f1))) (forall ((?v1 S2) (?v2 S2)) (=> (= (f73 ?v1 ?v2) f1) (= (f67 (f3 ?v0 ?v2) (f3 ?v0 ?v1)) f1)))))))
(assert (forall ((?v0 S4)) (= (f5 f13 (f24 f25 ?v0)) ?v0)))
(assert (forall ((?v0 S4) (?v1 S6)) (= (f5 f6 (f36 (f37 f38 ?v0) ?v1)) (f28 (f41 f42 ?v0) (f5 f6 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S6)) (= (f5 f13 (f36 (f37 f38 ?v0) ?v1)) (f28 (f41 f42 ?v0) (f5 f13 ?v1)))))
(assert (forall ((?v0 S7) (?v1 S8)) (=> (= (f66 ?v0) f1) (=> (= (f64 ?v1) f1) (= (f66 (f74 (f75 f76 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S8)) (=> (= (f63 ?v0) f1) (=> (= (f64 ?v1) f1) (= (f63 (f14 (f16 f17 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S7)) (=> (= (f66 ?v0) f1) (= (f63 (f18 f30 ?v0)) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f5 f13 ?v0) (f5 f13 ?v1)) (=> (= (f5 f6 ?v0) (f5 f6 ?v1)) (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= ?v0 ?v1) (and (= (f5 f13 ?v0) (f5 f13 ?v1)) (= (f5 f6 ?v0) (f5 f6 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S4)) (=> (= (f63 ?v0) f1) (= (f63 (f46 (f47 f52 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S7) (?v1 S4)) (=> (= (f66 ?v0) f1) (= (f66 (f49 (f50 f51 ?v0) ?v1)) f1))))
(assert (= (f67 (f5 f68 (f7 f8 f77)) f69) f1))
(assert (= (f67 f78 f69) f1))
(assert (forall ((?v0 S8)) (exists ((?v1 S8)) (and (= (f64 ?v1) f1) (= (f72 (f58 (f59 f60 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3)) (exists ((?v1 S8)) (and (= (f64 ?v1) f1) (= (f65 (f14 (f16 f57 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S4)) (= (f71 (f37 f38 ?v0)) f1)))
(assert (forall ((?v0 S4)) (= (f70 (f41 f42 ?v0)) f1)))
(assert (forall ((?v0 S8)) (=> (forall ((?v1 S2) (?v2 S2)) (=> (= (f73 ?v1 ?v2) f1) (= (f73 (f9 ?v0 ?v2) (f9 ?v0 ?v1)) f1))) (= (f72 ?v0) f1))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2) (?v2 S2)) (=> (= (f73 ?v1 ?v2) f1) (= (f67 (f3 ?v0 ?v2) (f3 ?v0 ?v1)) f1))) (= (f65 ?v0) f1))))
(assert (forall ((?v0 S8)) (=> (forall ((?v1 S2) (?v2 S2)) (=> (= (f73 ?v1 ?v2) f1) (= (f73 (f9 ?v0 ?v1) (f9 ?v0 ?v2)) f1))) (= (f72 ?v0) f1))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2) (?v2 S2)) (=> (= (f73 ?v1 ?v2) f1) (= (f67 (f3 ?v0 ?v1) (f3 ?v0 ?v2)) f1))) (= (f65 ?v0) f1))))
(assert (forall ((?v0 S4)) (= (f67 ?v0 ?v0) f1)))
(assert (forall ((?v0 S2)) (= (f73 ?v0 ?v0) f1)))
(assert (forall ((?v0 S19) (?v1 S4) (?v2 S6)) (let ((?v_0 (f37 f38 ?v1))) (=> (= (f71 ?v0) f1) (= (f36 ?v0 (f36 ?v_0 ?v2)) (f36 ?v_0 (f36 ?v0 ?v2)))))))
(assert (forall ((?v0 S16) (?v1 S4) (?v2 S4)) (let ((?v_0 (f41 f42 ?v1))) (=> (= (f70 ?v0) f1) (= (f28 ?v0 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v0 ?v2)))))))
(assert (= (f28 f29 f78) f78))
(assert (= (f24 f25 f78) f79))
(assert (= (f28 f29 f78) f78))
(assert (= (f24 f25 f78) f79))
(assert (= (f5 f68 f79) f78))
(assert (= (f28 f80 f78) f78))
(assert (forall ((?v0 S6)) (= (f36 (f37 f38 f78) ?v0) f79)))
(assert (forall ((?v0 S4)) (= (f28 (f41 f42 f78) ?v0) f78)))
(assert (forall ((?v0 S6)) (= (f36 (f37 f38 f78) ?v0) f79)))
(assert (forall ((?v0 S4)) (= (f28 (f41 f42 f78) ?v0) f78)))
(assert (forall ((?v0 S4)) (= (= (f28 f29 ?v0) f78) (= ?v0 f78))))
(assert (forall ((?v0 S4)) (= (= (f24 f25 ?v0) f79) (= ?v0 f78))))
(assert (forall ((?v0 S6)) (= (= (f5 f68 ?v0) f78) (= ?v0 f79))))
(assert (forall ((?v0 S4)) (= (= (f28 f80 ?v0) f78) (= ?v0 f78))))
(assert (forall ((?v0 S4) (?v1 S6)) (= (= (f36 (f37 f38 ?v0) ?v1) f79) (or (= ?v0 f78) (= ?v1 f79)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f28 (f41 f42 ?v0) ?v1) f78) (or (= ?v0 f78) (= ?v1 f78)))))
(assert (forall ((?v0 S6) (?v1 S4) (?v2 S4)) (=> (not (= ?v0 f79)) (=> (= (f36 (f37 f38 ?v1) ?v0) (f36 (f37 f38 ?v2) ?v0)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (=> (not (= ?v0 f78)) (=> (= (f28 (f41 f42 ?v1) ?v0) (f28 (f41 f42 ?v2) ?v0)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S4) (?v1 S6) (?v2 S4)) (= (= (f36 (f37 f38 ?v0) ?v1) (f36 (f37 f38 ?v2) ?v1)) (or (= ?v0 ?v2) (= ?v1 f79)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (= (f28 (f41 f42 ?v0) ?v1) (f28 (f41 f42 ?v2) ?v1)) (or (= ?v0 ?v2) (= ?v1 f78)))))
(assert (forall ((?v0 S4)) (= (f36 (f37 f38 ?v0) f79) f79)))
(assert (forall ((?v0 S4)) (= (f28 (f41 f42 ?v0) f78) f78)))
(assert (forall ((?v0 S4)) (= (f36 (f37 f38 ?v0) f79) f79)))
(assert (forall ((?v0 S4)) (= (f28 (f41 f42 ?v0) f78) f78)))
(assert (forall ((?v0 S4) (?v1 S6) (?v2 S6)) (let ((?v_0 (f37 f38 ?v0))) (=> (not (= ?v0 f78)) (=> (= (f36 ?v_0 ?v1) (f36 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f41 f42 ?v0))) (=> (not (= ?v0 f78)) (=> (= (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S6) (?v2 S6)) (let ((?v_0 (f37 f38 ?v0))) (= (= (f36 ?v_0 ?v1) (f36 ?v_0 ?v2)) (or (= ?v1 ?v2) (= ?v0 f78))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f41 f42 ?v0))) (= (= (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) (or (= ?v1 ?v2) (= ?v0 f78))))))
(assert (forall ((?v0 S6)) (= (= (f67 (f5 f68 ?v0) f78) f1) (= ?v0 f79))))
(assert (forall ((?v0 S4)) (= (= (f67 (f28 f80 ?v0) f78) f1) (= ?v0 f78))))
(assert (forall ((?v0 S4)) (= (f5 f6 (f24 f25 ?v0)) f78)))
(assert (forall ((?v0 S4)) (= (f67 f78 (f28 f80 ?v0)) f1)))
(assert (forall ((?v0 S6)) (= (f67 f78 (f5 f68 ?v0)) f1)))
(assert (forall ((?v0 S8) (?v1 S2)) (=> (= (f64 ?v0) f1) (= (f73 ?v1 (f9 ?v0 ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (=> (= (f67 ?v0 ?v1) f1) false) (=> (=> (= (f67 ?v1 ?v0) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f73 ?v0 ?v1) f1) false) (=> (=> (= (f73 ?v1 ?v0) f1) false) false))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (=> (= (f67 ?v0 ?v1) f1) (=> (= (f67 ?v2 ?v0) f1) (= (f67 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f73 ?v0 ?v1) f1) (=> (= (f73 ?v2 ?v0) f1) (= (f73 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (= (f67 ?v0 ?v1) f1) (=> (= (f67 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f73 ?v0 ?v1) f1) (=> (= (f73 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (=> (= (f67 ?v0 ?v1) f1) (=> (= (f67 ?v1 ?v2) f1) (= (f67 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f73 ?v0 ?v1) f1) (=> (= (f73 ?v1 ?v2) f1) (= (f73 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (= (f67 ?v0 ?v1) f1) (=> (= (f67 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f73 ?v0 ?v1) f1) (=> (= (f73 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (=> (= (f67 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f67 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f73 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f73 ?v2 ?v1) f1)))))
(check-sat)
(exit)