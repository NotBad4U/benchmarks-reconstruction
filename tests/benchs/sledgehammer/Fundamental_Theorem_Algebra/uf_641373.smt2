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
(declare-fun f3 () S2)
(declare-fun f4 () S2)
(declare-fun f5 (S3 S2) S2)
(declare-fun f6 (S4 S2) S3)
(declare-fun f7 () S4)
(declare-fun f8 (S5 S6) S3)
(declare-fun f9 () S5)
(declare-fun f10 () S6)
(declare-fun f11 () S5)
(declare-fun f12 () S6)
(declare-fun f13 (S9 S8) S8)
(declare-fun f14 (S10 S7) S9)
(declare-fun f15 () S10)
(declare-fun f16 () S10)
(declare-fun f17 () S8)
(declare-fun f18 (S13 S12) S12)
(declare-fun f19 (S14 S11) S13)
(declare-fun f20 () S14)
(declare-fun f21 () S14)
(declare-fun f22 () S12)
(declare-fun f23 (S15 S11) S11)
(declare-fun f24 (S16 S2) S15)
(declare-fun f25 () S16)
(declare-fun f26 () S16)
(declare-fun f27 () S11)
(declare-fun f28 (S18 S7) S7)
(declare-fun f29 (S19 S17) S18)
(declare-fun f30 () S19)
(declare-fun f31 () S19)
(declare-fun f32 () S7)
(declare-fun f33 (S20 S6) S6)
(declare-fun f34 (S21 S6) S20)
(declare-fun f35 () S21)
(declare-fun f36 (S22 S11) S15)
(declare-fun f37 () S22)
(declare-fun f38 (S23 S7) S18)
(declare-fun f39 () S23)
(declare-fun f40 (S24 S8) S9)
(declare-fun f41 () S24)
(declare-fun f42 (S26 S25) S25)
(declare-fun f43 (S27 S12) S26)
(declare-fun f44 () S27)
(declare-fun f45 (S28 S12) S13)
(declare-fun f46 () S28)
(declare-fun f47 (S29 S25) S26)
(declare-fun f48 () S29)
(declare-fun f49 (S30 S17) S17)
(declare-fun f50 (S31 S17) S30)
(declare-fun f51 () S31)
(declare-fun f52 () S27)
(declare-fun f53 () S6)
(declare-fun f54 () S17)
(declare-fun f55 (S33 S32) S32)
(declare-fun f56 (S34 S8) S33)
(declare-fun f57 () S34)
(declare-fun f58 () S32)
(declare-fun f59 () S25)
(declare-fun f60 () S34)
(declare-fun f61 (S35 S6) S2)
(declare-fun f62 (S36 S2) S35)
(declare-fun f63 () S36)
(declare-fun f64 (S37 S7) S8)
(declare-fun f65 (S38 S8) S37)
(declare-fun f66 () S38)
(declare-fun f67 (S39 S11) S12)
(declare-fun f68 (S40 S12) S39)
(declare-fun f69 () S40)
(declare-fun f70 (S41 S2) S11)
(declare-fun f71 (S42 S11) S41)
(declare-fun f72 () S42)
(declare-fun f73 (S43 S17) S7)
(declare-fun f74 (S44 S7) S43)
(declare-fun f75 () S44)
(declare-fun f76 (S45 S2) S1)
(declare-fun f77 (S46 S8) S1)
(declare-fun f78 (S47 S12) S1)
(declare-fun f79 (S48 S11) S1)
(declare-fun f80 (S49 S7) S1)
(assert (not (= f1 f2)))
(assert (not (= f3 f4)))
(assert (= (f5 (f6 f7 (f5 (f8 f9 f10) f3)) (f5 (f8 f11 f12) f3)) f4))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6)) (=> (= (f5 (f8 f9 ?v0) ?v1) (f5 (f8 f11 ?v2) ?v1)) (= ?v1 f4))))
(assert (forall ((?v0 S7) (?v1 S8) (?v2 S7)) (=> (= (f13 (f14 f15 ?v0) ?v1) (f13 (f14 f16 ?v2) ?v1)) (= ?v1 f17))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11)) (=> (= (f18 (f19 f20 ?v0) ?v1) (f18 (f19 f21 ?v2) ?v1)) (= ?v1 f22))))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S2)) (=> (= (f23 (f24 f25 ?v0) ?v1) (f23 (f24 f26 ?v2) ?v1)) (= ?v1 f27))))
(assert (forall ((?v0 S17) (?v1 S7) (?v2 S17)) (=> (= (f28 (f29 f30 ?v0) ?v1) (f28 (f29 f31 ?v2) ?v1)) (= ?v1 f32))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S2)) (= (f5 (f8 f9 (f33 (f34 f35 ?v0) ?v1)) ?v2) (f5 (f6 f7 (f5 (f8 f9 ?v0) ?v2)) (f5 (f8 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S11)) (= (f23 (f24 f25 (f5 (f6 f7 ?v0) ?v1)) ?v2) (f23 (f36 f37 (f23 (f24 f25 ?v0) ?v2)) (f23 (f24 f25 ?v1) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S8)) (= (f13 (f14 f15 (f28 (f38 f39 ?v0) ?v1)) ?v2) (f13 (f40 f41 (f13 (f14 f15 ?v0) ?v2)) (f13 (f14 f15 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S25)) (= (f42 (f43 f44 (f18 (f45 f46 ?v0) ?v1)) ?v2) (f42 (f47 f48 (f42 (f43 f44 ?v0) ?v2)) (f42 (f43 f44 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (= (f18 (f19 f20 (f23 (f36 f37 ?v0) ?v1)) ?v2) (f18 (f45 f46 (f18 (f19 f20 ?v0) ?v2)) (f18 (f19 f20 ?v1) ?v2)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S7)) (= (f28 (f29 f30 (f49 (f50 f51 ?v0) ?v1)) ?v2) (f28 (f38 f39 (f28 (f29 f30 ?v0) ?v2)) (f28 (f29 f30 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6) (?v3 S2)) (= (f5 (f6 f7 (f5 (f8 f11 ?v0) ?v1)) (f5 (f8 f11 ?v2) ?v3)) (f5 (f8 f11 (f33 (f34 f35 ?v0) ?v2)) (f5 (f6 f7 ?v1) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S2) (?v3 S11)) (= (f23 (f36 f37 (f23 (f24 f26 ?v0) ?v1)) (f23 (f24 f26 ?v2) ?v3)) (f23 (f24 f26 (f5 (f6 f7 ?v0) ?v2)) (f23 (f36 f37 ?v1) ?v3)))))
(assert (forall ((?v0 S7) (?v1 S8) (?v2 S7) (?v3 S8)) (= (f13 (f40 f41 (f13 (f14 f16 ?v0) ?v1)) (f13 (f14 f16 ?v2) ?v3)) (f13 (f14 f16 (f28 (f38 f39 ?v0) ?v2)) (f13 (f40 f41 ?v1) ?v3)))))
(assert (forall ((?v0 S12) (?v1 S25) (?v2 S12) (?v3 S25)) (= (f42 (f47 f48 (f42 (f43 f52 ?v0) ?v1)) (f42 (f43 f52 ?v2) ?v3)) (f42 (f43 f52 (f18 (f45 f46 ?v0) ?v2)) (f42 (f47 f48 ?v1) ?v3)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11) (?v3 S12)) (= (f18 (f45 f46 (f18 (f19 f21 ?v0) ?v1)) (f18 (f19 f21 ?v2) ?v3)) (f18 (f19 f21 (f23 (f36 f37 ?v0) ?v2)) (f18 (f45 f46 ?v1) ?v3)))))
(assert (forall ((?v0 S17) (?v1 S7) (?v2 S17) (?v3 S7)) (= (f28 (f38 f39 (f28 (f29 f31 ?v0) ?v1)) (f28 (f29 f31 ?v2) ?v3)) (f28 (f29 f31 (f49 (f50 f51 ?v0) ?v2)) (f28 (f38 f39 ?v1) ?v3)))))
(assert (forall ((?v0 S2)) (= (f5 (f8 f9 f53) ?v0) f4)))
(assert (forall ((?v0 S7)) (= (f28 (f29 f30 f54) ?v0) f32)))
(assert (forall ((?v0 S11)) (= (f23 (f24 f25 f4) ?v0) f27)))
(assert (forall ((?v0 S32)) (= (f55 (f56 f57 f17) ?v0) f58)))
(assert (forall ((?v0 S25)) (= (f42 (f43 f44 f22) ?v0) f59)))
(assert (forall ((?v0 S12)) (= (f18 (f19 f20 f27) ?v0) f22)))
(assert (forall ((?v0 S8)) (= (f13 (f14 f15 f32) ?v0) f17)))
(assert (forall ((?v0 S17) (?v1 S7)) (= (= (f28 (f29 f30 ?v0) ?v1) f32) (or (= ?v0 f54) (= ?v1 f32)))))
(assert (forall ((?v0 S8) (?v1 S32)) (= (= (f55 (f56 f57 ?v0) ?v1) f58) (or (= ?v0 f17) (= ?v1 f58)))))
(assert (forall ((?v0 S7) (?v1 S8)) (= (= (f13 (f14 f15 ?v0) ?v1) f17) (or (= ?v0 f32) (= ?v1 f17)))))
(assert (= (f5 (f8 f11 f53) f4) f4))
(assert (= (f28 (f29 f31 f54) f32) f32))
(assert (= (f23 (f24 f26 f4) f27) f27))
(assert (= (f55 (f56 f60 f17) f58) f58))
(assert (= (f42 (f43 f52 f22) f59) f59))
(assert (= (f18 (f19 f21 f27) f22) f22))
(assert (= (f13 (f14 f16 f32) f17) f17))
(assert (forall ((?v0 S6) (?v1 S2)) (= (= (f5 (f8 f11 ?v0) ?v1) f4) (and (= ?v0 f53) (= ?v1 f4)))))
(assert (forall ((?v0 S17) (?v1 S7)) (= (= (f28 (f29 f31 ?v0) ?v1) f32) (and (= ?v0 f54) (= ?v1 f32)))))
(assert (forall ((?v0 S2) (?v1 S11)) (= (= (f23 (f24 f26 ?v0) ?v1) f27) (and (= ?v0 f4) (= ?v1 f27)))))
(assert (forall ((?v0 S8) (?v1 S32)) (= (= (f55 (f56 f60 ?v0) ?v1) f58) (and (= ?v0 f17) (= ?v1 f58)))))
(assert (forall ((?v0 S12) (?v1 S25)) (= (= (f42 (f43 f52 ?v0) ?v1) f59) (and (= ?v0 f22) (= ?v1 f59)))))
(assert (forall ((?v0 S11) (?v1 S12)) (= (= (f18 (f19 f21 ?v0) ?v1) f22) (and (= ?v0 f27) (= ?v1 f22)))))
(assert (forall ((?v0 S7) (?v1 S8)) (= (= (f13 (f14 f16 ?v0) ?v1) f17) (and (= ?v0 f32) (= ?v1 f17)))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f5 (f6 f7 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S7) (?v1 S8) (?v2 S8)) (let ((?v_0 (f14 f15 ?v0))) (= (f13 ?v_0 (f13 (f40 f41 ?v1) ?v2)) (f13 (f40 f41 (f13 ?v_0 ?v1)) (f13 ?v_0 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S12)) (let ((?v_0 (f19 f20 ?v0))) (= (f18 ?v_0 (f18 (f45 f46 ?v1) ?v2)) (f18 (f45 f46 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S11)) (let ((?v_0 (f24 f25 ?v0))) (= (f23 ?v_0 (f23 (f36 f37 ?v1) ?v2)) (f23 (f36 f37 (f23 ?v_0 ?v1)) (f23 ?v_0 ?v2))))))
(assert (forall ((?v0 S17) (?v1 S7) (?v2 S7)) (let ((?v_0 (f29 f30 ?v0))) (= (f28 ?v_0 (f28 (f38 f39 ?v1) ?v2)) (f28 (f38 f39 (f28 ?v_0 ?v1)) (f28 ?v_0 ?v2))))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 f4) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f18 (f45 f46 f22) ?v0) ?v0)))
(assert (forall ((?v0 S8)) (= (f13 (f40 f41 f17) ?v0) ?v0)))
(assert (forall ((?v0 S7)) (= (f28 (f38 f39 f32) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f23 (f36 f37 f27) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 ?v0) f4) ?v0)))
(assert (forall ((?v0 S12)) (= (f18 (f45 f46 ?v0) f22) ?v0)))
(assert (forall ((?v0 S8)) (= (f13 (f40 f41 ?v0) f17) ?v0)))
(assert (forall ((?v0 S7)) (= (f28 (f38 f39 ?v0) f32) ?v0)))
(assert (forall ((?v0 S11)) (= (f23 (f36 f37 ?v0) f27) ?v0)))
(assert (forall ((?v0 S6)) (= (f5 (f8 f9 ?v0) f4) f4)))
(assert (forall ((?v0 S7)) (= (f13 (f14 f15 ?v0) f17) f17)))
(assert (forall ((?v0 S11)) (= (f18 (f19 f20 ?v0) f22) f22)))
(assert (forall ((?v0 S2)) (= (f23 (f24 f25 ?v0) f27) f27)))
(assert (forall ((?v0 S17)) (= (f28 (f29 f30 ?v0) f32) f32)))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6)) (let ((?v_0 (f8 f11 ?v0)) (?v_1 (f61 (f62 f63 ?v1) ?v2))) (= (f61 (f62 f63 (f5 ?v_0 ?v1)) ?v2) (f5 (f6 f7 (f5 (f8 f9 ?v2) ?v_1)) (f5 ?v_0 ?v_1))))))
(assert (forall ((?v0 S7) (?v1 S8) (?v2 S7)) (let ((?v_0 (f14 f16 ?v0)) (?v_1 (f64 (f65 f66 ?v1) ?v2))) (= (f64 (f65 f66 (f13 ?v_0 ?v1)) ?v2) (f13 (f40 f41 (f13 (f14 f15 ?v2) ?v_1)) (f13 ?v_0 ?v_1))))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11)) (let ((?v_0 (f19 f21 ?v0)) (?v_1 (f67 (f68 f69 ?v1) ?v2))) (= (f67 (f68 f69 (f18 ?v_0 ?v1)) ?v2) (f18 (f45 f46 (f18 (f19 f20 ?v2) ?v_1)) (f18 ?v_0 ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S2)) (let ((?v_0 (f24 f26 ?v0)) (?v_1 (f70 (f71 f72 ?v1) ?v2))) (= (f70 (f71 f72 (f23 ?v_0 ?v1)) ?v2) (f23 (f36 f37 (f23 (f24 f25 ?v2) ?v_1)) (f23 ?v_0 ?v_1))))))
(assert (forall ((?v0 S17) (?v1 S7) (?v2 S17)) (let ((?v_0 (f29 f31 ?v0)) (?v_1 (f73 (f74 f75 ?v1) ?v2))) (= (f73 (f74 f75 (f28 ?v_0 ?v1)) ?v2) (f28 (f38 f39 (f28 (f29 f30 ?v2) ?v_1)) (f28 ?v_0 ?v_1))))))
(assert (forall ((?v0 S6)) (= (f61 (f62 f63 f4) ?v0) f4)))
(assert (forall ((?v0 S7)) (= (f64 (f65 f66 f17) ?v0) f17)))
(assert (forall ((?v0 S11)) (= (f67 (f68 f69 f22) ?v0) f22)))
(assert (forall ((?v0 S2)) (= (f70 (f71 f72 f27) ?v0) f27)))
(assert (forall ((?v0 S17)) (= (f73 (f74 f75 f32) ?v0) f32)))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6) (?v3 S2)) (= (= (f5 (f8 f11 ?v0) ?v1) (f5 (f8 f11 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S7) (?v1 S8) (?v2 S7) (?v3 S8)) (= (= (f13 (f14 f16 ?v0) ?v1) (f13 (f14 f16 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11) (?v3 S12)) (= (= (f18 (f19 f21 ?v0) ?v1) (f18 (f19 f21 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S2) (?v3 S11)) (= (= (f23 (f24 f26 ?v0) ?v1) (f23 (f24 f26 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S17) (?v1 S7) (?v2 S17) (?v3 S7)) (= (= (f28 (f29 f31 ?v0) ?v1) (f28 (f29 f31 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f5 (f8 f11 ?v0) f4))) (= (f61 (f62 f63 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f13 (f14 f16 ?v0) f17))) (= (f64 (f65 f66 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f18 (f19 f21 ?v0) f22))) (= (f67 (f68 f69 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f23 (f24 f26 ?v0) f27))) (= (f70 (f71 f72 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S17) (?v1 S17)) (let ((?v_0 (f28 (f29 f31 ?v0) f32))) (= (f73 (f74 f75 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S45) (?v1 S2)) (=> (= (f76 ?v0 f4) f1) (=> (forall ((?v2 S6) (?v3 S2)) (=> (= (f76 ?v0 ?v3) f1) (= (f76 ?v0 (f5 (f8 f11 ?v2) ?v3)) f1))) (= (f76 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S46) (?v1 S8)) (=> (= (f77 ?v0 f17) f1) (=> (forall ((?v2 S7) (?v3 S8)) (=> (= (f77 ?v0 ?v3) f1) (= (f77 ?v0 (f13 (f14 f16 ?v2) ?v3)) f1))) (= (f77 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S47) (?v1 S12)) (=> (= (f78 ?v0 f22) f1) (=> (forall ((?v2 S11) (?v3 S12)) (=> (= (f78 ?v0 ?v3) f1) (= (f78 ?v0 (f18 (f19 f21 ?v2) ?v3)) f1))) (= (f78 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S48) (?v1 S11)) (=> (= (f79 ?v0 f27) f1) (=> (forall ((?v2 S2) (?v3 S11)) (=> (= (f79 ?v0 ?v3) f1) (= (f79 ?v0 (f23 (f24 f26 ?v2) ?v3)) f1))) (= (f79 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S49) (?v1 S7)) (=> (= (f80 ?v0 f32) f1) (=> (forall ((?v2 S17) (?v3 S7)) (=> (= (f80 ?v0 ?v3) f1) (= (f80 ?v0 (f28 (f29 f31 ?v2) ?v3)) f1))) (= (f80 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S17)) (= (= (f49 (f50 f51 ?v0) ?v0) f54) (= ?v0 f54))))
(assert (forall ((?v0 S8)) (= (= (f13 (f40 f41 ?v0) ?v0) f17) (= ?v0 f17))))
(assert (forall ((?v0 S7)) (= (= (f28 (f38 f39 ?v0) ?v0) f32) (= ?v0 f32))))
(assert (forall ((?v0 S17) (?v1 S17)) (= (= ?v0 (f49 (f50 f51 ?v0) ?v1)) (= ?v1 f54))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= ?v0 (f13 (f40 f41 ?v0) ?v1)) (= ?v1 f17))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= ?v0 (f28 (f38 f39 ?v0) ?v1)) (= ?v1 f32))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 ?v0) f4) ?v0)))
(assert (forall ((?v0 S17)) (= (f49 (f50 f51 ?v0) f54) ?v0)))
(assert (forall ((?v0 S12)) (= (f18 (f45 f46 ?v0) f22) ?v0)))
(assert (forall ((?v0 S8)) (= (f13 (f40 f41 ?v0) f17) ?v0)))
(assert (forall ((?v0 S7)) (= (f28 (f38 f39 ?v0) f32) ?v0)))
(assert (forall ((?v0 S11)) (= (f23 (f36 f37 ?v0) f27) ?v0)))
(assert (forall ((?v0 S6)) (= (f33 (f34 f35 ?v0) f53) ?v0)))
(assert (forall ((?v0 S17)) (= (f49 (f50 f51 ?v0) f54) ?v0)))
(assert (forall ((?v0 S8)) (= (f13 (f40 f41 ?v0) f17) ?v0)))
(assert (forall ((?v0 S7)) (= (f28 (f38 f39 ?v0) f32) ?v0)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 ?v0) f4) ?v0)))
(assert (forall ((?v0 S17)) (= (f49 (f50 f51 ?v0) f54) ?v0)))
(assert (forall ((?v0 S12)) (= (f18 (f45 f46 ?v0) f22) ?v0)))
(assert (forall ((?v0 S8)) (= (f13 (f40 f41 ?v0) f17) ?v0)))
(assert (forall ((?v0 S7)) (= (f28 (f38 f39 ?v0) f32) ?v0)))
(assert (forall ((?v0 S11)) (= (f23 (f36 f37 ?v0) f27) ?v0)))
(assert (forall ((?v0 S6)) (= (f33 (f34 f35 ?v0) f53) ?v0)))
(assert (forall ((?v0 S17)) (= (= f54 (f49 (f50 f51 ?v0) ?v0)) (= ?v0 f54))))
(assert (forall ((?v0 S8)) (= (= f17 (f13 (f40 f41 ?v0) ?v0)) (= ?v0 f17))))
(assert (forall ((?v0 S7)) (= (= f32 (f28 (f38 f39 ?v0) ?v0)) (= ?v0 f32))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 f4) ?v0) ?v0)))
(assert (forall ((?v0 S17)) (= (f49 (f50 f51 f54) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f18 (f45 f46 f22) ?v0) ?v0)))
(assert (forall ((?v0 S8)) (= (f13 (f40 f41 f17) ?v0) ?v0)))
(assert (forall ((?v0 S7)) (= (f28 (f38 f39 f32) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f23 (f36 f37 f27) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f33 (f34 f35 f53) ?v0) ?v0)))
(assert (forall ((?v0 S17)) (= (f49 (f50 f51 f54) ?v0) ?v0)))
(assert (forall ((?v0 S8)) (= (f13 (f40 f41 f17) ?v0) ?v0)))
(assert (forall ((?v0 S7)) (= (f28 (f38 f39 f32) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 f4) ?v0) ?v0)))
(assert (forall ((?v0 S17)) (= (f49 (f50 f51 f54) ?v0) ?v0)))
(assert (forall ((?v0 S12)) (= (f18 (f45 f46 f22) ?v0) ?v0)))
(assert (forall ((?v0 S8)) (= (f13 (f40 f41 f17) ?v0) ?v0)))
(assert (forall ((?v0 S7)) (= (f28 (f38 f39 f32) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f23 (f36 f37 f27) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f33 (f34 f35 f53) ?v0) ?v0)))
(assert (forall ((?v0 S17)) (= (= f54 ?v0) (= ?v0 f54))))
(assert (forall ((?v0 S2)) (= (= f4 ?v0) (= ?v0 f4))))
(assert (forall ((?v0 S8)) (= (= f17 ?v0) (= ?v0 f17))))
(assert (forall ((?v0 S12)) (= (= f22 ?v0) (= ?v0 f22))))
(assert (forall ((?v0 S11)) (= (= f27 ?v0) (= ?v0 f27))))
(assert (forall ((?v0 S7)) (= (= f32 ?v0) (= ?v0 f32))))
(assert (forall ((?v0 S6)) (= (= f53 ?v0) (= ?v0 f53))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f28 (f38 f39 ?v0) ?v1) (f28 (f38 f39 ?v1) ?v0))))
(assert (forall ((?v0 S17) (?v1 S17)) (= (f49 (f50 f51 ?v0) ?v1) (f49 (f50 f51 ?v1) ?v0))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_1 (f38 f39 ?v0)) (?v_0 (f38 f39 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17)) (let ((?v_1 (f50 f51 ?v0)) (?v_0 (f50 f51 ?v1))) (= (f49 ?v_1 (f49 ?v_0 ?v2)) (f49 ?v_0 (f49 ?v_1 ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f38 f39 ?v0))) (= (f28 ?v_0 (f28 (f38 f39 ?v1) ?v2)) (f28 (f38 f39 (f28 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17)) (let ((?v_0 (f50 f51 ?v0))) (= (f49 ?v_0 (f49 (f50 f51 ?v1) ?v2)) (f49 (f50 f51 (f49 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f38 f39 ?v0))) (= (f28 (f38 f39 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f38 f39 ?v1) ?v2))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17)) (let ((?v_0 (f50 f51 ?v0))) (= (f49 (f50 f51 (f49 ?v_0 ?v1)) ?v2) (f49 ?v_0 (f49 (f50 f51 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f38 f39 ?v0))) (= (f28 (f38 f39 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f38 f39 ?v1) ?v2))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f45 f46 ?v0))) (= (f18 (f45 f46 (f18 ?v_0 ?v1)) ?v2) (f18 ?v_0 (f18 (f45 f46 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f36 f37 ?v0))) (= (f23 (f36 f37 (f23 ?v_0 ?v1)) ?v2) (f23 ?v_0 (f23 (f36 f37 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f34 f35 ?v0))) (= (f33 (f34 f35 (f33 ?v_0 ?v1)) ?v2) (f33 ?v_0 (f33 (f34 f35 ?v1) ?v2))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17)) (let ((?v_0 (f50 f51 ?v0))) (= (f49 (f50 f51 (f49 ?v_0 ?v1)) ?v2) (f49 ?v_0 (f49 (f50 f51 ?v1) ?v2))))))
(check-sat)
(exit)