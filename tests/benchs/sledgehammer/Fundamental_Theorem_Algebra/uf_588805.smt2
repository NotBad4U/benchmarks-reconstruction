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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 (S5 S4) S2)
(declare-fun f5 () S5)
(declare-fun f6 (S6 S4) S4)
(declare-fun f7 () S6)
(declare-fun f8 () S4)
(declare-fun f9 (S7 S8) S3)
(declare-fun f10 () S7)
(declare-fun f11 (S9 S8) S8)
(declare-fun f12 () S9)
(declare-fun f13 () S9)
(declare-fun f14 () S8)
(declare-fun f15 () S10)
(declare-fun f16 () S10)
(declare-fun f17 (S11 S10) S4)
(declare-fun f18 (S12 S10) S11)
(declare-fun f19 () S12)
(declare-fun f20 () S10)
(declare-fun f21 (S13 S3) S10)
(declare-fun f22 (S14 S10) S13)
(declare-fun f23 () S14)
(declare-fun f24 (S15 S3) S8)
(declare-fun f25 (S16 S8) S15)
(declare-fun f26 () S16)
(declare-fun f27 () S8)
(declare-fun f28 (S17 S3) S3)
(declare-fun f29 (S18 S3) S17)
(declare-fun f30 () S18)
(declare-fun f31 () S3)
(declare-fun f32 () S4)
(declare-fun f33 () S18)
(declare-fun f34 (S19 S8) S4)
(declare-fun f35 () S19)
(declare-fun f36 (S20 S4) S6)
(declare-fun f37 () S20)
(declare-fun f38 () S9)
(declare-fun f39 (S21 S8) S9)
(declare-fun f40 () S21)
(declare-fun f41 (S22 S8) S10)
(declare-fun f42 () S22)
(declare-fun f43 (S23 S10) S10)
(declare-fun f44 (S24 S10) S23)
(declare-fun f45 () S24)
(declare-fun f46 () S8)
(declare-fun f47 () S3)
(declare-fun f48 () S4)
(declare-fun f49 () S10)
(declare-fun f50 () S24)
(declare-fun f51 () S23)
(declare-fun f52 () S8)
(declare-fun f53 () S20)
(declare-fun f54 () S24)
(declare-fun f55 (S25 S4) S3)
(declare-fun f56 () S25)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 f5 (f6 f7 f8)) (f9 f10 (f11 f12 (f11 f13 f14)))) f8)))
(assert (not (= f15 f16)))
(assert (= f8 (f17 (f18 f19 f20) f15)))
(assert (= f8 (f17 (f18 f19 f20) f15)))
(assert (=> (forall ((?v0 S10) (?v1 S10)) (=> (= f8 (f17 (f18 f19 ?v0) ?v1)) false)) false))
(assert (=> (= f15 f16) (= (f3 (f4 f5 (f6 f7 f8)) (f9 f10 (f11 f12 (f11 f13 f14)))) f8)))
(assert (= (f21 (f22 f23 f16) (f9 f10 (f11 f12 (f11 f13 f14)))) f16))
(assert (= (f24 (f25 f26 f27) (f9 f10 (f11 f12 (f11 f13 f14)))) f27))
(assert (= (f28 (f29 f30 f31) (f9 f10 (f11 f12 (f11 f13 f14)))) f31))
(assert (= (f3 (f4 f5 f32) (f9 f10 (f11 f12 (f11 f13 f14)))) f32))
(assert (forall ((?v0 S10)) (= (= (f21 (f22 f23 ?v0) (f9 f10 (f11 f12 (f11 f13 f14)))) f16) (= ?v0 f16))))
(assert (forall ((?v0 S8)) (= (= (f24 (f25 f26 ?v0) (f9 f10 (f11 f12 (f11 f13 f14)))) f27) (= ?v0 f27))))
(assert (forall ((?v0 S4)) (= (= (f3 (f4 f5 ?v0) (f9 f10 (f11 f12 (f11 f13 f14)))) f32) (= ?v0 f32))))
(assert (= (f11 f12 f14) f14))
(assert (forall ((?v0 S8)) (= (= f14 (f11 f12 ?v0)) (= f14 ?v0))))
(assert (forall ((?v0 S8)) (= (= (f11 f12 ?v0) f14) (= ?v0 f14))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f11 f12 ?v0) (f11 f13 ?v1)) false)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f11 f13 ?v0) (f11 f12 ?v1)) false)))
(assert (forall ((?v0 S8)) (= (= f14 (f11 f13 ?v0)) false)))
(assert (forall ((?v0 S8)) (= (= (f11 f13 ?v0) f14) false)))
(assert (forall ((?v0 S8)) (let ((?v_0 (f9 f10 ?v0))) (= (f28 (f29 f30 ?v_0) (f9 f10 (f11 f12 (f11 f13 f14)))) (f28 (f29 f33 ?v_0) ?v_0)))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f34 f35 ?v0))) (= (f3 (f4 f5 ?v_0) (f9 f10 (f11 f12 (f11 f13 f14)))) (f6 (f36 f37 ?v_0) ?v_0)))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f11 f38 ?v0))) (= (f24 (f25 f26 ?v_0) (f9 f10 (f11 f12 (f11 f13 f14)))) (f11 (f39 f40 ?v_0) ?v_0)))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f41 f42 ?v0))) (= (f21 (f22 f23 ?v_0) (f9 f10 (f11 f12 (f11 f13 f14)))) (f43 (f44 f45 ?v_0) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f9 f10 (f11 f12 (f11 f13 f14)))) (?v_0 (f29 f30 ?v0))) (= (f28 ?v_0 (f28 (f29 f33 ?v_1) ?v1)) (f28 (f29 f30 (f28 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_1 (f9 f10 (f11 f12 (f11 f13 f14)))) (?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f28 (f29 f33 ?v_1) ?v1)) (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S8) (?v1 S3)) (let ((?v_1 (f9 f10 (f11 f12 (f11 f13 f14)))) (?v_0 (f25 f26 ?v0))) (= (f24 ?v_0 (f28 (f29 f33 ?v_1) ?v1)) (f24 (f25 f26 (f24 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S10) (?v1 S3)) (let ((?v_1 (f9 f10 (f11 f12 (f11 f13 f14)))) (?v_0 (f22 f23 ?v0))) (= (f21 ?v_0 (f28 (f29 f33 ?v_1) ?v1)) (f21 (f22 f23 (f21 ?v_0 ?v1)) ?v_1)))))
(assert (= (f24 (f25 f26 f46) (f9 f10 (f11 f12 (f11 f13 f14)))) f46))
(assert (= (f28 (f29 f30 f47) (f9 f10 (f11 f12 (f11 f13 f14)))) f47))
(assert (= (f3 (f4 f5 f48) (f9 f10 (f11 f12 (f11 f13 f14)))) f48))
(assert (= (f21 (f22 f23 f49) (f9 f10 (f11 f12 (f11 f13 f14)))) f49))
(assert (not (= f15 f16)))
(assert (= f27 (f11 f38 f14)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f34 f35 (f11 (f39 f40 ?v0) ?v1)) (f6 (f36 f37 (f34 f35 ?v0)) (f34 f35 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f11 f38 (f11 (f39 f40 ?v0) ?v1)) (f11 (f39 f40 (f11 f38 ?v0)) (f11 f38 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f41 f42 (f11 (f39 f40 ?v0) ?v1)) (f43 (f44 f45 (f41 f42 ?v0)) (f41 f42 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f6 (f36 f37 (f34 f35 ?v0)) (f34 f35 ?v1)) (f34 f35 (f11 (f39 f40 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f11 (f39 f40 (f11 f38 ?v0)) (f11 f38 ?v1)) (f11 f38 (f11 (f39 f40 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f43 (f44 f45 (f41 f42 ?v0)) (f41 f42 ?v1)) (f41 f42 (f11 (f39 f40 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S4)) (= (f6 (f36 f37 (f34 f35 ?v0)) (f6 (f36 f37 (f34 f35 ?v1)) ?v2)) (f6 (f36 f37 (f34 f35 (f11 (f39 f40 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (f11 (f39 f40 (f11 f38 ?v0)) (f11 (f39 f40 (f11 f38 ?v1)) ?v2)) (f11 (f39 f40 (f11 f38 (f11 (f39 f40 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S10)) (= (f43 (f44 f45 (f41 f42 ?v0)) (f43 (f44 f45 (f41 f42 ?v1)) ?v2)) (f43 (f44 f45 (f41 f42 (f11 (f39 f40 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S3)) (let ((?v_0 (f25 f26 ?v0))) (= (f24 (f25 f26 (f24 ?v_0 ?v1)) ?v2) (f24 ?v_0 (f28 (f29 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S8)) (= (f11 (f39 f40 f14) ?v0) f14)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f11 (f39 f40 (f11 f12 ?v0)) ?v1) (f11 f12 (f11 (f39 f40 ?v0) ?v1)))))
(assert (= f14 f27))
(assert (= f46 (f11 f38 (f11 f13 f14))))
(assert (= (f9 f10 f14) f31))
(assert (= f31 (f9 f10 f14)))
(assert (forall ((?v0 S4)) (= (f6 (f36 f37 (f34 f35 (f11 f13 f14))) ?v0) ?v0)))
(assert (forall ((?v0 S8)) (= (f11 (f39 f40 (f11 f38 (f11 f13 f14))) ?v0) ?v0)))
(assert (forall ((?v0 S10)) (= (f43 (f44 f45 (f41 f42 (f11 f13 f14))) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f6 (f36 f37 ?v0) (f34 f35 (f11 f13 f14))) ?v0)))
(assert (forall ((?v0 S8)) (= (f11 (f39 f40 ?v0) (f11 f38 (f11 f13 f14))) ?v0)))
(assert (forall ((?v0 S10)) (= (f43 (f44 f45 ?v0) (f41 f42 (f11 f13 f14))) ?v0)))
(assert (= (f11 f38 (f11 f13 f14)) f46))
(assert (= (f9 f10 (f11 f13 f14)) f47))
(assert (= (f34 f35 (f11 f13 f14)) f48))
(assert (= (f41 f42 (f11 f13 f14)) f49))
(assert (= (f11 f38 (f11 f13 f14)) f46))
(assert (= (f34 f35 (f11 f13 f14)) f48))
(assert (= (f41 f42 (f11 f13 f14)) f49))
(assert (= f46 (f11 f38 (f11 f13 f14))))
(assert (= f48 (f34 f35 (f11 f13 f14))))
(assert (= f49 (f41 f42 (f11 f13 f14))))
(assert (= (f9 f10 (f11 f13 f14)) f47))
(assert (= f47 (f9 f10 (f11 f13 f14))))
(assert (forall ((?v0 S3)) (= (f28 (f29 f30 ?v0) (f9 f10 (f11 f13 (f11 f13 f14)))) (f28 (f29 f33 (f28 (f29 f33 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) (f9 f10 (f11 f13 (f11 f13 f14)))) (f6 (f36 f37 (f6 (f36 f37 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S8)) (= (f24 (f25 f26 ?v0) (f9 f10 (f11 f13 (f11 f13 f14)))) (f11 (f39 f40 (f11 (f39 f40 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S10)) (= (f21 (f22 f23 ?v0) (f9 f10 (f11 f13 (f11 f13 f14)))) (f43 (f44 f45 (f43 (f44 f45 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f11 f38 ?v0) (f11 f38 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f41 f42 ?v0) (f41 f42 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f34 f35 ?v0) (f34 f35 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S3)) (let ((?v_0 (f9 f10 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f11 f38 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S10)) (let ((?v_0 (f41 f42 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S4)) (let ((?v_0 (f34 f35 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f11 f13 ?v0) (f11 f13 ?v1)) (= ?v0 ?v1))))
(assert (= (= f14 f14) true))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f11 f12 ?v0) (f11 f12 ?v1)) (= ?v0 ?v1))))
(assert (= (f41 f42 f14) f16))
(assert (= (f11 f38 f14) f27))
(assert (= (f9 f10 f14) f31))
(assert (= (f34 f35 f14) f32))
(assert (= (f41 f42 f14) f16))
(assert (= (f11 f38 f14) f27))
(assert (= (f34 f35 f14) f32))
(assert (= f16 (f41 f42 f14)))
(assert (= f27 (f11 f38 f14)))
(assert (= f32 (f34 f35 f14)))
(assert (forall ((?v0 S3)) (= (f28 (f29 f30 ?v0) (f9 f10 (f11 f12 (f11 f13 f14)))) (f28 (f29 f33 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) (f9 f10 (f11 f12 (f11 f13 f14)))) (f6 (f36 f37 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f24 (f25 f26 ?v0) (f9 f10 (f11 f12 (f11 f13 f14)))) (f11 (f39 f40 ?v0) ?v0))))
(assert (forall ((?v0 S10)) (= (f21 (f22 f23 ?v0) (f9 f10 (f11 f12 (f11 f13 f14)))) (f43 (f44 f45 ?v0) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f29 f30 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 (f28 (f29 f33 (f9 f10 (f11 f12 (f11 f13 f14)))) ?v1)) (f28 (f29 f33 ?v_1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f4 f5 ?v0))) (let ((?v_1 (f3 ?v_0 ?v1))) (= (f3 ?v_0 (f28 (f29 f33 (f9 f10 (f11 f12 (f11 f13 f14)))) ?v1)) (f6 (f36 f37 ?v_1) ?v_1))))))
(assert (forall ((?v0 S8) (?v1 S3)) (let ((?v_0 (f25 f26 ?v0))) (let ((?v_1 (f24 ?v_0 ?v1))) (= (f24 ?v_0 (f28 (f29 f33 (f9 f10 (f11 f12 (f11 f13 f14)))) ?v1)) (f11 (f39 f40 ?v_1) ?v_1))))))
(assert (forall ((?v0 S10) (?v1 S3)) (let ((?v_0 (f22 f23 ?v0))) (let ((?v_1 (f21 ?v_0 ?v1))) (= (f21 ?v_0 (f28 (f29 f33 (f9 f10 (f11 f12 (f11 f13 f14)))) ?v1)) (f43 (f44 f45 ?v_1) ?v_1))))))
(assert (forall ((?v0 S3)) (= (f28 (f29 f33 ?v0) ?v0) (f28 (f29 f30 ?v0) (f9 f10 (f11 f12 (f11 f13 f14)))))))
(assert (forall ((?v0 S4)) (= (f6 (f36 f37 ?v0) ?v0) (f3 (f4 f5 ?v0) (f9 f10 (f11 f12 (f11 f13 f14)))))))
(assert (forall ((?v0 S8)) (= (f11 (f39 f40 ?v0) ?v0) (f24 (f25 f26 ?v0) (f9 f10 (f11 f12 (f11 f13 f14)))))))
(assert (forall ((?v0 S10)) (= (f43 (f44 f45 ?v0) ?v0) (f21 (f22 f23 ?v0) (f9 f10 (f11 f12 (f11 f13 f14)))))))
(assert (forall ((?v0 S10)) (let ((?v_0 (f11 f12 (f11 f13 f14)))) (let ((?v_1 (f9 f10 ?v_0))) (= (f43 (f44 f45 (f41 f42 (f11 f12 ?v_0))) (f21 (f22 f23 ?v0) ?v_1)) (f21 (f22 f23 (f43 (f44 f45 (f41 f42 ?v_0)) ?v0)) ?v_1))))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f9 f10 ?v0))) (= (f24 (f25 f26 f27) ?v_0) (ite (= ?v_0 f31) f46 f27)))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f9 f10 ?v0))) (= (f28 (f29 f30 f31) ?v_0) (ite (= ?v_0 f31) f47 f31)))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f9 f10 ?v0))) (= (f3 (f4 f5 f32) ?v_0) (ite (= ?v_0 f31) f48 f32)))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f9 f10 ?v0))) (= (f21 (f22 f23 f16) ?v_0) (ite (= ?v_0 f31) f49 f16)))))
(assert (forall ((?v0 S10) (?v1 S8)) (let ((?v_0 (f9 f10 ?v1))) (= (= (f21 (f22 f23 ?v0) ?v_0) f16) (and (= ?v0 f16) (not (= ?v_0 f31)))))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f9 f10 ?v1))) (= (= (f24 (f25 f26 ?v0) ?v_0) f27) (and (= ?v0 f27) (not (= ?v_0 f31)))))))
(assert (forall ((?v0 S3) (?v1 S8)) (let ((?v_0 (f9 f10 ?v1))) (= (= (f28 (f29 f30 ?v0) ?v_0) f31) (and (= ?v0 f31) (not (= ?v_0 f31)))))))
(assert (forall ((?v0 S4) (?v1 S8)) (let ((?v_0 (f9 f10 ?v1))) (= (= (f3 (f4 f5 ?v0) ?v_0) f32) (and (= ?v0 f32) (not (= ?v_0 f31)))))))
(assert (forall ((?v0 S10)) (let ((?v_0 (f11 f12 (f11 f13 f14)))) (let ((?v_1 (f9 f10 ?v_0))) (= (f43 (f44 f50 (f21 (f22 f23 ?v0) ?v_1)) (f41 f42 (f11 f12 ?v_0))) (f21 (f22 f23 (f43 (f44 f50 ?v0) (f41 f42 ?v_0))) ?v_1))))))
(assert (forall ((?v0 S3)) (= (f24 (f25 f26 f27) ?v0) (ite (= ?v0 f31) f46 f27))))
(assert (forall ((?v0 S3)) (= (f28 (f29 f30 f31) ?v0) (ite (= ?v0 f31) f47 f31))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f32) ?v0) (ite (= ?v0 f31) f48 f32))))
(assert (forall ((?v0 S3)) (= (f21 (f22 f23 f16) ?v0) (ite (= ?v0 f31) f49 f16))))
(assert (let ((?v_0 (f11 f12 (f11 f13 f14)))) (= (f43 f51 (f41 f42 (f11 f12 ?v_0))) (f43 f51 (f21 (f22 f23 (f41 f42 ?v_0)) (f9 f10 ?v_0))))))
(assert (forall ((?v0 S3)) (= (f24 (f25 f26 (f11 f38 f52)) (f28 (f29 f33 (f9 f10 (f11 f12 (f11 f13 f14)))) ?v0)) f46)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 (f34 f35 f52)) (f28 (f29 f33 (f9 f10 (f11 f12 (f11 f13 f14)))) ?v0)) f48)))
(assert (forall ((?v0 S3)) (= (f21 (f22 f23 (f41 f42 f52)) (f28 (f29 f33 (f9 f10 (f11 f12 (f11 f13 f14)))) ?v0)) f49)))
(assert (= f48 (f17 (f18 f19 f49) f16)))
(assert (let ((?v_0 (f11 f12 (f11 f13 f14)))) (= (f43 f51 (f41 f42 (f11 f12 ?v_0))) (f41 f42 ?v_0))))
(assert (not (= f27 f46)))
(assert (= (f43 f51 f49) f49))
(assert (forall ((?v0 S8)) (= (f11 f38 ?v0) ?v0)))
(assert (forall ((?v0 S10) (?v1 S3)) (= (f43 f51 (f21 (f22 f23 ?v0) ?v1)) (f21 (f22 f23 (f43 f51 ?v0)) ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f43 f51 (f43 (f44 f45 ?v0) ?v1)) (f43 (f44 f45 (f43 f51 ?v0)) (f43 f51 ?v1)))))
(assert (= (= f52 f52) true))
(assert (forall ((?v0 S8)) (= (f11 (f39 f40 f46) ?v0) ?v0)))
(assert (forall ((?v0 S8)) (= (f11 (f39 f40 ?v0) f46) ?v0)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f11 (f39 f40 ?v0) ?v1) (f11 (f39 f40 ?v1) ?v0))))
(assert (forall ((?v0 S10)) (= (= (f43 f51 ?v0) f49) (= ?v0 f49))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f11 (f39 f40 (f11 f38 ?v0)) (f11 f38 ?v1)) (f11 f38 (f11 (f39 f40 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f11 f38 f52))) (= (= (f11 (f39 f40 ?v0) ?v1) f46) (or (and (= ?v0 f46) (= ?v1 f46)) (and (= ?v0 ?v_0) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f39 f40 ?v0))) (= (f11 (f39 f40 (f11 ?v_0 ?v1)) ?v2) (f11 ?v_0 (f11 (f39 f40 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f44 f45 ?v0))) (= (f43 (f44 f50 (f43 ?v_0 ?v1)) (f43 ?v_0 ?v0)) (f43 (f44 f50 ?v1) ?v0)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f11 (f39 f40 ?v0) ?v1) f46) (or (= ?v0 f46) (= ?v0 (f11 f38 f52))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f43 f51 ?v0) (f43 f51 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f43 f51 (f43 (f44 f50 ?v0) ?v1)) (f43 (f44 f50 (f43 f51 ?v0)) (f43 f51 ?v1)))))
(assert (forall ((?v0 S10)) (= (= (f43 f51 ?v0) f16) (= ?v0 f16))))
(assert (= (f43 f51 f16) f16))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (= (f3 (f4 f5 (f6 (f36 f53 ?v0) ?v1)) ?v2) (f6 (f36 f53 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S3)) (= (f21 (f22 f23 (f43 (f44 f50 ?v0) ?v1)) ?v2) (f43 (f44 f50 (f21 (f22 f23 ?v0) ?v2)) (f21 (f22 f23 ?v1) ?v2)))))
(assert (= (f11 f13 f52) f52))
(assert (forall ((?v0 S8)) (= (= f52 (f11 f13 ?v0)) (= f52 ?v0))))
(assert (forall ((?v0 S8)) (= (= (f11 f13 ?v0) f52) (= ?v0 f52))))
(assert (= (= f52 f14) false))
(assert (= (= f14 f52) false))
(assert (not (= (f11 f38 f14) (f11 f38 f52))))
(assert (forall ((?v0 S8)) (= (= f52 (f11 f12 ?v0)) false)))
(assert (forall ((?v0 S8)) (= (= (f11 f12 ?v0) f52) false)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S3)) (=> (not (= ?v0 f16)) (= (f21 (f22 f23 (f43 (f44 f50 ?v1) ?v0)) ?v2) (f43 (f44 f50 (f21 (f22 f23 ?v1) ?v2)) (f21 (f22 f23 ?v0) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (=> (not (= ?v0 f32)) (= (f3 (f4 f5 (f6 (f36 f53 ?v1) ?v0)) ?v2) (f6 (f36 f53 (f3 (f4 f5 ?v1) ?v2)) (f3 (f4 f5 ?v0) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f36 f53 f48))) (= (f6 ?v_0 (f3 (f4 f5 ?v0) ?v1)) (f3 (f4 f5 (f6 ?v_0 ?v0)) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S3)) (let ((?v_0 (f44 f50 f49))) (= (f43 ?v_0 (f21 (f22 f23 ?v0) ?v1)) (f21 (f22 f23 (f43 ?v_0 ?v0)) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S8) (?v2 S10)) (let ((?v_0 (f41 f42 ?v1))) (= (= (f43 (f44 f50 ?v0) ?v_0) ?v2) (ite (not (= ?v_0 f16)) (= ?v0 (f43 (f44 f45 ?v2) ?v_0)) (= ?v2 f16))))))
(assert (forall ((?v0 S4) (?v1 S8) (?v2 S4)) (let ((?v_0 (f34 f35 ?v1))) (= (= (f6 (f36 f53 ?v0) ?v_0) ?v2) (ite (not (= ?v_0 f32)) (= ?v0 (f6 (f36 f37 ?v2) ?v_0)) (= ?v2 f32))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S8)) (let ((?v_0 (f41 f42 ?v2))) (= (= (f43 (f44 f50 ?v0) ?v1) ?v_0) (ite (not (= ?v1 f16)) (= ?v0 (f43 (f44 f45 ?v_0) ?v1)) (= ?v_0 f16))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S8)) (let ((?v_0 (f34 f35 ?v2))) (= (= (f6 (f36 f53 ?v0) ?v1) ?v_0) (ite (not (= ?v1 f32)) (= ?v0 (f6 (f36 f37 ?v_0) ?v1)) (= ?v_0 f32))))))
(assert (forall ((?v0 S8) (?v1 S10) (?v2 S10)) (let ((?v_0 (f41 f42 ?v0))) (= (= ?v_0 (f43 (f44 f50 ?v1) ?v2)) (ite (not (= ?v2 f16)) (= (f43 (f44 f45 ?v_0) ?v2) ?v1) (= ?v_0 f16))))))
(assert (forall ((?v0 S8) (?v1 S4) (?v2 S4)) (let ((?v_0 (f34 f35 ?v0))) (= (= ?v_0 (f6 (f36 f53 ?v1) ?v2)) (ite (not (= ?v2 f32)) (= (f6 (f36 f37 ?v_0) ?v2) ?v1) (= ?v_0 f32))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S8)) (let ((?v_0 (f41 f42 ?v2))) (= (= ?v0 (f43 (f44 f50 ?v1) ?v_0)) (ite (not (= ?v_0 f16)) (= (f43 (f44 f45 ?v0) ?v_0) ?v1) (= ?v0 f16))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S8)) (let ((?v_0 (f34 f35 ?v2))) (= (= ?v0 (f6 (f36 f53 ?v1) ?v_0)) (ite (not (= ?v_0 f32)) (= (f6 (f36 f37 ?v0) ?v_0) ?v1) (= ?v0 f32))))))
(assert (forall ((?v0 S10)) (= (f43 (f44 f50 ?v0) (f41 f42 f14)) f16)))
(assert (forall ((?v0 S4)) (= (f6 (f36 f53 ?v0) (f34 f35 f14)) f32)))
(assert (forall ((?v0 S10)) (= (f43 (f44 f50 ?v0) (f41 f42 (f11 f13 f14))) ?v0)))
(assert (forall ((?v0 S4)) (= (f6 (f36 f53 ?v0) (f34 f35 (f11 f13 f14))) ?v0)))
(assert (forall ((?v0 S10)) (= (f43 (f44 f50 ?v0) (f41 f42 (f11 f13 f14))) ?v0)))
(assert (forall ((?v0 S4)) (= (f6 (f36 f53 ?v0) (f34 f35 (f11 f13 f14))) ?v0)))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f36 f37 ?v0))) (= (f6 (f36 f37 (f6 ?v_0 ?v1)) (f6 (f36 f37 ?v2) ?v3)) (f6 (f36 f37 (f6 ?v_0 ?v2)) (f6 (f36 f37 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f29 f33 ?v0))) (= (f28 (f29 f33 (f28 ?v_0 ?v1)) (f28 (f29 f33 ?v2) ?v3)) (f28 (f29 f33 (f28 ?v_0 ?v2)) (f28 (f29 f33 ?v1) ?v3))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f39 f40 ?v0))) (= (f11 (f39 f40 (f11 ?v_0 ?v1)) (f11 (f39 f40 ?v2) ?v3)) (f11 (f39 f40 (f11 ?v_0 ?v2)) (f11 (f39 f40 ?v1) ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f44 f45 ?v0))) (= (f43 (f44 f45 (f43 ?v_0 ?v1)) (f43 (f44 f45 ?v2) ?v3)) (f43 (f44 f45 (f43 ?v_0 ?v2)) (f43 (f44 f45 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_1 (f36 f37 (f6 (f36 f37 ?v0) ?v1))) (?v_0 (f36 f37 ?v2))) (= (f6 ?v_1 (f6 ?v_0 ?v3)) (f6 ?v_0 (f6 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f29 f33 (f28 (f29 f33 ?v0) ?v1))) (?v_0 (f29 f33 ?v2))) (= (f28 ?v_1 (f28 ?v_0 ?v3)) (f28 ?v_0 (f28 ?v_1 ?v3))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_1 (f39 f40 (f11 (f39 f40 ?v0) ?v1))) (?v_0 (f39 f40 ?v2))) (= (f11 ?v_1 (f11 ?v_0 ?v3)) (f11 ?v_0 (f11 ?v_1 ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_1 (f44 f45 (f43 (f44 f45 ?v0) ?v1))) (?v_0 (f44 f45 ?v2))) (= (f43 ?v_1 (f43 ?v_0 ?v3)) (f43 ?v_0 (f43 ?v_1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f36 f37 ?v0)) (?v_1 (f6 (f36 f37 ?v2) ?v3))) (= (f6 (f36 f37 (f6 ?v_0 ?v1)) ?v_1) (f6 ?v_0 (f6 (f36 f37 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f29 f33 ?v0)) (?v_1 (f28 (f29 f33 ?v2) ?v3))) (= (f28 (f29 f33 (f28 ?v_0 ?v1)) ?v_1) (f28 ?v_0 (f28 (f29 f33 ?v1) ?v_1))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f39 f40 ?v0)) (?v_1 (f11 (f39 f40 ?v2) ?v3))) (= (f11 (f39 f40 (f11 ?v_0 ?v1)) ?v_1) (f11 ?v_0 (f11 (f39 f40 ?v1) ?v_1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f44 f45 ?v0)) (?v_1 (f43 (f44 f45 ?v2) ?v3))) (= (f43 (f44 f45 (f43 ?v_0 ?v1)) ?v_1) (f43 ?v_0 (f43 (f44 f45 ?v1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f36 f37 ?v0))) (= (f6 (f36 f37 (f6 ?v_0 ?v1)) ?v2) (f6 (f36 f37 (f6 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f29 f33 ?v0))) (= (f28 (f29 f33 (f28 ?v_0 ?v1)) ?v2) (f28 (f29 f33 (f28 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f39 f40 ?v0))) (= (f11 (f39 f40 (f11 ?v_0 ?v1)) ?v2) (f11 (f39 f40 (f11 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f44 f45 ?v0))) (= (f43 (f44 f45 (f43 ?v_0 ?v1)) ?v2) (f43 (f44 f45 (f43 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f36 f37 ?v0))) (= (f6 (f36 f37 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f36 f37 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f29 f33 ?v0))) (= (f28 (f29 f33 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f29 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f39 f40 ?v0))) (= (f11 (f39 f40 (f11 ?v_0 ?v1)) ?v2) (f11 ?v_0 (f11 (f39 f40 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f44 f45 ?v0))) (= (f43 (f44 f45 (f43 ?v_0 ?v1)) ?v2) (f43 ?v_0 (f43 (f44 f45 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f36 f37 ?v0))) (= (f6 ?v_0 (f6 (f36 f37 ?v1) ?v2)) (f6 (f36 f37 (f6 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f29 f33 ?v0))) (= (f28 ?v_0 (f28 (f29 f33 ?v1) ?v2)) (f28 (f29 f33 (f28 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f39 f40 ?v0))) (= (f11 ?v_0 (f11 (f39 f40 ?v1) ?v2)) (f11 (f39 f40 (f11 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f44 f45 ?v0))) (= (f43 ?v_0 (f43 (f44 f45 ?v1) ?v2)) (f43 (f44 f45 (f43 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f36 f37 ?v0)) (?v_0 (f36 f37 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f29 f33 ?v0)) (?v_0 (f29 f33 ?v1))) (= (f28 ?v_1 (f28 ?v_0 ?v2)) (f28 ?v_0 (f28 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f39 f40 ?v0)) (?v_0 (f39 f40 ?v1))) (= (f11 ?v_1 (f11 ?v_0 ?v2)) (f11 ?v_0 (f11 ?v_1 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_1 (f44 f45 ?v0)) (?v_0 (f44 f45 ?v1))) (= (f43 ?v_1 (f43 ?v_0 ?v2)) (f43 ?v_0 (f43 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f6 (f36 f37 ?v0) ?v1) (f6 (f36 f37 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f28 (f29 f33 ?v0) ?v1) (f28 (f29 f33 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f11 (f39 f40 ?v0) ?v1) (f11 (f39 f40 ?v1) ?v0))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f43 (f44 f45 ?v0) ?v1) (f43 (f44 f45 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (= (f28 (f29 f30 ?v0) f47) ?v0)))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) f47) ?v0)))
(assert (forall ((?v0 S8)) (= (f24 (f25 f26 ?v0) f47) ?v0)))
(assert (forall ((?v0 S10)) (= (f21 (f22 f23 ?v0) f47) ?v0)))
(assert (forall ((?v0 S3)) (= (f28 (f29 f30 ?v0) f47) ?v0)))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) f47) ?v0)))
(assert (forall ((?v0 S8)) (= (f24 (f25 f26 ?v0) f47) ?v0)))
(assert (forall ((?v0 S10)) (= (f21 (f22 f23 ?v0) f47) ?v0)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (= (= (f17 (f18 f19 ?v0) ?v1) (f17 (f18 f19 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S10)) (= (f43 (f44 f45 ?v0) f16) f16)))
(assert (forall ((?v0 S8)) (= (f11 (f39 f40 ?v0) f27) f27)))
(assert (forall ((?v0 S3)) (= (f28 (f29 f33 ?v0) f31) f31)))
(assert (forall ((?v0 S4)) (= (f6 (f36 f37 ?v0) f32) f32)))
(assert (forall ((?v0 S10)) (= (f43 (f44 f45 f16) ?v0) f16)))
(assert (forall ((?v0 S8)) (= (f11 (f39 f40 f27) ?v0) f27)))
(assert (forall ((?v0 S3)) (= (f28 (f29 f33 f31) ?v0) f31)))
(assert (forall ((?v0 S4)) (= (f6 (f36 f37 f32) ?v0) f32)))
(assert (forall ((?v0 S8)) (= (f11 (f39 f40 ?v0) f46) ?v0)))
(assert (forall ((?v0 S3)) (= (f28 (f29 f33 ?v0) f47) ?v0)))
(assert (forall ((?v0 S4)) (= (f6 (f36 f37 ?v0) f48) ?v0)))
(assert (forall ((?v0 S10)) (= (f43 (f44 f45 ?v0) f49) ?v0)))
(assert (forall ((?v0 S8)) (= (f11 (f39 f40 f46) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f28 (f29 f33 f47) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f6 (f36 f37 f48) ?v0) ?v0)))
(assert (forall ((?v0 S10)) (= (f43 (f44 f45 f49) ?v0) ?v0)))
(assert (forall ((?v0 S10) (?v1 S3)) (=> (not (= ?v0 f16)) (not (= (f21 (f22 f23 ?v0) ?v1) f16)))))
(assert (forall ((?v0 S8) (?v1 S3)) (=> (not (= ?v0 f27)) (not (= (f24 (f25 f26 ?v0) ?v1) f27)))))
(assert (forall ((?v0 S4) (?v1 S3)) (=> (not (= ?v0 f32)) (not (= (f3 (f4 f5 ?v0) ?v1) f32)))))
(assert (forall ((?v0 S10) (?v1 S3)) (= (= (f21 (f22 f23 ?v0) ?v1) f16) (and (= ?v0 f16) (not (= ?v1 f31))))))
(assert (forall ((?v0 S8) (?v1 S3)) (= (= (f24 (f25 f26 ?v0) ?v1) f27) (and (= ?v0 f27) (not (= ?v1 f31))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f28 (f29 f30 ?v0) ?v1) f31) (and (= ?v0 f31) (not (= ?v1 f31))))))
(assert (forall ((?v0 S4) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f32) (and (= ?v0 f32) (not (= ?v1 f31))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f28 (f29 f30 ?v0) ?v1))) (= (f28 (f29 f33 ?v_0) ?v0) (f28 (f29 f33 ?v0) ?v_0)))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f3 (f4 f5 ?v0) ?v1))) (= (f6 (f36 f37 ?v_0) ?v0) (f6 (f36 f37 ?v0) ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S3)) (let ((?v_0 (f24 (f25 f26 ?v0) ?v1))) (= (f11 (f39 f40 ?v_0) ?v0) (f11 (f39 f40 ?v0) ?v_0)))))
(assert (forall ((?v0 S10) (?v1 S3)) (let ((?v_0 (f21 (f22 f23 ?v0) ?v1))) (= (f43 (f44 f45 ?v_0) ?v0) (f43 (f44 f45 ?v0) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f28 (f29 f30 (f28 (f29 f33 ?v0) ?v1)) ?v2) (f28 (f29 f33 (f28 (f29 f30 ?v0) ?v2)) (f28 (f29 f30 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (= (f3 (f4 f5 (f6 (f36 f37 ?v0) ?v1)) ?v2) (f6 (f36 f37 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S3)) (= (f24 (f25 f26 (f11 (f39 f40 ?v0) ?v1)) ?v2) (f11 (f39 f40 (f24 (f25 f26 ?v0) ?v2)) (f24 (f25 f26 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S3)) (= (f21 (f22 f23 (f43 (f44 f45 ?v0) ?v1)) ?v2) (f43 (f44 f45 (f21 (f22 f23 ?v0) ?v2)) (f21 (f22 f23 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f28 (f29 f30 (f28 (f29 f33 ?v0) ?v1)) ?v2) (f28 (f29 f33 (f28 (f29 f30 ?v0) ?v2)) (f28 (f29 f30 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (= (f3 (f4 f5 (f6 (f36 f37 ?v0) ?v1)) ?v2) (f6 (f36 f37 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S3)) (= (f24 (f25 f26 (f11 (f39 f40 ?v0) ?v1)) ?v2) (f11 (f39 f40 (f24 (f25 f26 ?v0) ?v2)) (f24 (f25 f26 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S3)) (= (f21 (f22 f23 (f43 (f44 f45 ?v0) ?v1)) ?v2) (f43 (f44 f45 (f21 (f22 f23 ?v0) ?v2)) (f21 (f22 f23 ?v1) ?v2)))))
(assert (forall ((?v0 S3)) (= (f24 (f25 f26 f46) ?v0) f46)))
(assert (forall ((?v0 S3)) (= (f28 (f29 f30 f47) ?v0) f47)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f48) ?v0) f48)))
(assert (forall ((?v0 S3)) (= (f21 (f22 f23 f49) ?v0) f49)))
(assert (forall ((?v0 S8)) (= (f24 (f25 f26 ?v0) f31) f46)))
(assert (forall ((?v0 S3)) (= (f28 (f29 f30 ?v0) f31) f47)))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) f31) f48)))
(assert (forall ((?v0 S10)) (= (f21 (f22 f23 ?v0) f31) f49)))
(assert (forall ((?v0 S8)) (= (f24 (f25 f26 ?v0) f31) f46)))
(assert (forall ((?v0 S3)) (= (f28 (f29 f30 ?v0) f31) f47)))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) f31) f48)))
(assert (forall ((?v0 S10)) (= (f21 (f22 f23 ?v0) f31) f49)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f29 f30 ?v0))) (= (f28 ?v_0 (f28 (f29 f33 ?v1) ?v2)) (f28 (f29 f30 (f28 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f28 (f29 f33 ?v1) ?v2)) (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S3)) (let ((?v_0 (f25 f26 ?v0))) (= (f24 ?v_0 (f28 (f29 f33 ?v1) ?v2)) (f24 (f25 f26 (f24 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S3) (?v2 S3)) (let ((?v_0 (f22 f23 ?v0))) (= (f21 ?v_0 (f28 (f29 f33 ?v1) ?v2)) (f21 (f22 f23 (f21 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f29 f30 ?v0))) (= (f28 (f29 f30 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f29 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f28 (f29 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S3)) (let ((?v_0 (f25 f26 ?v0))) (= (f24 (f25 f26 (f24 ?v_0 ?v1)) ?v2) (f24 ?v_0 (f28 (f29 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S3) (?v2 S3)) (let ((?v_0 (f22 f23 ?v0))) (= (f21 (f22 f23 (f21 ?v_0 ?v1)) ?v2) (f21 ?v_0 (f28 (f29 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S8)) (= (= (f17 (f18 f19 ?v0) ?v1) (f34 f35 ?v2)) (and (= ?v0 (f41 f42 ?v2)) (= ?v1 f16)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f17 (f18 f19 ?v0) ?v1) f32) (and (= ?v0 f16) (= ?v1 f16)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f17 (f18 f19 ?v0) ?v1) f48) (and (= ?v0 f49) (= ?v1 f16)))))
(assert (= f32 (f17 (f18 f19 f16) f16)))
(assert (let ((?v_0 (f11 f12 (f11 f13 f14))) (?v_1 (f43 (f44 f54 (f43 f51 (f43 (f44 f54 (f43 (f44 f45 f20) f20)) (f43 (f44 f45 f15) f15)))) f20))) (= (f43 f51 (f43 (f44 f50 (f21 (f22 f23 ?v_1) (f9 f10 ?v_0))) (f41 f42 (f11 f12 ?v_0)))) (f43 (f44 f50 ?v_1) (f41 f42 ?v_0)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f44 f45 (f41 f42 (f11 f12 (f11 f13 f14))))) (?v_1 (f44 f50 ?v1))) (= (= ?v0 (f43 ?v_1 (f43 ?v_0 ?v2))) (= (f43 ?v_0 ?v0) (f43 ?v_1 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f55 f56 (f17 (f18 f19 ?v0) ?v1)) f31)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 (f28 (f29 f33 ?v0) ?v1)) (or (= ?v1 f47) (= ?v0 f31)))))
(check-sat)
(exit)