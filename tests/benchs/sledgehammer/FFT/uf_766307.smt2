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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S4) S4)
(declare-fun f6 (S6 S4) S5)
(declare-fun f7 () S6)
(declare-fun f8 () S3)
(declare-fun f9 (S7 S2) S2)
(declare-fun f10 () S7)
(declare-fun f11 (S8 S2) S7)
(declare-fun f12 () S8)
(declare-fun f13 (S9 S10) S2)
(declare-fun f14 () S9)
(declare-fun f15 (S11 S10) S10)
(declare-fun f16 () S11)
(declare-fun f17 () S11)
(declare-fun f18 () S10)
(declare-fun f19 (S12 S4) S3)
(declare-fun f20 () S12)
(declare-fun f21 () S3)
(declare-fun f22 () S2)
(declare-fun f23 () S8)
(declare-fun f24 () S2)
(declare-fun f25 () S3)
(declare-fun f26 (S13 S2) S3)
(declare-fun f27 (S14 S3) S13)
(declare-fun f28 (S15 S2) S14)
(declare-fun f29 () S15)
(declare-fun f30 (S16 S17) S4)
(declare-fun f31 (S18 S3) S16)
(declare-fun f32 () S18)
(declare-fun f33 (S2 S2) S17)
(declare-fun f34 () S2)
(declare-fun f35 () S6)
(declare-fun f36 () S4)
(declare-fun f37 (S19 S3) S3)
(declare-fun f38 (S20 S2) S19)
(declare-fun f39 () S20)
(declare-fun f40 (S21 S2) S10)
(declare-fun f41 (S22 S10) S21)
(declare-fun f42 () S22)
(declare-fun f43 (S23 S10) S11)
(declare-fun f44 () S23)
(declare-fun f45 () S8)
(declare-fun f46 () S23)
(declare-fun f47 () S11)
(declare-fun f48 () S6)
(declare-fun f49 (S24 S10) S4)
(declare-fun f50 () S24)
(declare-fun f51 () S10)
(declare-fun f52 () S4)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f11 f12 (f13 f14 (f15 f16 (f15 f17 f18)))))) (let ((?v_1 (f9 ?v_0 ?v0))) (= (f3 f4 ?v0) (f5 (f6 f7 (f3 f8 (f9 f10 ?v_1))) (f3 (f19 f20 (f3 f21 (f9 ?v_0 f22))) (f9 (f11 f23 f24) (f9 (f11 f12 f24) ?v_1)))))))))
(assert (forall ((?v0 S2)) (= (f3 f25 ?v0) (f5 (f6 f7 (f3 f8 (f9 f10 (f9 (f11 f12 (f13 f14 (f15 f16 (f15 f17 f18)))) ?v0)))) (f3 (f19 f20 (f3 f21 f22)) (f9 (f11 f12 f24) ?v0))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2)) (= (f3 (f26 (f27 (f28 f29 ?v0) ?v1) ?v2) ?v3) (f5 (f6 f7 (f3 ?v1 ?v3)) (f3 (f19 f20 (f3 f21 ?v0)) (f9 (f11 f12 ?v2) ?v3))))))
(assert (let ((?v_0 (f33 f34 f22))) (not (= (f30 (f31 f32 f4) ?v_0) (f5 (f6 f35 (f3 (f19 f20 (f5 (f6 f7 f36) (f3 f21 (f9 (f11 f12 (f13 f14 (f15 f16 (f15 f17 f18)))) f22)))) f24)) (f30 (f31 f32 f25) ?v_0))))))
(assert (= (f3 f21 f34) f36))
(assert (forall ((?v0 S2)) (= (f3 (f19 f20 (f3 f21 ?v0)) ?v0) f36)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f12 (f13 f14 (f15 f16 (f15 f17 f18))))) (?v_1 (f11 f12 ?v1))) (= (f3 (f19 f20 (f3 f21 (f9 ?v_0 ?v0))) (f9 ?v_1 (f9 ?v_0 ?v2))) (f3 (f19 f20 (f3 f21 ?v0)) (f9 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (f3 (f37 (f38 f39 ?v0) ?v1) ?v2) (f30 (f31 f32 (f26 (f27 (f28 f29 ?v0) ?v1) ?v2)) (f33 f34 ?v0)))))
(assert (forall ((?v0 S10) (?v1 S2)) (let ((?v_1 (f13 f14 (f15 f16 (f15 f17 f18)))) (?v_0 (f41 f42 ?v0))) (= (f40 ?v_0 (f9 f10 (f9 (f11 f12 ?v_1) ?v1))) (f15 (f43 f44 ?v0) (f40 (f41 f42 (f40 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f13 f14 (f15 f16 (f15 f17 f18)))) (?v_0 (f11 f45 ?v0))) (= (f9 ?v_0 (f9 f10 (f9 (f11 f12 ?v_1) ?v1))) (f9 (f11 f12 ?v0) (f9 (f11 f45 (f9 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_1 (f13 f14 (f15 f16 (f15 f17 f18)))) (?v_0 (f19 f20 ?v0))) (= (f3 ?v_0 (f9 f10 (f9 (f11 f12 ?v_1) ?v1))) (f5 (f6 f35 ?v0) (f3 (f19 f20 (f3 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S10) (?v1 S2)) (let ((?v_0 (f41 f42 ?v0))) (let ((?v_1 (f40 ?v_0 ?v1))) (= (f40 ?v_0 (f9 f10 (f9 (f11 f12 (f13 f14 (f15 f16 (f15 f17 f18)))) ?v1))) (f15 (f43 f44 ?v0) (f15 (f43 f44 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f11 f45 ?v0))) (let ((?v_1 (f9 ?v_0 ?v1))) (= (f9 ?v_0 (f9 f10 (f9 (f11 f12 (f13 f14 (f15 f16 (f15 f17 f18)))) ?v1))) (f9 (f11 f12 ?v0) (f9 (f11 f12 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f19 f20 ?v0))) (let ((?v_1 (f3 ?v_0 ?v1))) (= (f3 ?v_0 (f9 f10 (f9 (f11 f12 (f13 f14 (f15 f16 (f15 f17 f18)))) ?v1))) (f5 (f6 f35 ?v0) (f5 (f6 f35 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_1 (f15 f16 (f15 f17 f18)))) (let ((?v_0 (f13 f14 ?v_1))) (= (f40 (f41 f42 (f15 (f43 f46 ?v0) ?v1)) ?v_0) (f15 (f43 f46 (f15 (f43 f46 (f40 (f41 f42 ?v0) ?v_0)) (f40 (f41 f42 ?v1) ?v_0))) (f15 (f43 f44 (f15 (f43 f44 (f15 f47 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_1 (f15 f16 (f15 f17 f18)))) (let ((?v_0 (f13 f14 ?v_1))) (= (f3 (f19 f20 (f5 (f6 f48 ?v0) ?v1)) ?v_0) (f5 (f6 f48 (f5 (f6 f48 (f3 (f19 f20 ?v0) ?v_0)) (f3 (f19 f20 ?v1) ?v_0))) (f5 (f6 f35 (f5 (f6 f35 (f49 f50 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f13 f14 (f15 f16 (f15 f17 f18))))) (= (f9 (f11 f45 (f9 (f11 f23 ?v0) ?v1)) ?v_0) (f9 (f11 f23 (f9 (f11 f23 (f9 (f11 f45 ?v0) ?v_0)) (f9 (f11 f45 ?v1) ?v_0))) (f9 (f11 f12 (f9 (f11 f12 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S10) (?v1 S2)) (let ((?v_0 (f41 f42 ?v0))) (let ((?v_1 (f40 ?v_0 ?v1))) (= (f40 ?v_0 (f9 (f11 f12 (f13 f14 (f15 f16 (f15 f17 f18)))) ?v1)) (f15 (f43 f44 ?v_1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f11 f45 ?v0))) (let ((?v_1 (f9 ?v_0 ?v1))) (= (f9 ?v_0 (f9 (f11 f12 (f13 f14 (f15 f16 (f15 f17 f18)))) ?v1)) (f9 (f11 f12 ?v_1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f19 f20 ?v0))) (let ((?v_1 (f3 ?v_0 ?v1))) (= (f3 ?v_0 (f9 (f11 f12 (f13 f14 (f15 f16 (f15 f17 f18)))) ?v1)) (f5 (f6 f35 ?v_1) ?v_1))))))
(assert (forall ((?v0 S10)) (let ((?v_0 (f15 f47 ?v0))) (= (f40 (f41 f42 ?v_0) (f13 f14 (f15 f16 (f15 f17 f18)))) (f15 (f43 f44 ?v_0) ?v_0)))))
(assert (forall ((?v0 S10)) (let ((?v_0 (f13 f14 ?v0))) (= (f9 (f11 f45 ?v_0) (f13 f14 (f15 f16 (f15 f17 f18)))) (f9 (f11 f12 ?v_0) ?v_0)))))
(assert (forall ((?v0 S10)) (let ((?v_0 (f49 f50 ?v0))) (= (f3 (f19 f20 ?v_0) (f13 f14 (f15 f16 (f15 f17 f18)))) (f5 (f6 f35 ?v_0) ?v_0)))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f13 f14 (f15 f16 (f15 f17 f18))))) (= (= (f15 (f43 f46 (f40 (f41 f42 ?v0) ?v_0)) (f40 (f41 f42 ?v1) ?v_0)) f51) (and (= ?v0 f51) (= ?v1 f51))))))
(assert (forall ((?v0 S2)) (= (f9 (f11 f12 ?v0) (f13 f14 (f15 f16 (f15 f17 f18)))) (f9 (f11 f23 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f9 (f11 f12 (f13 f14 (f15 f16 (f15 f17 f18)))) ?v0) (f9 (f11 f23 ?v0) ?v0))))
(assert (forall ((?v0 S10) (?v1 S2)) (let ((?v_1 (f13 f14 (f15 f16 (f15 f17 f18)))) (?v_0 (f41 f42 ?v0))) (= (f40 ?v_0 (f9 (f11 f12 ?v_1) ?v1)) (f40 (f41 f42 (f40 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f13 f14 (f15 f16 (f15 f17 f18)))) (?v_0 (f11 f45 ?v0))) (= (f9 ?v_0 (f9 (f11 f12 ?v_1) ?v1)) (f9 (f11 f45 (f9 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_1 (f13 f14 (f15 f16 (f15 f17 f18)))) (?v_0 (f19 f20 ?v0))) (= (f3 ?v_0 (f9 (f11 f12 ?v_1) ?v1)) (f3 (f19 f20 (f3 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S2)) (= (f9 (f11 f23 ?v0) (f13 f14 (f15 f16 (f15 f17 f18)))) (f9 f10 (f9 f10 ?v0)))))
(assert (forall ((?v0 S2)) (= (f9 (f11 f23 (f13 f14 (f15 f16 (f15 f17 f18)))) ?v0) (f9 f10 (f9 f10 ?v0)))))
(assert (forall ((?v0 S2)) (not (= (f3 f21 ?v0) f52))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f43 f44 ?v0))) (= (f15 (f43 f44 (f15 ?v_0 ?v1)) (f15 (f43 f44 ?v2) ?v3)) (f15 (f43 f44 (f15 ?v_0 ?v2)) (f15 (f43 f44 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f11 f12 ?v0))) (= (f9 (f11 f12 (f9 ?v_0 ?v1)) (f9 (f11 f12 ?v2) ?v3)) (f9 (f11 f12 (f9 ?v_0 ?v2)) (f9 (f11 f12 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f35 ?v0))) (= (f5 (f6 f35 (f5 ?v_0 ?v1)) (f5 (f6 f35 ?v2) ?v3)) (f5 (f6 f35 (f5 ?v_0 ?v2)) (f5 (f6 f35 ?v1) ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_1 (f43 f44 (f15 (f43 f44 ?v0) ?v1))) (?v_0 (f43 f44 ?v2))) (= (f15 ?v_1 (f15 ?v_0 ?v3)) (f15 ?v_0 (f15 ?v_1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_1 (f11 f12 (f9 (f11 f12 ?v0) ?v1))) (?v_0 (f11 f12 ?v2))) (= (f9 ?v_1 (f9 ?v_0 ?v3)) (f9 ?v_0 (f9 ?v_1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_1 (f6 f35 (f5 (f6 f35 ?v0) ?v1))) (?v_0 (f6 f35 ?v2))) (= (f5 ?v_1 (f5 ?v_0 ?v3)) (f5 ?v_0 (f5 ?v_1 ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f43 f44 ?v0)) (?v_1 (f15 (f43 f44 ?v2) ?v3))) (= (f15 (f43 f44 (f15 ?v_0 ?v1)) ?v_1) (f15 ?v_0 (f15 (f43 f44 ?v1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f11 f12 ?v0)) (?v_1 (f9 (f11 f12 ?v2) ?v3))) (= (f9 (f11 f12 (f9 ?v_0 ?v1)) ?v_1) (f9 ?v_0 (f9 (f11 f12 ?v1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f35 ?v0)) (?v_1 (f5 (f6 f35 ?v2) ?v3))) (= (f5 (f6 f35 (f5 ?v_0 ?v1)) ?v_1) (f5 ?v_0 (f5 (f6 f35 ?v1) ?v_1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f43 f44 ?v0))) (= (f15 (f43 f44 (f15 ?v_0 ?v1)) ?v2) (f15 (f43 f44 (f15 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f12 ?v0))) (= (f9 (f11 f12 (f9 ?v_0 ?v1)) ?v2) (f9 (f11 f12 (f9 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f35 ?v0))) (= (f5 (f6 f35 (f5 ?v_0 ?v1)) ?v2) (f5 (f6 f35 (f5 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f43 f44 ?v0))) (= (f15 (f43 f44 (f15 ?v_0 ?v1)) ?v2) (f15 ?v_0 (f15 (f43 f44 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f12 ?v0))) (= (f9 (f11 f12 (f9 ?v_0 ?v1)) ?v2) (f9 ?v_0 (f9 (f11 f12 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f35 ?v0))) (= (f5 (f6 f35 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f35 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f43 f44 ?v0))) (= (f15 ?v_0 (f15 (f43 f44 ?v1) ?v2)) (f15 (f43 f44 (f15 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f12 ?v0))) (= (f9 ?v_0 (f9 (f11 f12 ?v1) ?v2)) (f9 (f11 f12 (f9 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f35 ?v0))) (= (f5 ?v_0 (f5 (f6 f35 ?v1) ?v2)) (f5 (f6 f35 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_1 (f43 f44 ?v0)) (?v_0 (f43 f44 ?v1))) (= (f15 ?v_1 (f15 ?v_0 ?v2)) (f15 ?v_0 (f15 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f11 f12 ?v0)) (?v_0 (f11 f12 ?v1))) (= (f9 ?v_1 (f9 ?v_0 ?v2)) (f9 ?v_0 (f9 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f6 f35 ?v0)) (?v_0 (f6 f35 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f15 (f43 f44 ?v0) ?v1) (f15 (f43 f44 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f11 f12 ?v0) ?v1) (f9 (f11 f12 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f5 (f6 f35 ?v0) ?v1) (f5 (f6 f35 ?v1) ?v0))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f43 f46 ?v0))) (= (f15 (f43 f46 (f15 ?v_0 ?v1)) (f15 (f43 f46 ?v2) ?v3)) (f15 (f43 f46 (f15 ?v_0 ?v2)) (f15 (f43 f46 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f48 ?v0))) (= (f5 (f6 f48 (f5 ?v_0 ?v1)) (f5 (f6 f48 ?v2) ?v3)) (f5 (f6 f48 (f5 ?v_0 ?v2)) (f5 (f6 f48 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f11 f23 ?v0))) (= (f9 (f11 f23 (f9 ?v_0 ?v1)) (f9 (f11 f23 ?v2) ?v3)) (f9 (f11 f23 (f9 ?v_0 ?v2)) (f9 (f11 f23 ?v1) ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f43 f46 ?v0))) (= (f15 (f43 f46 (f15 ?v_0 ?v1)) ?v2) (f15 (f43 f46 (f15 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f48 ?v0))) (= (f5 (f6 f48 (f5 ?v_0 ?v1)) ?v2) (f5 (f6 f48 (f5 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f23 ?v0))) (= (f9 (f11 f23 (f9 ?v_0 ?v1)) ?v2) (f9 (f11 f23 (f9 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f43 f46 ?v0))) (= (f15 (f43 f46 (f15 ?v_0 ?v1)) ?v2) (f15 ?v_0 (f15 (f43 f46 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f48 ?v0))) (= (f5 (f6 f48 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f48 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f23 ?v0))) (= (f9 (f11 f23 (f9 ?v_0 ?v1)) ?v2) (f9 ?v_0 (f9 (f11 f23 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f43 f46 ?v0))) (= (f15 ?v_0 (f15 (f43 f46 ?v1) ?v2)) (f15 (f43 f46 (f15 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f48 ?v0))) (= (f5 ?v_0 (f5 (f6 f48 ?v1) ?v2)) (f5 (f6 f48 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f23 ?v0))) (= (f9 ?v_0 (f9 (f11 f23 ?v1) ?v2)) (f9 (f11 f23 (f9 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_1 (f43 f46 ?v0)) (?v_0 (f43 f46 ?v1))) (= (f15 ?v_1 (f15 ?v_0 ?v2)) (f15 ?v_0 (f15 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f6 f48 ?v0)) (?v_0 (f6 f48 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f11 f23 ?v0)) (?v_0 (f11 f23 ?v1))) (= (f9 ?v_1 (f9 ?v_0 ?v2)) (f9 ?v_0 (f9 ?v_1 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f15 (f43 f46 ?v0) ?v1) (f15 (f43 f46 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f5 (f6 f48 ?v0) ?v1) (f5 (f6 f48 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f11 f23 ?v0) ?v1) (f9 (f11 f23 ?v1) ?v0))))
(assert (forall ((?v0 S2)) (= (f9 (f11 f12 ?v0) f34) f34)))
(assert (forall ((?v0 S10)) (= (f15 (f43 f44 ?v0) f51) f51)))
(assert (forall ((?v0 S4)) (= (f5 (f6 f35 ?v0) f52) f52)))
(assert (forall ((?v0 S2)) (= (f9 (f11 f12 f34) ?v0) f34)))
(assert (forall ((?v0 S10)) (= (f15 (f43 f44 f51) ?v0) f51)))
(assert (forall ((?v0 S4)) (= (f5 (f6 f35 f52) ?v0) f52)))
(check-sat)
(exit)