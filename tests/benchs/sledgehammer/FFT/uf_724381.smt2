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
(declare-fun f8 (S7 S4) S3)
(declare-fun f9 () S7)
(declare-fun f10 () S3)
(declare-fun f11 (S8 S2) S2)
(declare-fun f12 (S9 S2) S8)
(declare-fun f13 () S9)
(declare-fun f14 (S10 S11) S2)
(declare-fun f15 () S10)
(declare-fun f16 (S12 S11) S11)
(declare-fun f17 () S12)
(declare-fun f18 () S12)
(declare-fun f19 () S11)
(declare-fun f20 () S2)
(declare-fun f21 () S2)
(declare-fun f22 () S9)
(declare-fun f23 () S2)
(declare-fun f24 () S3)
(declare-fun f25 () S3)
(declare-fun f26 () S3)
(declare-fun f27 () S8)
(declare-fun f28 () S3)
(declare-fun f29 () S3)
(declare-fun f30 (S13 S2) S3)
(declare-fun f31 (S14 S3) S13)
(declare-fun f32 (S15 S2) S14)
(declare-fun f33 () S15)
(declare-fun f34 (S16 S17) S4)
(declare-fun f35 (S18 S3) S16)
(declare-fun f36 () S18)
(declare-fun f37 (S2 S2) S17)
(declare-fun f38 () S2)
(declare-fun f39 (S19 S3) S3)
(declare-fun f40 (S20 S2) S19)
(declare-fun f41 () S20)
(declare-fun f42 (S21 S2) S11)
(declare-fun f43 (S22 S11) S21)
(declare-fun f44 () S22)
(declare-fun f45 (S23 S11) S12)
(declare-fun f46 () S23)
(declare-fun f47 () S9)
(declare-fun f48 () S23)
(declare-fun f49 () S12)
(declare-fun f50 () S6)
(declare-fun f51 (S24 S11) S4)
(declare-fun f52 () S24)
(declare-fun f53 () S11)
(declare-fun f54 () S4)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))))) (let ((?v_1 (f11 (f12 f22 (f11 ?v_0 ?v0)) f23))) (= (f3 f4 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f11 ?v_0 f20))) (f11 (f12 f13 f21) ?v_1))) (f3 f24 ?v_1)))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))))) (let ((?v_1 (f11 ?v_0 ?v0))) (= (f3 f25 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f11 ?v_0 f20))) (f11 (f12 f13 f21) ?v_1))) (f3 f24 ?v_1)))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))))) (let ((?v_1 (f11 ?v_0 ?v0))) (= (f3 f26 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f11 ?v_0 f20))) (f11 (f12 f22 f21) (f11 (f12 f13 f21) ?v_1)))) (f3 f24 (f11 f27 ?v_1))))))))
(assert (forall ((?v0 S2)) (= (f3 f28 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) f20))) (f11 (f12 f13 f21) ?v0))) (f3 f24 ?v0)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))))) (= (f3 f29 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f11 ?v_0 f20))) f21)) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 f20)) (f11 (f12 f13 f21) ?v0))) (f3 f24 (f11 f27 (f11 ?v_0 ?v0)))))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2)) (= (f3 (f30 (f31 (f32 f33 ?v0) ?v1) ?v2) ?v3) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 ?v0)) (f11 (f12 f13 ?v2) ?v3))) (f3 ?v1 ?v3)))))
(assert (let ((?v_0 (f37 f38 f20))) (not (= (f34 (f35 f36 f26) ?v_0) (f34 (f35 f36 f29) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19))))) (?v_1 (f12 f13 ?v1))) (= (f3 (f8 f9 (f3 f10 (f11 ?v_0 ?v0))) (f11 ?v_1 (f11 ?v_0 ?v2))) (f3 (f8 f9 (f3 f10 ?v0)) (f11 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (f3 (f39 (f40 f41 ?v0) ?v1) ?v2) (f34 (f35 f36 (f30 (f31 (f32 f33 ?v0) ?v1) ?v2)) (f37 f38 ?v0)))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_1 (f14 f15 (f16 f17 (f16 f18 f19)))) (?v_0 (f43 f44 ?v0))) (= (f42 ?v_0 (f11 f27 (f11 (f12 f13 ?v_1) ?v1))) (f16 (f45 f46 ?v0) (f42 (f43 f44 (f42 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f14 f15 (f16 f17 (f16 f18 f19)))) (?v_0 (f12 f47 ?v0))) (= (f11 ?v_0 (f11 f27 (f11 (f12 f13 ?v_1) ?v1))) (f11 (f12 f13 ?v0) (f11 (f12 f47 (f11 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_1 (f14 f15 (f16 f17 (f16 f18 f19)))) (?v_0 (f8 f9 ?v0))) (= (f3 ?v_0 (f11 f27 (f11 (f12 f13 ?v_1) ?v1))) (f5 (f6 f7 ?v0) (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_0 (f43 f44 ?v0))) (let ((?v_1 (f42 ?v_0 ?v1))) (= (f42 ?v_0 (f11 f27 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1))) (f16 (f45 f46 ?v0) (f16 (f45 f46 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f12 f47 ?v0))) (let ((?v_1 (f11 ?v_0 ?v1))) (= (f11 ?v_0 (f11 f27 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1))) (f11 (f12 f13 ?v0) (f11 (f12 f13 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (let ((?v_1 (f3 ?v_0 ?v1))) (= (f3 ?v_0 (f11 f27 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1))) (f5 (f6 f7 ?v0) (f5 (f6 f7 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_1 (f16 f17 (f16 f18 f19)))) (let ((?v_0 (f14 f15 ?v_1))) (= (f42 (f43 f44 (f16 (f45 f48 ?v0) ?v1)) ?v_0) (f16 (f45 f48 (f16 (f45 f48 (f42 (f43 f44 ?v0) ?v_0)) (f42 (f43 f44 ?v1) ?v_0))) (f16 (f45 f46 (f16 (f45 f46 (f16 f49 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f14 f15 (f16 f17 (f16 f18 f19))))) (= (f11 (f12 f47 (f11 (f12 f22 ?v0) ?v1)) ?v_0) (f11 (f12 f22 (f11 (f12 f22 (f11 (f12 f47 ?v0) ?v_0)) (f11 (f12 f47 ?v1) ?v_0))) (f11 (f12 f13 (f11 (f12 f13 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_1 (f16 f17 (f16 f18 f19)))) (let ((?v_0 (f14 f15 ?v_1))) (= (f3 (f8 f9 (f5 (f6 f50 ?v0) ?v1)) ?v_0) (f5 (f6 f50 (f5 (f6 f50 (f3 (f8 f9 ?v0) ?v_0)) (f3 (f8 f9 ?v1) ?v_0))) (f5 (f6 f7 (f5 (f6 f7 (f51 f52 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_0 (f43 f44 ?v0))) (let ((?v_1 (f42 ?v_0 ?v1))) (= (f42 ?v_0 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1)) (f16 (f45 f46 ?v_1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f12 f47 ?v0))) (let ((?v_1 (f11 ?v_0 ?v1))) (= (f11 ?v_0 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1)) (f11 (f12 f13 ?v_1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (let ((?v_1 (f3 ?v_0 ?v1))) (= (f3 ?v_0 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1)) (f5 (f6 f7 ?v_1) ?v_1))))))
(assert (forall ((?v0 S11)) (let ((?v_0 (f16 f49 ?v0))) (= (f42 (f43 f44 ?v_0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f16 (f45 f46 ?v_0) ?v_0)))))
(assert (forall ((?v0 S11)) (let ((?v_0 (f14 f15 ?v0))) (= (f11 (f12 f47 ?v_0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f11 (f12 f13 ?v_0) ?v_0)))))
(assert (forall ((?v0 S11)) (let ((?v_0 (f51 f52 ?v0))) (= (f3 (f8 f9 ?v_0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f5 (f6 f7 ?v_0) ?v_0)))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f14 f15 (f16 f17 (f16 f18 f19))))) (= (= (f16 (f45 f48 (f42 (f43 f44 ?v0) ?v_0)) (f42 (f43 f44 ?v1) ?v_0)) f53) (and (= ?v0 f53) (= ?v1 f53))))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f13 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f11 (f12 f22 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v0) (f11 (f12 f22 ?v0) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f14 f15 (f16 f17 (f16 f18 f19)))) (?v_0 (f12 f47 ?v0))) (= (f11 ?v_0 (f11 (f12 f13 ?v_1) ?v1)) (f11 (f12 f47 (f11 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_1 (f14 f15 (f16 f17 (f16 f18 f19)))) (?v_0 (f43 f44 ?v0))) (= (f42 ?v_0 (f11 (f12 f13 ?v_1) ?v1)) (f42 (f43 f44 (f42 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_1 (f14 f15 (f16 f17 (f16 f18 f19)))) (?v_0 (f8 f9 ?v0))) (= (f3 ?v_0 (f11 (f12 f13 ?v_1) ?v1)) (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f22 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f11 f27 (f11 f27 ?v0)))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f22 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v0) (f11 f27 (f11 f27 ?v0)))))
(assert (forall ((?v0 S2)) (not (= (f3 f10 ?v0) f54))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f45 f46 ?v0))) (= (f16 (f45 f46 (f16 ?v_0 ?v1)) (f16 (f45 f46 ?v2) ?v3)) (f16 (f45 f46 (f16 ?v_0 ?v2)) (f16 (f45 f46 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) (f5 (f6 f7 ?v2) ?v3)) (f5 (f6 f7 (f5 ?v_0 ?v2)) (f5 (f6 f7 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (f11 (f12 f13 (f11 ?v_0 ?v1)) (f11 (f12 f13 ?v2) ?v3)) (f11 (f12 f13 (f11 ?v_0 ?v2)) (f11 (f12 f13 ?v1) ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_1 (f45 f46 (f16 (f45 f46 ?v0) ?v1))) (?v_0 (f45 f46 ?v2))) (= (f16 ?v_1 (f16 ?v_0 ?v3)) (f16 ?v_0 (f16 ?v_1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_1 (f6 f7 (f5 (f6 f7 ?v0) ?v1))) (?v_0 (f6 f7 ?v2))) (= (f5 ?v_1 (f5 ?v_0 ?v3)) (f5 ?v_0 (f5 ?v_1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_1 (f12 f13 (f11 (f12 f13 ?v0) ?v1))) (?v_0 (f12 f13 ?v2))) (= (f11 ?v_1 (f11 ?v_0 ?v3)) (f11 ?v_0 (f11 ?v_1 ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f45 f46 ?v0)) (?v_1 (f16 (f45 f46 ?v2) ?v3))) (= (f16 (f45 f46 (f16 ?v_0 ?v1)) ?v_1) (f16 ?v_0 (f16 (f45 f46 ?v1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f7 ?v0)) (?v_1 (f5 (f6 f7 ?v2) ?v3))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v_1) (f5 ?v_0 (f5 (f6 f7 ?v1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f12 f13 ?v0)) (?v_1 (f11 (f12 f13 ?v2) ?v3))) (= (f11 (f12 f13 (f11 ?v_0 ?v1)) ?v_1) (f11 ?v_0 (f11 (f12 f13 ?v1) ?v_1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f45 f46 ?v0))) (= (f16 (f45 f46 (f16 ?v_0 ?v1)) ?v2) (f16 (f45 f46 (f16 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2) (f5 (f6 f7 (f5 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (f11 (f12 f13 (f11 ?v_0 ?v1)) ?v2) (f11 (f12 f13 (f11 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f45 f46 ?v0))) (= (f16 (f45 f46 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f45 f46 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (f11 (f12 f13 (f11 ?v_0 ?v1)) ?v2) (f11 ?v_0 (f11 (f12 f13 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f45 f46 ?v0))) (= (f16 ?v_0 (f16 (f45 f46 ?v1) ?v2)) (f16 (f45 f46 (f16 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (f11 ?v_0 (f11 (f12 f13 ?v1) ?v2)) (f11 (f12 f13 (f11 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_1 (f45 f46 ?v0)) (?v_0 (f45 f46 ?v1))) (= (f16 ?v_1 (f16 ?v_0 ?v2)) (f16 ?v_0 (f16 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f6 f7 ?v0)) (?v_0 (f6 f7 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f12 f13 ?v0)) (?v_0 (f12 f13 ?v1))) (= (f11 ?v_1 (f11 ?v_0 ?v2)) (f11 ?v_0 (f11 ?v_1 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f16 (f45 f46 ?v0) ?v1) (f16 (f45 f46 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f5 (f6 f7 ?v0) ?v1) (f5 (f6 f7 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f11 (f12 f13 ?v0) ?v1) (f11 (f12 f13 ?v1) ?v0))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f45 f48 ?v0))) (= (f16 (f45 f48 (f16 ?v_0 ?v1)) (f16 (f45 f48 ?v2) ?v3)) (f16 (f45 f48 (f16 ?v_0 ?v2)) (f16 (f45 f48 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f12 f22 ?v0))) (= (f11 (f12 f22 (f11 ?v_0 ?v1)) (f11 (f12 f22 ?v2) ?v3)) (f11 (f12 f22 (f11 ?v_0 ?v2)) (f11 (f12 f22 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f50 ?v0))) (= (f5 (f6 f50 (f5 ?v_0 ?v1)) (f5 (f6 f50 ?v2) ?v3)) (f5 (f6 f50 (f5 ?v_0 ?v2)) (f5 (f6 f50 ?v1) ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f45 f48 ?v0))) (= (f16 (f45 f48 (f16 ?v_0 ?v1)) ?v2) (f16 (f45 f48 (f16 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f22 ?v0))) (= (f11 (f12 f22 (f11 ?v_0 ?v1)) ?v2) (f11 (f12 f22 (f11 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f50 ?v0))) (= (f5 (f6 f50 (f5 ?v_0 ?v1)) ?v2) (f5 (f6 f50 (f5 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f45 f48 ?v0))) (= (f16 (f45 f48 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f45 f48 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f22 ?v0))) (= (f11 (f12 f22 (f11 ?v_0 ?v1)) ?v2) (f11 ?v_0 (f11 (f12 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f50 ?v0))) (= (f5 (f6 f50 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f50 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f45 f48 ?v0))) (= (f16 ?v_0 (f16 (f45 f48 ?v1) ?v2)) (f16 (f45 f48 (f16 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f22 ?v0))) (= (f11 ?v_0 (f11 (f12 f22 ?v1) ?v2)) (f11 (f12 f22 (f11 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f50 ?v0))) (= (f5 ?v_0 (f5 (f6 f50 ?v1) ?v2)) (f5 (f6 f50 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_1 (f45 f48 ?v0)) (?v_0 (f45 f48 ?v1))) (= (f16 ?v_1 (f16 ?v_0 ?v2)) (f16 ?v_0 (f16 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f12 f22 ?v0)) (?v_0 (f12 f22 ?v1))) (= (f11 ?v_1 (f11 ?v_0 ?v2)) (f11 ?v_0 (f11 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f6 f50 ?v0)) (?v_0 (f6 f50 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f16 (f45 f48 ?v0) ?v1) (f16 (f45 f48 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f11 (f12 f22 ?v0) ?v1) (f11 (f12 f22 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f5 (f6 f50 ?v0) ?v1) (f5 (f6 f50 ?v1) ?v0))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f13 ?v0) f38) f38)))
(assert (forall ((?v0 S11)) (= (f16 (f45 f46 ?v0) f53) f53)))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 ?v0) f54) f54)))
(assert (forall ((?v0 S2)) (= (f11 (f12 f13 f38) ?v0) f38)))
(assert (forall ((?v0 S11)) (= (f16 (f45 f46 f53) ?v0) f53)))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 f54) ?v0) f54)))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= ?v0 (f16 (f45 f48 ?v0) ?v1)) (= ?v1 f53))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 (f11 (f12 f22 ?v0) ?v1)) (= ?v1 f38))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= ?v0 (f5 (f6 f50 ?v0) ?v1)) (= ?v1 f54))))
(assert (forall ((?v0 S11)) (= (f16 (f45 f48 ?v0) f53) ?v0)))
(assert (forall ((?v0 S2)) (= (f11 (f12 f22 ?v0) f38) ?v0)))
(assert (forall ((?v0 S4)) (= (f5 (f6 f50 ?v0) f54) ?v0)))
(assert (forall ((?v0 S11)) (= (f16 (f45 f48 f53) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f11 (f12 f22 f38) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f5 (f6 f50 f54) ?v0) ?v0)))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f45 f46 ?v0)) (?v_1 (f45 f46 ?v2))) (= (= (f16 (f45 f48 (f16 ?v_0 ?v1)) (f16 ?v_1 ?v3)) (f16 (f45 f48 (f16 ?v_0 ?v3)) (f16 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f12 f13 ?v0)) (?v_1 (f12 f13 ?v2))) (= (= (f11 (f12 f22 (f11 ?v_0 ?v1)) (f11 ?v_1 ?v3)) (f11 (f12 f22 (f11 ?v_0 ?v3)) (f11 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f7 ?v0)) (?v_1 (f6 f7 ?v2))) (= (= (f5 (f6 f50 (f5 ?v_0 ?v1)) (f5 ?v_1 ?v3)) (f5 (f6 f50 (f5 ?v_0 ?v3)) (f5 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (= (f16 (f45 f48 (f16 (f45 f46 ?v0) ?v1)) (f16 (f45 f46 ?v2) ?v1)) (f16 (f45 f46 (f16 (f45 f48 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f11 (f12 f22 (f11 (f12 f13 ?v0) ?v1)) (f11 (f12 f13 ?v2) ?v1)) (f11 (f12 f13 (f11 (f12 f22 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f5 (f6 f50 (f5 (f6 f7 ?v0) ?v1)) (f5 (f6 f7 ?v2) ?v1)) (f5 (f6 f7 (f5 (f6 f50 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (= (f16 (f45 f46 (f16 (f45 f48 ?v0) ?v1)) ?v2) (f16 (f45 f48 (f16 (f45 f46 ?v0) ?v2)) (f16 (f45 f46 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f11 (f12 f13 (f11 (f12 f22 ?v0) ?v1)) ?v2) (f11 (f12 f22 (f11 (f12 f13 ?v0) ?v2)) (f11 (f12 f13 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f5 (f6 f7 (f5 (f6 f50 ?v0) ?v1)) ?v2) (f5 (f6 f50 (f5 (f6 f7 ?v0) ?v2)) (f5 (f6 f7 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f45 f46 ?v0)) (?v_1 (f45 f46 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f16 (f45 f48 (f16 ?v_0 ?v2)) (f16 ?v_1 ?v3)) (f16 (f45 f48 (f16 ?v_0 ?v3)) (f16 ?v_1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f12 f13 ?v0)) (?v_1 (f12 f13 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f11 (f12 f22 (f11 ?v_0 ?v2)) (f11 ?v_1 ?v3)) (f11 (f12 f22 (f11 ?v_0 ?v3)) (f11 ?v_1 ?v2))))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f7 ?v0)) (?v_1 (f6 f7 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f5 (f6 f50 (f5 ?v_0 ?v2)) (f5 ?v_1 ?v3)) (f5 (f6 f50 (f5 ?v_0 ?v3)) (f5 ?v_1 ?v2))))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f45 f46 ?v0))) (= (f16 ?v_0 (f16 (f45 f48 ?v1) ?v2)) (f16 (f45 f48 (f16 ?v_0 ?v1)) (f16 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (f11 ?v_0 (f11 (f12 f22 ?v1) ?v2)) (f11 (f12 f22 (f11 ?v_0 ?v1)) (f11 ?v_0 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 ?v_0 (f5 (f6 f50 ?v1) ?v2)) (f5 (f6 f50 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S2)) (= (f42 (f43 f44 (f16 (f45 f46 ?v0) ?v1)) ?v2) (f16 (f45 f46 (f42 (f43 f44 ?v0) ?v2)) (f42 (f43 f44 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f11 (f12 f47 (f11 (f12 f13 ?v0) ?v1)) ?v2) (f11 (f12 f13 (f11 (f12 f47 ?v0) ?v2)) (f11 (f12 f47 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2)) (= (f3 (f8 f9 (f5 (f6 f7 ?v0) ?v1)) ?v2) (f5 (f6 f7 (f3 (f8 f9 ?v0) ?v2)) (f3 (f8 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f47 ?v0))) (= (f11 (f12 f47 (f11 ?v_0 ?v1)) ?v2) (f11 ?v_0 (f11 (f12 f13 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S2)) (let ((?v_0 (f43 f44 ?v0))) (= (f42 (f43 f44 (f42 ?v_0 ?v1)) ?v2) (f42 ?v_0 (f11 (f12 f13 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f11 (f12 f13 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11) (?v4 S11)) (let ((?v_0 (f45 f46 ?v0))) (=> (not (= ?v0 f53)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f16 (f45 f48 ?v1) (f16 ?v_0 ?v3)) (f16 (f45 f48 ?v2) (f16 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (let ((?v_0 (f12 f13 ?v0))) (=> (not (= ?v0 f38)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f11 (f12 f22 ?v1) (f11 ?v_0 ?v3)) (f11 (f12 f22 ?v2) (f11 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4) (?v4 S4)) (let ((?v_0 (f6 f7 ?v0))) (=> (not (= ?v0 f54)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f5 (f6 f50 ?v1) (f5 ?v_0 ?v3)) (f5 (f6 f50 ?v2) (f5 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f16 (f45 f48 (f16 (f45 f46 ?v0) ?v0)) (f16 (f45 f46 ?v1) ?v1)) f53) (and (= ?v0 f53) (= ?v1 f53)))))
(assert (= f53 (f16 f49 f19)))
(assert (= f54 (f51 f52 f19)))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_0 (f43 f44 ?v0))) (= (f16 (f45 f46 (f42 ?v_0 ?v1)) ?v0) (f42 ?v_0 (f11 f27 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f12 f47 ?v0))) (= (f11 (f12 f13 (f11 ?v_0 ?v1)) ?v0) (f11 ?v_0 (f11 f27 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f5 (f6 f7 (f3 ?v_0 ?v1)) ?v0) (f3 ?v_0 (f11 f27 ?v1))))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_0 (f43 f44 ?v0))) (= (f16 (f45 f46 ?v0) (f42 ?v_0 ?v1)) (f42 ?v_0 (f11 f27 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f12 f47 ?v0))) (= (f11 (f12 f13 ?v0) (f11 ?v_0 ?v1)) (f11 ?v_0 (f11 f27 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f5 (f6 f7 ?v0) (f3 ?v_0 ?v1)) (f3 ?v_0 (f11 f27 ?v1))))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_0 (f43 f44 ?v0))) (= (f42 ?v_0 (f11 f27 ?v1)) (f16 (f45 f46 ?v0) (f42 ?v_0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f12 f47 ?v0))) (= (f11 ?v_0 (f11 f27 ?v1)) (f11 (f12 f13 ?v0) (f11 ?v_0 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f3 ?v_0 (f11 f27 ?v1)) (f5 (f6 f7 ?v0) (f3 ?v_0 ?v1))))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S2)) (let ((?v_0 (f43 f44 ?v0))) (= (f16 (f45 f46 (f42 ?v_0 ?v1)) (f42 ?v_0 ?v2)) (f42 ?v_0 (f11 (f12 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f47 ?v0))) (= (f11 (f12 f13 (f11 ?v_0 ?v1)) (f11 ?v_0 ?v2)) (f11 ?v_0 (f11 (f12 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f5 (f6 f7 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2)) (f3 ?v_0 (f11 (f12 f22 ?v1) ?v2))))))
(assert (= (f14 f15 f19) f38))
(assert (= f38 (f14 f15 f19)))
(assert (forall ((?v0 S11)) (= (f42 (f43 f44 ?v0) (f14 f15 (f16 f18 (f16 f18 f19)))) (f16 (f45 f46 (f16 (f45 f46 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f47 ?v0) (f14 f15 (f16 f18 (f16 f18 f19)))) (f11 (f12 f13 (f11 (f12 f13 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S4)) (= (f3 (f8 f9 ?v0) (f14 f15 (f16 f18 (f16 f18 f19)))) (f5 (f6 f7 (f5 (f6 f7 ?v0) ?v0)) ?v0))))
(assert (= (f14 f15 (f16 f18 (f16 f18 f19))) (f11 f27 (f11 f27 (f11 f27 f38)))))
(assert (= (f14 f15 (f16 f18 f19)) (f11 f27 f38)))
(assert (forall ((?v0 S2)) (= (f11 f27 (f11 f27 (f11 f27 ?v0))) (f11 (f12 f22 (f14 f15 (f16 f18 (f16 f18 f19)))) ?v0))))
(assert (forall ((?v0 S11)) (= (= (f42 (f43 f44 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) f53) (= ?v0 f53))))
(assert (forall ((?v0 S4)) (= (= (f3 (f8 f9 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) f54) (= ?v0 f54))))
(assert (= (f11 (f12 f47 f38) (f14 f15 (f16 f17 (f16 f18 f19)))) f38))
(assert (= (f42 (f43 f44 f53) (f14 f15 (f16 f17 (f16 f18 f19)))) f53))
(assert (= (f3 (f8 f9 f54) (f14 f15 (f16 f17 (f16 f18 f19)))) f54))
(assert (forall ((?v0 S11)) (= (f42 (f43 f44 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f16 (f45 f46 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f47 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f11 (f12 f13 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f3 (f8 f9 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f5 (f6 f7 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f16 (f45 f46 ?v0) ?v0) (f42 (f43 f44 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f13 ?v0) ?v0) (f11 (f12 f47 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))))))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 ?v0) ?v0) (f3 (f8 f9 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))))))
(assert (= (f14 f15 (f16 f17 (f16 f18 f19))) (f11 f27 (f11 f27 f38))))
(assert (= (f11 f27 (f11 f27 f38)) (f14 f15 (f16 f17 (f16 f18 f19)))))
(assert (let ((?v_0 (f37 f38 f20))) (= (f34 (f35 f36 f28) (f37 f38 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) f20))) (f5 (f6 f50 (f34 (f35 f36 f25) ?v_0)) (f34 (f35 f36 f4) ?v_0)))))
(assert (forall ((?v0 S11)) (= (f16 (f45 f46 (f16 f49 (f16 f17 (f16 f18 f19)))) ?v0) (f16 (f45 f48 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v0) (f11 (f12 f22 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 (f51 f52 (f16 f17 (f16 f18 f19)))) ?v0) (f5 (f6 f50 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f16 (f45 f46 (f16 f49 (f16 f17 (f16 f18 f19)))) ?v0) (f16 (f45 f48 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 (f51 f52 (f16 f17 (f16 f18 f19)))) ?v0) (f5 (f6 f50 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f16 (f45 f46 ?v0) (f16 f49 (f16 f17 (f16 f18 f19)))) (f16 (f45 f48 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f13 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f11 (f12 f22 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 ?v0) (f51 f52 (f16 f17 (f16 f18 f19)))) (f5 (f6 f50 ?v0) ?v0))))
(check-sat)
(exit)
