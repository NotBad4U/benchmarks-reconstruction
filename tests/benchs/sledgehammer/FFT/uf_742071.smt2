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
(declare-fun f11 () S2)
(declare-fun f12 () S2)
(declare-fun f13 () S3)
(declare-fun f14 (S8 S2) S2)
(declare-fun f15 () S8)
(declare-fun f16 (S9 S2) S8)
(declare-fun f17 () S9)
(declare-fun f18 (S10 S11) S2)
(declare-fun f19 () S10)
(declare-fun f20 (S12 S11) S11)
(declare-fun f21 () S12)
(declare-fun f22 () S12)
(declare-fun f23 () S11)
(declare-fun f24 () S3)
(declare-fun f25 () S9)
(declare-fun f26 () S2)
(declare-fun f27 () S3)
(declare-fun f28 () S3)
(declare-fun f29 () S3)
(declare-fun f30 (S13 S2) S3)
(declare-fun f31 (S14 S3) S13)
(declare-fun f32 (S15 S2) S14)
(declare-fun f33 () S15)
(declare-fun f34 () S15)
(declare-fun f35 () S6)
(declare-fun f36 (S16 S17) S4)
(declare-fun f37 (S18 S3) S16)
(declare-fun f38 () S18)
(declare-fun f39 (S2 S2) S17)
(declare-fun f40 () S2)
(declare-fun f41 () S5)
(declare-fun f42 (S2 S2) S1)
(declare-fun f43 (S2 S2) S1)
(declare-fun f44 (S19 S3) S3)
(declare-fun f45 (S20 S2) S19)
(declare-fun f46 () S20)
(declare-fun f47 () S9)
(declare-fun f48 (S21 S2) S11)
(declare-fun f49 (S22 S11) S21)
(declare-fun f50 () S22)
(declare-fun f51 (S23 S11) S12)
(declare-fun f52 () S23)
(declare-fun f53 () S6)
(declare-fun f54 (S24 S11) S4)
(declare-fun f55 () S24)
(declare-fun f56 () S23)
(declare-fun f57 () S12)
(declare-fun f58 () S12)
(declare-fun f59 () S11)
(declare-fun f60 () S20)
(declare-fun f61 () S4)
(declare-fun f62 (S11 S11) S1)
(declare-fun f63 (S11 S11) S1)
(declare-fun f64 (S25 S17) S2)
(declare-fun f65 (S26 S8) S25)
(declare-fun f66 () S26)
(declare-fun f67 (S27 S17) S11)
(declare-fun f68 (S28 S21) S27)
(declare-fun f69 () S28)
(declare-fun f70 () S11)
(declare-fun f71 () S4)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 (f8 f9 (f3 f10 f11)) f12)) ?v0)) (f3 f13 (f14 f15 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v0)))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))))) (let ((?v_1 (f14 (f16 f25 (f14 ?v_0 ?v0)) f26))) (= (f3 f24 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f14 ?v_0 f11))) (f14 (f16 f17 f12) ?v_1))) (f3 f13 ?v_1)))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))))) (let ((?v_1 (f14 ?v_0 ?v0))) (= (f3 f27 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f14 ?v_0 f11))) (f14 (f16 f17 f12) ?v_1))) (f3 f13 ?v_1)))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))))) (let ((?v_1 (f14 ?v_0 ?v0))) (= (f3 f28 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f14 ?v_0 f11))) (f14 (f16 f25 f12) (f14 (f16 f17 f12) ?v_1)))) (f3 f13 (f14 f15 ?v_1))))))))
(assert (forall ((?v0 S2)) (= (f3 f29 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) f11))) (f14 (f16 f17 f12) ?v0))) (f3 f13 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2)) (= (f3 (f30 (f31 (f32 f33 ?v0) ?v1) ?v2) ?v3) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 ?v0)) (f14 (f16 f17 ?v2) ?v3))) (f3 ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2)) (= (f3 (f30 (f31 (f32 f34 ?v0) ?v1) ?v2) ?v3) (f5 (f6 f35 (f3 ?v1 ?v3)) (f3 (f8 f9 (f3 f10 ?v0)) (f14 (f16 f17 ?v2) ?v3))))))
(assert (let ((?v_1 (f8 f9 (f3 f10 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) f11)))) (?v_0 (f39 f40 f11))) (not (= (f36 (f37 f38 f28) ?v_0) (f5 f41 (f5 (f6 f35 (f5 (f6 f7 (f3 ?v_1 f12)) (f36 (f37 f38 f4) ?v_0))) (f3 ?v_1 f11)))))))
(assert (= (f42 f40 f11) f1))
(assert (= (f43 f11 f12) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23))))) (?v_1 (f16 f17 ?v1))) (= (f3 (f8 f9 (f3 f10 (f14 ?v_0 ?v0))) (f14 ?v_1 (f14 ?v_0 ?v2))) (f3 (f8 f9 (f3 f10 ?v0)) (f14 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (f3 (f44 (f45 f46 ?v0) ?v1) ?v2) (f36 (f37 f38 (f30 (f31 (f32 f34 ?v0) ?v1) ?v2)) (f39 f40 ?v0)))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_1 (f18 f19 (f20 f21 (f20 f22 f23)))) (?v_0 (f8 f9 ?v0))) (= (f3 ?v_0 (f14 f15 (f14 (f16 f17 ?v_1) ?v1))) (f5 (f6 f7 ?v0) (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f18 f19 (f20 f21 (f20 f22 f23)))) (?v_0 (f16 f47 ?v0))) (= (f14 ?v_0 (f14 f15 (f14 (f16 f17 ?v_1) ?v1))) (f14 (f16 f17 ?v0) (f14 (f16 f47 (f14 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_1 (f18 f19 (f20 f21 (f20 f22 f23)))) (?v_0 (f49 f50 ?v0))) (= (f48 ?v_0 (f14 f15 (f14 (f16 f17 ?v_1) ?v1))) (f20 (f51 f52 ?v0) (f48 (f49 f50 (f48 ?v_0 ?v1)) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (let ((?v_1 (f3 ?v_0 ?v1))) (= (f3 ?v_0 (f14 f15 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v1))) (f5 (f6 f7 ?v0) (f5 (f6 f7 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f16 f47 ?v0))) (let ((?v_1 (f14 ?v_0 ?v1))) (= (f14 ?v_0 (f14 f15 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v1))) (f14 (f16 f17 ?v0) (f14 (f16 f17 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_0 (f49 f50 ?v0))) (let ((?v_1 (f48 ?v_0 ?v1))) (= (f48 ?v_0 (f14 f15 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v1))) (f20 (f51 f52 ?v0) (f20 (f51 f52 ?v_1) ?v_1)))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_1 (f20 f21 (f20 f22 f23)))) (let ((?v_0 (f18 f19 ?v_1))) (= (f3 (f8 f9 (f5 (f6 f53 ?v0) ?v1)) ?v_0) (f5 (f6 f53 (f5 (f6 f53 (f3 (f8 f9 ?v0) ?v_0)) (f3 (f8 f9 ?v1) ?v_0))) (f5 (f6 f7 (f5 (f6 f7 (f54 f55 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (= (f14 (f16 f47 (f14 (f16 f25 ?v0) ?v1)) ?v_0) (f14 (f16 f25 (f14 (f16 f25 (f14 (f16 f47 ?v0) ?v_0)) (f14 (f16 f47 ?v1) ?v_0))) (f14 (f16 f17 (f14 (f16 f17 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_1 (f20 f21 (f20 f22 f23)))) (let ((?v_0 (f18 f19 ?v_1))) (= (f48 (f49 f50 (f20 (f51 f56 ?v0) ?v1)) ?v_0) (f20 (f51 f56 (f20 (f51 f56 (f48 (f49 f50 ?v0) ?v_0)) (f48 (f49 f50 ?v1) ?v_0))) (f20 (f51 f52 (f20 (f51 f52 (f20 f57 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v1))) (= (f3 (f8 f9 (f5 f41 ?v0)) ?v_0) (f3 (f8 f9 ?v0) ?v_0)))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_0 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v1))) (= (f48 (f49 f50 (f20 f58 ?v0)) ?v_0) (f48 (f49 f50 ?v0) ?v_0)))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (let ((?v_1 (f3 ?v_0 ?v1))) (= (f3 ?v_0 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v1)) (f5 (f6 f7 ?v_1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f16 f47 ?v0))) (let ((?v_1 (f14 ?v_0 ?v1))) (= (f14 ?v_0 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v1)) (f14 (f16 f17 ?v_1) ?v_1))))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_0 (f49 f50 ?v0))) (let ((?v_1 (f48 ?v_0 ?v1))) (= (f48 ?v_0 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v1)) (f20 (f51 f52 ?v_1) ?v_1))))))
(assert (forall ((?v0 S11)) (let ((?v_0 (f54 f55 ?v0))) (= (f3 (f8 f9 ?v_0) (f18 f19 (f20 f21 (f20 f22 f23)))) (f5 (f6 f7 ?v_0) ?v_0)))))
(assert (forall ((?v0 S11)) (let ((?v_0 (f18 f19 ?v0))) (= (f14 (f16 f47 ?v_0) (f18 f19 (f20 f21 (f20 f22 f23)))) (f14 (f16 f17 ?v_0) ?v_0)))))
(assert (forall ((?v0 S11)) (let ((?v_0 (f20 f57 ?v0))) (= (f48 (f49 f50 ?v_0) (f18 f19 (f20 f21 (f20 f22 f23)))) (f20 (f51 f52 ?v_0) ?v_0)))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (= (= (f20 (f51 f56 (f48 (f49 f50 ?v0) ?v_0)) (f48 (f49 f50 ?v1) ?v_0)) f59) (and (= ?v0 f59) (= ?v1 f59))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (f3 (f44 (f45 f60 ?v0) ?v1) ?v2) (f36 (f37 f38 (f30 (f31 (f32 f33 ?v0) ?v1) ?v2)) (f39 f40 ?v0)))))
(assert (forall ((?v0 S2)) (= (f14 (f16 f17 ?v0) (f18 f19 (f20 f21 (f20 f22 f23)))) (f14 (f16 f25 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v0) (f14 (f16 f25 ?v0) ?v0))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_1 (f18 f19 (f20 f21 (f20 f22 f23)))) (?v_0 (f8 f9 ?v0))) (= (f3 ?v_0 (f14 (f16 f17 ?v_1) ?v1)) (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f18 f19 (f20 f21 (f20 f22 f23)))) (?v_0 (f16 f47 ?v0))) (= (f14 ?v_0 (f14 (f16 f17 ?v_1) ?v1)) (f14 (f16 f47 (f14 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_1 (f18 f19 (f20 f21 (f20 f22 f23)))) (?v_0 (f49 f50 ?v0))) (= (f48 ?v_0 (f14 (f16 f17 ?v_1) ?v1)) (f48 (f49 f50 (f48 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S2)) (not (= (f3 f10 ?v0) f61))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f62 f59 (f20 (f51 f56 (f20 (f51 f52 ?v0) ?v0)) (f20 (f51 f52 ?v1) ?v1))) f1) (or (not (= ?v0 f59)) (not (= ?v1 f59))))))
(assert (forall ((?v0 S11) (?v1 S11)) (not (= (f62 (f20 (f51 f56 (f20 (f51 f52 ?v0) ?v0)) (f20 (f51 f52 ?v1) ?v1)) f59) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f63 (f20 (f51 f56 (f20 (f51 f52 ?v0) ?v0)) (f20 (f51 f52 ?v1) ?v1)) f59) f1) (and (= ?v0 f59) (= ?v1 f59)))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f63 f59 (f20 (f51 f56 (f20 (f51 f52 ?v0) ?v0)) (f20 (f51 f52 ?v1) ?v1))) f1)))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (=> (= (f62 (f48 (f49 f50 ?v0) ?v_0) (f48 (f49 f50 ?v1) ?v_0)) f1) (=> (= (f63 f59 ?v1) f1) (= (f62 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (=> (= (f42 (f14 (f16 f47 ?v0) ?v_0) (f14 (f16 f47 ?v1) ?v_0)) f1) (=> (= (f43 f40 ?v1) f1) (= (f42 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f16 f17 ?v0))) (= (f14 (f16 f17 (f14 ?v_0 ?v1)) (f14 (f16 f17 ?v2) ?v3)) (f14 (f16 f17 (f14 ?v_0 ?v2)) (f14 (f16 f17 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) (f5 (f6 f7 ?v2) ?v3)) (f5 (f6 f7 (f5 ?v_0 ?v2)) (f5 (f6 f7 ?v1) ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f51 f52 ?v0))) (= (f20 (f51 f52 (f20 ?v_0 ?v1)) (f20 (f51 f52 ?v2) ?v3)) (f20 (f51 f52 (f20 ?v_0 ?v2)) (f20 (f51 f52 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_1 (f16 f17 (f14 (f16 f17 ?v0) ?v1))) (?v_0 (f16 f17 ?v2))) (= (f14 ?v_1 (f14 ?v_0 ?v3)) (f14 ?v_0 (f14 ?v_1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_1 (f6 f7 (f5 (f6 f7 ?v0) ?v1))) (?v_0 (f6 f7 ?v2))) (= (f5 ?v_1 (f5 ?v_0 ?v3)) (f5 ?v_0 (f5 ?v_1 ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_1 (f51 f52 (f20 (f51 f52 ?v0) ?v1))) (?v_0 (f51 f52 ?v2))) (= (f20 ?v_1 (f20 ?v_0 ?v3)) (f20 ?v_0 (f20 ?v_1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f16 f17 ?v0)) (?v_1 (f14 (f16 f17 ?v2) ?v3))) (= (f14 (f16 f17 (f14 ?v_0 ?v1)) ?v_1) (f14 ?v_0 (f14 (f16 f17 ?v1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f7 ?v0)) (?v_1 (f5 (f6 f7 ?v2) ?v3))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v_1) (f5 ?v_0 (f5 (f6 f7 ?v1) ?v_1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f51 f52 ?v0)) (?v_1 (f20 (f51 f52 ?v2) ?v3))) (= (f20 (f51 f52 (f20 ?v_0 ?v1)) ?v_1) (f20 ?v_0 (f20 (f51 f52 ?v1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f17 ?v0))) (= (f14 (f16 f17 (f14 ?v_0 ?v1)) ?v2) (f14 (f16 f17 (f14 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2) (f5 (f6 f7 (f5 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f51 f52 ?v0))) (= (f20 (f51 f52 (f20 ?v_0 ?v1)) ?v2) (f20 (f51 f52 (f20 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f17 ?v0))) (= (f14 (f16 f17 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f16 f17 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f51 f52 ?v0))) (= (f20 (f51 f52 (f20 ?v_0 ?v1)) ?v2) (f20 ?v_0 (f20 (f51 f52 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f17 ?v0))) (= (f14 ?v_0 (f14 (f16 f17 ?v1) ?v2)) (f14 (f16 f17 (f14 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f51 f52 ?v0))) (= (f20 ?v_0 (f20 (f51 f52 ?v1) ?v2)) (f20 (f51 f52 (f20 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f16 f17 ?v0)) (?v_0 (f16 f17 ?v1))) (= (f14 ?v_1 (f14 ?v_0 ?v2)) (f14 ?v_0 (f14 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f6 f7 ?v0)) (?v_0 (f6 f7 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_1 (f51 f52 ?v0)) (?v_0 (f51 f52 ?v1))) (= (f20 ?v_1 (f20 ?v_0 ?v2)) (f20 ?v_0 (f20 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f14 (f16 f17 ?v0) ?v1) (f14 (f16 f17 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f5 (f6 f7 ?v0) ?v1) (f5 (f6 f7 ?v1) ?v0))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f20 (f51 f52 ?v0) ?v1) (f20 (f51 f52 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f53 ?v0))) (= (f5 (f6 f53 (f5 ?v_0 ?v1)) (f5 (f6 f53 ?v2) ?v3)) (f5 (f6 f53 (f5 ?v_0 ?v2)) (f5 (f6 f53 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f16 f25 ?v0))) (= (f14 (f16 f25 (f14 ?v_0 ?v1)) (f14 (f16 f25 ?v2) ?v3)) (f14 (f16 f25 (f14 ?v_0 ?v2)) (f14 (f16 f25 ?v1) ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f51 f56 ?v0))) (= (f20 (f51 f56 (f20 ?v_0 ?v1)) (f20 (f51 f56 ?v2) ?v3)) (f20 (f51 f56 (f20 ?v_0 ?v2)) (f20 (f51 f56 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f53 ?v0))) (= (f5 (f6 f53 (f5 ?v_0 ?v1)) ?v2) (f5 (f6 f53 (f5 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f25 ?v0))) (= (f14 (f16 f25 (f14 ?v_0 ?v1)) ?v2) (f14 (f16 f25 (f14 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f51 f56 ?v0))) (= (f20 (f51 f56 (f20 ?v_0 ?v1)) ?v2) (f20 (f51 f56 (f20 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f53 ?v0))) (= (f5 (f6 f53 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f53 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f25 ?v0))) (= (f14 (f16 f25 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f16 f25 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f51 f56 ?v0))) (= (f20 (f51 f56 (f20 ?v_0 ?v1)) ?v2) (f20 ?v_0 (f20 (f51 f56 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f53 ?v0))) (= (f5 ?v_0 (f5 (f6 f53 ?v1) ?v2)) (f5 (f6 f53 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f25 ?v0))) (= (f14 ?v_0 (f14 (f16 f25 ?v1) ?v2)) (f14 (f16 f25 (f14 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f51 f56 ?v0))) (= (f20 ?v_0 (f20 (f51 f56 ?v1) ?v2)) (f20 (f51 f56 (f20 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f6 f53 ?v0)) (?v_0 (f6 f53 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f16 f25 ?v0)) (?v_0 (f16 f25 ?v1))) (= (f14 ?v_1 (f14 ?v_0 ?v2)) (f14 ?v_0 (f14 ?v_1 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_1 (f51 f56 ?v0)) (?v_0 (f51 f56 ?v1))) (= (f20 ?v_1 (f20 ?v_0 ?v2)) (f20 ?v_0 (f20 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f5 (f6 f53 ?v0) ?v1) (f5 (f6 f53 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f14 (f16 f25 ?v0) ?v1) (f14 (f16 f25 ?v1) ?v0))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f20 (f51 f56 ?v0) ?v1) (f20 (f51 f56 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f42 f40 ?v0) f1) (=> (= (f42 ?v0 ?v1) f1) (= (f36 (f37 f38 (f8 f9 (f3 (f8 f9 (f3 f10 ?v1)) ?v0))) (f39 f40 ?v1)) f61)))))
(assert (forall ((?v0 S11)) (= (= (f62 f59 (f48 (f49 f50 ?v0) (f18 f19 (f20 f21 (f20 f22 f23))))) f1) (not (= ?v0 f59)))))
(assert (forall ((?v0 S11)) (not (= (f62 (f48 (f49 f50 ?v0) (f18 f19 (f20 f21 (f20 f22 f23)))) f59) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (=> (= (f48 (f49 f50 ?v0) ?v_0) (f48 (f49 f50 ?v1) ?v_0)) (=> (= (f63 f59 ?v0) f1) (=> (= (f63 f59 ?v1) f1) (= ?v0 ?v1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (=> (= (f14 (f16 f47 ?v0) ?v_0) (f14 (f16 f47 ?v1) ?v_0)) (=> (= (f43 f40 ?v0) f1) (=> (= (f43 f40 ?v1) f1) (= ?v0 ?v1)))))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (=> (= (f63 (f48 (f49 f50 ?v0) ?v_0) (f48 (f49 f50 ?v1) ?v_0)) f1) (=> (= (f63 f59 ?v1) f1) (= (f63 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (=> (= (f43 (f14 (f16 f47 ?v0) ?v_0) (f14 (f16 f47 ?v1) ?v_0)) f1) (=> (= (f43 f40 ?v1) f1) (= (f43 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S11)) (= (f63 f59 (f48 (f49 f50 ?v0) (f18 f19 (f20 f21 (f20 f22 f23))))) f1)))
(assert (forall ((?v0 S2)) (=> (= (f42 ?v0 (f18 f19 (f20 f21 (f20 f22 f23)))) f1) (or (= ?v0 f40) (= ?v0 (f14 f15 f40))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f17 ?v0))) (=> (= (f42 f40 ?v0) f1) (= (f3 (f8 f9 (f3 f10 (f14 ?v_0 ?v1))) (f14 ?v_0 ?v2)) (f3 (f8 f9 (f3 f10 ?v1)) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (= (= (f62 f59 (f20 (f51 f56 (f48 (f49 f50 ?v0) ?v_0)) (f48 (f49 f50 ?v1) ?v_0))) f1) (or (not (= ?v0 f59)) (not (= ?v1 f59)))))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (not (= (f62 (f20 (f51 f56 (f48 (f49 f50 ?v0) ?v_0)) (f48 (f49 f50 ?v1) ?v_0)) f59) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (= (= (f63 (f20 (f51 f56 (f48 (f49 f50 ?v0) ?v_0)) (f48 (f49 f50 ?v1) ?v_0)) f59) f1) (and (= ?v0 f59) (= ?v1 f59))))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (= (f63 f59 (f20 (f51 f56 (f48 (f49 f50 ?v0) ?v_0)) (f48 (f49 f50 ?v1) ?v_0))) f1))))
(assert (forall ((?v0 S11) (?v1 S2)) (= (f63 f59 (f48 (f49 f50 ?v0) (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v1))) f1)))
(assert (forall ((?v0 S11) (?v1 S2)) (=> (= (f62 ?v0 f59) f1) (= (f62 (f48 (f49 f50 ?v0) (f14 f15 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v1))) f59) f1))))
(assert (forall ((?v0 S11) (?v1 S2)) (=> (= (f63 f59 (f48 (f49 f50 ?v0) (f14 f15 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v1)))) f1) (= (f63 f59 ?v0) f1))))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 ?v0) f61) f61)))
(assert (forall ((?v0 S11)) (= (f20 (f51 f52 ?v0) f59) f59)))
(assert (forall ((?v0 S2)) (= (f14 (f16 f17 ?v0) f40) f40)))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 f61) ?v0) f61)))
(assert (forall ((?v0 S11)) (= (f20 (f51 f52 f59) ?v0) f59)))
(assert (forall ((?v0 S2)) (= (f14 (f16 f17 f40) ?v0) f40)))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= ?v0 (f5 (f6 f53 ?v0) ?v1)) (= ?v1 f61))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 (f14 (f16 f25 ?v0) ?v1)) (= ?v1 f40))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= ?v0 (f20 (f51 f56 ?v0) ?v1)) (= ?v1 f59))))
(assert (forall ((?v0 S4)) (= (f5 (f6 f53 ?v0) f61) ?v0)))
(assert (forall ((?v0 S2)) (= (f14 (f16 f25 ?v0) f40) ?v0)))
(assert (forall ((?v0 S11)) (= (f20 (f51 f56 ?v0) f59) ?v0)))
(assert (forall ((?v0 S4)) (= (f5 (f6 f53 f61) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f14 (f16 f25 f40) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f20 (f51 f56 f59) ?v0) ?v0)))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f7 ?v0)) (?v_1 (f6 f7 ?v2))) (= (= (f5 (f6 f53 (f5 ?v_0 ?v1)) (f5 ?v_1 ?v3)) (f5 (f6 f53 (f5 ?v_0 ?v3)) (f5 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f16 f17 ?v0)) (?v_1 (f16 f17 ?v2))) (= (= (f14 (f16 f25 (f14 ?v_0 ?v1)) (f14 ?v_1 ?v3)) (f14 (f16 f25 (f14 ?v_0 ?v3)) (f14 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f51 f52 ?v0)) (?v_1 (f51 f52 ?v2))) (= (= (f20 (f51 f56 (f20 ?v_0 ?v1)) (f20 ?v_1 ?v3)) (f20 (f51 f56 (f20 ?v_0 ?v3)) (f20 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f5 (f6 f53 (f5 (f6 f7 ?v0) ?v1)) (f5 (f6 f7 ?v2) ?v1)) (f5 (f6 f7 (f5 (f6 f53 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f14 (f16 f25 (f14 (f16 f17 ?v0) ?v1)) (f14 (f16 f17 ?v2) ?v1)) (f14 (f16 f17 (f14 (f16 f25 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (= (f20 (f51 f56 (f20 (f51 f52 ?v0) ?v1)) (f20 (f51 f52 ?v2) ?v1)) (f20 (f51 f52 (f20 (f51 f56 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f5 (f6 f7 (f5 (f6 f53 ?v0) ?v1)) ?v2) (f5 (f6 f53 (f5 (f6 f7 ?v0) ?v2)) (f5 (f6 f7 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f14 (f16 f17 (f14 (f16 f25 ?v0) ?v1)) ?v2) (f14 (f16 f25 (f14 (f16 f17 ?v0) ?v2)) (f14 (f16 f17 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (= (f20 (f51 f52 (f20 (f51 f56 ?v0) ?v1)) ?v2) (f20 (f51 f56 (f20 (f51 f52 ?v0) ?v2)) (f20 (f51 f52 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f7 ?v0)) (?v_1 (f6 f7 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f5 (f6 f53 (f5 ?v_0 ?v2)) (f5 ?v_1 ?v3)) (f5 (f6 f53 (f5 ?v_0 ?v3)) (f5 ?v_1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f16 f17 ?v0)) (?v_1 (f16 f17 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f14 (f16 f25 (f14 ?v_0 ?v2)) (f14 ?v_1 ?v3)) (f14 (f16 f25 (f14 ?v_0 ?v3)) (f14 ?v_1 ?v2))))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f51 f52 ?v0)) (?v_1 (f51 f52 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f20 (f51 f56 (f20 ?v_0 ?v2)) (f20 ?v_1 ?v3)) (f20 (f51 f56 (f20 ?v_0 ?v3)) (f20 ?v_1 ?v2))))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 ?v_0 (f5 (f6 f53 ?v1) ?v2)) (f5 (f6 f53 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f17 ?v0))) (= (f14 ?v_0 (f14 (f16 f25 ?v1) ?v2)) (f14 (f16 f25 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f51 f52 ?v0))) (= (f20 ?v_0 (f20 (f51 f56 ?v1) ?v2)) (f20 (f51 f56 (f20 ?v_0 ?v1)) (f20 ?v_0 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2)) (= (f3 (f8 f9 (f5 (f6 f7 ?v0) ?v1)) ?v2) (f5 (f6 f7 (f3 (f8 f9 ?v0) ?v2)) (f3 (f8 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f14 (f16 f47 (f14 (f16 f17 ?v0) ?v1)) ?v2) (f14 (f16 f17 (f14 (f16 f47 ?v0) ?v2)) (f14 (f16 f47 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S2)) (= (f48 (f49 f50 (f20 (f51 f52 ?v0) ?v1)) ?v2) (f20 (f51 f52 (f48 (f49 f50 ?v0) ?v2)) (f48 (f49 f50 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f14 (f16 f17 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f47 ?v0))) (= (f14 (f16 f47 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f16 f17 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S2)) (let ((?v_0 (f49 f50 ?v0))) (= (f48 (f49 f50 (f48 ?v_0 ?v1)) ?v2) (f48 ?v_0 (f14 (f16 f17 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4) (?v4 S4)) (let ((?v_0 (f6 f7 ?v0))) (=> (not (= ?v0 f61)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f5 (f6 f53 ?v1) (f5 ?v_0 ?v3)) (f5 (f6 f53 ?v2) (f5 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (let ((?v_0 (f16 f17 ?v0))) (=> (not (= ?v0 f40)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f14 (f16 f25 ?v1) (f14 ?v_0 ?v3)) (f14 (f16 f25 ?v2) (f14 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11) (?v4 S11)) (let ((?v_0 (f51 f52 ?v0))) (=> (not (= ?v0 f59)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f20 (f51 f56 ?v1) (f20 ?v_0 ?v3)) (f20 (f51 f56 ?v2) (f20 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f20 (f51 f56 (f20 (f51 f52 ?v0) ?v0)) (f20 (f51 f52 ?v1) ?v1)) f59) (and (= ?v0 f59) (= ?v1 f59)))))
(assert (= f61 (f54 f55 f23)))
(assert (= f59 (f20 f57 f23)))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f5 (f6 f7 (f3 ?v_0 ?v1)) ?v0) (f3 ?v_0 (f14 f15 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f16 f47 ?v0))) (= (f14 (f16 f17 (f14 ?v_0 ?v1)) ?v0) (f14 ?v_0 (f14 f15 ?v1))))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_0 (f49 f50 ?v0))) (= (f20 (f51 f52 (f48 ?v_0 ?v1)) ?v0) (f48 ?v_0 (f14 f15 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f5 (f6 f7 ?v0) (f3 ?v_0 ?v1)) (f3 ?v_0 (f14 f15 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f16 f47 ?v0))) (= (f14 (f16 f17 ?v0) (f14 ?v_0 ?v1)) (f14 ?v_0 (f14 f15 ?v1))))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_0 (f49 f50 ?v0))) (= (f20 (f51 f52 ?v0) (f48 ?v_0 ?v1)) (f48 ?v_0 (f14 f15 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f3 ?v_0 (f14 f15 ?v1)) (f5 (f6 f7 ?v0) (f3 ?v_0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f16 f47 ?v0))) (= (f14 ?v_0 (f14 f15 ?v1)) (f14 (f16 f17 ?v0) (f14 ?v_0 ?v1))))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_0 (f49 f50 ?v0))) (= (f48 ?v_0 (f14 f15 ?v1)) (f20 (f51 f52 ?v0) (f48 ?v_0 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f5 (f6 f7 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2)) (f3 ?v_0 (f14 (f16 f25 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f47 ?v0))) (= (f14 (f16 f17 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2)) (f14 ?v_0 (f14 (f16 f25 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S2)) (let ((?v_0 (f49 f50 ?v0))) (= (f20 (f51 f52 (f48 ?v_0 ?v1)) (f48 ?v_0 ?v2)) (f48 ?v_0 (f14 (f16 f25 ?v1) ?v2))))))
(assert (= (f18 f19 f23) f40))
(assert (= f40 (f18 f19 f23)))
(assert (forall ((?v0 S4)) (= (f3 (f8 f9 ?v0) (f18 f19 (f20 f22 (f20 f22 f23)))) (f5 (f6 f7 (f5 (f6 f7 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S2)) (= (f14 (f16 f47 ?v0) (f18 f19 (f20 f22 (f20 f22 f23)))) (f14 (f16 f17 (f14 (f16 f17 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S11)) (= (f48 (f49 f50 ?v0) (f18 f19 (f20 f22 (f20 f22 f23)))) (f20 (f51 f52 (f20 (f51 f52 ?v0) ?v0)) ?v0))))
(assert (= (f18 f19 (f20 f22 (f20 f22 f23))) (f14 f15 (f14 f15 (f14 f15 f40)))))
(assert (= (f18 f19 (f20 f22 f23)) (f14 f15 f40)))
(assert (forall ((?v0 S2)) (= (f14 f15 (f14 f15 (f14 f15 ?v0))) (f14 (f16 f25 (f18 f19 (f20 f22 (f20 f22 f23)))) ?v0))))
(assert (forall ((?v0 S4)) (= (= (f3 (f8 f9 ?v0) (f18 f19 (f20 f21 (f20 f22 f23)))) f61) (= ?v0 f61))))
(assert (forall ((?v0 S11)) (= (= (f48 (f49 f50 ?v0) (f18 f19 (f20 f21 (f20 f22 f23)))) f59) (= ?v0 f59))))
(assert (= (f3 (f8 f9 f61) (f18 f19 (f20 f21 (f20 f22 f23)))) f61))
(assert (= (f48 (f49 f50 f59) (f18 f19 (f20 f21 (f20 f22 f23)))) f59))
(assert (= (f14 (f16 f47 f40) (f18 f19 (f20 f21 (f20 f22 f23)))) f40))
(assert (forall ((?v0 S4)) (= (f3 (f8 f9 ?v0) (f18 f19 (f20 f21 (f20 f22 f23)))) (f5 (f6 f7 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f14 (f16 f47 ?v0) (f18 f19 (f20 f21 (f20 f22 f23)))) (f14 (f16 f17 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f48 (f49 f50 ?v0) (f18 f19 (f20 f21 (f20 f22 f23)))) (f20 (f51 f52 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 ?v0) ?v0) (f3 (f8 f9 ?v0) (f18 f19 (f20 f21 (f20 f22 f23)))))))
(assert (forall ((?v0 S2)) (= (f14 (f16 f17 ?v0) ?v0) (f14 (f16 f47 ?v0) (f18 f19 (f20 f21 (f20 f22 f23)))))))
(assert (forall ((?v0 S11)) (= (f20 (f51 f52 ?v0) ?v0) (f48 (f49 f50 ?v0) (f18 f19 (f20 f21 (f20 f22 f23)))))))
(assert (= (f18 f19 (f20 f21 (f20 f22 f23))) (f14 f15 (f14 f15 f40))))
(assert (= (f14 f15 (f14 f15 f40)) (f18 f19 (f20 f21 (f20 f22 f23)))))
(assert (forall ((?v0 S4)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (= (f3 (f8 f9 (f5 f41 ?v0)) ?v_0) (f3 (f8 f9 ?v0) ?v_0)))))
(assert (forall ((?v0 S11)) (let ((?v_0 (f18 f19 (f20 f21 (f20 f22 f23))))) (= (f48 (f49 f50 (f20 f58 ?v0)) ?v_0) (f48 (f49 f50 ?v0) ?v_0)))))
(assert (forall ((?v0 S2)) (= (f14 (f16 f25 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v0) (f14 f15 (f14 f15 ?v0)))))
(assert (forall ((?v0 S2)) (= (f14 (f16 f25 ?v0) (f18 f19 (f20 f21 (f20 f22 f23)))) (f14 f15 (f14 f15 ?v0)))))
(assert (let ((?v_0 (f39 f40 f11))) (= (f36 (f37 f38 f29) (f39 f40 (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) f11))) (f5 (f6 f53 (f36 (f37 f38 f27) ?v_0)) (f36 (f37 f38 f24) ?v_0)))))
(assert (forall ((?v0 S11) (?v1 S2)) (=> (= (f63 (f48 (f49 f50 ?v0) (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v1)) f59) f1) (= ?v0 f59))))
(assert (forall ((?v0 S2)) (= (f42 f40 (f14 f15 ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f37 f38 ?v0))) (= (f36 ?v_0 (f39 ?v1 (f14 f15 ?v2))) (ite (= (f42 ?v2 ?v1) f1) f61 (f5 (f6 f53 (f36 ?v_0 (f39 ?v1 ?v2))) (f3 ?v0 ?v2)))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (let ((?v_0 (f65 f66 ?v0))) (= (f64 ?v_0 (f39 ?v1 (f14 f15 ?v2))) (ite (= (f42 ?v2 ?v1) f1) f40 (f14 (f16 f25 (f64 ?v_0 (f39 ?v1 ?v2))) (f14 ?v0 ?v2)))))))
(assert (forall ((?v0 S21) (?v1 S2) (?v2 S2)) (let ((?v_0 (f68 f69 ?v0))) (= (f67 ?v_0 (f39 ?v1 (f14 f15 ?v2))) (ite (= (f42 ?v2 ?v1) f1) f59 (f20 (f51 f56 (f67 ?v_0 (f39 ?v1 ?v2))) (f48 ?v0 ?v2)))))))
(assert (= (f42 f40 (f18 f19 (f20 f21 (f20 f22 f23)))) f1))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 (f54 f55 (f20 f21 (f20 f22 f23)))) ?v0) (f5 (f6 f53 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f14 (f16 f17 (f18 f19 (f20 f21 (f20 f22 f23)))) ?v0) (f14 (f16 f25 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f20 (f51 f52 (f20 f57 (f20 f21 (f20 f22 f23)))) ?v0) (f20 (f51 f56 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 (f54 f55 (f20 f21 (f20 f22 f23)))) ?v0) (f5 (f6 f53 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f20 (f51 f52 (f20 f57 (f20 f21 (f20 f22 f23)))) ?v0) (f20 (f51 f56 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 ?v0) (f54 f55 (f20 f21 (f20 f22 f23)))) (f5 (f6 f53 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f14 (f16 f17 ?v0) (f18 f19 (f20 f21 (f20 f22 f23)))) (f14 (f16 f25 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f20 (f51 f52 ?v0) (f20 f57 (f20 f21 (f20 f22 f23)))) (f20 (f51 f56 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (=> (= (f42 ?v0 f40) f1) false)))
(assert (forall ((?v0 S2)) (= (f42 ?v0 (f14 f15 ?v0)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f42 ?v0 ?v1) f1) (= (f42 (f14 f15 ?v0) (f14 f15 ?v1)) f1))))
(assert (forall ((?v0 S2)) (= (f43 f40 ?v0) f1)))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f62 (f20 f22 ?v0) (f20 f22 ?v1)) f1) (= (f62 ?v0 ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f62 (f20 f22 ?v0) (f20 f22 ?v1)) f1) (= (f62 ?v0 ?v1) f1))))
(assert (forall ((?v0 S11)) (= (= (f62 (f20 f22 ?v0) f59) f1) (= (f62 ?v0 f59) f1))))
(assert (= (= (f62 f23 f23) f1) false))
(assert (= (= (f62 f23 f59) f1) false))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f62 (f20 f21 ?v0) (f20 f21 ?v1)) f1) (= (f62 ?v0 ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f62 (f20 f21 ?v0) (f20 f21 ?v1)) f1) (= (f62 ?v0 ?v1) f1))))
(assert (forall ((?v0 S11)) (= (= (f62 (f20 f21 ?v0) f59) f1) (= (f62 ?v0 f59) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f63 (f20 f22 ?v0) (f20 f22 ?v1)) f1) (= (f63 ?v0 ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f63 (f20 f22 ?v0) (f20 f22 ?v1)) f1) (= (f63 ?v0 ?v1) f1))))
(assert (= (= (f63 f23 f23) f1) true))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f63 (f20 f21 ?v0) (f20 f21 ?v1)) f1) (= (f63 ?v0 ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f63 (f20 f21 ?v0) (f20 f21 ?v1)) f1) (= (f63 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2)) (= (f14 (f16 f17 f26) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= f26 (f14 (f16 f17 ?v0) ?v1)) (and (= ?v0 f26) (= ?v1 f26)))))
(assert (forall ((?v0 S2)) (= (f14 (f16 f17 ?v0) f26) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f14 (f16 f17 ?v0) ?v1) f26) (and (= ?v0 f26) (= ?v1 f26)))))
(assert (forall ((?v0 S11)) (= (= (f62 f23 (f20 f22 ?v0)) f1) (= (f63 f23 ?v0) f1))))
(assert (forall ((?v0 S11)) (= (= (f63 (f20 f22 ?v0) f23) f1) (= (f62 ?v0 f23) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f62 (f20 f21 ?v0) (f20 f22 ?v1)) f1) (= (f63 ?v0 ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f62 (f20 f21 ?v0) (f20 f22 ?v1)) f1) (= (f63 ?v0 ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f63 (f20 f22 ?v0) (f20 f21 ?v1)) f1) (= (f62 ?v0 ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f63 (f20 f22 ?v0) (f20 f21 ?v1)) f1) (= (f62 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2)) (= (f14 (f16 f17 f26) ?v0) ?v0)))
(assert (forall ((?v0 S11)) (= (f20 (f51 f52 f70) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 f71) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f14 (f16 f17 ?v0) f26) ?v0)))
(assert (forall ((?v0 S11)) (= (f20 (f51 f52 ?v0) f70) ?v0)))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 ?v0) f71) ?v0)))
(assert (forall ((?v0 S4)) (= (f3 (f8 f9 ?v0) f26) ?v0)))
(assert (forall ((?v0 S2)) (= (f14 (f16 f47 ?v0) f26) ?v0)))
(assert (forall ((?v0 S11)) (= (f48 (f49 f50 ?v0) f26) ?v0)))
(assert (forall ((?v0 S11)) (= (= (f62 (f20 f22 ?v0) f23) f1) (= (f62 ?v0 f23) f1))))
(check-sat)
(exit)