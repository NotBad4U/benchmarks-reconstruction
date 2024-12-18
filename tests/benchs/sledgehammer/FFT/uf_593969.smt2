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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 () S3)
(declare-fun f6 (S5 S2) S2)
(declare-fun f7 (S6 S2) S5)
(declare-fun f8 () S6)
(declare-fun f9 () S6)
(declare-fun f10 (S7 S8) S2)
(declare-fun f11 () S7)
(declare-fun f12 (S9 S8) S8)
(declare-fun f13 () S9)
(declare-fun f14 () S9)
(declare-fun f15 () S8)
(declare-fun f16 () S2)
(declare-fun f17 () S3)
(declare-fun f18 (S10 S2) S11)
(declare-fun f19 (S12 S2) S10)
(declare-fun f20 (S13 S10) S12)
(declare-fun f21 () S13)
(declare-fun f22 (S14 S15) S11)
(declare-fun f23 (S16 S10) S14)
(declare-fun f24 () S16)
(declare-fun f25 (S2 S2) S15)
(declare-fun f26 (S17 S5) S6)
(declare-fun f27 () S17)
(declare-fun f28 (S18 S15) S2)
(declare-fun f29 (S19 S5) S18)
(declare-fun f30 () S19)
(declare-fun f31 (S20 S2) S8)
(declare-fun f32 (S21 S2) S20)
(declare-fun f33 (S22 S20) S21)
(declare-fun f34 () S22)
(declare-fun f35 (S23 S15) S8)
(declare-fun f36 (S24 S20) S23)
(declare-fun f37 () S24)
(declare-fun f38 (S25 S2) S3)
(declare-fun f39 (S3) S25)
(declare-fun f40 (S3 S15) S4)
(declare-fun f41 () S13)
(declare-fun f42 () S17)
(declare-fun f43 () S22)
(declare-fun f44 (S3) S25)
(declare-fun f45 (S26 S10) S10)
(declare-fun f46 (S27 S2) S26)
(declare-fun f47 () S27)
(declare-fun f48 () S2)
(declare-fun f49 () S2)
(declare-fun f50 (S4 S4) S4)
(declare-fun f51 (S28 S8) S9)
(declare-fun f52 () S28)
(declare-fun f53 (S29 S11) S11)
(declare-fun f54 (S30 S11) S29)
(declare-fun f55 () S30)
(declare-fun f56 () S11)
(declare-fun f57 (S31 S8) S11)
(declare-fun f58 () S31)
(declare-fun f59 () S8)
(declare-fun f60 () S9)
(declare-fun f61 () S28)
(declare-fun f62 () S30)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f3 f5 (f6 (f7 f8 (f6 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v0)) f16)))))
(assert (forall ((?v0 S2)) (= (f3 f17 ?v0) (f3 f5 (f6 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v0)))))
(assert (forall ((?v0 S10) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 (f7 f9 ?v2) ?v1))) (= (f18 (f19 (f20 f21 ?v0) ?v1) ?v2) (f22 (f23 f24 ?v0) (f25 ?v_0 (f6 (f7 f8 ?v_0) ?v1)))))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 (f7 f9 ?v2) ?v1))) (= (f6 (f7 (f26 f27 ?v0) ?v1) ?v2) (f28 (f29 f30 ?v0) (f25 ?v_0 (f6 (f7 f8 ?v_0) ?v1)))))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 (f7 f9 ?v2) ?v1))) (= (f31 (f32 (f33 f34 ?v0) ?v1) ?v2) (f35 (f36 f37 ?v0) (f25 ?v_0 (f6 (f7 f8 ?v_0) ?v1)))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 (f7 f9 ?v2) ?v1))) (= (f3 (f38 (f39 ?v0) ?v1) ?v2) (f40 ?v0 (f25 ?v_0 (f6 (f7 f8 ?v_0) ?v1)))))))
(assert (forall ((?v0 S10) (?v1 S2) (?v2 S2)) (= (f18 (f19 (f20 f41 ?v0) ?v1) ?v2) (f18 ?v0 (f6 (f7 f8 ?v2) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2)) (= (f6 (f7 (f26 f42 ?v0) ?v1) ?v2) (f6 ?v0 (f6 (f7 f8 ?v2) ?v1)))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S2)) (= (f31 (f32 (f33 f43 ?v0) ?v1) ?v2) (f31 ?v0 (f6 (f7 f8 ?v2) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (= (f3 (f38 (f44 ?v0) ?v1) ?v2) (f3 ?v0 (f6 (f7 f8 ?v2) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S10) (?v2 S2)) (= (f18 (f45 (f46 f47 ?v0) ?v1) ?v2) (f18 ?v1 (f6 (f7 f8 ?v2) ?v0)))))
(assert (let ((?v_0 (f25 f48 f49))) (not (= (f40 f5 (f25 f48 (f6 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) f49))) (f50 (f40 f17 ?v_0) (f40 f4 ?v_0))))))
(assert (forall ((?v0 S3)) (let ((?v_1 (f12 f14 f15))) (let ((?v_0 (f12 f13 ?v_1))) (= (f40 ?v0 (f25 f48 (f10 f11 (f12 f13 ?v_0)))) (f50 (f50 (f50 (f3 ?v0 f48) (f3 ?v0 f16)) (f3 ?v0 (f10 f11 ?v_0))) (f3 ?v0 (f10 f11 (f12 f14 ?v_1)))))))))
(assert (forall ((?v0 S5)) (let ((?v_1 (f12 f14 f15))) (let ((?v_0 (f12 f13 ?v_1))) (= (f28 (f29 f30 ?v0) (f25 f48 (f10 f11 (f12 f13 ?v_0)))) (f6 (f7 f8 (f6 (f7 f8 (f6 (f7 f8 (f6 ?v0 f48)) (f6 ?v0 f16))) (f6 ?v0 (f10 f11 ?v_0)))) (f6 ?v0 (f10 f11 (f12 f14 ?v_1)))))))))
(assert (forall ((?v0 S20)) (let ((?v_1 (f12 f14 f15))) (let ((?v_0 (f12 f13 ?v_1))) (= (f35 (f36 f37 ?v0) (f25 f48 (f10 f11 (f12 f13 ?v_0)))) (f12 (f51 f52 (f12 (f51 f52 (f12 (f51 f52 (f31 ?v0 f48)) (f31 ?v0 f16))) (f31 ?v0 (f10 f11 ?v_0)))) (f31 ?v0 (f10 f11 (f12 f14 ?v_1)))))))))
(assert (forall ((?v0 S10)) (let ((?v_1 (f12 f14 f15))) (let ((?v_0 (f12 f13 ?v_1))) (= (f22 (f23 f24 ?v0) (f25 f48 (f10 f11 (f12 f13 ?v_0)))) (f53 (f54 f55 (f53 (f54 f55 (f53 (f54 f55 (f18 ?v0 f48)) (f18 ?v0 f16))) (f18 ?v0 (f10 f11 ?v_0)))) (f18 ?v0 (f10 f11 (f12 f14 ?v_1)))))))))
(assert (= (f6 (f7 f8 f16) f16) (f10 f11 (f12 f13 (f12 f14 f15)))))
(assert (forall ((?v0 S2)) (= (f6 (f7 f9 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f6 (f7 f8 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f6 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v0) (f6 (f7 f8 ?v0) ?v0))))
(assert (= (f53 (f54 f55 f56) f56) (f57 f58 (f12 f13 (f12 f14 f15)))))
(assert (= (f12 (f51 f52 f59) f59) (f12 f60 (f12 f13 (f12 f14 f15)))))
(assert (= (f53 (f54 f55 f56) f56) (f57 f58 (f12 f13 (f12 f14 f15)))))
(assert (= (f6 (f7 f8 f16) f16) (f10 f11 (f12 f13 (f12 f14 f15)))))
(assert (= (f12 (f51 f52 f59) f59) (f12 f60 (f12 f13 (f12 f14 f15)))))
(assert (forall ((?v0 S8)) (= (f12 (f51 f61 ?v0) (f12 f60 (f12 f13 (f12 f14 f15)))) (f12 (f51 f52 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f53 (f54 f62 ?v0) (f57 f58 (f12 f13 (f12 f14 f15)))) (f53 (f54 f55 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f6 (f7 f9 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f6 (f7 f8 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f12 (f51 f61 ?v0) (f12 f60 (f12 f13 (f12 f14 f15)))) (f12 (f51 f52 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f53 (f54 f62 ?v0) (f57 f58 (f12 f13 (f12 f14 f15)))) (f53 (f54 f55 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f12 (f51 f61 (f12 f60 (f12 f13 (f12 f14 f15)))) ?v0) (f12 (f51 f52 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f53 (f54 f62 (f57 f58 (f12 f13 (f12 f14 f15)))) ?v0) (f53 (f54 f55 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f6 (f7 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v0) (f6 (f7 f8 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f12 (f51 f61 (f12 f60 (f12 f13 (f12 f14 f15)))) ?v0) (f12 (f51 f52 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f53 (f54 f62 (f57 f58 (f12 f13 (f12 f14 f15)))) ?v0) (f53 (f54 f55 ?v0) ?v0))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S2)) (= (f35 (f36 f37 (f32 (f33 f34 ?v0) ?v1)) (f25 f48 ?v2)) (f35 (f36 f37 ?v0) (f25 f48 (f6 (f7 f9 ?v2) ?v1))))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2)) (= (f28 (f29 f30 (f7 (f26 f27 ?v0) ?v1)) (f25 f48 ?v2)) (f28 (f29 f30 ?v0) (f25 f48 (f6 (f7 f9 ?v2) ?v1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (= (f40 (f38 (f39 ?v0) ?v1) (f25 f48 ?v2)) (f40 ?v0 (f25 f48 (f6 (f7 f9 ?v2) ?v1))))))
(assert (forall ((?v0 S10) (?v1 S2) (?v2 S2)) (= (f22 (f23 f24 (f19 (f20 f21 ?v0) ?v1)) (f25 f48 ?v2)) (f22 (f23 f24 ?v0) (f25 f48 (f6 (f7 f9 ?v2) ?v1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (= (f40 ?v0 (f25 f48 (f6 (f7 f8 ?v1) ?v2))) (f50 (f40 (f38 (f44 ?v0) ?v2) (f25 f48 ?v1)) (f40 ?v0 (f25 f48 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2)) (let ((?v_0 (f29 f30 ?v0))) (= (f28 ?v_0 (f25 f48 (f6 (f7 f8 ?v1) ?v2))) (f6 (f7 f8 (f28 (f29 f30 (f7 (f26 f42 ?v0) ?v2)) (f25 f48 ?v1))) (f28 ?v_0 (f25 f48 ?v2)))))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S2)) (let ((?v_0 (f36 f37 ?v0))) (= (f35 ?v_0 (f25 f48 (f6 (f7 f8 ?v1) ?v2))) (f12 (f51 f52 (f35 (f36 f37 (f32 (f33 f43 ?v0) ?v2)) (f25 f48 ?v1))) (f35 ?v_0 (f25 f48 ?v2)))))))
(assert (forall ((?v0 S10) (?v1 S2) (?v2 S2)) (let ((?v_0 (f23 f24 ?v0))) (= (f22 ?v_0 (f25 f48 (f6 (f7 f8 ?v1) ?v2))) (f53 (f54 f55 (f22 (f23 f24 (f19 (f20 f41 ?v0) ?v2)) (f25 f48 ?v1))) (f22 ?v_0 (f25 f48 ?v2)))))))
(assert (forall ((?v0 S8)) (= (f53 (f54 f55 f56) (f57 f58 ?v0)) (f57 f58 (f12 (f51 f52 (f12 f14 f15)) ?v0)))))
(assert (forall ((?v0 S8)) (= (f12 (f51 f52 f59) (f12 f60 ?v0)) (f12 f60 (f12 (f51 f52 (f12 f14 f15)) ?v0)))))
(assert (forall ((?v0 S8)) (= (f12 f14 ?v0) (f12 (f51 f52 (f12 (f51 f52 f59) ?v0)) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f51 f52 ?v0) ?v1) (f12 (f51 f52 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f51 f52 ?v0)) (?v_0 (f51 f52 ?v1))) (= (f12 ?v_1 (f12 ?v_0 ?v2)) (f12 ?v_0 (f12 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f51 f61 ?v0))) (= (f12 ?v_0 (f12 (f51 f52 ?v1) ?v2)) (f12 (f51 f52 (f12 ?v_0 ?v1)) (f12 ?v_0 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f51 f52 (f12 f60 ?v0)) (f12 f60 ?v1)) (f12 f60 (f12 (f51 f52 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f51 f52 ?v0))) (= (f12 (f51 f52 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f51 f52 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (f12 (f51 f61 (f12 (f51 f52 ?v0) ?v1)) ?v2) (f12 (f51 f52 (f12 (f51 f61 ?v0) ?v2)) (f12 (f51 f61 ?v1) ?v2)))))
(assert (forall ((?v0 S8)) (= (f12 (f51 f52 ?v0) f15) ?v0)))
(assert (forall ((?v0 S8)) (= (f12 (f51 f52 f15) ?v0) ?v0)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f51 f52 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f12 (f51 f52 ?v0) ?v1)))))
(assert (forall ((?v0 S8)) (= (f12 f13 ?v0) (f12 (f51 f52 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f12 (f51 f61 f15) ?v0) f15)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f51 f61 (f12 f13 ?v0)) ?v1) (f12 f13 (f12 (f51 f61 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f51 f61 (f12 f14 ?v0)) ?v1) (f12 (f51 f52 (f12 f13 (f12 (f51 f61 ?v0) ?v1))) ?v1))))
(assert (= f59 (f12 f60 (f12 f14 f15))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S10)) (let ((?v_0 (f23 f24 ?v2))) (= (f22 ?v_0 (f25 f48 (f6 (f7 f8 ?v1) ?v0))) (f53 (f54 f55 (f22 (f23 f24 (f45 (f46 f47 ?v0) ?v2)) (f25 f48 ?v1))) (f22 ?v_0 (f25 f48 ?v0)))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f51 f52 (f12 f14 ?v0)) (f12 f13 ?v1)) (f12 f14 (f12 (f51 f52 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 (f51 f52 (f12 f13 ?v0)) (f12 f14 ?v1)) (f12 f14 (f12 (f51 f52 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f57 f58 ?v0) (f57 f58 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f12 f60 ?v0) (f12 f60 ?v1)) (= ?v0 ?v1))))
(check-sat)
(exit)
