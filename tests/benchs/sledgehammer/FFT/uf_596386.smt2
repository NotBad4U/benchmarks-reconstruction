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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S2)
(declare-fun f4 () S3)
(declare-fun f5 (S4 S2) S3)
(declare-fun f6 () S4)
(declare-fun f7 () S4)
(declare-fun f8 (S5 S6) S2)
(declare-fun f9 () S5)
(declare-fun f10 (S7 S6) S6)
(declare-fun f11 () S7)
(declare-fun f12 () S7)
(declare-fun f13 () S6)
(declare-fun f14 () S2)
(declare-fun f15 (S8 S2) S9)
(declare-fun f16 (S10 S2) S8)
(declare-fun f17 (S11 S8) S10)
(declare-fun f18 () S11)
(declare-fun f19 (S12 S13) S9)
(declare-fun f20 (S14 S8) S12)
(declare-fun f21 () S14)
(declare-fun f22 (S2 S2) S13)
(declare-fun f23 (S15 S3) S4)
(declare-fun f24 () S15)
(declare-fun f25 (S16 S13) S2)
(declare-fun f26 (S17 S3) S16)
(declare-fun f27 () S17)
(declare-fun f28 (S18 S2) S6)
(declare-fun f29 (S19 S2) S18)
(declare-fun f30 (S20 S18) S19)
(declare-fun f31 () S20)
(declare-fun f32 (S21 S13) S6)
(declare-fun f33 (S22 S18) S21)
(declare-fun f34 () S22)
(declare-fun f35 (S23 S2) S24)
(declare-fun f36 (S25 S2) S23)
(declare-fun f37 (S23) S25)
(declare-fun f38 (S23 S13) S24)
(declare-fun f39 () S11)
(declare-fun f40 () S15)
(declare-fun f41 () S20)
(declare-fun f42 (S23) S25)
(declare-fun f43 (S26 S8) S8)
(declare-fun f44 (S27 S2) S26)
(declare-fun f45 () S27)
(declare-fun f46 () S23)
(declare-fun f47 () S2)
(declare-fun f48 () S2)
(declare-fun f49 (S24 S24) S24)
(declare-fun f50 (S3 S13) S13)
(declare-fun f51 (S28 S6) S7)
(declare-fun f52 () S28)
(declare-fun f53 (S29 S9) S9)
(declare-fun f54 (S30 S9) S29)
(declare-fun f55 () S30)
(declare-fun f56 () S9)
(declare-fun f57 (S31 S6) S9)
(declare-fun f58 () S31)
(declare-fun f59 () S6)
(declare-fun f60 () S7)
(declare-fun f61 () S28)
(declare-fun f62 () S30)
(declare-fun f63 () S6)
(declare-fun f64 () S9)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f3 (f5 f6 (f3 (f5 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) ?v0)) f14))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (let ((?v_0 (f3 (f5 f7 ?v2) ?v1))) (= (f15 (f16 (f17 f18 ?v0) ?v1) ?v2) (f19 (f20 f21 ?v0) (f22 ?v_0 (f3 (f5 f6 ?v_0) ?v1)))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f3 (f5 f7 ?v2) ?v1))) (= (f3 (f5 (f23 f24 ?v0) ?v1) ?v2) (f25 (f26 f27 ?v0) (f22 ?v_0 (f3 (f5 f6 ?v_0) ?v1)))))))
(assert (forall ((?v0 S18) (?v1 S2) (?v2 S2)) (let ((?v_0 (f3 (f5 f7 ?v2) ?v1))) (= (f28 (f29 (f30 f31 ?v0) ?v1) ?v2) (f32 (f33 f34 ?v0) (f22 ?v_0 (f3 (f5 f6 ?v_0) ?v1)))))))
(assert (forall ((?v0 S23) (?v1 S2) (?v2 S2)) (let ((?v_0 (f3 (f5 f7 ?v2) ?v1))) (= (f35 (f36 (f37 ?v0) ?v1) ?v2) (f38 ?v0 (f22 ?v_0 (f3 (f5 f6 ?v_0) ?v1)))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (= (f15 (f16 (f17 f39 ?v0) ?v1) ?v2) (f15 ?v0 (f3 (f5 f6 ?v2) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (= (f3 (f5 (f23 f40 ?v0) ?v1) ?v2) (f3 ?v0 (f3 (f5 f6 ?v2) ?v1)))))
(assert (forall ((?v0 S18) (?v1 S2) (?v2 S2)) (= (f28 (f29 (f30 f41 ?v0) ?v1) ?v2) (f28 ?v0 (f3 (f5 f6 ?v2) ?v1)))))
(assert (forall ((?v0 S23) (?v1 S2) (?v2 S2)) (= (f35 (f36 (f42 ?v0) ?v1) ?v2) (f35 ?v0 (f3 (f5 f6 ?v2) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S8) (?v2 S2)) (= (f15 (f43 (f44 f45 ?v0) ?v1) ?v2) (f15 ?v1 (f3 (f5 f6 ?v2) ?v0)))))
(assert (let ((?v_0 (f5 f7 (f8 f9 (f10 f11 (f10 f12 f13))))) (?v_1 (f22 f47 f48))) (not (= (f38 f46 (f22 f47 (f3 ?v_0 f48))) (f49 (f38 f46 (f50 ?v_0 ?v_1)) (f38 f46 (f50 f4 ?v_1)))))))
(assert (forall ((?v0 S23)) (let ((?v_1 (f10 f12 f13))) (let ((?v_0 (f10 f11 ?v_1))) (= (f38 ?v0 (f22 f47 (f8 f9 (f10 f11 ?v_0)))) (f49 (f49 (f49 (f35 ?v0 f47) (f35 ?v0 f14)) (f35 ?v0 (f8 f9 ?v_0))) (f35 ?v0 (f8 f9 (f10 f12 ?v_1)))))))))
(assert (forall ((?v0 S3)) (let ((?v_1 (f10 f12 f13))) (let ((?v_0 (f10 f11 ?v_1))) (= (f25 (f26 f27 ?v0) (f22 f47 (f8 f9 (f10 f11 ?v_0)))) (f3 (f5 f6 (f3 (f5 f6 (f3 (f5 f6 (f3 ?v0 f47)) (f3 ?v0 f14))) (f3 ?v0 (f8 f9 ?v_0)))) (f3 ?v0 (f8 f9 (f10 f12 ?v_1)))))))))
(assert (forall ((?v0 S18)) (let ((?v_1 (f10 f12 f13))) (let ((?v_0 (f10 f11 ?v_1))) (= (f32 (f33 f34 ?v0) (f22 f47 (f8 f9 (f10 f11 ?v_0)))) (f10 (f51 f52 (f10 (f51 f52 (f10 (f51 f52 (f28 ?v0 f47)) (f28 ?v0 f14))) (f28 ?v0 (f8 f9 ?v_0)))) (f28 ?v0 (f8 f9 (f10 f12 ?v_1)))))))))
(assert (forall ((?v0 S8)) (let ((?v_1 (f10 f12 f13))) (let ((?v_0 (f10 f11 ?v_1))) (= (f19 (f20 f21 ?v0) (f22 f47 (f8 f9 (f10 f11 ?v_0)))) (f53 (f54 f55 (f53 (f54 f55 (f53 (f54 f55 (f15 ?v0 f47)) (f15 ?v0 f14))) (f15 ?v0 (f8 f9 ?v_0)))) (f15 ?v0 (f8 f9 (f10 f12 ?v_1)))))))))
(assert (= (f3 (f5 f6 f14) f14) (f8 f9 (f10 f11 (f10 f12 f13)))))
(assert (forall ((?v0 S2)) (= (f3 (f5 f7 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f3 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f3 (f5 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) ?v0) (f3 (f5 f6 ?v0) ?v0))))
(assert (= (f53 (f54 f55 f56) f56) (f57 f58 (f10 f11 (f10 f12 f13)))))
(assert (= (f10 (f51 f52 f59) f59) (f10 f60 (f10 f11 (f10 f12 f13)))))
(assert (= (f53 (f54 f55 f56) f56) (f57 f58 (f10 f11 (f10 f12 f13)))))
(assert (= (f3 (f5 f6 f14) f14) (f8 f9 (f10 f11 (f10 f12 f13)))))
(assert (= (f10 (f51 f52 f59) f59) (f10 f60 (f10 f11 (f10 f12 f13)))))
(assert (forall ((?v0 S6)) (= (f10 (f51 f61 ?v0) (f10 f60 (f10 f11 (f10 f12 f13)))) (f10 (f51 f52 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f53 (f54 f62 ?v0) (f57 f58 (f10 f11 (f10 f12 f13)))) (f53 (f54 f55 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f3 (f5 f7 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f3 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f10 (f51 f61 ?v0) (f10 f60 (f10 f11 (f10 f12 f13)))) (f10 (f51 f52 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f53 (f54 f62 ?v0) (f57 f58 (f10 f11 (f10 f12 f13)))) (f53 (f54 f55 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f10 (f51 f61 (f10 f60 (f10 f11 (f10 f12 f13)))) ?v0) (f10 (f51 f52 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f53 (f54 f62 (f57 f58 (f10 f11 (f10 f12 f13)))) ?v0) (f53 (f54 f55 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f3 (f5 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) ?v0) (f3 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f10 (f51 f61 (f10 f60 (f10 f11 (f10 f12 f13)))) ?v0) (f10 (f51 f52 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f53 (f54 f62 (f57 f58 (f10 f11 (f10 f12 f13)))) ?v0) (f53 (f54 f55 ?v0) ?v0))))
(assert (forall ((?v0 S18) (?v1 S2) (?v2 S2)) (= (f32 (f33 f34 (f29 (f30 f31 ?v0) ?v1)) (f22 f47 ?v2)) (f32 (f33 f34 ?v0) (f22 f47 (f3 (f5 f7 ?v2) ?v1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (= (f25 (f26 f27 (f5 (f23 f24 ?v0) ?v1)) (f22 f47 ?v2)) (f25 (f26 f27 ?v0) (f22 f47 (f3 (f5 f7 ?v2) ?v1))))))
(assert (forall ((?v0 S23) (?v1 S2) (?v2 S2)) (= (f38 (f36 (f37 ?v0) ?v1) (f22 f47 ?v2)) (f38 ?v0 (f22 f47 (f3 (f5 f7 ?v2) ?v1))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (= (f19 (f20 f21 (f16 (f17 f18 ?v0) ?v1)) (f22 f47 ?v2)) (f19 (f20 f21 ?v0) (f22 f47 (f3 (f5 f7 ?v2) ?v1))))))
(assert (forall ((?v0 S23) (?v1 S2) (?v2 S2)) (= (f38 ?v0 (f22 f47 (f3 (f5 f6 ?v1) ?v2))) (f49 (f38 (f36 (f42 ?v0) ?v2) (f22 f47 ?v1)) (f38 ?v0 (f22 f47 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f26 f27 ?v0))) (= (f25 ?v_0 (f22 f47 (f3 (f5 f6 ?v1) ?v2))) (f3 (f5 f6 (f25 (f26 f27 (f5 (f23 f40 ?v0) ?v2)) (f22 f47 ?v1))) (f25 ?v_0 (f22 f47 ?v2)))))))
(assert (forall ((?v0 S18) (?v1 S2) (?v2 S2)) (let ((?v_0 (f33 f34 ?v0))) (= (f32 ?v_0 (f22 f47 (f3 (f5 f6 ?v1) ?v2))) (f10 (f51 f52 (f32 (f33 f34 (f29 (f30 f41 ?v0) ?v2)) (f22 f47 ?v1))) (f32 ?v_0 (f22 f47 ?v2)))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 ?v_0 (f22 f47 (f3 (f5 f6 ?v1) ?v2))) (f53 (f54 f55 (f19 (f20 f21 (f16 (f17 f39 ?v0) ?v2)) (f22 f47 ?v1))) (f19 ?v_0 (f22 f47 ?v2)))))))
(assert (forall ((?v0 S6)) (= (f53 (f54 f55 f56) (f57 f58 ?v0)) (f57 f58 (f10 (f51 f52 (f10 f12 f13)) ?v0)))))
(assert (forall ((?v0 S6)) (= (f10 (f51 f52 f59) (f10 f60 ?v0)) (f10 f60 (f10 (f51 f52 (f10 f12 f13)) ?v0)))))
(assert (forall ((?v0 S6)) (= (f10 f12 ?v0) (f10 (f51 f52 (f10 (f51 f52 f59) ?v0)) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f51 f52 ?v0) ?v1) (f10 (f51 f52 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f51 f52 ?v0)) (?v_0 (f51 f52 ?v1))) (= (f10 ?v_1 (f10 ?v_0 ?v2)) (f10 ?v_0 (f10 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f51 f61 ?v0))) (= (f10 ?v_0 (f10 (f51 f52 ?v1) ?v2)) (f10 (f51 f52 (f10 ?v_0 ?v1)) (f10 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f51 f52 (f10 f60 ?v0)) (f10 f60 ?v1)) (f10 f60 (f10 (f51 f52 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f51 f52 ?v0))) (= (f10 (f51 f52 (f10 ?v_0 ?v1)) ?v2) (f10 ?v_0 (f10 (f51 f52 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f10 (f51 f61 (f10 (f51 f52 ?v0) ?v1)) ?v2) (f10 (f51 f52 (f10 (f51 f61 ?v0) ?v2)) (f10 (f51 f61 ?v1) ?v2)))))
(assert (forall ((?v0 S6)) (= (f10 (f51 f52 ?v0) f13) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f51 f52 f13) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f51 f52 (f10 f11 ?v0)) (f10 f11 ?v1)) (f10 f11 (f10 (f51 f52 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (f10 f11 ?v0) (f10 (f51 f52 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f10 (f51 f61 f13) ?v0) f13)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f51 f61 (f10 f11 ?v0)) ?v1) (f10 f11 (f10 (f51 f61 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f51 f61 (f10 f12 ?v0)) ?v1) (f10 (f51 f52 (f10 f11 (f10 (f51 f61 ?v0) ?v1))) ?v1))))
(assert (= f59 (f10 f60 (f10 f12 f13))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S8)) (let ((?v_0 (f20 f21 ?v2))) (= (f19 ?v_0 (f22 f47 (f3 (f5 f6 ?v1) ?v0))) (f53 (f54 f55 (f19 (f20 f21 (f43 (f44 f45 ?v0) ?v2)) (f22 f47 ?v1))) (f19 ?v_0 (f22 f47 ?v0)))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f51 f52 (f10 f12 ?v0)) (f10 f11 ?v1)) (f10 f12 (f10 (f51 f52 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f51 f52 (f10 f11 ?v0)) (f10 f12 ?v1)) (f10 f12 (f10 (f51 f52 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f57 f58 ?v0) (f57 f58 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f10 f60 ?v0) (f10 f60 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S9)) (let ((?v_0 (f57 f58 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f10 f60 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f10 f12 ?v0) (f10 f12 ?v1)) (= ?v0 ?v1))))
(assert (= (= f13 f13) true))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f10 f11 ?v0) (f10 f11 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6)) (= (= (f10 (f51 f52 ?v0) ?v0) f63) (= ?v0 f63))))
(assert (forall ((?v0 S9)) (= (= (f53 (f54 f55 ?v0) ?v0) f64) (= ?v0 f64))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S9)) (= (f53 (f54 f62 (f57 f58 ?v0)) (f53 (f54 f62 (f57 f58 ?v1)) ?v2)) (f53 (f54 f62 (f57 f58 (f10 (f51 f61 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f10 (f51 f61 (f10 f60 ?v0)) (f10 (f51 f61 (f10 f60 ?v1)) ?v2)) (f10 (f51 f61 (f10 f60 (f10 (f51 f61 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f53 (f54 f62 (f57 f58 ?v0)) (f57 f58 ?v1)) (f57 f58 (f10 (f51 f61 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f51 f61 (f10 f60 ?v0)) (f10 f60 ?v1)) (f10 f60 (f10 (f51 f61 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f57 f58 (f10 (f51 f61 ?v0) ?v1)) (f53 (f54 f62 (f57 f58 ?v0)) (f57 f58 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 f60 (f10 (f51 f61 ?v0) ?v1)) (f10 (f51 f61 (f10 f60 ?v0)) (f10 f60 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f10 (f51 f52 (f10 f60 ?v0)) (f10 (f51 f52 (f10 f60 ?v1)) ?v2)) (f10 (f51 f52 (f10 f60 (f10 (f51 f52 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S9)) (= (f53 (f54 f55 (f57 f58 ?v0)) (f53 (f54 f55 (f57 f58 ?v1)) ?v2)) (f53 (f54 f55 (f57 f58 (f10 (f51 f52 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f51 f52 (f10 f60 ?v0)) (f10 f60 ?v1)) (f10 f60 (f10 (f51 f52 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f53 (f54 f55 (f57 f58 ?v0)) (f57 f58 ?v1)) (f57 f58 (f10 (f51 f52 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 f60 (f10 (f51 f52 ?v0) ?v1)) (f10 (f51 f52 (f10 f60 ?v0)) (f10 f60 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f57 f58 (f10 (f51 f52 ?v0) ?v1)) (f53 (f54 f55 (f57 f58 ?v0)) (f57 f58 ?v1)))))
(assert (forall ((?v0 S6)) (= (= (f10 f12 ?v0) f13) false)))
(assert (forall ((?v0 S6)) (= (= f13 (f10 f12 ?v0)) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f10 f12 ?v0) (f10 f11 ?v1)) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f10 f11 ?v0) (f10 f12 ?v1)) false)))
(assert (forall ((?v0 S6)) (= (= (f10 f11 ?v0) f13) (= ?v0 f13))))
(assert (forall ((?v0 S6)) (= (= f13 (f10 f11 ?v0)) (= f13 ?v0))))
(assert (= (f10 f11 f13) f13))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f10 (f51 f52 (f10 (f51 f61 ?v0) ?v0)) (f10 (f51 f61 ?v1) ?v1)) f63) (and (= ?v0 f63) (= ?v1 f63)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f53 (f54 f55 (f53 (f54 f62 ?v0) ?v0)) (f53 (f54 f62 ?v1) ?v1)) f64) (and (= ?v0 f64) (= ?v1 f64)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (let ((?v_0 (f8 f9 ?v2))) (= (f3 (f5 f7 (f3 (f5 f6 ?v0) ?v1)) ?v_0) (f3 (f5 f6 (f3 (f5 f7 ?v0) ?v_0)) (f3 (f5 f7 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f10 f60 ?v2))) (= (f10 (f51 f61 (f10 (f51 f52 ?v0) ?v1)) ?v_0) (f10 (f51 f52 (f10 (f51 f61 ?v0) ?v_0)) (f10 (f51 f61 ?v1) ?v_0))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S6)) (let ((?v_0 (f57 f58 ?v2))) (= (f53 (f54 f62 (f53 (f54 f55 ?v0) ?v1)) ?v_0) (f53 (f54 f55 (f53 (f54 f62 ?v0) ?v_0)) (f53 (f54 f62 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 (f8 f9 ?v0)))) (= (f3 ?v_0 (f3 (f5 f6 ?v1) ?v2)) (f3 (f5 f6 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f51 f61 (f10 f60 ?v0)))) (= (f10 ?v_0 (f10 (f51 f52 ?v1) ?v2)) (f10 (f51 f52 (f10 ?v_0 ?v1)) (f10 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S9)) (let ((?v_0 (f54 f62 (f57 f58 ?v0)))) (= (f53 ?v_0 (f53 (f54 f55 ?v1) ?v2)) (f53 (f54 f55 (f53 ?v_0 ?v1)) (f53 ?v_0 ?v2))))))
(assert (= (f57 f58 f13) f64))
(assert (= (f8 f9 f13) f47))
(assert (= (f10 f60 f13) f63))
(assert (= (f57 f58 f13) f64))
(assert (= (f10 f60 f13) f63))
(assert (= f64 (f57 f58 f13)))
(assert (= f63 (f10 f60 f13)))
(assert (forall ((?v0 S6)) (= (f10 (f51 f52 (f10 f60 f13)) ?v0) ?v0)))
(assert (forall ((?v0 S9)) (= (f53 (f54 f55 (f57 f58 f13)) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f51 f52 ?v0) (f10 f60 f13)) ?v0)))
(assert (forall ((?v0 S9)) (= (f53 (f54 f55 ?v0) (f57 f58 f13)) ?v0)))
(assert (= (f8 f9 f13) f47))
(assert (= f47 (f8 f9 f13)))
(assert (forall ((?v0 S6)) (let ((?v_0 (f10 f60 ?v0))) (= (f10 f60 (f10 f11 ?v0)) (f10 (f51 f52 (f10 (f51 f52 f63) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f57 f58 ?v0))) (= (f57 f58 (f10 f11 ?v0)) (f53 (f54 f55 (f53 (f54 f55 f64) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f57 f58 ?v0))) (= (f57 f58 (f10 f12 ?v0)) (f53 (f54 f55 (f53 (f54 f55 f56) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f10 f60 ?v0))) (= (f10 f60 (f10 f12 ?v0)) (f10 (f51 f52 (f10 (f51 f52 f59) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S9)) (= (f53 (f54 f62 (f57 f58 (f10 f12 f13))) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f51 f61 (f10 f60 (f10 f12 f13))) ?v0) ?v0)))
(check-sat)
(exit)