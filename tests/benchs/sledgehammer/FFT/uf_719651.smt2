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
(declare-fun f27 () S3)
(declare-fun f28 () S3)
(declare-fun f29 (S13 S3) S3)
(declare-fun f30 () S13)
(declare-fun f31 (S14 S8) S8)
(declare-fun f32 () S14)
(declare-fun f33 (S15 S2) S11)
(declare-fun f34 (S16 S15) S15)
(declare-fun f35 () S16)
(declare-fun f36 () S13)
(declare-fun f37 () S14)
(declare-fun f38 () S16)
(declare-fun f39 (S17 S2) S3)
(declare-fun f40 (S18 S3) S17)
(declare-fun f41 (S19 S2) S18)
(declare-fun f42 () S19)
(declare-fun f43 () S6)
(declare-fun f44 (S20 S21) S4)
(declare-fun f45 (S22 S3) S20)
(declare-fun f46 () S22)
(declare-fun f47 (S2 S2) S21)
(declare-fun f48 () S2)
(declare-fun f49 (S23 S21) S2)
(declare-fun f50 (S24 S8) S23)
(declare-fun f51 () S24)
(declare-fun f52 (S25 S21) S11)
(declare-fun f53 (S26 S15) S25)
(declare-fun f54 () S26)
(declare-fun f55 (S27 S11) S12)
(declare-fun f56 () S27)
(declare-fun f57 (S28 S2) S13)
(declare-fun f58 () S28)
(declare-fun f59 () S9)
(declare-fun f60 (S29 S11) S4)
(declare-fun f61 () S29)
(declare-fun f62 (S30 S11) S15)
(declare-fun f63 () S30)
(declare-fun f64 () S27)
(declare-fun f65 () S12)
(declare-fun f66 () S11)
(declare-fun f67 () S4)
(declare-fun f68 () S11)
(declare-fun f69 () S4)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))))) (let ((?v_1 (f11 (f12 f22 (f11 ?v_0 ?v0)) f23))) (= (f3 f4 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f11 ?v_0 f20))) (f11 (f12 f13 f21) ?v_1))) (f3 f24 ?v_1)))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))))) (let ((?v_1 (f11 ?v_0 ?v0))) (= (f3 f25 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f11 ?v_0 f20))) (f11 (f12 f13 f21) ?v_1))) (f3 f24 ?v_1)))))))
(assert (forall ((?v0 S2)) (= (f3 f26 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) f20))) (f11 (f12 f13 f21) ?v0))) (f3 f24 ?v0)))))
(assert (forall ((?v0 S2)) (= (f3 f27 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 f20)) (f11 (f12 f13 f21) ?v0))) (f3 f24 (f11 (f12 f22 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v0)) f23))))))
(assert (forall ((?v0 S2)) (= (f3 f28 ?v0) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 f20)) (f11 (f12 f13 f21) ?v0))) (f3 f24 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v0))))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f3 (f29 f30 ?v0) ?v1) (f3 ?v0 (f11 (f12 f22 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1)) f23)))))
(assert (forall ((?v0 S8) (?v1 S2)) (= (f11 (f31 f32 ?v0) ?v1) (f11 ?v0 (f11 (f12 f22 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1)) f23)))))
(assert (forall ((?v0 S15) (?v1 S2)) (= (f33 (f34 f35 ?v0) ?v1) (f33 ?v0 (f11 (f12 f22 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1)) f23)))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f3 (f29 f36 ?v0) ?v1) (f3 ?v0 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S2)) (= (f11 (f31 f37 ?v0) ?v1) (f11 ?v0 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1)))))
(assert (forall ((?v0 S15) (?v1 S2)) (= (f33 (f34 f38 ?v0) ?v1) (f33 ?v0 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2)) (= (f3 (f39 (f40 (f41 f42 ?v0) ?v1) ?v2) ?v3) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 ?v0)) (f11 (f12 f13 ?v2) ?v3))) (f3 ?v1 ?v3)))))
(assert (let ((?v_0 (f47 f48 f20))) (not (= (f5 (f6 f43 (f44 (f45 f46 f25) ?v_0)) (f44 (f45 f46 f4) ?v_0)) (f5 (f6 f43 (f44 (f45 f46 f28) ?v_0)) (f5 (f6 f7 (f3 (f8 f9 (f3 f10 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) f20))) f21)) (f44 (f45 f46 f27) ?v_0)))))))
(assert (let ((?v_0 (f47 f48 f20))) (= (f44 (f45 f46 f26) (f47 f48 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) f20))) (f5 (f6 f43 (f44 (f45 f46 f25) ?v_0)) (f44 (f45 f46 f4) ?v_0)))))
(assert (forall ((?v0 S8)) (let ((?v_1 (f16 f18 f19))) (let ((?v_0 (f16 f17 ?v_1))) (= (f49 (f50 f51 ?v0) (f47 f48 (f14 f15 (f16 f17 ?v_0)))) (f11 (f12 f22 (f11 (f12 f22 (f11 (f12 f22 (f11 ?v0 f48)) (f11 ?v0 f23))) (f11 ?v0 (f14 f15 ?v_0)))) (f11 ?v0 (f14 f15 (f16 f18 ?v_1)))))))))
(assert (forall ((?v0 S3)) (let ((?v_1 (f16 f18 f19))) (let ((?v_0 (f16 f17 ?v_1))) (= (f44 (f45 f46 ?v0) (f47 f48 (f14 f15 (f16 f17 ?v_0)))) (f5 (f6 f43 (f5 (f6 f43 (f5 (f6 f43 (f3 ?v0 f48)) (f3 ?v0 f23))) (f3 ?v0 (f14 f15 ?v_0)))) (f3 ?v0 (f14 f15 (f16 f18 ?v_1)))))))))
(assert (forall ((?v0 S15)) (let ((?v_1 (f16 f18 f19))) (let ((?v_0 (f16 f17 ?v_1))) (= (f52 (f53 f54 ?v0) (f47 f48 (f14 f15 (f16 f17 ?v_0)))) (f16 (f55 f56 (f16 (f55 f56 (f16 (f55 f56 (f33 ?v0 f48)) (f33 ?v0 f23))) (f33 ?v0 (f14 f15 ?v_0)))) (f33 ?v0 (f14 f15 (f16 f18 ?v_1)))))))))
(assert (forall ((?v0 S8) (?v1 S2)) (let ((?v_0 (f47 f48 ?v1))) (= (f49 (f50 f51 ?v0) (f47 f48 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1))) (f11 (f12 f22 (f49 (f50 f51 (f31 f37 ?v0)) ?v_0)) (f49 (f50 f51 (f31 f32 ?v0)) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S2)) (let ((?v_0 (f47 f48 ?v1))) (= (f44 (f45 f46 ?v0) (f47 f48 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1))) (f5 (f6 f43 (f44 (f45 f46 (f29 f36 ?v0)) ?v_0)) (f44 (f45 f46 (f29 f30 ?v0)) ?v_0))))))
(assert (forall ((?v0 S15) (?v1 S2)) (let ((?v_0 (f47 f48 ?v1))) (= (f52 (f53 f54 ?v0) (f47 f48 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1))) (f16 (f55 f56 (f52 (f53 f54 (f34 f38 ?v0)) ?v_0)) (f52 (f53 f54 (f34 f35 ?v0)) ?v_0))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19))))) (?v_1 (f12 f13 ?v1))) (= (f3 (f8 f9 (f3 f10 (f11 ?v_0 ?v0))) (f11 ?v_1 (f11 ?v_0 ?v2))) (f3 (f8 f9 (f3 f10 ?v0)) (f11 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (f3 (f29 (f57 f58 ?v0) ?v1) ?v2) (f44 (f45 f46 (f39 (f40 (f41 f42 ?v0) ?v1) ?v2)) (f47 f48 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f14 f15 (f16 f17 (f16 f18 f19))))) (= (f11 (f12 f59 (f11 (f12 f22 ?v0) ?v1)) ?v_0) (f11 (f12 f22 (f11 (f12 f22 (f11 (f12 f59 ?v0) ?v_0)) (f11 (f12 f59 ?v1) ?v_0))) (f11 (f12 f13 (f11 (f12 f13 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_1 (f16 f17 (f16 f18 f19)))) (let ((?v_0 (f14 f15 ?v_1))) (= (f3 (f8 f9 (f5 (f6 f43 ?v0) ?v1)) ?v_0) (f5 (f6 f43 (f5 (f6 f43 (f3 (f8 f9 ?v0) ?v_0)) (f3 (f8 f9 ?v1) ?v_0))) (f5 (f6 f7 (f5 (f6 f7 (f60 f61 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_1 (f16 f17 (f16 f18 f19)))) (let ((?v_0 (f14 f15 ?v_1))) (= (f33 (f62 f63 (f16 (f55 f56 ?v0) ?v1)) ?v_0) (f16 (f55 f56 (f16 (f55 f56 (f33 (f62 f63 ?v0) ?v_0)) (f33 (f62 f63 ?v1) ?v_0))) (f16 (f55 f64 (f16 (f55 f64 (f16 f65 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (let ((?v_1 (f3 ?v_0 ?v1))) (= (f3 ?v_0 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1)) (f5 (f6 f7 ?v_1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f12 f59 ?v0))) (let ((?v_1 (f11 ?v_0 ?v1))) (= (f11 ?v_0 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1)) (f11 (f12 f13 ?v_1) ?v_1))))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_0 (f62 f63 ?v0))) (let ((?v_1 (f33 ?v_0 ?v1))) (= (f33 ?v_0 (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v1)) (f16 (f55 f64 ?v_1) ?v_1))))))
(assert (forall ((?v0 S11)) (let ((?v_0 (f60 f61 ?v0))) (= (f3 (f8 f9 ?v_0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f5 (f6 f7 ?v_0) ?v_0)))))
(assert (forall ((?v0 S11)) (let ((?v_0 (f14 f15 ?v0))) (= (f11 (f12 f59 ?v_0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f11 (f12 f13 ?v_0) ?v_0)))))
(assert (forall ((?v0 S11)) (let ((?v_0 (f16 f65 ?v0))) (= (f33 (f62 f63 ?v_0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f16 (f55 f64 ?v_0) ?v_0)))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f14 f15 (f16 f17 (f16 f18 f19))))) (= (= (f16 (f55 f56 (f33 (f62 f63 ?v0) ?v_0)) (f33 (f62 f63 ?v1) ?v_0)) f66) (and (= ?v0 f66) (= ?v1 f66))))))
(assert (= (f11 (f12 f22 f23) f23) (f14 f15 (f16 f17 (f16 f18 f19)))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f13 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f11 (f12 f22 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v0) (f11 (f12 f22 ?v0) ?v0))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_1 (f14 f15 (f16 f17 (f16 f18 f19)))) (?v_0 (f8 f9 ?v0))) (= (f3 ?v_0 (f11 (f12 f13 ?v_1) ?v1)) (f3 (f8 f9 (f3 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S11) (?v1 S2)) (let ((?v_1 (f14 f15 (f16 f17 (f16 f18 f19)))) (?v_0 (f62 f63 ?v0))) (= (f33 ?v_0 (f11 (f12 f13 ?v_1) ?v1)) (f33 (f62 f63 (f33 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f14 f15 (f16 f17 (f16 f18 f19)))) (?v_0 (f12 f59 ?v0))) (= (f11 ?v_0 (f11 (f12 f13 ?v_1) ?v1)) (f11 (f12 f59 (f11 ?v_0 ?v1)) ?v_1)))))
(assert (= (f3 (f8 f9 f67) (f14 f15 (f16 f17 (f16 f18 f19)))) f67))
(assert (= (f33 (f62 f63 f68) (f14 f15 (f16 f17 (f16 f18 f19)))) f68))
(assert (= (f11 (f12 f59 f23) (f14 f15 (f16 f17 (f16 f18 f19)))) f23))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 ?v0) ?v0) (f3 (f8 f9 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f13 ?v0) ?v0) (f11 (f12 f59 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))))))
(assert (forall ((?v0 S11)) (= (f16 (f55 f64 ?v0) ?v0) (f33 (f62 f63 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))))))
(assert (forall ((?v0 S4)) (= (f3 (f8 f9 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f5 (f6 f7 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f11 (f12 f59 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f11 (f12 f13 ?v0) ?v0))))
(assert (forall ((?v0 S11)) (= (f33 (f62 f63 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f16 (f55 f64 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (not (= (f3 f10 ?v0) f69))))
(assert (= (f3 f10 f48) f67))
(assert (= (f3 f10 f23) f67))
(assert (forall ((?v0 S2)) (= (f3 (f8 f9 (f3 f10 ?v0)) ?v0) f67)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (f11 (f12 f13 (f11 ?v_0 ?v1)) (f11 (f12 f13 ?v2) ?v3)) (f11 (f12 f13 (f11 ?v_0 ?v2)) (f11 (f12 f13 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) (f5 (f6 f7 ?v2) ?v3)) (f5 (f6 f7 (f5 ?v_0 ?v2)) (f5 (f6 f7 ?v1) ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f55 f64 ?v0))) (= (f16 (f55 f64 (f16 ?v_0 ?v1)) (f16 (f55 f64 ?v2) ?v3)) (f16 (f55 f64 (f16 ?v_0 ?v2)) (f16 (f55 f64 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_1 (f12 f13 (f11 (f12 f13 ?v0) ?v1))) (?v_0 (f12 f13 ?v2))) (= (f11 ?v_1 (f11 ?v_0 ?v3)) (f11 ?v_0 (f11 ?v_1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_1 (f6 f7 (f5 (f6 f7 ?v0) ?v1))) (?v_0 (f6 f7 ?v2))) (= (f5 ?v_1 (f5 ?v_0 ?v3)) (f5 ?v_0 (f5 ?v_1 ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_1 (f55 f64 (f16 (f55 f64 ?v0) ?v1))) (?v_0 (f55 f64 ?v2))) (= (f16 ?v_1 (f16 ?v_0 ?v3)) (f16 ?v_0 (f16 ?v_1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f12 f13 ?v0)) (?v_1 (f11 (f12 f13 ?v2) ?v3))) (= (f11 (f12 f13 (f11 ?v_0 ?v1)) ?v_1) (f11 ?v_0 (f11 (f12 f13 ?v1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f7 ?v0)) (?v_1 (f5 (f6 f7 ?v2) ?v3))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v_1) (f5 ?v_0 (f5 (f6 f7 ?v1) ?v_1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f55 f64 ?v0)) (?v_1 (f16 (f55 f64 ?v2) ?v3))) (= (f16 (f55 f64 (f16 ?v_0 ?v1)) ?v_1) (f16 ?v_0 (f16 (f55 f64 ?v1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (f11 (f12 f13 (f11 ?v_0 ?v1)) ?v2) (f11 (f12 f13 (f11 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2) (f5 (f6 f7 (f5 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f55 f64 ?v0))) (= (f16 (f55 f64 (f16 ?v_0 ?v1)) ?v2) (f16 (f55 f64 (f16 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (f11 (f12 f13 (f11 ?v_0 ?v1)) ?v2) (f11 ?v_0 (f11 (f12 f13 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f55 f64 ?v0))) (= (f16 (f55 f64 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f55 f64 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (f11 ?v_0 (f11 (f12 f13 ?v1) ?v2)) (f11 (f12 f13 (f11 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f55 f64 ?v0))) (= (f16 ?v_0 (f16 (f55 f64 ?v1) ?v2)) (f16 (f55 f64 (f16 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f12 f13 ?v0)) (?v_0 (f12 f13 ?v1))) (= (f11 ?v_1 (f11 ?v_0 ?v2)) (f11 ?v_0 (f11 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f6 f7 ?v0)) (?v_0 (f6 f7 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_1 (f55 f64 ?v0)) (?v_0 (f55 f64 ?v1))) (= (f16 ?v_1 (f16 ?v_0 ?v2)) (f16 ?v_0 (f16 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f11 (f12 f13 ?v0) ?v1) (f11 (f12 f13 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f5 (f6 f7 ?v0) ?v1) (f5 (f6 f7 ?v1) ?v0))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f16 (f55 f64 ?v0) ?v1) (f16 (f55 f64 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f12 f22 ?v0))) (= (f11 (f12 f22 (f11 ?v_0 ?v1)) (f11 (f12 f22 ?v2) ?v3)) (f11 (f12 f22 (f11 ?v_0 ?v2)) (f11 (f12 f22 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f6 f43 ?v0))) (= (f5 (f6 f43 (f5 ?v_0 ?v1)) (f5 (f6 f43 ?v2) ?v3)) (f5 (f6 f43 (f5 ?v_0 ?v2)) (f5 (f6 f43 ?v1) ?v3))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f55 f56 ?v0))) (= (f16 (f55 f56 (f16 ?v_0 ?v1)) (f16 (f55 f56 ?v2) ?v3)) (f16 (f55 f56 (f16 ?v_0 ?v2)) (f16 (f55 f56 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f22 ?v0))) (= (f11 (f12 f22 (f11 ?v_0 ?v1)) ?v2) (f11 (f12 f22 (f11 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f43 ?v0))) (= (f5 (f6 f43 (f5 ?v_0 ?v1)) ?v2) (f5 (f6 f43 (f5 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f55 f56 ?v0))) (= (f16 (f55 f56 (f16 ?v_0 ?v1)) ?v2) (f16 (f55 f56 (f16 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f22 ?v0))) (= (f11 (f12 f22 (f11 ?v_0 ?v1)) ?v2) (f11 ?v_0 (f11 (f12 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f43 ?v0))) (= (f5 (f6 f43 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f43 ?v1) ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f55 f56 ?v0))) (= (f16 (f55 f56 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f55 f56 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f22 ?v0))) (= (f11 ?v_0 (f11 (f12 f22 ?v1) ?v2)) (f11 (f12 f22 (f11 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f43 ?v0))) (= (f5 ?v_0 (f5 (f6 f43 ?v1) ?v2)) (f5 (f6 f43 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f55 f56 ?v0))) (= (f16 ?v_0 (f16 (f55 f56 ?v1) ?v2)) (f16 (f55 f56 (f16 ?v_0 ?v1)) ?v2)))))
(check-sat)
(exit)