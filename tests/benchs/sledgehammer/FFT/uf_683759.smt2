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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 (S5 S2) S2)
(declare-fun f5 (S6 S2) S5)
(declare-fun f6 () S6)
(declare-fun f7 (S7 S4) S4)
(declare-fun f8 (S8 S4) S7)
(declare-fun f9 () S8)
(declare-fun f10 (S9 S3) S10)
(declare-fun f11 (S11 S9) S9)
(declare-fun f12 (S12 S9) S11)
(declare-fun f13 () S12)
(declare-fun f14 (S13 S10) S10)
(declare-fun f15 (S14 S10) S13)
(declare-fun f16 () S14)
(declare-fun f17 (S15 S4) S2)
(declare-fun f18 (S16 S2) S15)
(declare-fun f19 () S16)
(declare-fun f20 () S8)
(declare-fun f21 (S17 S10) S9)
(declare-fun f22 (S18 S9) S17)
(declare-fun f23 () S18)
(declare-fun f24 () S14)
(declare-fun f25 () S2)
(declare-fun f26 () S4)
(declare-fun f27 () S9)
(declare-fun f28 () S10)
(declare-fun f29 () S15)
(declare-fun f30 () S4)
(declare-fun f31 () S2)
(declare-fun f32 () S3)
(declare-fun f33 () S3)
(declare-fun f34 (S19 S3) S1)
(declare-fun f35 (S3) S19)
(declare-fun f36 () S10)
(declare-fun f37 () S17)
(declare-fun f38 (S20 S3) S3)
(declare-fun f39 (S21 S3) S20)
(declare-fun f40 () S21)
(declare-fun f41 () S3)
(declare-fun f42 (S22 S3) S23)
(declare-fun f43 (S24 S23) S22)
(declare-fun f44 () S24)
(declare-fun f45 () S23)
(declare-fun f46 (S25 S23) S23)
(declare-fun f47 (S26 S23) S25)
(declare-fun f48 () S26)
(declare-fun f49 () S3)
(declare-fun f50 (S27 S19) S4)
(declare-fun f51 (S28 S2) S27)
(declare-fun f52 () S28)
(declare-fun f53 (S29 S3) S19)
(declare-fun f54 (S3) S29)
(declare-fun f55 (S10 S10) S1)
(declare-fun f56 (S23 S23) S1)
(declare-fun f57 () S23)
(declare-fun f58 (S30 S19) S10)
(declare-fun f59 (S31 S9) S30)
(declare-fun f60 () S31)
(declare-fun f61 (S3 S19) S1)
(declare-fun f62 () S21)
(declare-fun f63 (S10 S10) S32)
(declare-fun f64 (S23 S23) S33)
(declare-fun f65 (S3) S19)
(declare-fun f66 (S23 S23) S1)
(declare-fun f67 (S10 S10) S1)
(declare-fun f68 () S21)
(declare-fun f69 (S19 S19) S1)
(declare-fun f70 (S32 S32) S1)
(declare-fun f71 (S33 S33) S1)
(declare-fun f72 () S14)
(declare-fun f73 () S26)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (f3 (f4 (f5 f6 ?v0) ?v1) ?v2) (f7 (f8 f9 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S3)) (= (f10 (f11 (f12 f13 ?v0) ?v1) ?v2) (f14 (f15 f16 (f10 ?v0 ?v2)) (f10 ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S3)) (= (f3 (f17 (f18 f19 ?v0) ?v1) ?v2) (f7 (f8 f20 (f3 ?v0 ?v2)) ?v1))))
(assert (forall ((?v0 S9) (?v1 S10) (?v2 S3)) (= (f10 (f21 (f22 f23 ?v0) ?v1) ?v2) (f14 (f15 f24 (f10 ?v0 ?v2)) ?v1))))
(assert (forall ((?v0 S3)) (= (f3 f25 ?v0) f26)))
(assert (forall ((?v0 S3)) (= (f10 f27 ?v0) f28)))
(assert (let ((?v_1 (f17 f29 (f7 (f8 f20 f30) (f3 f31 f32))))) (let ((?v_0 (f3 ?v_1 f33))) (let ((?v_2 (f7 (f8 f9 ?v_0) f30))) (not (= (f7 (f8 f20 (f7 (f8 f9 (f3 (f17 f29 ?v_0) f32)) f30)) ?v_2) (f7 (f8 f20 (f7 (f8 f9 (f3 (f17 f29 (f3 ?v_1 f32)) f33)) f30)) ?v_2)))))))
(assert (= (f34 (f35 f33) f32) f1))
(assert (forall ((?v0 S3)) (= (f3 (f17 f29 (f3 f31 ?v0)) ?v0) f30)))
(assert (forall ((?v0 S10) (?v1 S3)) (let ((?v_0 (f15 f24 f36))) (= (f14 ?v_0 (f10 (f21 f37 ?v0) ?v1)) (f10 (f21 f37 (f14 ?v_0 ?v0)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f8 f20 f30))) (= (f7 ?v_0 (f3 (f17 f29 ?v0) ?v1)) (f3 (f17 f29 (f7 ?v_0 ?v0)) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S3)) (= (f10 (f21 f37 (f14 (f15 f24 ?v0) ?v1)) ?v2) (f14 (f15 f24 (f10 (f21 f37 ?v0) ?v2)) (f10 (f21 f37 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (= (f3 (f17 f29 (f7 (f8 f20 ?v0) ?v1)) ?v2) (f7 (f8 f20 (f3 (f17 f29 ?v0) ?v2)) (f3 (f17 f29 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (f14 (f15 f24 (f14 (f15 f16 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f14 (f15 f24 ?v0) ?v2)) (f14 (f15 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f7 (f8 f20 (f7 (f8 f9 ?v0) ?v1)) ?v2) (f7 (f8 f9 (f7 (f8 f20 ?v0) ?v2)) (f7 (f8 f20 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (f14 (f15 f24 (f14 (f15 f16 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f14 (f15 f24 ?v0) ?v2)) (f14 (f15 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f7 (f8 f20 (f7 (f8 f9 ?v0) ?v1)) ?v2) (f7 (f8 f9 (f7 (f8 f20 ?v0) ?v2)) (f7 (f8 f20 ?v1) ?v2)))))
(assert (forall ((?v0 S10)) (= (f14 (f15 f24 ?v0) f36) ?v0)))
(assert (forall ((?v0 S4)) (= (f7 (f8 f20 ?v0) f30) ?v0)))
(assert (forall ((?v0 S3)) (= (f38 (f39 f40 f41) ?v0) f41)))
(assert (forall ((?v0 S3)) (= (f10 (f21 f37 f36) ?v0) f36)))
(assert (forall ((?v0 S3)) (= (f42 (f43 f44 f45) ?v0) f45)))
(assert (forall ((?v0 S3)) (= (f3 (f17 f29 f30) ?v0) f30)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f14 (f15 f16 ?v0) ?v1) (f14 (f15 f16 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (=> (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23) (?v3 S23)) (=> (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 f48 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S3)) (= (= f41 ?v0) (= ?v0 f41))))
(assert (forall ((?v0 S10)) (= (= f36 ?v0) (= ?v0 f36))))
(assert (forall ((?v0 S23)) (= (= f45 ?v0) (= ?v0 f45))))
(assert (forall ((?v0 S4)) (= (= f30 ?v0) (= ?v0 f30))))
(assert (= (f34 (f35 f49) f33) f1))
(assert (let ((?v_1 (f3 (f17 f29 (f7 (f8 f20 f30) (f3 f31 f32))) f33))) (let ((?v_0 (f17 f29 ?v_1))) (= (f50 (f51 f52 ?v_0) (f53 (f54 f49) f32)) (f7 (f8 f20 (f7 (f8 f9 (f3 ?v_0 f32)) f30)) (f7 (f8 f9 ?v_1) f30))))))
(assert (not (= (f34 (f35 f41) f49) f1)))
(assert (not (= (f55 f36 f28) f1)))
(assert (not (= (f56 f45 f57) f1)))
(assert (= (f34 (f35 f49) f41) f1))
(assert (= (f55 f28 f36) f1))
(assert (= (f56 f57 f45) f1))
(assert (forall ((?v0 S4)) (= (= f26 ?v0) (= ?v0 f26))))
(assert (forall ((?v0 S3)) (= (= f49 ?v0) (= ?v0 f49))))
(assert (forall ((?v0 S23)) (= (= f57 ?v0) (= ?v0 f57))))
(assert (forall ((?v0 S10)) (= (= f28 ?v0) (= ?v0 f28))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f35 f49))) (= (= (f34 ?v_0 (f38 (f39 f40 ?v0) ?v1)) f1) (or (= (f34 ?v_0 ?v0) f1) (= ?v1 f49))))))
(assert (forall ((?v0 S23) (?v1 S23)) (= (= (f56 ?v0 ?v1) f1) (= (f56 (f46 (f47 f48 ?v0) ?v1) f57) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f55 ?v0 ?v1) f1) (= (f55 (f14 (f15 f16 ?v0) ?v1) f28) f1))))
(assert (forall ((?v0 S4) (?v1 S3)) (= (= (f3 (f17 f29 ?v0) ?v1) f26) (and (= ?v0 f26) (not (= ?v1 f49))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f38 (f39 f40 ?v0) ?v1) f49) (and (= ?v0 f49) (not (= ?v1 f49))))))
(assert (forall ((?v0 S23) (?v1 S3)) (= (= (f42 (f43 f44 ?v0) ?v1) f57) (and (= ?v0 f57) (not (= ?v1 f49))))))
(assert (forall ((?v0 S10) (?v1 S3)) (= (= (f10 (f21 f37 ?v0) ?v1) f28) (and (= ?v0 f28) (not (= ?v1 f49))))))
(assert (forall ((?v0 S9) (?v1 S19) (?v2 S10)) (= (f14 (f15 f24 (f58 (f59 f60 ?v0) ?v1)) ?v2) (f58 (f59 f60 (f21 (f22 f23 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S19) (?v2 S4)) (= (f7 (f8 f20 (f50 (f51 f52 ?v0) ?v1)) ?v2) (f50 (f51 f52 (f17 (f18 f19 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f55 ?v0 ?v1) f1) false) (=> (=> (= (f55 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S23) (?v1 S23)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f56 ?v0 ?v1) f1) false) (=> (=> (= (f56 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f35 f49))) (=> (= (f34 ?v_0 ?v0) f1) (= (f34 ?v_0 (f38 (f39 f40 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S23) (?v1 S3)) (=> (= (f56 f57 ?v0) f1) (= (f56 f57 (f42 (f43 f44 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S10) (?v1 S3)) (=> (= (f55 f28 ?v0) f1) (= (f55 f28 (f10 (f21 f37 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f40 ?v0))) (=> (= (f34 (f35 f49) ?v0) f1) (=> (= (f34 (f35 (f38 ?v_0 ?v1)) (f38 ?v_0 ?v2)) f1) (= (f34 (f35 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f40 ?v2))) (=> (= (f34 (f35 ?v0) ?v1) f1) (=> (= (f34 (f35 f49) ?v2) f1) (=> (= (f34 (f35 ?v2) f41) f1) (= (f34 (f35 (f38 ?v_0 ?v1)) (f38 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (let ((?v_0 (f21 f37 ?v2))) (=> (= (f34 (f35 ?v0) ?v1) f1) (=> (= (f55 f28 ?v2) f1) (=> (= (f55 ?v2 f36) f1) (= (f55 (f10 ?v_0 ?v1) (f10 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S23)) (let ((?v_0 (f43 f44 ?v2))) (=> (= (f34 (f35 ?v0) ?v1) f1) (=> (= (f56 f57 ?v2) f1) (=> (= (f56 ?v2 f45) f1) (= (f56 (f42 ?v_0 ?v1) (f42 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f35 f41))) (=> (= (f34 ?v_0 ?v0) f1) (=> (= (f34 (f35 f49) ?v1) f1) (= (f34 ?v_0 (f38 (f39 f40 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S10) (?v1 S3)) (=> (= (f55 f36 ?v0) f1) (=> (= (f34 (f35 f49) ?v1) f1) (= (f55 f36 (f10 (f21 f37 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S23) (?v1 S3)) (=> (= (f56 f45 ?v0) f1) (=> (= (f34 (f35 f49) ?v1) f1) (= (f56 f45 (f42 (f43 f44 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f14 (f15 f16 ?v0) ?v1) (f14 (f15 f16 ?v2) ?v3)) (= (= (f55 ?v0 ?v1) f1) (= (f55 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23) (?v3 S23)) (=> (= (f46 (f47 f48 ?v0) ?v1) (f46 (f47 f48 ?v2) ?v3)) (= (= (f56 ?v0 ?v1) f1) (= (f56 ?v2 ?v3) f1)))))
(assert (not (= f49 f41)))
(assert (not (= f28 f36)))
(assert (not (= f57 f45)))
(assert (not (= f26 f30)))
(assert (not (= f41 f49)))
(assert (not (= f36 f28)))
(assert (not (= f45 f57)))
(assert (not (= f30 f26)))
(assert (forall ((?v0 S10)) (= (f10 (f21 f37 ?v0) f41) ?v0)))
(assert (forall ((?v0 S3)) (= (f38 (f39 f40 ?v0) f41) ?v0)))
(assert (forall ((?v0 S4)) (= (f3 (f17 f29 ?v0) f41) ?v0)))
(assert (forall ((?v0 S23)) (= (f42 (f43 f44 ?v0) f41) ?v0)))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f7 (f8 f9 ?v0) ?v1) f26) (= ?v0 ?v1))))
(assert (forall ((?v0 S23) (?v1 S23)) (= (= (f46 (f47 f48 ?v0) ?v1) f57) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f14 (f15 f16 ?v0) ?v1) f28) (= ?v0 ?v1))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= ?v0 ?v1) (= (f7 (f8 f9 ?v0) ?v1) f26))))
(assert (forall ((?v0 S23) (?v1 S23)) (= (= ?v0 ?v1) (= (f46 (f47 f48 ?v0) ?v1) f57))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= ?v0 ?v1) (= (f14 (f15 f16 ?v0) ?v1) f28))))
(assert (forall ((?v0 S4)) (= (f7 (f8 f9 ?v0) ?v0) f26)))
(assert (forall ((?v0 S23)) (= (f46 (f47 f48 ?v0) ?v0) f57)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f16 ?v0) ?v0) f28)))
(assert (forall ((?v0 S4)) (= (f7 (f8 f9 ?v0) f26) ?v0)))
(assert (forall ((?v0 S23)) (= (f46 (f47 f48 ?v0) f57) ?v0)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f16 ?v0) f28) ?v0)))
(assert (forall ((?v0 S4) (?v1 S3)) (=> (not (= ?v0 f26)) (not (= (f3 (f17 f29 ?v0) ?v1) f26)))))
(assert (forall ((?v0 S23) (?v1 S3)) (=> (not (= ?v0 f57)) (not (= (f42 (f43 f44 ?v0) ?v1) f57)))))
(assert (forall ((?v0 S10) (?v1 S3)) (=> (not (= ?v0 f28)) (not (= (f10 (f21 f37 ?v0) ?v1) f28)))))
(assert (forall ((?v0 S4)) (= (f7 (f8 f20 ?v0) f26) f26)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f24 ?v0) f28) f28)))
(assert (forall ((?v0 S4)) (= (f7 (f8 f20 f26) ?v0) f26)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f24 f28) ?v0) f28)))
(assert (forall ((?v0 S4)) (= (f7 (f8 f20 f26) ?v0) f26)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f24 f28) ?v0) f28)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f40 ?v2))) (=> (= (f34 (f35 ?v0) ?v1) f1) (=> (= (f34 (f35 f41) ?v2) f1) (= (f34 (f35 (f38 ?v_0 ?v0)) (f38 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (let ((?v_0 (f21 f37 ?v2))) (=> (= (f34 (f35 ?v0) ?v1) f1) (=> (= (f55 f36 ?v2) f1) (= (f55 (f10 ?v_0 ?v0) (f10 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S23)) (let ((?v_0 (f43 f44 ?v2))) (=> (= (f34 (f35 ?v0) ?v1) f1) (=> (= (f56 f45 ?v2) f1) (= (f56 (f42 ?v_0 ?v0) (f42 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f40 ?v0))) (=> (= (f34 (f35 f41) ?v0) f1) (=> (= (f34 (f35 (f38 ?v_0 ?v1)) (f38 ?v_0 ?v2)) f1) (= (f34 (f35 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S3) (?v2 S3)) (let ((?v_0 (f21 f37 ?v0))) (=> (= (f55 f36 ?v0) f1) (=> (= (f55 (f10 ?v_0 ?v1) (f10 ?v_0 ?v2)) f1) (= (f34 (f35 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S23) (?v1 S3) (?v2 S3)) (let ((?v_0 (f43 f44 ?v0))) (=> (= (f56 f45 ?v0) f1) (=> (= (f56 (f42 ?v_0 ?v1) (f42 ?v_0 ?v2)) f1) (= (f34 (f35 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f40 ?v0))) (=> (= (f34 (f35 f41) ?v0) f1) (= (= (f34 (f35 (f38 ?v_0 ?v1)) (f38 ?v_0 ?v2)) f1) (= (f34 (f35 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S3) (?v2 S3)) (let ((?v_0 (f21 f37 ?v0))) (=> (= (f55 f36 ?v0) f1) (= (= (f55 (f10 ?v_0 ?v1) (f10 ?v_0 ?v2)) f1) (= (f34 (f35 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S23) (?v1 S3) (?v2 S3)) (let ((?v_0 (f43 f44 ?v0))) (=> (= (f56 f45 ?v0) f1) (= (= (f56 (f42 ?v_0 ?v1) (f42 ?v_0 ?v2)) f1) (= (f34 (f35 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3)) (= (f38 (f39 f40 f49) ?v0) (ite (= ?v0 f49) f41 f49))))
(assert (forall ((?v0 S3)) (= (f10 (f21 f37 f28) ?v0) (ite (= ?v0 f49) f36 f28))))
(assert (forall ((?v0 S3)) (= (f42 (f43 f44 f57) ?v0) (ite (= ?v0 f49) f45 f57))))
(assert (forall ((?v0 S3)) (= (f3 (f17 f29 f26) ?v0) (ite (= ?v0 f49) f30 f26))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f40 ?v0))) (=> (= (f34 (f35 f41) ?v0) f1) (= (= (f38 ?v_0 ?v1) (f38 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S3) (?v2 S3)) (let ((?v_0 (f21 f37 ?v0))) (=> (= (f55 f36 ?v0) f1) (= (= (f10 ?v_0 ?v1) (f10 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S23) (?v1 S3) (?v2 S3)) (let ((?v_0 (f43 f44 ?v0))) (=> (= (f56 f45 ?v0) f1) (= (= (f42 ?v_0 ?v1) (f42 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (not (= ?v0 f28)) (= (= (f14 (f15 f24 ?v1) ?v0) f36) (= ?v1 ?v0)))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (not (= ?v0 f26)) (= (= (f7 (f8 f20 ?v1) ?v0) f30) (= ?v1 ?v0)))))
(assert (forall ((?v0 S10)) (=> (not (= ?v0 f28)) (= (f14 (f15 f24 ?v0) ?v0) f36))))
(assert (forall ((?v0 S4)) (=> (not (= ?v0 f26)) (= (f7 (f8 f20 ?v0) ?v0) f30))))
(assert (forall ((?v0 S10)) (= (f14 (f15 f24 ?v0) ?v0) (ite (= ?v0 f28) f28 f36))))
(assert (forall ((?v0 S4)) (= (f7 (f8 f20 ?v0) ?v0) (ite (= ?v0 f26) f26 f30))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (=> (not (= ?v0 f26)) (= (f3 (f17 f29 (f7 (f8 f20 ?v1) ?v0)) ?v2) (f7 (f8 f20 (f3 (f17 f29 ?v1) ?v2)) (f3 (f17 f29 ?v0) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S3)) (=> (not (= ?v0 f28)) (= (f10 (f21 f37 (f14 (f15 f24 ?v1) ?v0)) ?v2) (f14 (f15 f24 (f10 (f21 f37 ?v1) ?v2)) (f10 (f21 f37 ?v0) ?v2))))))
(assert (forall ((?v0 S3)) (= (f38 (f39 f40 ?v0) f49) f41)))
(assert (forall ((?v0 S10)) (= (f10 (f21 f37 ?v0) f49) f36)))
(assert (forall ((?v0 S23)) (= (f42 (f43 f44 ?v0) f49) f45)))
(assert (forall ((?v0 S4)) (= (f3 (f17 f29 ?v0) f49) f30)))
(assert (forall ((?v0 S10) (?v1 S3)) (let ((?v_0 (f21 f37 ?v0))) (=> (not (= ?v0 f36)) (= (f58 (f59 f60 ?v_0) (f53 (f54 f49) ?v1)) (f14 (f15 f24 (f14 (f15 f16 (f10 ?v_0 ?v1)) f36)) (f14 (f15 f16 ?v0) f36)))))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f17 f29 ?v0))) (=> (not (= ?v0 f30)) (= (f50 (f51 f52 ?v_0) (f53 (f54 f49) ?v1)) (f7 (f8 f20 (f7 (f8 f9 (f3 ?v_0 ?v1)) f30)) (f7 (f8 f9 ?v0) f30)))))))
(assert (forall ((?v0 S3)) (=> (= (f34 (f35 ?v0) f49) f1) false)))
(assert (forall ((?v0 S3) (?v1 S19)) (= (exists ((?v2 S3)) (and (= (f34 (f35 ?v2) ?v0) f1) (= (f34 ?v1 ?v2) f1))) (exists ((?v2 S3)) (and (= (f61 ?v2 (f53 (f54 f49) ?v0)) f1) (= (f34 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S19)) (= (forall ((?v2 S3)) (=> (= (f34 (f35 ?v2) ?v0) f1) (= (f34 ?v1 ?v2) f1))) (forall ((?v2 S3)) (=> (= (f61 ?v2 (f53 (f54 f49) ?v0)) f1) (= (f34 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S3)) (= (f38 (f39 f40 ?v0) f49) f41)))
(assert (forall ((?v0 S10)) (= (f10 (f21 f37 ?v0) f49) f36)))
(assert (forall ((?v0 S23)) (= (f42 (f43 f44 ?v0) f49) f45)))
(assert (forall ((?v0 S4)) (= (f3 (f17 f29 ?v0) f49) f30)))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f55 f28 (f14 (f15 f24 ?v0) ?v1)) f1) (or (and (= (f55 f28 ?v0) f1) (= (f55 f28 ?v1) f1)) (and (= (f55 ?v0 f28) f1) (= (f55 ?v1 f28) f1))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f55 (f14 (f15 f24 ?v0) ?v1) f28) f1) (or (and (= (f55 f28 ?v0) f1) (= (f55 ?v1 f28) f1)) (and (= (f55 ?v0 f28) f1) (= (f55 f28 ?v1) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (= (f55 (f14 (f15 f24 ?v0) ?v1) (f14 (f15 f24 ?v2) ?v1)) f1) (and (=> (= (f55 f28 ?v1) f1) (= (f55 ?v0 ?v2) f1)) (and (=> (= (f55 ?v1 f28) f1) (= (f55 ?v2 ?v0) f1)) (not (= ?v1 f28)))))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f55 f28 ?v0) f1) (=> (= (f55 f28 ?v1) f1) (= (f55 f28 (f14 (f15 f24 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f55 f28 ?v0) f1) (=> (= (f55 ?v1 f28) f1) (= (f55 (f14 (f15 f24 ?v0) ?v1) f28) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f55 ?v0 f28) f1) (=> (= (f55 f28 ?v1) f1) (= (f55 (f14 (f15 f24 ?v0) ?v1) f28) f1)))))
(assert (forall ((?v0 S3)) (not (= (f3 f31 ?v0) f26))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f38 (f39 f62 ?v0) ?v1) f49) (=> (= (f38 (f39 f62 ?v1) ?v0) f49) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3)) (= (f38 (f39 f62 ?v0) ?v0) f49)))
(assert (forall ((?v0 S3)) (= (f38 (f39 f62 ?v0) f49) ?v0)))
(assert (forall ((?v0 S3)) (= (f38 (f39 f62 f49) ?v0) f49)))
(assert (forall ((?v0 S10)) (= (f10 (f21 f37 ?v0) f41) ?v0)))
(assert (forall ((?v0 S3)) (= (f38 (f39 f40 ?v0) f41) ?v0)))
(assert (forall ((?v0 S4)) (= (f3 (f17 f29 ?v0) f41) ?v0)))
(assert (forall ((?v0 S23)) (= (f42 (f43 f44 ?v0) f41) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S29)) (let ((?v_0 (= (f34 (f53 ?v2 ?v1) ?v0) f1))) (=> (=> (= (f34 (f35 ?v0) ?v1) f1) ?v_0) (=> (=> (= ?v0 ?v1) ?v_0) (=> (=> (= (f34 (f35 ?v1) ?v0) f1) ?v_0) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f35 ?v0)) (?v_1 (f39 f62 ?v2))) (=> (= (f34 ?v_0 ?v1) f1) (=> (= (f34 ?v_0 ?v2) f1) (= (f34 (f35 (f38 ?v_1 ?v1)) (f38 ?v_1 ?v0)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f34 (f35 ?v0) ?v1) f1) (= (f34 (f35 (f38 (f39 f62 ?v0) ?v2)) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f34 (f35 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f34 (f35 ?v0) ?v1) f1) (not (= ?v1 ?v0)))))
(assert (forall ((?v0 S3)) (=> (= (f34 (f35 ?v0) ?v0) f1) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f34 (f35 ?v0) ?v1) f1) false) (=> (=> (= (f34 (f35 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (not (= ?v0 ?v1)) (or (= (f34 (f35 ?v0) ?v1) f1) (= (f34 (f35 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (not (= (f34 (f35 ?v0) ?v0) f1))))
(assert (forall ((?v0 S3)) (=> (=> (= ?v0 f49) false) (= (f34 (f35 f49) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f34 (f35 ?v0) ?v1) f1) (not (= ?v1 f49)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f35 f49))) (=> (= (f34 ?v_0 ?v0) f1) (=> (= (f34 ?v_0 ?v1) f1) (= (f34 (f35 (f38 (f39 f62 ?v1) ?v0)) ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (= (f34 (f35 ?v0) f49) f1) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f34 (f35 f49) (f38 (f39 f62 ?v0) ?v1)) f1) (= (f34 (f35 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f49)) (= (f34 (f35 f49) ?v0) f1))))
(assert (forall ((?v0 S3)) (not (= (f34 (f35 ?v0) f49) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f53 (f54 ?v0) ?v1) (f53 (f54 ?v2) ?v3)) (=> (= (f34 (f35 ?v0) ?v1) f1) (=> (= (f34 (f35 ?v2) ?v3) f1) (= ?v1 ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f63 ?v0 ?v1) (f63 ?v2 ?v3)) (=> (= (f55 ?v0 ?v1) f1) (=> (= (f55 ?v2 ?v3) f1) (= ?v1 ?v3))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23) (?v3 S23)) (=> (= (f64 ?v0 ?v1) (f64 ?v2 ?v3)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f56 ?v2 ?v3) f1) (= ?v1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f53 (f54 ?v0) ?v1) (f53 (f54 ?v2) ?v3)) (=> (= (f34 (f35 ?v0) ?v1) f1) (=> (= (f34 (f35 ?v2) ?v3) f1) (= ?v0 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f63 ?v0 ?v1) (f63 ?v2 ?v3)) (=> (= (f55 ?v0 ?v1) f1) (=> (= (f55 ?v2 ?v3) f1) (= ?v0 ?v2))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23) (?v3 S23)) (=> (= (f64 ?v0 ?v1) (f64 ?v2 ?v3)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f56 ?v2 ?v3) f1) (= ?v0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f34 (f35 ?v0) ?v1) f1) (=> (= (f34 (f35 ?v2) ?v3) f1) (= (= (f53 (f54 ?v0) ?v1) (f53 (f54 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f55 ?v0 ?v1) f1) (=> (= (f55 ?v2 ?v3) f1) (= (= (f63 ?v0 ?v1) (f63 ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23) (?v3 S23)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f56 ?v2 ?v3) f1) (= (= (f64 ?v0 ?v1) (f64 ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f34 (f35 f49) ?v0) f1) (=> (= (f34 (f35 ?v0) ?v1) f1) (= (f50 (f51 f52 (f17 f29 (f3 (f17 f29 (f3 f31 ?v1)) ?v0))) (f53 (f54 f49) ?v1)) f26)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f55 ?v0 ?v1) f1) (=> (= (f55 ?v2 f28) f1) (= (f55 (f14 (f15 f24 ?v1) ?v2) (f14 (f15 f24 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f55 ?v0 ?v1) f1) (=> (= (f55 f28 ?v2) f1) (= (f55 (f14 (f15 f24 ?v0) ?v2) (f14 (f15 f24 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f55 ?v0 f28) f1) (=> (= (f55 ?v1 f28) f1) (= (f55 f28 (f14 (f15 f24 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f35 f49))) (= (= (f34 ?v_0 (f38 (f39 f40 ?v0) ?v1)) f1) (or (= ?v1 f49) (= (f34 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S10) (?v1 S3)) (let ((?v_0 (f21 f37 ?v0))) (=> (not (= ?v0 f36)) (= (f58 (f59 f60 ?v_0) (f53 (f54 f49) ?v1)) (f14 (f15 f24 (f14 (f15 f16 (f10 ?v_0 ?v1)) f36)) (f14 (f15 f16 ?v0) f36)))))))
(assert (forall ((?v0 S9) (?v1 S19) (?v2 S10)) (= (f14 (f15 f24 (f58 (f59 f60 ?v0) ?v1)) ?v2) (f58 (f59 f60 (f21 (f22 f23 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S19) (?v2 S4)) (= (f7 (f8 f20 (f50 (f51 f52 ?v0) ?v1)) ?v2) (f50 (f51 f52 (f17 (f18 f19 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S19)) (= (f58 (f59 f60 (f11 (f12 f13 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f58 (f59 f60 ?v0) ?v2)) (f58 (f59 f60 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S19)) (= (f50 (f51 f52 (f4 (f5 f6 ?v0) ?v1)) ?v2) (f7 (f8 f9 (f50 (f51 f52 ?v0) ?v2)) (f50 (f51 f52 ?v1) ?v2)))))
(assert (forall ((?v0 S19)) (= (f58 (f59 f60 f27) ?v0) f28)))
(assert (forall ((?v0 S19)) (= (f50 (f51 f52 f25) ?v0) f26)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f34 (f35 ?v0) ?v1) f1) (=> (= (f34 (f65 f49) ?v0) f1) (=> (= (f34 (f35 f49) ?v2) f1) (= (f34 (f35 (f38 (f39 f40 ?v0) ?v2)) (f38 (f39 f40 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S3)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f66 f57 ?v0) f1) (=> (= (f34 (f35 f49) ?v2) f1) (= (f56 (f42 (f43 f44 ?v0) ?v2) (f42 (f43 f44 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S3)) (=> (= (f55 ?v0 ?v1) f1) (=> (= (f67 f28 ?v0) f1) (=> (= (f34 (f35 f49) ?v2) f1) (= (f55 (f10 (f21 f37 ?v0) ?v2) (f10 (f21 f37 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f68 ?v0))) (=> (= (f34 (f35 f49) ?v0) f1) (= (f3 (f17 f29 (f3 f31 (f38 ?v_0 ?v1))) (f38 ?v_0 ?v2)) (f3 (f17 f29 (f3 f31 ?v1)) ?v2))))))
(assert (forall ((?v0 S3)) (= (f34 (f65 f49) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f34 (f65 (f38 (f39 f62 ?v0) ?v1)) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f68 ?v0))) (= (f38 ?v_0 (f38 (f39 f62 ?v1) ?v2)) (f38 (f39 f62 (f38 ?v_0 ?v1)) (f38 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f62 ?v0))) (= (f38 (f39 f62 (f38 ?v_0 ?v1)) ?v2) (f38 (f39 f62 (f38 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f38 (f39 f68 (f38 (f39 f62 ?v0) ?v1)) ?v2) (f38 (f39 f62 (f38 (f39 f68 ?v0) ?v2)) (f38 (f39 f68 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f62 ?v2))) (=> (= (f34 (f65 ?v0) ?v1) f1) (= (f34 (f65 (f38 ?v_0 ?v1)) (f38 ?v_0 ?v0)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f34 (f65 ?v0) ?v1) f1) (= (f34 (f65 (f38 (f39 f62 ?v0) ?v2)) (f38 (f39 f62 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f39 f62 ?v1))) (=> (= (f34 (f65 ?v0) ?v1) f1) (= (f38 ?v_0 (f38 ?v_0 ?v0)) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f65 ?v0))) (=> (= (f34 ?v_0 ?v1) f1) (=> (= (f34 ?v_0 ?v2) f1) (= (= (f38 (f39 f62 ?v1) ?v0) (f38 (f39 f62 ?v2) ?v0)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f65 ?v0)) (?v_1 (f39 f62 ?v1))) (=> (= (f34 ?v_0 ?v1) f1) (=> (= (f34 ?v_0 ?v2) f1) (= (f38 (f39 f62 (f38 ?v_1 ?v0)) (f38 (f39 f62 ?v2) ?v0)) (f38 ?v_1 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f65 ?v0))) (=> (= (f34 ?v_0 ?v1) f1) (=> (= (f34 ?v_0 ?v2) f1) (= (= (f34 (f65 (f38 (f39 f62 ?v1) ?v0)) (f38 (f39 f62 ?v2) ?v0)) f1) (= (f34 (f65 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f65 ?v1))) (=> (= (f69 (f53 (f54 ?v0) ?v1) (f53 (f54 ?v2) ?v3)) f1) (or (= (f34 ?v_0 ?v0) f1) (and (= (f34 (f65 ?v2) ?v0) f1) (= (f34 ?v_0 ?v3) f1)))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f70 (f63 ?v0 ?v1) (f63 ?v2 ?v3)) f1) (or (= (f67 ?v1 ?v0) f1) (and (= (f67 ?v2 ?v0) f1) (= (f67 ?v1 ?v3) f1))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23) (?v3 S23)) (=> (= (f71 (f64 ?v0 ?v1) (f64 ?v2 ?v3)) f1) (or (= (f66 ?v1 ?v0) f1) (and (= (f66 ?v2 ?v0) f1) (= (f66 ?v1 ?v3) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f34 (f65 ?v0) ?v1) f1) (=> (= (f34 (f65 ?v2) ?v3) f1) (= (f34 (f65 (f38 (f39 f68 ?v0) ?v2)) (f38 (f39 f68 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f68 ?v2))) (=> (= (f34 (f65 ?v0) ?v1) f1) (= (f34 (f65 (f38 ?v_0 ?v0)) (f38 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f34 (f65 ?v0) ?v1) f1) (= (f34 (f65 (f38 (f39 f68 ?v0) ?v2)) (f38 (f39 f68 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f39 f68 ?v0))) (= (f38 (f39 f68 (f38 ?v_0 ?v1)) (f38 (f39 f68 ?v2) ?v3)) (f38 (f39 f68 (f38 ?v_0 ?v2)) (f38 (f39 f68 ?v1) ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f15 f72 ?v0))) (= (f14 (f15 f72 (f14 ?v_0 ?v1)) (f14 (f15 f72 ?v2) ?v3)) (f14 (f15 f72 (f14 ?v_0 ?v2)) (f14 (f15 f72 ?v1) ?v3))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23) (?v3 S23)) (let ((?v_0 (f47 f73 ?v0))) (= (f46 (f47 f73 (f46 ?v_0 ?v1)) (f46 (f47 f73 ?v2) ?v3)) (f46 (f47 f73 (f46 ?v_0 ?v2)) (f46 (f47 f73 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f39 f68 (f38 (f39 f68 ?v0) ?v1))) (?v_0 (f39 f68 ?v2))) (= (f38 ?v_1 (f38 ?v_0 ?v3)) (f38 ?v_0 (f38 ?v_1 ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_1 (f15 f72 (f14 (f15 f72 ?v0) ?v1))) (?v_0 (f15 f72 ?v2))) (= (f14 ?v_1 (f14 ?v_0 ?v3)) (f14 ?v_0 (f14 ?v_1 ?v3))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23) (?v3 S23)) (let ((?v_1 (f47 f73 (f46 (f47 f73 ?v0) ?v1))) (?v_0 (f47 f73 ?v2))) (= (f46 ?v_1 (f46 ?v_0 ?v3)) (f46 ?v_0 (f46 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f39 f68 ?v0)) (?v_1 (f38 (f39 f68 ?v2) ?v3))) (= (f38 (f39 f68 (f38 ?v_0 ?v1)) ?v_1) (f38 ?v_0 (f38 (f39 f68 ?v1) ?v_1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f15 f72 ?v0)) (?v_1 (f14 (f15 f72 ?v2) ?v3))) (= (f14 (f15 f72 (f14 ?v_0 ?v1)) ?v_1) (f14 ?v_0 (f14 (f15 f72 ?v1) ?v_1))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23) (?v3 S23)) (let ((?v_0 (f47 f73 ?v0)) (?v_1 (f46 (f47 f73 ?v2) ?v3))) (= (f46 (f47 f73 (f46 ?v_0 ?v1)) ?v_1) (f46 ?v_0 (f46 (f47 f73 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f68 ?v0))) (= (f38 (f39 f68 (f38 ?v_0 ?v1)) ?v2) (f38 (f39 f68 (f38 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f72 ?v0))) (= (f14 (f15 f72 (f14 ?v_0 ?v1)) ?v2) (f14 (f15 f72 (f14 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f47 f73 ?v0))) (= (f46 (f47 f73 (f46 ?v_0 ?v1)) ?v2) (f46 (f47 f73 (f46 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f68 ?v0))) (= (f38 (f39 f68 (f38 ?v_0 ?v1)) ?v2) (f38 ?v_0 (f38 (f39 f68 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f72 ?v0))) (= (f14 (f15 f72 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f72 ?v1) ?v2))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f47 f73 ?v0))) (= (f46 (f47 f73 (f46 ?v_0 ?v1)) ?v2) (f46 ?v_0 (f46 (f47 f73 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f68 ?v0))) (= (f38 (f39 f68 (f38 ?v_0 ?v1)) ?v2) (f38 ?v_0 (f38 (f39 f68 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 f68 ?v0))) (= (f38 ?v_0 (f38 (f39 f68 ?v1) ?v2)) (f38 (f39 f68 (f38 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f72 ?v0))) (= (f14 ?v_0 (f14 (f15 f72 ?v1) ?v2)) (f14 (f15 f72 (f14 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_0 (f47 f73 ?v0))) (= (f46 ?v_0 (f46 (f47 f73 ?v1) ?v2)) (f46 (f47 f73 (f46 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f39 f68 ?v0)) (?v_0 (f39 f68 ?v1))) (= (f38 ?v_1 (f38 ?v_0 ?v2)) (f38 ?v_0 (f38 ?v_1 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_1 (f15 f72 ?v0)) (?v_0 (f15 f72 ?v1))) (= (f14 ?v_1 (f14 ?v_0 ?v2)) (f14 ?v_0 (f14 ?v_1 ?v2))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (let ((?v_1 (f47 f73 ?v0)) (?v_0 (f47 f73 ?v1))) (= (f46 ?v_1 (f46 ?v_0 ?v2)) (f46 ?v_0 (f46 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f38 (f39 f68 ?v0) ?v1) (f38 (f39 f68 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f38 (f39 f68 ?v0) ?v1) (f38 (f39 f68 ?v1) ?v0))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f14 (f15 f72 ?v0) ?v1) (f14 (f15 f72 ?v1) ?v0))))
(assert (forall ((?v0 S23) (?v1 S23)) (= (f46 (f47 f73 ?v0) ?v1) (f46 (f47 f73 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f39 f68 ?v0))) (= (f34 (f65 ?v0) (f38 ?v_0 (f38 ?v_0 ?v0))) f1))))
(assert (forall ((?v0 S3)) (= (f34 (f65 ?v0) (f38 (f39 f68 ?v0) ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f65 f49))) (=> (or (and (= (f34 ?v_0 ?v0) f1) (= (f34 (f65 ?v1) f49) f1)) (and (= (f34 (f65 ?v0) f49) f1) (= (f34 ?v_0 ?v1) f1))) (= (f34 (f65 (f38 (f39 f68 ?v0) ?v1)) f49) f1)))))
(assert (forall ((?v0 S23) (?v1 S23)) (=> (or (and (= (f66 f57 ?v0) f1) (= (f66 ?v1 f57) f1)) (and (= (f66 ?v0 f57) f1) (= (f66 f57 ?v1) f1))) (= (f66 (f46 (f47 f73 ?v0) ?v1) f57) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (or (and (= (f67 f28 ?v0) f1) (= (f67 ?v1 f28) f1)) (and (= (f67 ?v0 f28) f1) (= (f67 f28 ?v1) f1))) (= (f67 (f14 (f15 f72 ?v0) ?v1) f28) f1))))
(assert (forall ((?v0 S23) (?v1 S23)) (=> (or (and (= (f66 f57 ?v0) f1) (= (f66 f57 ?v1) f1)) (and (= (f66 ?v0 f57) f1) (= (f66 ?v1 f57) f1))) (= (f66 f57 (f46 (f47 f73 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (or (and (= (f67 f28 ?v0) f1) (= (f67 f28 ?v1) f1)) (and (= (f67 ?v0 f28) f1) (= (f67 ?v1 f28) f1))) (= (f67 f28 (f14 (f15 f72 ?v0) ?v1)) f1))))
(check-sat)
(exit)