(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unsat)
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
(declare-fun f29 (S19 S20) S4)
(declare-fun f30 (S21 S2) S19)
(declare-fun f31 () S21)
(declare-fun f32 () S15)
(declare-fun f33 () S4)
(declare-fun f34 () S2)
(declare-fun f35 () S3)
(declare-fun f36 () S3)
(declare-fun f37 (S22 S3) S20)
(declare-fun f38 (S3) S22)
(declare-fun f39 () S3)
(declare-fun f40 (S20 S3) S1)
(declare-fun f41 (S3) S20)
(declare-fun f42 () S10)
(declare-fun f43 (S23 S20) S10)
(declare-fun f44 (S24 S9) S23)
(declare-fun f45 () S24)
(declare-fun f46 () S17)
(declare-fun f47 (S25 S3) S3)
(declare-fun f48 (S26 S3) S25)
(declare-fun f49 () S26)
(declare-fun f50 () S3)
(declare-fun f51 (S27 S3) S28)
(declare-fun f52 (S29 S28) S27)
(declare-fun f53 () S29)
(declare-fun f54 () S28)
(declare-fun f55 () S28)
(declare-fun f56 (S10 S10) S1)
(declare-fun f57 (S28 S28) S1)
(declare-fun f58 (S10 S10) S30)
(declare-fun f59 (S28 S28) S31)
(declare-fun f60 (S3 S20) S1)
(declare-fun f61 () S26)
(declare-fun f62 (S32 S28) S28)
(declare-fun f63 (S33 S28) S32)
(declare-fun f64 () S33)
(declare-fun f65 () S26)
(declare-fun f66 (S10 S10) S1)
(declare-fun f67 (S28 S28) S1)
(declare-fun f68 (S3) S20)
(declare-fun f69 () S33)
(declare-fun f70 () S14)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (f3 (f4 (f5 f6 ?v0) ?v1) ?v2) (f7 (f8 f9 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S3)) (= (f10 (f11 (f12 f13 ?v0) ?v1) ?v2) (f14 (f15 f16 (f10 ?v0 ?v2)) (f10 ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S3)) (= (f3 (f17 (f18 f19 ?v0) ?v1) ?v2) (f7 (f8 f20 (f3 ?v0 ?v2)) ?v1))))
(assert (forall ((?v0 S9) (?v1 S10) (?v2 S3)) (= (f10 (f21 (f22 f23 ?v0) ?v1) ?v2) (f14 (f15 f24 (f10 ?v0 ?v2)) ?v1))))
(assert (forall ((?v0 S3)) (= (f3 f25 ?v0) f26)))
(assert (forall ((?v0 S3)) (= (f10 f27 ?v0) f28)))
(assert (let ((?v_1 (f3 (f17 f32 (f7 (f8 f20 f33) (f3 f34 f35))) f36))) (let ((?v_0 (f17 f32 ?v_1))) (not (= (f29 (f30 f31 ?v_0) (f37 (f38 f39) f35)) (f7 (f8 f20 (f7 (f8 f9 (f3 ?v_0 f35)) f33)) (f7 (f8 f9 ?v_1) f33)))))))
(assert (= (f40 (f41 f39) f36) f1))
(assert (= (f40 (f41 f36) f35) f1))
(assert (forall ((?v0 S3)) (= (f3 (f17 f32 (f3 f34 ?v0)) ?v0) f33)))
(assert (forall ((?v0 S10) (?v1 S3)) (let ((?v_0 (f21 f46 ?v0))) (=> (not (= ?v0 f42)) (= (f43 (f44 f45 ?v_0) (f37 (f38 f39) ?v1)) (f14 (f15 f24 (f14 (f15 f16 (f10 ?v_0 ?v1)) f42)) (f14 (f15 f16 ?v0) f42)))))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f17 f32 ?v0))) (=> (not (= ?v0 f33)) (= (f29 (f30 f31 ?v_0) (f37 (f38 f39) ?v1)) (f7 (f8 f20 (f7 (f8 f9 (f3 ?v_0 ?v1)) f33)) (f7 (f8 f9 ?v0) f33)))))))
(assert (forall ((?v0 S3)) (= (f47 (f48 f49 f39) ?v0) (ite (= ?v0 f39) f50 f39))))
(assert (forall ((?v0 S3)) (= (f10 (f21 f46 f28) ?v0) (ite (= ?v0 f39) f42 f28))))
(assert (forall ((?v0 S3)) (= (f51 (f52 f53 f54) ?v0) (ite (= ?v0 f39) f55 f54))))
(assert (forall ((?v0 S3)) (= (f3 (f17 f32 f26) ?v0) (ite (= ?v0 f39) f33 f26))))
(assert (forall ((?v0 S10) (?v1 S3)) (let ((?v_0 (f15 f24 f42))) (= (f14 ?v_0 (f10 (f21 f46 ?v0) ?v1)) (f10 (f21 f46 (f14 ?v_0 ?v0)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f8 f20 f33))) (= (f7 ?v_0 (f3 (f17 f32 ?v0) ?v1)) (f3 (f17 f32 (f7 ?v_0 ?v0)) ?v1)))))
(assert (forall ((?v0 S3)) (= (f47 (f48 f49 ?v0) f39) f50)))
(assert (forall ((?v0 S10)) (= (f10 (f21 f46 ?v0) f39) f42)))
(assert (forall ((?v0 S28)) (= (f51 (f52 f53 ?v0) f39) f55)))
(assert (forall ((?v0 S4)) (= (f3 (f17 f32 ?v0) f39) f33)))
(assert (forall ((?v0 S3)) (= (f47 (f48 f49 ?v0) f39) f50)))
(assert (forall ((?v0 S10)) (= (f10 (f21 f46 ?v0) f39) f42)))
(assert (forall ((?v0 S28)) (= (f51 (f52 f53 ?v0) f39) f55)))
(assert (forall ((?v0 S4)) (= (f3 (f17 f32 ?v0) f39) f33)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S3)) (=> (not (= ?v0 f28)) (= (f10 (f21 f46 (f14 (f15 f24 ?v1) ?v0)) ?v2) (f14 (f15 f24 (f10 (f21 f46 ?v1) ?v2)) (f10 (f21 f46 ?v0) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (=> (not (= ?v0 f26)) (= (f3 (f17 f32 (f7 (f8 f20 ?v1) ?v0)) ?v2) (f7 (f8 f20 (f3 (f17 f32 ?v1) ?v2)) (f3 (f17 f32 ?v0) ?v2))))))
(assert (forall ((?v0 S10)) (= (f14 (f15 f24 ?v0) ?v0) (ite (= ?v0 f28) f28 f42))))
(assert (forall ((?v0 S4)) (= (f7 (f8 f20 ?v0) ?v0) (ite (= ?v0 f26) f26 f33))))
(assert (forall ((?v0 S10)) (=> (not (= ?v0 f28)) (= (f14 (f15 f24 ?v0) ?v0) f42))))
(assert (forall ((?v0 S4)) (=> (not (= ?v0 f26)) (= (f7 (f8 f20 ?v0) ?v0) f33))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (not (= ?v0 f28)) (= (= (f14 (f15 f24 ?v1) ?v0) f42) (= ?v1 ?v0)))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (not (= ?v0 f26)) (= (= (f7 (f8 f20 ?v1) ?v0) f33) (= ?v1 ?v0)))))
(assert (forall ((?v0 S10) (?v1 S3)) (= (= (f10 (f21 f46 ?v0) ?v1) f28) (and (= ?v0 f28) (not (= ?v1 f39))))))
(assert (forall ((?v0 S4) (?v1 S3)) (= (= (f3 (f17 f32 ?v0) ?v1) f26) (and (= ?v0 f26) (not (= ?v1 f39))))))
(assert (forall ((?v0 S28) (?v1 S3)) (= (= (f51 (f52 f53 ?v0) ?v1) f54) (and (= ?v0 f54) (not (= ?v1 f39))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f47 (f48 f49 ?v0) ?v1) f39) (and (= ?v0 f39) (not (= ?v1 f39))))))
(assert (forall ((?v0 S9) (?v1 S20) (?v2 S10)) (= (f14 (f15 f24 (f43 (f44 f45 ?v0) ?v1)) ?v2) (f43 (f44 f45 (f21 (f22 f23 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S20) (?v2 S4)) (= (f7 (f8 f20 (f29 (f30 f31 ?v0) ?v1)) ?v2) (f29 (f30 f31 (f17 (f18 f19 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S9) (?v1 S20) (?v2 S10)) (= (f14 (f15 f24 (f43 (f44 f45 ?v0) ?v1)) ?v2) (f43 (f44 f45 (f21 (f22 f23 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S20) (?v2 S4)) (= (f7 (f8 f20 (f29 (f30 f31 ?v0) ?v1)) ?v2) (f29 (f30 f31 (f17 (f18 f19 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f41 f39))) (= (= (f40 ?v_0 (f47 (f48 f49 ?v0) ?v1)) f1) (or (= (f40 ?v_0 ?v0) f1) (= ?v1 f39))))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f56 ?v0 ?v1) f1) false) (=> (=> (= (f56 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S28) (?v1 S28)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f57 ?v0 ?v1) f1) false) (=> (=> (= (f57 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f49 ?v0))) (=> (= (f40 (f41 f39) ?v0) f1) (=> (= (f40 (f41 (f47 ?v_0 ?v1)) (f47 ?v_0 ?v2)) f1) (= (f40 (f41 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10)) (= (f10 (f21 f46 ?v0) f50) ?v0)))
(assert (forall ((?v0 S3)) (= (f47 (f48 f49 ?v0) f50) ?v0)))
(assert (forall ((?v0 S4)) (= (f3 (f17 f32 ?v0) f50) ?v0)))
(assert (forall ((?v0 S28)) (= (f51 (f52 f53 ?v0) f50) ?v0)))
(assert (forall ((?v0 S10)) (= (f10 (f21 f46 ?v0) f50) ?v0)))
(assert (forall ((?v0 S3)) (= (f47 (f48 f49 ?v0) f50) ?v0)))
(assert (forall ((?v0 S4)) (= (f3 (f17 f32 ?v0) f50) ?v0)))
(assert (forall ((?v0 S28)) (= (f51 (f52 f53 ?v0) f50) ?v0)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f58 ?v0 ?v1) (f58 ?v2 ?v3)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f56 ?v2 ?v3) f1) (= ?v1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f37 (f38 ?v0) ?v1) (f37 (f38 ?v2) ?v3)) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f40 (f41 ?v2) ?v3) f1) (= ?v1 ?v3))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f59 ?v0 ?v1) (f59 ?v2 ?v3)) (=> (= (f57 ?v0 ?v1) f1) (=> (= (f57 ?v2 ?v3) f1) (= ?v1 ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f58 ?v0 ?v1) (f58 ?v2 ?v3)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f56 ?v2 ?v3) f1) (= ?v0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f37 (f38 ?v0) ?v1) (f37 (f38 ?v2) ?v3)) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f40 (f41 ?v2) ?v3) f1) (= ?v0 ?v2))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f59 ?v0 ?v1) (f59 ?v2 ?v3)) (=> (= (f57 ?v0 ?v1) f1) (=> (= (f57 ?v2 ?v3) f1) (= ?v0 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f56 ?v2 ?v3) f1) (= (= (f58 ?v0 ?v1) (f58 ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f40 (f41 ?v2) ?v3) f1) (= (= (f37 (f38 ?v0) ?v1) (f37 (f38 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f57 ?v0 ?v1) f1) (=> (= (f57 ?v2 ?v3) f1) (= (= (f59 ?v0 ?v1) (f59 ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f49 ?v2))) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f40 (f41 f50) ?v2) f1) (= (f40 (f41 (f47 ?v_0 ?v0)) (f47 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (let ((?v_0 (f21 f46 ?v2))) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f56 f42 ?v2) f1) (= (f56 (f10 ?v_0 ?v0) (f10 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S28)) (let ((?v_0 (f52 f53 ?v2))) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f57 f55 ?v2) f1) (= (f57 (f51 ?v_0 ?v0) (f51 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f49 ?v0))) (=> (= (f40 (f41 f50) ?v0) f1) (=> (= (f40 (f41 (f47 ?v_0 ?v1)) (f47 ?v_0 ?v2)) f1) (= (f40 (f41 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S3) (?v2 S3)) (let ((?v_0 (f21 f46 ?v0))) (=> (= (f56 f42 ?v0) f1) (=> (= (f56 (f10 ?v_0 ?v1) (f10 ?v_0 ?v2)) f1) (= (f40 (f41 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S28) (?v1 S3) (?v2 S3)) (let ((?v_0 (f52 f53 ?v0))) (=> (= (f57 f55 ?v0) f1) (=> (= (f57 (f51 ?v_0 ?v1) (f51 ?v_0 ?v2)) f1) (= (f40 (f41 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f49 ?v0))) (=> (= (f40 (f41 f50) ?v0) f1) (= (= (f40 (f41 (f47 ?v_0 ?v1)) (f47 ?v_0 ?v2)) f1) (= (f40 (f41 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S3) (?v2 S3)) (let ((?v_0 (f21 f46 ?v0))) (=> (= (f56 f42 ?v0) f1) (= (= (f56 (f10 ?v_0 ?v1) (f10 ?v_0 ?v2)) f1) (= (f40 (f41 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S28) (?v1 S3) (?v2 S3)) (let ((?v_0 (f52 f53 ?v0))) (=> (= (f57 f55 ?v0) f1) (= (= (f57 (f51 ?v_0 ?v1) (f51 ?v_0 ?v2)) f1) (= (f40 (f41 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f49 ?v2))) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f40 (f41 f39) ?v2) f1) (=> (= (f40 (f41 ?v2) f50) f1) (= (f40 (f41 (f47 ?v_0 ?v1)) (f47 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (let ((?v_0 (f21 f46 ?v2))) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f56 f28 ?v2) f1) (=> (= (f56 ?v2 f42) f1) (= (f56 (f10 ?v_0 ?v1) (f10 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S28)) (let ((?v_0 (f52 f53 ?v2))) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f57 f54 ?v2) f1) (=> (= (f57 ?v2 f55) f1) (= (f57 (f51 ?v_0 ?v1) (f51 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f41 f50))) (=> (= (f40 ?v_0 ?v0) f1) (=> (= (f40 (f41 f39) ?v1) f1) (= (f40 ?v_0 (f47 (f48 f49 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S10) (?v1 S3)) (=> (= (f56 f42 ?v0) f1) (=> (= (f40 (f41 f39) ?v1) f1) (= (f56 f42 (f10 (f21 f46 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S28) (?v1 S3)) (=> (= (f57 f55 ?v0) f1) (=> (= (f40 (f41 f39) ?v1) f1) (= (f57 f55 (f51 (f52 f53 ?v0) ?v1)) f1)))))
(assert (= (f40 (f41 f39) f50) f1))
(assert (= (f56 f28 f42) f1))
(assert (= (f57 f54 f55) f1))
(assert (not (= (f40 (f41 f50) f39) f1)))
(assert (not (= (f56 f42 f28) f1)))
(assert (not (= (f57 f55 f54) f1)))
(assert (forall ((?v0 S10) (?v1 S3)) (=> (= (f56 f28 ?v0) f1) (= (f56 f28 (f10 (f21 f46 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S28) (?v1 S3)) (=> (= (f57 f54 ?v0) f1) (= (f57 f54 (f51 (f52 f53 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f41 f39))) (=> (= (f40 ?v_0 ?v0) f1) (= (f40 ?v_0 (f47 (f48 f49 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f49 ?v0))) (=> (= (f40 (f41 f50) ?v0) f1) (= (= (f47 ?v_0 ?v1) (f47 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S3) (?v2 S3)) (let ((?v_0 (f21 f46 ?v0))) (=> (= (f56 f42 ?v0) f1) (= (= (f10 ?v_0 ?v1) (f10 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S28) (?v1 S3) (?v2 S3)) (let ((?v_0 (f52 f53 ?v0))) (=> (= (f57 f55 ?v0) f1) (= (= (f51 ?v_0 ?v1) (f51 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S3)) (not (= (f3 f34 ?v0) f26))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f40 (f41 f39) ?v0) f1) (=> (= (f40 (f41 ?v0) ?v1) f1) (= (f29 (f30 f31 (f17 f32 (f3 (f17 f32 (f3 f34 ?v1)) ?v0))) (f37 (f38 f39) ?v1)) f26)))))
(assert (not (= f39 f50)))
(assert (not (= f28 f42)))
(assert (not (= f54 f55)))
(assert (not (= f26 f33)))
(assert (not (= f50 f39)))
(assert (not (= f42 f28)))
(assert (not (= f55 f54)))
(assert (not (= f33 f26)))
(assert (forall ((?v0 S10) (?v1 S3)) (=> (not (= ?v0 f28)) (not (= (f10 (f21 f46 ?v0) ?v1) f28)))))
(assert (forall ((?v0 S4) (?v1 S3)) (=> (not (= ?v0 f26)) (not (= (f3 (f17 f32 ?v0) ?v1) f26)))))
(assert (forall ((?v0 S28) (?v1 S3)) (=> (not (= ?v0 f54)) (not (= (f51 (f52 f53 ?v0) ?v1) f54)))))
(assert (forall ((?v0 S10)) (= (f14 (f15 f24 ?v0) f28) f28)))
(assert (forall ((?v0 S4)) (= (f7 (f8 f20 ?v0) f26) f26)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f24 f28) ?v0) f28)))
(assert (forall ((?v0 S4)) (= (f7 (f8 f20 f26) ?v0) f26)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f24 f28) ?v0) f28)))
(assert (forall ((?v0 S4)) (= (f7 (f8 f20 f26) ?v0) f26)))
(assert (forall ((?v0 S3)) (= (f47 (f48 f49 f50) ?v0) f50)))
(assert (forall ((?v0 S3)) (= (f10 (f21 f46 f42) ?v0) f42)))
(assert (forall ((?v0 S3)) (= (f51 (f52 f53 f55) ?v0) f55)))
(assert (forall ((?v0 S3)) (= (f3 (f17 f32 f33) ?v0) f33)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f24 ?v0) f42) ?v0)))
(assert (forall ((?v0 S4)) (= (f7 (f8 f20 ?v0) f33) ?v0)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (f14 (f15 f24 (f14 (f15 f16 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f14 (f15 f24 ?v0) ?v2)) (f14 (f15 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f7 (f8 f20 (f7 (f8 f9 ?v0) ?v1)) ?v2) (f7 (f8 f9 (f7 (f8 f20 ?v0) ?v2)) (f7 (f8 f20 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (f14 (f15 f24 (f14 (f15 f16 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f14 (f15 f24 ?v0) ?v2)) (f14 (f15 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f7 (f8 f20 (f7 (f8 f9 ?v0) ?v1)) ?v2) (f7 (f8 f9 (f7 (f8 f20 ?v0) ?v2)) (f7 (f8 f20 ?v1) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S3)) (= (f10 (f21 f46 (f14 (f15 f24 ?v0) ?v1)) ?v2) (f14 (f15 f24 (f10 (f21 f46 ?v0) ?v2)) (f10 (f21 f46 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (= (f3 (f17 f32 (f7 (f8 f20 ?v0) ?v1)) ?v2) (f7 (f8 f20 (f3 (f17 f32 ?v0) ?v2)) (f3 (f17 f32 ?v1) ?v2)))))
(assert (forall ((?v0 S20)) (= (f43 (f44 f45 f27) ?v0) f28)))
(assert (forall ((?v0 S20)) (= (f29 (f30 f31 f25) ?v0) f26)))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S20)) (= (f43 (f44 f45 (f11 (f12 f13 ?v0) ?v1)) ?v2) (f14 (f15 f16 (f43 (f44 f45 ?v0) ?v2)) (f43 (f44 f45 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S20)) (= (f29 (f30 f31 (f4 (f5 f6 ?v0) ?v1)) ?v2) (f7 (f8 f9 (f29 (f30 f31 ?v0) ?v2)) (f29 (f30 f31 ?v1) ?v2)))))
(assert (forall ((?v0 S3)) (=> (= (f40 (f41 ?v0) f39) f1) false)))
(assert (forall ((?v0 S3) (?v1 S20)) (= (forall ((?v2 S3)) (=> (= (f40 (f41 ?v2) ?v0) f1) (= (f40 ?v1 ?v2) f1))) (forall ((?v2 S3)) (=> (= (f60 ?v2 (f37 (f38 f39) ?v0)) f1) (= (f40 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S20)) (= (exists ((?v2 S3)) (and (= (f40 (f41 ?v2) ?v0) f1) (= (f40 ?v1 ?v2) f1))) (exists ((?v2 S3)) (and (= (f60 ?v2 (f37 (f38 f39) ?v0)) f1) (= (f40 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f56 ?v2 f28) f1) (= (f56 (f14 (f15 f24 ?v1) ?v2) (f14 (f15 f24 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f56 f28 ?v2) f1) (= (f56 (f14 (f15 f24 ?v0) ?v2) (f14 (f15 f24 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f56 ?v0 f28) f1) (=> (= (f56 ?v1 f28) f1) (= (f56 f28 (f14 (f15 f24 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f56 ?v0 f28) f1) (=> (= (f56 f28 ?v1) f1) (= (f56 (f14 (f15 f24 ?v0) ?v1) f28) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f56 f28 ?v0) f1) (=> (= (f56 ?v1 f28) f1) (= (f56 (f14 (f15 f24 ?v0) ?v1) f28) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f56 f28 ?v0) f1) (=> (= (f56 f28 ?v1) f1) (= (f56 f28 (f14 (f15 f24 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (= (= (f56 (f14 (f15 f24 ?v0) ?v1) (f14 (f15 f24 ?v2) ?v1)) f1) (and (=> (= (f56 f28 ?v1) f1) (= (f56 ?v0 ?v2) f1)) (and (=> (= (f56 ?v1 f28) f1) (= (f56 ?v2 ?v0) f1)) (not (= ?v1 f28)))))))
(assert (forall ((?v0 S3)) (= (f47 (f48 f61 f39) ?v0) f39)))
(assert (forall ((?v0 S3)) (= (f47 (f48 f61 ?v0) f39) ?v0)))
(assert (forall ((?v0 S3)) (= (f47 (f48 f61 ?v0) ?v0) f39)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f47 (f48 f61 ?v0) ?v1) f39) (=> (= (f47 (f48 f61 ?v1) ?v0) f39) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S22)) (let ((?v_0 (= (f40 (f37 ?v2 ?v1) ?v0) f1))) (=> (=> (= (f40 (f41 ?v0) ?v1) f1) ?v_0) (=> (=> (= ?v0 ?v1) ?v_0) (=> (=> (= (f40 (f41 ?v1) ?v0) f1) ?v_0) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f41 ?v0)) (?v_1 (f48 f61 ?v2))) (=> (= (f40 ?v_0 ?v1) f1) (=> (= (f40 ?v_0 ?v2) f1) (= (f40 (f41 (f47 ?v_1 ?v1)) (f47 ?v_1 ?v0)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f40 (f41 ?v0) ?v1) f1) (= (f40 (f41 (f47 (f48 f61 ?v0) ?v2)) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f40 (f41 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f40 (f41 ?v0) ?v1) f1) (not (= ?v1 ?v0)))))
(assert (forall ((?v0 S3)) (=> (= (f40 (f41 ?v0) ?v0) f1) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f40 (f41 ?v0) ?v1) f1) false) (=> (=> (= (f40 (f41 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (not (= ?v0 ?v1)) (or (= (f40 (f41 ?v0) ?v1) f1) (= (f40 (f41 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (not (= (f40 (f41 ?v0) ?v0) f1))))
(assert (forall ((?v0 S3)) (not (= (f40 (f41 ?v0) f39) f1))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f39)) (= (f40 (f41 f39) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (= (f40 (f41 ?v0) f39) f1) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f40 (f41 ?v0) ?v1) f1) (not (= ?v1 f39)))))
(assert (forall ((?v0 S3) (?v1 S20)) (= (= (f60 ?v0 ?v1) f1) (= (f40 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (=> (=> (= ?v0 f39) false) (= (f40 (f41 f39) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f41 f39))) (=> (= (f40 ?v_0 ?v0) f1) (=> (= (f40 ?v_0 ?v1) f1) (= (f40 (f41 (f47 (f48 f61 ?v1) ?v0)) ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f40 (f41 f39) (f47 (f48 f61 ?v0) ?v1)) f1) (= (f40 (f41 ?v1) ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f56 f28 (f14 (f15 f24 ?v0) ?v1)) f1) (or (and (= (f56 f28 ?v0) f1) (= (f56 f28 ?v1) f1)) (and (= (f56 ?v0 f28) f1) (= (f56 ?v1 f28) f1))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f56 (f14 (f15 f24 ?v0) ?v1) f28) f1) (or (and (= (f56 f28 ?v0) f1) (= (f56 ?v1 f28) f1)) (and (= (f56 ?v0 f28) f1) (= (f56 f28 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f41 f39))) (= (= (f40 ?v_0 (f47 (f48 f49 ?v0) ?v1)) f1) (or (= ?v1 f39) (= (f40 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f56 ?v0 ?v1) f1) (= (f56 (f14 (f15 f16 ?v0) ?v1) f28) f1))))
(assert (forall ((?v0 S28) (?v1 S28)) (= (= (f57 ?v0 ?v1) f1) (= (f57 (f62 (f63 f64 ?v0) ?v1) f54) f1))))
(assert (forall ((?v0 S10) (?v1 S3)) (let ((?v_0 (f21 f46 ?v0))) (=> (not (= ?v0 f42)) (= (f43 (f44 f45 ?v_0) (f37 (f38 f39) ?v1)) (f14 (f15 f24 (f14 (f15 f16 (f10 ?v_0 ?v1)) f42)) (f14 (f15 f16 ?v0) f42)))))))
(assert (forall ((?v0 S20) (?v1 S9)) (=> (forall ((?v2 S3)) (=> (= (f60 ?v2 ?v0) f1) (= (f10 ?v1 ?v2) f28))) (= (f43 (f44 f45 ?v1) ?v0) f28))))
(assert (forall ((?v0 S20) (?v1 S2)) (=> (forall ((?v2 S3)) (=> (= (f60 ?v2 ?v0) f1) (= (f3 ?v1 ?v2) f26))) (= (f29 (f30 f31 ?v1) ?v0) f26))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f14 (f15 f16 ?v0) ?v1) (f14 (f15 f16 ?v2) ?v3)) (= (= (f56 ?v0 ?v1) f1) (= (f56 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f62 (f63 f64 ?v0) ?v1) (f62 (f63 f64 ?v2) ?v3)) (= (= (f57 ?v0 ?v1) f1) (= (f57 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S10)) (= (f14 (f15 f16 ?v0) f28) ?v0)))
(assert (forall ((?v0 S4)) (= (f7 (f8 f9 ?v0) f26) ?v0)))
(assert (forall ((?v0 S28)) (= (f62 (f63 f64 ?v0) f54) ?v0)))
(assert (forall ((?v0 S10)) (= (f14 (f15 f16 ?v0) ?v0) f28)))
(assert (forall ((?v0 S4)) (= (f7 (f8 f9 ?v0) ?v0) f26)))
(assert (forall ((?v0 S28)) (= (f62 (f63 f64 ?v0) ?v0) f54)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f61 ?v0))) (= (f47 (f48 f61 (f47 ?v_0 ?v1)) ?v2) (f47 (f48 f61 (f47 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S10)) (= (= f28 ?v0) (= ?v0 f28))))
(assert (forall ((?v0 S4)) (= (= f26 ?v0) (= ?v0 f26))))
(assert (forall ((?v0 S28)) (= (= f54 ?v0) (= ?v0 f54))))
(assert (forall ((?v0 S3)) (= (= f39 ?v0) (= ?v0 f39))))
(assert (forall ((?v0 S3)) (= (= f50 ?v0) (= ?v0 f50))))
(assert (forall ((?v0 S10)) (= (= f42 ?v0) (= ?v0 f42))))
(assert (forall ((?v0 S28)) (= (= f55 ?v0) (= ?v0 f55))))
(assert (forall ((?v0 S4)) (= (= f33 ?v0) (= ?v0 f33))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f14 (f15 f16 ?v0) ?v1) (f14 (f15 f16 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (=> (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f62 (f63 f64 ?v0) ?v1) (f62 (f63 f64 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f14 (f15 f16 ?v0) ?v1) f28) (= ?v0 ?v1))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f7 (f8 f9 ?v0) ?v1) f26) (= ?v0 ?v1))))
(assert (forall ((?v0 S28) (?v1 S28)) (= (= (f62 (f63 f64 ?v0) ?v1) f54) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= ?v0 ?v1) (= (f14 (f15 f16 ?v0) ?v1) f28))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= ?v0 ?v1) (= (f7 (f8 f9 ?v0) ?v1) f26))))
(assert (forall ((?v0 S28) (?v1 S28)) (= (= ?v0 ?v1) (= (f62 (f63 f64 ?v0) ?v1) f54))))
(assert (forall ((?v0 S3) (?v1 S10)) (=> (= (f40 (f41 f39) ?v0) f1) (=> (= (f56 f28 ?v1) f1) (exists ((?v2 S10)) (and (= (f56 f28 ?v2) f1) (= (f10 (f21 f46 ?v2) ?v0) ?v1)))))))
(assert (forall ((?v0 S3) (?v1 S10)) (=> (= (f40 (f41 f39) ?v0) f1) (=> (= (f56 f28 ?v1) f1) (exists ((?v2 S10)) (and (and (= (f56 f28 ?v2) f1) (= (f10 (f21 f46 ?v2) ?v0) ?v1)) (forall ((?v3 S10)) (=> (and (= (f56 f28 ?v3) f1) (= (f10 (f21 f46 ?v3) ?v0) ?v1)) (= ?v3 ?v2)))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f65 ?v0))) (=> (= (f40 (f41 f39) ?v0) f1) (= (f3 (f17 f32 (f3 f34 (f47 ?v_0 ?v1))) (f47 ?v_0 ?v2)) (f3 (f17 f32 (f3 f34 ?v1)) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S3)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f66 f28 ?v0) f1) (=> (= (f40 (f41 f39) ?v2) f1) (= (f56 (f10 (f21 f46 ?v0) ?v2) (f10 (f21 f46 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S3)) (=> (= (f57 ?v0 ?v1) f1) (=> (= (f67 f54 ?v0) f1) (=> (= (f40 (f41 f39) ?v2) f1) (= (f57 (f51 (f52 f53 ?v0) ?v2) (f51 (f52 f53 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f40 (f68 f39) ?v0) f1) (=> (= (f40 (f41 f39) ?v2) f1) (= (f40 (f41 (f47 (f48 f49 ?v0) ?v2)) (f47 (f48 f49 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S9) (?v3 S9)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S3)) (=> (= (f60 ?v4 ?v1) f1) (= (f10 ?v2 ?v4) (f10 ?v3 ?v4)))) (= (f43 (f44 f45 ?v2) ?v0) (f43 (f44 f45 ?v3) ?v1))))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S2) (?v3 S2)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S3)) (=> (= (f60 ?v4 ?v1) f1) (= (f3 ?v2 ?v4) (f3 ?v3 ?v4)))) (= (f29 (f30 f31 ?v2) ?v0) (f29 (f30 f31 ?v3) ?v1))))))
(assert (forall ((?v0 S3)) (= (f40 (f68 f39) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f65 ?v0))) (= (f47 (f48 f65 (f47 ?v_0 ?v1)) ?v2) (f47 ?v_0 (f47 (f48 f65 ?v1) ?v2))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f63 f69 ?v0))) (= (f62 (f63 f69 (f62 ?v_0 ?v1)) ?v2) (f62 ?v_0 (f62 (f63 f69 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f70 ?v0))) (= (f14 (f15 f70 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f70 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f70 ?v0))) (=> (= (f56 f28 ?v0) f1) (= (= (f66 (f14 ?v_0 ?v1) (f14 ?v_0 ?v2)) f1) (= (f66 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f63 f69 ?v0))) (=> (= (f57 f54 ?v0) f1) (= (= (f67 (f62 ?v_0 ?v1) (f62 ?v_0 ?v2)) f1) (= (f67 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f70 ?v0))) (=> (= (f56 ?v0 f28) f1) (= (= (f66 (f14 ?v_0 ?v1) (f14 ?v_0 ?v2)) f1) (= (f66 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f63 f69 ?v0))) (=> (= (f57 ?v0 f54) f1) (= (= (f67 (f62 ?v_0 ?v1) (f62 ?v_0 ?v2)) f1) (= (f67 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f56 ?v2 ?v3) f1) (=> (= (f56 f28 ?v1) f1) (=> (= (f66 f28 ?v2) f1) (= (f56 (f14 (f15 f70 ?v0) ?v2) (f14 (f15 f70 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f57 ?v0 ?v1) f1) (=> (= (f57 ?v2 ?v3) f1) (=> (= (f57 f54 ?v1) f1) (=> (= (f67 f54 ?v2) f1) (= (f57 (f62 (f63 f69 ?v0) ?v2) (f62 (f63 f69 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f40 (f41 ?v2) ?v3) f1) (=> (= (f40 (f41 f39) ?v1) f1) (=> (= (f40 (f68 f39) ?v2) f1) (= (f40 (f41 (f47 (f48 f65 ?v0) ?v2)) (f47 (f48 f65 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f56 ?v2 ?v3) f1) (=> (= (f66 f28 ?v0) f1) (=> (= (f66 f28 ?v2) f1) (= (f56 (f14 (f15 f70 ?v0) ?v2) (f14 (f15 f70 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f57 ?v0 ?v1) f1) (=> (= (f57 ?v2 ?v3) f1) (=> (= (f67 f54 ?v0) f1) (=> (= (f67 f54 ?v2) f1) (= (f57 (f62 (f63 f69 ?v0) ?v2) (f62 (f63 f69 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f68 f39))) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f40 (f41 ?v2) ?v3) f1) (=> (= (f40 ?v_0 ?v0) f1) (=> (= (f40 ?v_0 ?v2) f1) (= (f40 (f41 (f47 (f48 f65 ?v0) ?v2)) (f47 (f48 f65 ?v1) ?v3)) f1))))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f66 ?v2 ?v3) f1) (=> (= (f66 f28 ?v0) f1) (=> (= (f56 f28 ?v2) f1) (= (f56 (f14 (f15 f70 ?v0) ?v2) (f14 (f15 f70 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f57 ?v0 ?v1) f1) (=> (= (f67 ?v2 ?v3) f1) (=> (= (f67 f54 ?v0) f1) (=> (= (f57 f54 ?v2) f1) (= (f57 (f62 (f63 f69 ?v0) ?v2) (f62 (f63 f69 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f40 (f41 ?v0) ?v1) f1) (=> (= (f40 (f68 ?v2) ?v3) f1) (=> (= (f40 (f68 f39) ?v0) f1) (=> (= (f40 (f41 f39) ?v2) f1) (= (f40 (f41 (f47 (f48 f65 ?v0) ?v2)) (f47 (f48 f65 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (=> (= (f66 ?v0 ?v1) f1) (=> (= (f56 ?v2 ?v3) f1) (=> (= (f56 f28 ?v0) f1) (=> (= (f66 f28 ?v2) f1) (= (f56 (f14 (f15 f70 ?v0) ?v2) (f14 (f15 f70 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f67 ?v0 ?v1) f1) (=> (= (f57 ?v2 ?v3) f1) (=> (= (f57 f54 ?v0) f1) (=> (= (f67 f54 ?v2) f1) (= (f57 (f62 (f63 f69 ?v0) ?v2) (f62 (f63 f69 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f40 (f68 ?v0) ?v1) f1) (=> (= (f40 (f41 ?v2) ?v3) f1) (=> (= (f40 (f41 f39) ?v0) f1) (=> (= (f40 (f68 f39) ?v2) f1) (= (f40 (f41 (f47 (f48 f65 ?v0) ?v2)) (f47 (f48 f65 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f56 (f14 (f15 f70 ?v0) ?v1) (f14 (f15 f70 ?v2) ?v1)) f1) (=> (= (f66 f28 ?v1) f1) (= (f56 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (=> (= (f57 (f62 (f63 f69 ?v0) ?v1) (f62 (f63 f69 ?v2) ?v1)) f1) (=> (= (f67 f54 ?v1) f1) (= (f57 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f40 (f41 (f47 (f48 f65 ?v0) ?v1)) (f47 (f48 f65 ?v2) ?v1)) f1) (=> (= (f40 (f68 f39) ?v1) f1) (= (f40 (f41 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f56 (f14 (f15 f70 ?v0) ?v1) (f14 (f15 f70 ?v2) ?v1)) f1) (=> (= (f66 f28 ?v1) f1) (= (f56 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (=> (= (f57 (f62 (f63 f69 ?v0) ?v1) (f62 (f63 f69 ?v2) ?v1)) f1) (=> (= (f67 f54 ?v1) f1) (= (f57 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f40 (f41 (f47 (f48 f65 ?v0) ?v1)) (f47 (f48 f65 ?v2) ?v1)) f1) (=> (= (f40 (f68 f39) ?v1) f1) (= (f40 (f41 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f70 ?v0))) (=> (= (f56 (f14 ?v_0 ?v1) (f14 ?v_0 ?v2)) f1) (=> (= (f66 f28 ?v0) f1) (= (f56 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f63 f69 ?v0))) (=> (= (f57 (f62 ?v_0 ?v1) (f62 ?v_0 ?v2)) f1) (=> (= (f67 f54 ?v0) f1) (= (f57 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f65 ?v0))) (=> (= (f40 (f41 (f47 ?v_0 ?v1)) (f47 ?v_0 ?v2)) f1) (=> (= (f40 (f68 f39) ?v0) f1) (= (f40 (f41 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f70 ?v0))) (=> (= (f56 (f14 ?v_0 ?v1) (f14 ?v_0 ?v2)) f1) (=> (= (f66 f28 ?v0) f1) (= (f56 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f63 f69 ?v0))) (=> (= (f57 (f62 ?v_0 ?v1) (f62 ?v_0 ?v2)) f1) (=> (= (f67 f54 ?v0) f1) (= (f57 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f65 ?v0))) (=> (= (f40 (f41 (f47 ?v_0 ?v1)) (f47 ?v_0 ?v2)) f1) (=> (= (f40 (f68 f39) ?v0) f1) (= (f40 (f41 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f66 (f14 (f15 f70 ?v0) ?v1) (f14 (f15 f70 ?v2) ?v1)) f1) (=> (= (f56 f28 ?v1) f1) (= (f66 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (=> (= (f67 (f62 (f63 f69 ?v0) ?v1) (f62 (f63 f69 ?v2) ?v1)) f1) (=> (= (f57 f54 ?v1) f1) (= (f67 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f40 (f68 (f47 (f48 f65 ?v0) ?v1)) (f47 (f48 f65 ?v2) ?v1)) f1) (=> (= (f40 (f41 f39) ?v1) f1) (= (f40 (f68 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f70 ?v0))) (=> (= (f66 (f14 ?v_0 ?v1) (f14 ?v_0 ?v2)) f1) (=> (= (f56 f28 ?v0) f1) (= (f66 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f63 f69 ?v0))) (=> (= (f67 (f62 ?v_0 ?v1) (f62 ?v_0 ?v2)) f1) (=> (= (f57 f54 ?v0) f1) (= (f67 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f65 ?v0))) (=> (= (f40 (f68 (f47 ?v_0 ?v1)) (f47 ?v_0 ?v2)) f1) (=> (= (f40 (f41 f39) ?v0) f1) (= (f40 (f68 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f66 f28 ?v0) f1) (=> (= (f66 f28 ?v1) f1) (=> (= (f66 ?v1 f42) f1) (= (f66 (f14 (f15 f70 ?v1) ?v0) ?v0) f1))))))
(assert (forall ((?v0 S28) (?v1 S28)) (=> (= (f67 f54 ?v0) f1) (=> (= (f67 f54 ?v1) f1) (=> (= (f67 ?v1 f55) f1) (= (f67 (f62 (f63 f69 ?v1) ?v0) ?v0) f1))))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f66 f28 ?v0) f1) (=> (= (f66 f28 ?v1) f1) (=> (= (f66 ?v1 f42) f1) (= (f66 (f14 (f15 f70 ?v0) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S28) (?v1 S28)) (=> (= (f67 f54 ?v0) f1) (=> (= (f67 f54 ?v1) f1) (=> (= (f67 ?v1 f55) f1) (= (f67 (f62 (f63 f69 ?v0) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f49 ?v2))) (=> (= (f40 (f68 ?v0) ?v1) f1) (=> (= (f40 (f68 f50) ?v2) f1) (= (f40 (f68 (f47 ?v_0 ?v0)) (f47 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (let ((?v_0 (f21 f46 ?v2))) (=> (= (f40 (f68 ?v0) ?v1) f1) (=> (= (f66 f42 ?v2) f1) (= (f66 (f10 ?v_0 ?v0) (f10 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S28)) (let ((?v_0 (f52 f53 ?v2))) (=> (= (f40 (f68 ?v0) ?v1) f1) (=> (= (f67 f55 ?v2) f1) (= (f67 (f51 ?v_0 ?v0) (f51 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f65 ?v0))) (= (= (f40 (f68 (f47 ?v_0 ?v1)) (f47 ?v_0 ?v2)) f1) (=> (= (f40 (f41 f39) ?v0) f1) (= (f40 (f68 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f40 (f68 (f47 (f48 f65 ?v0) ?v1)) (f47 (f48 f65 ?v2) ?v1)) f1) (=> (= (f40 (f41 f39) ?v1) f1) (= (f40 (f68 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f47 (f48 f65 ?v0) ?v1) (f47 (f48 f65 ?v1) ?v0))))
(assert (forall ((?v0 S28) (?v1 S28)) (= (f62 (f63 f69 ?v0) ?v1) (f62 (f63 f69 ?v1) ?v0))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f14 (f15 f70 ?v0) ?v1) (f14 (f15 f70 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f48 f65 ?v0)) (?v_0 (f48 f65 ?v1))) (= (f47 ?v_1 (f47 ?v_0 ?v2)) (f47 ?v_0 (f47 ?v_1 ?v2))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_1 (f63 f69 ?v0)) (?v_0 (f63 f69 ?v1))) (= (f62 ?v_1 (f62 ?v_0 ?v2)) (f62 ?v_0 (f62 ?v_1 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_1 (f15 f70 ?v0)) (?v_0 (f15 f70 ?v1))) (= (f14 ?v_1 (f14 ?v_0 ?v2)) (f14 ?v_0 (f14 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f65 ?v0))) (= (f47 ?v_0 (f47 (f48 f65 ?v1) ?v2)) (f47 (f48 f65 (f47 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f63 f69 ?v0))) (= (f62 ?v_0 (f62 (f63 f69 ?v1) ?v2)) (f62 (f63 f69 (f62 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f70 ?v0))) (= (f14 ?v_0 (f14 (f15 f70 ?v1) ?v2)) (f14 (f15 f70 (f14 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f65 ?v0))) (= (f47 (f48 f65 (f47 ?v_0 ?v1)) ?v2) (f47 ?v_0 (f47 (f48 f65 ?v1) ?v2))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f63 f69 ?v0))) (= (f62 (f63 f69 (f62 ?v_0 ?v1)) ?v2) (f62 ?v_0 (f62 (f63 f69 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f70 ?v0))) (= (f14 (f15 f70 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f70 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f48 f65 ?v0))) (= (f47 (f48 f65 (f47 ?v_0 ?v1)) ?v2) (f47 (f48 f65 (f47 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f63 f69 ?v0))) (= (f62 (f63 f69 (f62 ?v_0 ?v1)) ?v2) (f62 (f63 f69 (f62 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f15 f70 ?v0))) (= (f14 (f15 f70 (f14 ?v_0 ?v1)) ?v2) (f14 (f15 f70 (f14 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f48 f65 ?v0)) (?v_1 (f47 (f48 f65 ?v2) ?v3))) (= (f47 (f48 f65 (f47 ?v_0 ?v1)) ?v_1) (f47 ?v_0 (f47 (f48 f65 ?v1) ?v_1))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (let ((?v_0 (f63 f69 ?v0)) (?v_1 (f62 (f63 f69 ?v2) ?v3))) (= (f62 (f63 f69 (f62 ?v_0 ?v1)) ?v_1) (f62 ?v_0 (f62 (f63 f69 ?v1) ?v_1))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f15 f70 ?v0)) (?v_1 (f14 (f15 f70 ?v2) ?v3))) (= (f14 (f15 f70 (f14 ?v_0 ?v1)) ?v_1) (f14 ?v_0 (f14 (f15 f70 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f48 f65 (f47 (f48 f65 ?v0) ?v1))) (?v_0 (f48 f65 ?v2))) (= (f47 ?v_1 (f47 ?v_0 ?v3)) (f47 ?v_0 (f47 ?v_1 ?v3))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (let ((?v_1 (f63 f69 (f62 (f63 f69 ?v0) ?v1))) (?v_0 (f63 f69 ?v2))) (= (f62 ?v_1 (f62 ?v_0 ?v3)) (f62 ?v_0 (f62 ?v_1 ?v3))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_1 (f15 f70 (f14 (f15 f70 ?v0) ?v1))) (?v_0 (f15 f70 ?v2))) (= (f14 ?v_1 (f14 ?v_0 ?v3)) (f14 ?v_0 (f14 ?v_1 ?v3))))))
(check-sat)
(exit)
