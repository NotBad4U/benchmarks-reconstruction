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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S4 S2) S2)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S3) S4)
(declare-fun f7 () S5)
(declare-fun f8 () S2)
(declare-fun f9 (S6 S3) S2)
(declare-fun f10 () S6)
(declare-fun f11 () S6)
(declare-fun f12 () S5)
(declare-fun f13 (S7 S2) S1)
(declare-fun f14 (S8 S3) S7)
(declare-fun f15 () S8)
(declare-fun f16 () S5)
(declare-fun f17 () S5)
(declare-fun f18 () S5)
(declare-fun f19 (S11 S9) S1)
(declare-fun f20 (S12 S10) S11)
(declare-fun f21 (S13 S9) S12)
(declare-fun f22 () S13)
(declare-fun f23 (S14 S10) S12)
(declare-fun f24 (S15 S12) S14)
(declare-fun f25 () S15)
(declare-fun f26 (S16 S11) S12)
(declare-fun f27 (S17 S12) S16)
(declare-fun f28 () S17)
(declare-fun f29 (S18 S12) S12)
(declare-fun f30 (S19 S1) S18)
(declare-fun f31 () S19)
(declare-fun f32 () S12)
(declare-fun f33 () S12)
(declare-fun f34 () S2)
(declare-fun f35 (S20 S2) S7)
(declare-fun f36 () S20)
(declare-fun f37 () S2)
(declare-fun f38 (S21 S12) S3)
(declare-fun f39 (S22 S23) S21)
(declare-fun f40 (S24 S12) S22)
(declare-fun f41 () S24)
(declare-fun f42 () S12)
(declare-fun f43 () S23)
(declare-fun f44 () S4)
(declare-fun f45 (S25 S2) S3)
(declare-fun f46 () S25)
(declare-fun f47 () S1)
(declare-fun f48 () S23)
(declare-fun f49 (S26 S23) S23)
(declare-fun f50 (S27 S11) S26)
(declare-fun f51 () S27)
(declare-fun f52 (S28 S23) S26)
(declare-fun f53 () S28)
(declare-fun f54 () S25)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 (f4 (f6 f7 ?v1) f8)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f9 f10 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f9 f11 ?v0) ?v1) f1) (= ?v1 ?v0))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f6 f12 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f13 (f14 f15 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f6 f16 ?v0) ?v1) ?v2) f1) (and (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f6 f17 ?v0) ?v1) ?v2) f1) (and (= ?v2 ?v0) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f6 f18 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S10) (?v2 S9)) (= (= (f19 (f20 (f21 f22 ?v0) ?v1) ?v2) f1) (= ?v2 ?v0))))
(assert (forall ((?v0 S12) (?v1 S10) (?v2 S10)) (= (f20 (f23 (f24 f25 ?v0) ?v1) ?v2) (f20 ?v0 ?v1))))
(assert (forall ((?v0 S12) (?v1 S11) (?v2 S10) (?v3 S9)) (= (= (f19 (f20 (f26 (f27 f28 ?v0) ?v1) ?v2) ?v3) f1) (and (= (f19 (f20 ?v0 ?v2) ?v3) f1) (not (= (f19 ?v1 ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S12) (?v2 S10) (?v3 S9)) (= (= (f19 (f20 (f29 (f30 f31 ?v0) ?v1) ?v2) ?v3) f1) (and (= (f19 (f20 ?v1 ?v2) ?v3) f1) (= ?v0 f1)))))
(assert (forall ((?v0 S10) (?v1 S9)) (= (= (f19 (f20 f32 ?v0) ?v1) f1) false)))
(assert (forall ((?v0 S10) (?v1 S9)) (= (= (f19 (f20 f33 ?v0) ?v1) f1) true)))
(assert (forall ((?v0 S3)) (= (= (f3 f34 ?v0) f1) false)))
(assert (not (= (f13 (f35 f36 f37) (f4 (f6 f7 (f38 (f39 (f40 f41 f42) f43) f33)) f8)) f1)))
(assert (forall ((?v0 S2)) (= (f13 (f35 f36 ?v0) f8) f1)))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S12)) (= (f13 (f35 f36 ?v0) (f4 (f6 f7 (f38 (f39 (f40 f41 f32) ?v1) ?v2)) f8)) f1)))
(assert (forall ((?v0 S12) (?v1 S23) (?v2 S12) (?v3 S12) (?v4 S23) (?v5 S12)) (= (= (f38 (f39 (f40 f41 ?v0) ?v1) ?v2) (f38 (f39 (f40 f41 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f35 f36 ?v2))) (=> (= (f13 (f35 f36 ?v0) ?v1) f1) (=> (= (f13 ?v_0 ?v0) f1) (= (f13 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f35 f36 ?v0)) (?v_1 (f6 f7 ?v1))) (=> (= (f13 ?v_0 (f4 ?v_1 f8)) f1) (=> (= (f13 ?v_0 ?v2) f1) (= (f13 ?v_0 (f4 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f35 f36 ?v0)) (?v_1 (f6 f7 ?v1))) (=> (= (f13 ?v_0 (f4 ?v_1 ?v2)) f1) (and (= (f13 ?v_0 (f4 ?v_1 f8)) f1) (= (f13 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S2) (?v2 S12) (?v3 S23) (?v4 S12)) (let ((?v_0 (f35 f36 ?v1))) (=> (=> (= ?v0 f1) (= (f13 ?v_0 (f4 (f6 f7 (f38 (f39 (f40 f41 ?v2) ?v3) ?v4)) f8)) f1)) (= (f13 ?v_0 (f4 (f6 f7 (f38 (f39 (f40 f41 (f29 (f30 f31 ?v0) ?v2)) ?v3) ?v4)) f8)) f1)))))
(assert (forall ((?v0 S12) (?v1 S2) (?v2 S23) (?v3 S12)) (=> (forall ((?v4 S10) (?v5 S9)) (=> (= (f19 (f20 ?v0 ?v4) ?v5) f1) (= (f13 (f35 f36 ?v1) (f4 (f6 f7 (f38 (f39 (f40 f41 (f21 f22 ?v5)) ?v2) (f23 (f24 f25 ?v3) ?v4))) f8)) f1))) (= (f13 (f35 f36 ?v1) (f4 (f6 f7 (f38 (f39 (f40 f41 ?v0) ?v2) ?v3)) f8)) f1))))
(assert (forall ((?v0 S2) (?v1 S12) (?v2 S23) (?v3 S12) (?v4 S12)) (let ((?v_0 (f35 f36 ?v0)) (?v_1 (f39 (f40 f41 ?v1) ?v2))) (=> (= (f13 ?v_0 (f4 (f6 f7 (f38 ?v_1 ?v3)) f8)) f1) (=> (forall ((?v5 S10) (?v6 S9)) (=> (= (f19 (f20 ?v3 ?v5) ?v6) f1) (= (f19 (f20 ?v4 ?v5) ?v6) f1))) (= (f13 ?v_0 (f4 (f6 f7 (f38 ?v_1 ?v4)) f8)) f1))))))
(assert (forall ((?v0 S2) (?v1 S12) (?v2 S23) (?v3 S12) (?v4 S12)) (let ((?v_0 (f35 f36 ?v0))) (=> (= (f13 ?v_0 (f4 (f6 f7 (f38 (f39 (f40 f41 ?v1) ?v2) ?v3)) f8)) f1) (=> (forall ((?v5 S10) (?v6 S9)) (=> (= (f19 (f20 ?v4 ?v5) ?v6) f1) (= (f19 (f20 ?v1 ?v5) ?v6) f1))) (= (f13 ?v_0 (f4 (f6 f7 (f38 (f39 (f40 f41 ?v4) ?v2) ?v3)) f8)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f14 f15 ?v0))) (=> (= (f13 ?v_0 (f4 (f6 f7 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f13 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f14 f15 ?v0))) (=> (=> (not (= (f13 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f13 ?v_0 (f4 (f6 f7 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3)) (=> (= (f13 (f14 f15 ?v0) f8) f1) false)))
(assert (forall ((?v0 S2) (?v1 S12) (?v2 S23) (?v3 S12) (?v4 S12) (?v5 S12)) (let ((?v_0 (f35 f36 ?v0))) (=> (= (f13 ?v_0 (f4 (f6 f7 (f38 (f39 (f40 f41 ?v1) ?v2) ?v3)) f8)) f1) (=> (forall ((?v6 S10) (?v7 S9)) (=> (= (f19 (f20 ?v4 ?v6) ?v7) f1) (forall ((?v8 S9)) (=> (forall ((?v9 S10)) (=> (= (f19 (f20 ?v1 ?v9) ?v7) f1) (= (f19 (f20 ?v3 ?v9) ?v8) f1))) (= (f19 (f20 ?v5 ?v6) ?v8) f1))))) (= (f13 ?v_0 (f4 (f6 f7 (f38 (f39 (f40 f41 ?v4) ?v2) ?v5)) f8)) f1))))))
(assert (forall ((?v0 S3)) (= (f4 f44 (f9 f10 ?v0)) (f4 (f6 f7 ?v0) f8))))
(assert (forall ((?v0 S3)) (= (f4 f44 (f9 f11 ?v0)) (f4 (f6 f7 ?v0) f8))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f4 f44 (f4 (f6 f16 ?v0) ?v1)) (ite (= (f3 ?v1 ?v0) f1) (f4 (f6 f7 ?v0) f8) f8))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f4 f44 (f4 (f6 f17 ?v0) ?v1)) (ite (= (f3 ?v1 ?v0) f1) (f4 (f6 f7 ?v0) f8) f8))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= ?v0 f8) (not (= (f13 (f14 f15 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (= (f4 f44 ?v0) f8) (forall ((?v1 S3)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (= (f13 (f14 f15 ?v0) f8) f1) false)))
(assert (forall ((?v0 S2)) (= (= f8 (f4 f44 ?v0)) (forall ((?v1 S3)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (forall ((?v1 S3)) (=> (= (f13 (f14 f15 ?v1) f8) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S2)) (= (exists ((?v1 S3)) (and (= (f13 (f14 f15 ?v1) f8) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S2)) (= (exists ((?v1 S3)) (= (f13 (f14 f15 ?v1) ?v0) f1)) (not (= ?v0 f8)))))
(assert (forall ((?v0 S2)) (= (forall ((?v1 S3)) (not (= (f13 (f14 f15 ?v1) ?v0) f1))) (= ?v0 f8))))
(assert (= f8 (f4 f44 f34)))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f13 (f14 f15 ?v0) ?v1) f1) (= (f4 (f6 f7 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f14 f15 ?v0))) (=> (= (f13 ?v_0 ?v1) f1) (= (f13 ?v_0 (f4 (f6 f7 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f14 f15 ?v0)) (?v_1 (f6 f7 ?v0))) (=> (not (= (f13 ?v_0 ?v1) f1)) (=> (not (= (f13 ?v_0 ?v2) f1)) (= (= (f4 ?v_1 ?v1) (f4 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f6 f7 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f14 f15 ?v0))) (= (= (f13 ?v_0 (f4 (f6 f7 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f13 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_1 (f6 f7 ?v0)) (?v_0 (f6 f7 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S2)) (let ((?v_0 (f6 f7 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f4 (f6 f7 ?v0) (f4 f44 ?v1)) (f4 f44 (f4 (f6 f18 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f4 (f6 f7 ?v0) ?v1) (f4 f44 (f4 (f6 f12 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f13 (f14 f15 ?v0) (f4 (f6 f7 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f4 (f6 f7 ?v0) ?v1) (f4 f44 (f4 (f6 f12 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f4 (f6 f7 ?v0) f8) (f4 (f6 f7 ?v1) f8)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f13 (f14 f15 ?v0) (f4 (f6 f7 ?v1) f8)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (= (f4 (f6 f7 ?v0) (f4 (f6 f7 ?v1) f8)) (f4 (f6 f7 ?v2) (f4 (f6 f7 ?v3) f8))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f13 (f14 f15 ?v0) (f4 (f6 f7 ?v1) f8)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S2)) (not (= (f4 (f6 f7 ?v0) ?v1) f8))))
(assert (forall ((?v0 S3) (?v1 S2)) (not (= f8 (f4 (f6 f7 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f45 f46 (f4 (f6 f7 ?v0) f8)) ?v0)))
(assert (forall ((?v0 S3)) (= (= (f3 f8 ?v0) f1) (= f47 f1))))
(assert (forall ((?v0 S3)) (= (= (f3 f8 ?v0) f1) (= f47 f1))))
(assert (forall ((?v0 S2) (?v1 S12)) (= (f13 (f35 f36 ?v0) (f4 (f6 f7 (f38 (f39 (f40 f41 ?v1) f48) ?v1)) f8)) f1)))
(assert (forall ((?v0 S2) (?v1 S12) (?v2 S11) (?v3 S23)) (= (f13 (f35 f36 ?v0) (f4 (f6 f7 (f38 (f39 (f40 f41 (f26 (f27 f28 ?v1) ?v2)) (f49 (f50 f51 ?v2) ?v3)) ?v1)) f8)) f1)))
(assert (forall ((?v0 S2) (?v1 S12) (?v2 S23) (?v3 S12) (?v4 S23) (?v5 S12)) (let ((?v_0 (f35 f36 ?v0)) (?v_1 (f40 f41 ?v1))) (=> (= (f13 ?v_0 (f4 (f6 f7 (f38 (f39 ?v_1 ?v2) ?v3)) f8)) f1) (=> (= (f13 ?v_0 (f4 (f6 f7 (f38 (f39 (f40 f41 ?v3) ?v4) ?v5)) f8)) f1) (= (f13 ?v_0 (f4 (f6 f7 (f38 (f39 ?v_1 (f49 (f52 f53 ?v2) ?v4)) ?v5)) f8)) f1))))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S12) (?v2 S23) (?v3 S12)) (=> (= ?v0 (f38 (f39 (f40 f41 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f13 (f14 f15 ?v0) ?v1) f1) (=> (forall ((?v2 S2)) (=> (= ?v1 (f4 (f6 f7 ?v0) ?v2)) (=> (not (= (f13 (f14 f15 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f13 (f14 f15 ?v0) ?v1) f1) (exists ((?v2 S2)) (and (= ?v1 (f4 (f6 f7 ?v0) ?v2)) (not (= (f13 (f14 f15 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S23) (?v1 S23)) (not (= (f49 (f52 f53 ?v0) ?v1) f48))))
(assert (forall ((?v0 S23) (?v1 S23)) (not (= f48 (f49 (f52 f53 ?v0) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S23)) (not (= (f49 (f50 f51 ?v0) ?v1) f48))))
(assert (forall ((?v0 S11) (?v1 S23)) (not (= f48 (f49 (f50 f51 ?v0) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S23) (?v2 S23) (?v3 S23)) (not (= (f49 (f50 f51 ?v0) ?v1) (f49 (f52 f53 ?v2) ?v3)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S11) (?v3 S23)) (not (= (f49 (f52 f53 ?v0) ?v1) (f49 (f50 f51 ?v2) ?v3)))))
(assert (forall ((?v0 S2)) (= (f45 f46 ?v0) (f45 f54 (f4 f5 ?v0)))))
(assert (forall ((?v0 S11) (?v1 S23) (?v2 S11) (?v3 S23)) (= (= (f49 (f50 f51 ?v0) ?v1) (f49 (f50 f51 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(check-sat)
(exit)