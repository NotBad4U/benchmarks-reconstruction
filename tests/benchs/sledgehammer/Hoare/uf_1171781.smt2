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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S3) S3)
(declare-fun f5 (S2) S4)
(declare-fun f6 (S5 S3) S1)
(declare-fun f7 (S2) S5)
(declare-fun f8 (S3) S4)
(declare-fun f9 (S2) S4)
(declare-fun f10 () S3)
(declare-fun f11 (S3) S5)
(declare-fun f12 () S3)
(declare-fun f13 (S2) S4)
(declare-fun f14 (S6 S7) S2)
(declare-fun f15 (S8 S9) S6)
(declare-fun f16 (S10 S7) S8)
(declare-fun f17 () S10)
(declare-fun f18 () S7)
(declare-fun f19 () S9)
(declare-fun f20 () S7)
(declare-fun f21 () S3)
(declare-fun f22 (S11 S12) S1)
(declare-fun f23 (S11 S12) S1)
(declare-fun f24 (S13 S12) S1)
(declare-fun f25 (S7 S11) S13)
(declare-fun f26 (S3) S3)
(declare-fun f27 (S14 S3) S2)
(declare-fun f28 () S14)
(declare-fun f29 () S1)
(declare-fun f30 (S15 S9) S9)
(declare-fun f31 (S16 S9) S15)
(declare-fun f32 () S16)
(declare-fun f33 (S17) S4)
(declare-fun f34 (S17 S14) S1)
(declare-fun f35 (S3) S5)
(declare-fun f36 (S18 S17) S14)
(declare-fun f37 () S18)
(declare-fun f38 (S19 S2) S4)
(declare-fun f39 (S17) S19)
(declare-fun f40 (S3) S1)
(declare-fun f41 (S20 S2) S2)
(declare-fun f42 (S17 S2) S20)
(declare-fun f43 (S21) S3)
(declare-fun f44 (S17 S14) S1)
(declare-fun f45 (S17 S14) S1)
(declare-fun f46 (S3) S4)
(declare-fun f47 (S1 S1) S1)
(declare-fun f48 (S17) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f6 (f7 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v2))) (= (= (f3 (f4 (f8 ?v0) ?v1) ?v2) f1) (and (= (f6 ?v_0 ?v0) f1) (not (= (f6 ?v_0 ?v1) f1)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f9 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f10 ?v0) f1) false)))
(assert (not (= (f6 (f11 f12) (f4 (f13 (f14 (f15 (f16 f17 f18) f19) f20)) f21)) f1)))
(assert (forall ((?v0 S11) (?v1 S12)) (=> (= (f22 ?v0 ?v1) f1) (= (f23 ?v0 ?v1) f1))))
(assert (forall ((?v0 S3)) (= (f6 (f11 ?v0) f21) f1)))
(assert (forall ((?v0 S3) (?v1 S7)) (= (f6 (f11 ?v0) (f4 (f13 (f14 (f15 (f16 f17 ?v1) f19) ?v1)) f21)) f1)))
(assert (forall ((?v0 S7) (?v1 S9) (?v2 S7) (?v3 S7) (?v4 S9) (?v5 S7)) (= (= (f14 (f15 (f16 f17 ?v0) ?v1) ?v2) (f14 (f15 (f16 f17 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f11 ?v2))) (=> (= (f6 (f11 ?v0) ?v1) f1) (=> (= (f6 ?v_0 ?v0) f1) (= (f6 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f11 ?v0)) (?v_1 (f13 ?v1))) (=> (= (f6 ?v_0 (f4 ?v_1 f21)) f1) (=> (= (f6 ?v_0 ?v2) f1) (= (f6 ?v_0 (f4 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f11 ?v0)) (?v_1 (f13 ?v1))) (=> (= (f6 ?v_0 (f4 ?v_1 ?v2)) f1) (and (= (f6 ?v_0 (f4 ?v_1 f21)) f1) (= (f6 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S7)) (let ((?v_0 (f11 ?v0)) (?v_1 (f15 (f16 f17 ?v1) ?v2))) (=> (= (f6 ?v_0 (f4 (f13 (f14 ?v_1 ?v3)) f21)) f1) (=> (forall ((?v5 S11) (?v6 S12)) (=> (= (f24 (f25 ?v3 ?v5) ?v6) f1) (= (f24 (f25 ?v4 ?v5) ?v6) f1))) (= (f6 ?v_0 (f4 (f13 (f14 ?v_1 ?v4)) f21)) f1))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S7)) (let ((?v_0 (f11 ?v0))) (=> (= (f6 ?v_0 (f4 (f13 (f14 (f15 (f16 f17 ?v1) ?v2) ?v3)) f21)) f1) (=> (forall ((?v5 S11) (?v6 S12)) (=> (= (f24 (f25 ?v4 ?v5) ?v6) f1) (= (f24 (f25 ?v1 ?v5) ?v6) f1))) (= (f6 ?v_0 (f4 (f13 (f14 (f15 (f16 f17 ?v4) ?v2) ?v3)) f21)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f13 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f6 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v0))) (=> (=> (not (= (f6 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f6 ?v_0 (f4 (f13 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f6 (f7 ?v0) f21) f1) false)))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S7) (?v5 S7)) (let ((?v_0 (f11 ?v0))) (=> (= (f6 ?v_0 (f4 (f13 (f14 (f15 (f16 f17 ?v1) ?v2) ?v3)) f21)) f1) (=> (forall ((?v6 S11) (?v7 S12)) (=> (= (f24 (f25 ?v4 ?v6) ?v7) f1) (forall ((?v8 S12)) (=> (forall ((?v9 S11)) (=> (= (f24 (f25 ?v1 ?v9) ?v7) f1) (= (f24 (f25 ?v3 ?v9) ?v8) f1))) (= (f24 (f25 ?v5 ?v6) ?v8) f1))))) (= (f6 ?v_0 (f4 (f13 (f14 (f15 (f16 f17 ?v4) ?v2) ?v5)) f21)) f1))))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f21 (f4 (f13 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f4 (f13 ?v0) ?v1) f21))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f6 (f7 ?v0) (f4 (f13 ?v1) f21)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f4 (f13 ?v0) (f4 (f13 ?v1) f21)) (f4 (f13 ?v2) (f4 (f13 ?v3) f21))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f21) (not (= (f6 (f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f26 ?v0) f21) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f6 (f7 ?v0) f21) f1) false)))
(assert (forall ((?v0 S3)) (= (= f21 (f26 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f6 (f7 ?v1) f21) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f6 (f7 ?v1) f21) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f6 (f7 ?v1) ?v0) f1)) (not (= ?v0 f21)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f6 (f7 ?v1) ?v0) f1))) (= ?v0 f21))))
(assert (= f21 (f26 f10)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (= (f4 (f13 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 ?v1) f1) (= (f6 ?v_0 (f4 (f13 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0)) (?v_1 (f13 ?v0))) (=> (not (= (f6 ?v_0 ?v1) f1)) (=> (not (= (f6 ?v_0 ?v2) f1)) (= (= (f4 ?v_1 ?v1) (f4 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f13 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (= (= (f6 ?v_0 (f4 (f13 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f6 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f13 ?v0)) (?v_0 (f13 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f13 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f13 ?v0) (f26 ?v1)) (f26 (f4 (f9 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f13 ?v0) ?v1) (f26 (f4 (f5 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f6 (f7 ?v0) (f4 (f13 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f13 ?v0) f21) (f4 (f13 ?v1) f21)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f6 (f7 ?v0) (f4 (f13 ?v1) f21)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2)) (= (f27 f28 (f4 (f13 ?v0) f21)) ?v0)))
(assert (forall ((?v0 S2)) (= (= (f3 f21 ?v0) f1) (= f29 f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f21 ?v0) f1) (= f29 f1))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S9) (?v3 S7) (?v4 S9) (?v5 S7)) (let ((?v_0 (f11 ?v0)) (?v_1 (f16 f17 ?v1))) (=> (= (f6 ?v_0 (f4 (f13 (f14 (f15 ?v_1 ?v2) ?v3)) f21)) f1) (=> (= (f6 ?v_0 (f4 (f13 (f14 (f15 (f16 f17 ?v3) ?v4) ?v5)) f21)) f1) (= (f6 ?v_0 (f4 (f13 (f14 (f15 ?v_1 (f30 (f31 f32 ?v2) ?v4)) ?v5)) f21)) f1))))))
(assert (forall ((?v0 S2)) (=> (forall ((?v1 S7) (?v2 S9) (?v3 S7)) (=> (= ?v0 (f14 (f15 (f16 f17 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (=> (forall ((?v2 S3)) (=> (= ?v1 (f4 (f13 ?v0) ?v2)) (=> (not (= (f6 (f7 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (exists ((?v2 S3)) (and (= ?v1 (f4 (f13 ?v0) ?v2)) (not (= (f6 (f7 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2)) (=> (= (f6 (f7 ?v1) ?v0) f1) false)) (= ?v0 f21))))
(assert (forall ((?v0 S7) (?v1 S3) (?v2 S9) (?v3 S7)) (=> (forall ((?v4 S11) (?v5 S12)) (=> (= (f24 (f25 ?v0 ?v4) ?v5) f1) (exists ((?v6 S7) (?v7 S7)) (and (= (f6 (f11 ?v1) (f4 (f13 (f14 (f15 (f16 f17 ?v6) ?v2) ?v7)) f21)) f1) (forall ((?v8 S12)) (=> (forall ((?v9 S11)) (=> (= (f24 (f25 ?v6 ?v9) ?v5) f1) (= (f24 (f25 ?v7 ?v9) ?v8) f1))) (= (f24 (f25 ?v3 ?v4) ?v8) f1))))))) (= (f6 (f11 ?v1) (f4 (f13 (f14 (f15 (f16 f17 ?v0) ?v2) ?v3)) f21)) f1))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f21)) (exists ((?v1 S2) (?v2 S3)) (and (= ?v0 (f4 (f13 ?v1) ?v2)) (not (= (f6 (f7 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S9) (?v1 S9)) (not (= f19 (f30 (f31 f32 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (not (= (f30 (f31 f32 ?v0) ?v1) f19))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (= (= (f30 (f31 f32 ?v0) ?v1) (f30 (f31 f32 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f33 ?v0) (f4 (f13 ?v1) f21)) ?v2) f1) (= ?v1 ?v2))))
(assert (forall ((?v0 S17) (?v1 S14) (?v2 S2)) (=> (= (f34 ?v0 ?v1) f1) (= (f27 ?v1 (f4 (f13 ?v2) f21)) ?v2))))
(assert (forall ((?v0 S2)) (= (= (f3 f21 ?v0) f1) (= (f6 (f7 ?v0) f21) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f6 (f11 ?v0) ?v1) f1) (= (f6 (f35 ?v0) ?v1) f1))))
(assert (forall ((?v0 S17) (?v1 S2)) (= (f27 (f36 f37 ?v0) (f4 (f13 ?v1) f21)) ?v1)))
(assert (forall ((?v0 S17) (?v1 S3) (?v2 S2)) (=> (= (f3 (f4 (f33 ?v0) ?v1) ?v2) f1) (not (= ?v1 f21)))))
(assert (forall ((?v0 S17) (?v1 S2)) (=> (= (f3 (f4 (f33 ?v0) f21) ?v1) f1) false)))
(assert (forall ((?v0 S14) (?v1 S17) (?v2 S2)) (=> (= ?v0 (f36 f37 ?v1)) (= (f27 ?v0 (f4 (f13 ?v2) f21)) ?v2))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S3) (?v3 S2)) (=> (= (f3 (f4 (f38 (f39 ?v0) ?v1) ?v2) ?v3) f1) (=> (not (= (f6 (f7 ?v1) ?v2) f1)) (= (f3 (f4 (f33 ?v0) (f4 (f13 ?v1) ?v2)) ?v3) f1)))))
(assert (forall ((?v0 S17) (?v1 S14) (?v2 S3) (?v3 S2)) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f40 ?v2) f1) (=> (not (= (f6 (f7 ?v3) ?v2) f1)) (=> (not (= ?v2 f21)) (= (f27 ?v1 (f4 (f13 ?v3) ?v2)) (f41 (f42 ?v0 ?v3) (f27 ?v1 ?v2)))))))))
(assert (forall ((?v0 S17) (?v1 S14) (?v2 S3)) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f40 ?v2) f1) (= (f27 ?v1 ?v2) (f27 (f36 f37 ?v0) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 (f35 ?v0) ?v1) f1) (forall ((?v2 S21)) (=> (forall ((?v3 S2)) (=> (= (f6 (f7 ?v3) ?v0) f1) (= (f3 (f43 ?v2) ?v3) f1))) (forall ((?v3 S2)) (=> (= (f6 (f7 ?v3) ?v1) f1) (= (f3 (f43 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S17) (?v1 S14) (?v2 S3)) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f40 ?v2) f1) (=> (not (= ?v2 f21)) (=> (forall ((?v3 S2) (?v4 S2)) (= (f6 (f7 (f41 (f42 ?v0 ?v3) ?v4)) (f4 (f13 ?v3) (f4 (f13 ?v4) f21))) f1)) (= (f6 (f7 (f27 ?v1 ?v2)) ?v2) f1)))))))
(assert (= (f40 f21) f1))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f40 ?v0) f1) (= (f40 (f4 (f13 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f40 (f4 (f13 ?v0) ?v1)) f1) (= (f40 ?v1) f1))))
(assert (forall ((?v0 S17) (?v1 S2)) (= (f3 (f4 (f38 (f39 ?v0) ?v1) f21) ?v1) f1)))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 (f38 (f39 ?v0) ?v1) f21) ?v2) f1) (=> (=> (= ?v2 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S17) (?v3 S2) (?v4 S2)) (let ((?v_0 (f38 (f39 ?v2) ?v3))) (=> (not (= (f6 (f7 ?v0) ?v1) f1)) (=> (= (f3 (f4 ?v_0 ?v1) ?v4) f1) (= (f3 (f4 ?v_0 (f4 (f13 ?v0) ?v1)) (f41 (f42 ?v2 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f6 (f7 ?v0) ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f26 ?v0) ?v0)))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S3) (?v3 S2)) (=> (= (f3 (f4 (f33 ?v0) (f4 (f13 ?v1) ?v2)) ?v3) f1) (=> (forall ((?v4 S2) (?v5 S3)) (=> (= (f4 (f13 ?v1) ?v2) (f4 (f13 ?v4) ?v5)) (=> (= (f3 (f4 (f38 (f39 ?v0) ?v4) ?v5) ?v3) f1) (=> (not (= (f6 (f7 ?v4) ?v5) f1)) false)))) false))))
(assert (forall ((?v0 S3) (?v1 S17)) (=> (= (f40 ?v0) f1) (=> (not (= ?v0 f21)) (exists ((?v2 S2)) (= (f3 (f4 (f33 ?v1) ?v0) ?v2) f1))))))
(assert (forall ((?v0 S3)) (= (= (f40 ?v0) f1) (or (= ?v0 f21) (exists ((?v1 S3) (?v2 S2)) (and (= ?v0 (f4 (f13 ?v2) ?v1)) (= (f40 ?v1) f1)))))))
(assert (forall ((?v0 S3) (?v1 S5)) (=> (= (f40 ?v0) f1) (=> (= (f6 ?v1 f21) f1) (=> (forall ((?v2 S2) (?v3 S3)) (=> (= (f40 ?v3) f1) (=> (not (= (f6 (f7 ?v2) ?v3) f1)) (=> (= (f6 ?v1 ?v3) f1) (= (f6 ?v1 (f4 (f13 ?v2) ?v3)) f1))))) (= (f6 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S17) (?v2 S2)) (=> (= (f40 ?v0) f1) (exists ((?v3 S2)) (= (f3 (f4 (f38 (f39 ?v1) ?v2) ?v0) ?v3) f1)))))
(assert (forall ((?v0 S17) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f33 ?v0) ?v1) ?v2) f1) (exists ((?v3 S2) (?v4 S3) (?v5 S2)) (and (= ?v1 (f4 (f13 ?v3) ?v4)) (and (= ?v2 ?v5) (and (= (f3 (f4 (f38 (f39 ?v0) ?v3) ?v4) ?v5) f1) (not (= (f6 (f7 ?v3) ?v4) f1)))))))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S3) (?v3 S2)) (= (= (f3 (f4 (f38 (f39 ?v0) ?v1) ?v2) ?v3) f1) (or (and (= ?v2 f21) (= ?v3 ?v1)) (exists ((?v4 S2) (?v5 S3) (?v6 S2)) (and (= ?v2 (f4 (f13 ?v4) ?v5)) (and (= ?v3 (f41 (f42 ?v0 ?v4) ?v6)) (and (not (= (f6 (f7 ?v4) ?v5) f1)) (= (f3 (f4 (f38 (f39 ?v0) ?v1) ?v5) ?v6) f1)))))))))
(assert (forall ((?v0 S17) (?v1 S14) (?v2 S3) (?v3 S2)) (=> (= (f44 ?v0 ?v1) f1) (=> (= (f40 ?v2) f1) (=> (not (= ?v2 f21)) (= (f27 ?v1 (f4 (f13 ?v3) ?v2)) (f41 (f42 ?v0 ?v3) (f27 ?v1 ?v2))))))))
(assert (forall ((?v0 S3) (?v1 S5)) (=> (= (f40 ?v0) f1) (=> (not (= ?v0 f21)) (=> (forall ((?v2 S2)) (= (f6 ?v1 (f4 (f13 ?v2) f21)) f1)) (=> (forall ((?v2 S2) (?v3 S3)) (=> (= (f40 ?v3) f1) (=> (not (= ?v3 f21)) (=> (not (= (f6 (f7 ?v2) ?v3) f1)) (=> (= (f6 ?v1 ?v3) f1) (= (f6 ?v1 (f4 (f13 ?v2) ?v3)) f1)))))) (= (f6 ?v1 ?v0) f1)))))))
(assert (forall ((?v0 S17) (?v1 S14) (?v2 S3)) (=> (= (f45 ?v0 ?v1) f1) (=> (= (f40 ?v2) f1) (= (f27 ?v1 ?v2) (f27 (f36 f37 ?v0) ?v2))))))
(assert (forall ((?v0 S17) (?v1 S14) (?v2 S3) (?v3 S2)) (let ((?v_0 (f13 ?v3))) (let ((?v_1 (f4 (f46 ?v2) (f4 ?v_0 f21)))) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f40 ?v2) f1) (= (f27 ?v1 (f4 ?v_0 ?v2)) (ite (= ?v_1 f21) ?v3 (f41 (f42 ?v0 ?v3) (f27 ?v1 ?v_1))))))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 ?v1) f1) (=> (not (= (f6 ?v_0 ?v2) f1)) (= (f6 ?v_0 (f4 (f46 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f46 ?v1) ?v2)) f1) (=> (=> (= (f6 ?v_0 ?v1) f1) (=> (not (= (f6 ?v_0 ?v2) f1)) false)) false)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f40 ?v0) f1) (= (f40 (f4 (f46 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f4 (f46 ?v0) ?v1) (f26 (f4 (f8 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (= (= (f6 ?v_0 (f4 (f46 ?v1) ?v2)) f1) (and (= (f6 ?v_0 ?v1) f1) (not (= (f6 ?v_0 ?v2) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 (f46 ?v0) ?v1))) (= (f4 (f46 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f46 ?v1) ?v2)) f1) (= (f6 ?v_0 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f46 ?v1) ?v2)) f1) (=> (= (f6 ?v_0 ?v2) f1) false)))))
(assert (forall ((?v0 S17) (?v1 S14) (?v2 S2)) (=> (= (f44 ?v0 ?v1) f1) (= (f41 (f42 ?v0 ?v2) ?v2) ?v2))))
(assert (forall ((?v0 S3)) (= (f4 (f46 f21) ?v0) f21)))
(assert (forall ((?v0 S3)) (= (f4 (f46 ?v0) f21) ?v0)))
(assert (forall ((?v0 S3)) (= (f4 (f46 ?v0) ?v0) f21)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f40 ?v0) f1) (= (= (f40 (f4 (f46 ?v1) ?v0)) f1) (= (f40 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f13 ?v0)) (?v_1 (f4 (f46 ?v1) ?v2))) (= (f4 (f46 (f4 ?v_0 ?v1)) ?v2) (ite (= (f6 (f7 ?v0) ?v2) f1) ?v_1 (f4 ?v_0 ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (= (f4 (f46 (f4 (f13 ?v0) ?v2)) ?v1) (f4 (f46 ?v2) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f46 ?v0)) (?v_1 (f13 ?v1))) (= (f4 ?v_0 (f4 ?v_1 ?v2)) (f4 (f46 (f4 ?v_0 ?v2)) (f4 ?v_1 f21))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f46 ?v0)) (?v_1 (f13 ?v1))) (= (f4 ?v_0 (f4 ?v_1 ?v2)) (f4 (f46 (f4 ?v_0 (f4 ?v_1 f21))) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f13 ?v0))) (= (f4 ?v_0 (f4 (f46 ?v1) (f4 ?v_0 f21))) (f4 ?v_0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f13 ?v0))) (=> (not (= (f6 (f7 ?v0) ?v1) f1)) (= (f4 (f46 (f4 ?v_0 ?v1)) (f4 ?v_0 f21)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f13 ?v0))) (=> (= (f6 (f7 ?v0) ?v1) f1) (= (f4 ?v_0 (f4 (f46 ?v1) (f4 ?v_0 f21))) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f46 ?v0))) (= (= (f40 (f4 ?v_0 (f4 (f13 ?v1) ?v2))) f1) (= (f40 (f4 ?v_0 ?v2)) f1)))))
(assert (forall ((?v0 S17) (?v1 S14) (?v2 S3) (?v3 S2)) (let ((?v_0 (f27 ?v1 ?v2))) (=> (= (f44 ?v0 ?v1) f1) (=> (= (f40 ?v2) f1) (=> (= (f6 (f7 ?v3) ?v2) f1) (= (f41 (f42 ?v0 ?v3) ?v_0) ?v_0)))))))
(assert (forall ((?v0 S17) (?v1 S14) (?v2 S3) (?v3 S2)) (let ((?v_0 (f4 (f46 ?v2) (f4 (f13 ?v3) f21)))) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f40 ?v2) f1) (=> (= (f6 (f7 ?v3) ?v2) f1) (= (f27 ?v1 ?v2) (ite (= ?v_0 f21) ?v3 (f41 (f42 ?v0 ?v3) (f27 ?v1 ?v_0))))))))))
(assert (forall ((?v0 S3) (?v1 S5)) (=> (= (f40 ?v0) f1) (=> (= (f6 ?v1 ?v0) f1) (=> (forall ((?v2 S2) (?v3 S3)) (=> (= (f40 ?v3) f1) (=> (= (f6 (f7 ?v2) ?v3) f1) (=> (= (f6 ?v1 ?v3) f1) (= (f6 ?v1 (f4 (f46 ?v3) (f4 (f13 ?v2) f21))) f1))))) (= (f6 ?v1 f21) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f46 ?v0) ?v1) ?v2) f1) (= (f47 (f3 ?v0 ?v2) (f3 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f46 ?v0) ?v1) ?v2) f1) (= (f47 (f3 ?v0 ?v2) (f3 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S3) (?v3 S2) (?v4 S2)) (=> (= (f48 ?v0) f1) (=> (= (f3 (f4 (f38 (f39 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f6 (f7 ?v4) ?v2) f1) (exists ((?v5 S2)) (and (= ?v3 (f41 (f42 ?v0 ?v4) ?v5)) (= (f3 (f4 (f38 (f39 ?v0) ?v1) (f4 (f46 ?v2) (f4 (f13 ?v4) f21))) ?v5) f1))))))))
(check-sat)
(exit)