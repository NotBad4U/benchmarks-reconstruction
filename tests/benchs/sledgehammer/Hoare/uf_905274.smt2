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
(declare-fun f11 (S7 S6) S1)
(declare-fun f12 (S8 S6) S7)
(declare-fun f13 () S8)
(declare-fun f14 (S9 S6) S7)
(declare-fun f15 () S9)
(declare-fun f16 () S8)
(declare-fun f17 (S3) S5)
(declare-fun f18 () S3)
(declare-fun f19 (S2) S4)
(declare-fun f20 (S10 S8) S2)
(declare-fun f21 (S11 S9) S10)
(declare-fun f22 (S12 S8) S11)
(declare-fun f23 () S12)
(declare-fun f24 () S1)
(declare-fun f25 (S3) S3)
(declare-fun f26 (S13 S3) S2)
(declare-fun f27 () S13)
(declare-fun f28 (S14) S3)
(declare-fun f29 (S3) S5)
(declare-fun f30 () S9)
(declare-fun f31 (S15 S9) S9)
(declare-fun f32 (S16 S9) S15)
(declare-fun f33 () S16)
(declare-fun f34 (S17) S4)
(declare-fun f35 (S17 S13) S1)
(declare-fun f36 (S9 S6 S14 S6) S1)
(declare-fun f37 (S18 S17) S13)
(declare-fun f38 () S18)
(declare-fun f39 (S19 S2) S4)
(declare-fun f40 (S17) S19)
(declare-fun f41 (S20 S2) S2)
(declare-fun f42 (S17 S2) S20)
(declare-fun f43 (S3) S1)
(declare-fun f44 (S17 S13) S1)
(declare-fun f45 (S17 S13) S1)
(declare-fun f46 (S3) S4)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f6 (f7 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v2))) (= (= (f3 (f4 (f8 ?v0) ?v1) ?v2) f1) (and (= (f6 ?v_0 ?v0) f1) (not (= (f6 ?v_0 ?v1) f1)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f9 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f10 ?v0) f1) false)))
(assert (not (forall ((?v0 S6) (?v1 S6)) (=> (= (f11 (f12 f13 ?v0) ?v1) f1) (forall ((?v2 S6)) (=> (forall ((?v3 S6)) (=> (= ?v3 ?v1) (= (f11 (f14 f15 ?v3) ?v2) f1))) (= (f11 (f12 f16 ?v0) ?v2) f1)))))))
(assert (= (f6 (f17 f18) (f4 (f19 (f20 (f21 (f22 f23 f13) f15) f16)) f18)) f1))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S8) (?v3 S8) (?v4 S9) (?v5 S8)) (= (= (f20 (f21 (f22 f23 ?v0) ?v1) ?v2) (f20 (f21 (f22 f23 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f19 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f6 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v0))) (=> (=> (not (= (f6 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f6 ?v_0 (f4 (f19 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f6 (f7 ?v0) f18) f1) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f18 (f4 (f19 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f4 (f19 ?v0) ?v1) f18))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f6 (f7 ?v0) (f4 (f19 ?v1) f18)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f4 (f19 ?v0) (f4 (f19 ?v1) f18)) (f4 (f19 ?v2) (f4 (f19 ?v3) f18))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f6 (f7 ?v0) (f4 (f19 ?v1) f18)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f19 ?v0) f18) (f4 (f19 ?v1) f18)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2)) (= (= (f3 f18 ?v0) f1) (= f24 f1))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f18) (not (= (f6 (f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f25 ?v0) f18) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f6 (f7 ?v0) f18) f1) false)))
(assert (forall ((?v0 S3)) (= (= f18 (f25 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f6 (f7 ?v1) f18) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f6 (f7 ?v1) f18) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f6 (f7 ?v1) ?v0) f1)) (not (= ?v0 f18)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f6 (f7 ?v1) ?v0) f1))) (= ?v0 f18))))
(assert (= f18 (f25 f10)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (= (f4 (f19 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 ?v1) f1) (= (f6 ?v_0 (f4 (f19 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0)) (?v_1 (f19 ?v0))) (=> (not (= (f6 ?v_0 ?v1) f1)) (=> (not (= (f6 ?v_0 ?v2) f1)) (= (= (f4 ?v_1 ?v1) (f4 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f19 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (= (= (f6 ?v_0 (f4 (f19 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f6 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f19 ?v0)) (?v_0 (f19 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f19 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f19 ?v0) (f25 ?v1)) (f25 (f4 (f9 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f19 ?v0) ?v1) (f25 (f4 (f5 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f6 (f7 ?v0) (f4 (f19 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2)) (= (= (f3 f18 ?v0) f1) (= f24 f1))))
(assert (forall ((?v0 S2)) (= (f26 f27 (f4 (f19 ?v0) f18)) ?v0)))
(assert (forall ((?v0 S2)) (=> (forall ((?v1 S8) (?v2 S9) (?v3 S8)) (=> (= ?v0 (f20 (f21 (f22 f23 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (=> (forall ((?v2 S3)) (=> (= ?v1 (f4 (f19 ?v0) ?v2)) (=> (not (= (f6 (f7 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (exists ((?v2 S3)) (and (= ?v1 (f4 (f19 ?v0) ?v2)) (not (= (f6 (f7 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2)) (=> (= (f6 (f7 ?v1) ?v0) f1) false)) (= ?v0 f18))))
(assert (forall ((?v0 S9) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f14 ?v0 ?v1))) (=> (= (f11 ?v_0 ?v2) f1) (=> (= (f11 ?v_0 ?v3) f1) (= ?v3 ?v2))))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f18)) (exists ((?v1 S2) (?v2 S3)) (and (= ?v0 (f4 (f19 ?v1) ?v2)) (not (= (f6 (f7 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S2)) (= (= (f3 f18 ?v0) f1) (= (f6 (f7 ?v0) f18) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 (f17 ?v0) ?v1) f1) (forall ((?v2 S14)) (=> (forall ((?v3 S2)) (=> (= (f6 (f7 ?v3) ?v0) f1) (= (f3 (f28 ?v2) ?v3) f1))) (forall ((?v3 S2)) (=> (= (f6 (f7 ?v3) ?v1) f1) (= (f3 (f28 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S9) (?v3 S8) (?v4 S8)) (let ((?v_0 (f29 ?v0))) (=> (= (f6 ?v_0 (f4 (f19 (f20 (f21 (f22 f23 ?v1) ?v2) ?v3)) f18)) f1) (=> (forall ((?v5 S6) (?v6 S6)) (=> (= (f11 (f12 ?v4 ?v5) ?v6) f1) (= (f11 (f12 ?v1 ?v5) ?v6) f1))) (= (f6 ?v_0 (f4 (f19 (f20 (f21 (f22 f23 ?v4) ?v2) ?v3)) f18)) f1))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S9) (?v3 S8) (?v4 S8)) (let ((?v_0 (f29 ?v0)) (?v_1 (f21 (f22 f23 ?v1) ?v2))) (=> (= (f6 ?v_0 (f4 (f19 (f20 ?v_1 ?v3)) f18)) f1) (=> (forall ((?v5 S6) (?v6 S6)) (=> (= (f11 (f12 ?v3 ?v5) ?v6) f1) (= (f11 (f12 ?v4 ?v5) ?v6) f1))) (= (f6 ?v_0 (f4 (f19 (f20 ?v_1 ?v4)) f18)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f29 ?v2))) (=> (= (f6 (f29 ?v0) ?v1) f1) (=> (= (f6 ?v_0 ?v0) f1) (= (f6 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (f6 (f29 ?v0) f18) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f6 (f29 ?v0) ?v1) f1) (= (f6 (f17 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f29 ?v0)) (?v_1 (f19 ?v1))) (=> (= (f6 ?v_0 (f4 ?v_1 f18)) f1) (=> (= (f6 ?v_0 ?v2) f1) (= (f6 ?v_0 (f4 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f29 ?v0)) (?v_1 (f19 ?v1))) (=> (= (f6 ?v_0 (f4 ?v_1 ?v2)) f1) (and (= (f6 ?v_0 (f4 ?v_1 f18)) f1) (= (f6 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S9) (?v3 S8) (?v4 S8) (?v5 S8)) (let ((?v_0 (f29 ?v0))) (=> (= (f6 ?v_0 (f4 (f19 (f20 (f21 (f22 f23 ?v1) ?v2) ?v3)) f18)) f1) (=> (forall ((?v6 S6) (?v7 S6)) (=> (= (f11 (f12 ?v4 ?v6) ?v7) f1) (forall ((?v8 S6)) (=> (forall ((?v9 S6)) (=> (= (f11 (f12 ?v1 ?v9) ?v7) f1) (= (f11 (f12 ?v3 ?v9) ?v8) f1))) (= (f11 (f12 ?v5 ?v6) ?v8) f1))))) (= (f6 ?v_0 (f4 (f19 (f20 (f21 (f22 f23 ?v4) ?v2) ?v5)) f18)) f1))))))
(assert (forall ((?v0 S3) (?v1 S8)) (= (f6 (f29 ?v0) (f4 (f19 (f20 (f21 (f22 f23 ?v1) f30) ?v1)) f18)) f1)))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S9) (?v3 S8) (?v4 S9) (?v5 S8)) (let ((?v_0 (f29 ?v0)) (?v_1 (f22 f23 ?v1))) (=> (= (f6 ?v_0 (f4 (f19 (f20 (f21 ?v_1 ?v2) ?v3)) f18)) f1) (=> (= (f6 ?v_0 (f4 (f19 (f20 (f21 (f22 f23 ?v3) ?v4) ?v5)) f18)) f1) (= (f6 ?v_0 (f4 (f19 (f20 (f21 ?v_1 (f31 (f32 f33 ?v2) ?v4)) ?v5)) f18)) f1))))))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S9) (?v3 S8)) (=> (forall ((?v4 S6) (?v5 S6)) (=> (= (f11 (f12 ?v0 ?v4) ?v5) f1) (exists ((?v6 S8) (?v7 S8)) (and (= (f6 (f29 ?v1) (f4 (f19 (f20 (f21 (f22 f23 ?v6) ?v2) ?v7)) f18)) f1) (forall ((?v8 S6)) (=> (forall ((?v9 S6)) (=> (= (f11 (f12 ?v6 ?v9) ?v5) f1) (= (f11 (f12 ?v7 ?v9) ?v8) f1))) (= (f11 (f12 ?v3 ?v4) ?v8) f1))))))) (= (f6 (f29 ?v1) (f4 (f19 (f20 (f21 (f22 f23 ?v0) ?v2) ?v3)) f18)) f1))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f34 ?v0) (f4 (f19 ?v1) f18)) ?v2) f1) (= ?v1 ?v2))))
(assert (forall ((?v0 S17) (?v1 S13) (?v2 S2)) (=> (= (f35 ?v0 ?v1) f1) (= (f26 ?v1 (f4 (f19 ?v2) f18)) ?v2))))
(assert (forall ((?v0 S14) (?v1 S8) (?v2 S9) (?v3 S8)) (= (= (f3 (f28 ?v0) (f20 (f21 (f22 f23 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S6) (?v5 S6)) (=> (= (f11 (f12 ?v1 ?v4) ?v5) f1) (forall ((?v6 S6)) (=> (= (f36 ?v2 ?v5 ?v0 ?v6) f1) (= (f11 (f12 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S17) (?v1 S2)) (= (f26 (f37 f38 ?v0) (f4 (f19 ?v1) f18)) ?v1)))
(assert (forall ((?v0 S9) (?v1 S6) (?v2 S14) (?v3 S6) (?v4 S9) (?v5 S6)) (=> (= (f36 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f36 ?v4 ?v3 ?v2 ?v5) f1) (= (f36 (f31 (f32 f33 ?v0) ?v4) ?v1 ?v2 ?v5) f1)))))
(assert (forall ((?v0 S6) (?v1 S14) (?v2 S6)) (=> (= (f36 f30 ?v0 ?v1 ?v2) f1) (=> (=> (= ?v2 ?v0) false) false))))
(assert (forall ((?v0 S6) (?v1 S14)) (= (f36 f30 ?v0 ?v1 ?v0) f1)))
(assert (forall ((?v0 S9) (?v1 S6) (?v2 S6) (?v3 S9) (?v4 S6)) (=> (= (f11 (f14 ?v0 ?v1) ?v2) f1) (=> (= (f11 (f14 ?v3 ?v2) ?v4) f1) (= (f11 (f14 (f31 (f32 f33 ?v0) ?v3) ?v1) ?v4) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f11 (f14 f30 ?v0) ?v1) f1) (=> (=> (= ?v1 ?v0) false) false))))
(assert (forall ((?v0 S6)) (= (f11 (f14 f30 ?v0) ?v0) f1)))
(assert (forall ((?v0 S9) (?v1 S6) (?v2 S14) (?v3 S6)) (=> (= (f36 ?v0 ?v1 ?v2 ?v3) f1) (= (f11 (f14 ?v0 ?v1) ?v3) f1))))
(assert (forall ((?v0 S9) (?v1 S6) (?v2 S6)) (= (= (f11 (f14 ?v0 ?v1) ?v2) f1) (exists ((?v3 S14)) (= (f36 ?v0 ?v1 ?v3 ?v2) f1)))))
(assert (forall ((?v0 S17) (?v1 S3) (?v2 S2)) (=> (= (f3 (f4 (f34 ?v0) ?v1) ?v2) f1) (not (= ?v1 f18)))))
(assert (forall ((?v0 S17) (?v1 S2)) (=> (= (f3 (f4 (f34 ?v0) f18) ?v1) f1) false)))
(assert (forall ((?v0 S13) (?v1 S17) (?v2 S2)) (=> (= ?v0 (f37 f38 ?v1)) (= (f26 ?v0 (f4 (f19 ?v2) f18)) ?v2))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S6) (?v3 S6)) (=> (= (f11 (f14 (f31 (f32 f33 ?v0) ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S6)) (=> (= (f11 (f14 ?v0 ?v2) ?v4) f1) (=> (= (f11 (f14 ?v1 ?v4) ?v3) f1) false))) false))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S6) (?v3 S14) (?v4 S6)) (=> (= (f36 (f31 (f32 f33 ?v0) ?v1) ?v2 ?v3 ?v4) f1) (=> (forall ((?v5 S6)) (=> (= (f36 ?v0 ?v2 ?v3 ?v5) f1) (=> (= (f36 ?v1 ?v5 ?v3 ?v4) f1) false))) false))))
(assert (forall ((?v0 S9) (?v1 S6) (?v2 S6)) (=> (= (f11 (f14 ?v0 ?v1) ?v2) f1) (exists ((?v3 S14)) (= (f36 ?v0 ?v1 ?v3 ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (not (= f30 (f31 (f32 f33 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (not (= (f31 (f32 f33 ?v0) ?v1) f30))))
(assert (forall ((?v0 S9) (?v1 S6) (?v2 S14) (?v3 S6) (?v4 S9) (?v5 S6) (?v6 S14) (?v7 S6)) (=> (= (f36 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f36 ?v4 ?v5 ?v6 ?v7) f1) (exists ((?v8 S14)) (and (= (f36 ?v0 ?v1 ?v8 ?v3) f1) (= (f36 ?v4 ?v5 ?v8 ?v7) f1)))))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S3) (?v3 S2)) (=> (= (f3 (f4 (f39 (f40 ?v0) ?v1) ?v2) ?v3) f1) (=> (not (= (f6 (f7 ?v1) ?v2) f1)) (= (f3 (f4 (f34 ?v0) (f4 (f19 ?v1) ?v2)) ?v3) f1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f6 (f7 ?v0) ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f25 ?v0) ?v0)))
(assert (forall ((?v0 S17) (?v1 S2)) (= (f3 (f4 (f39 (f40 ?v0) ?v1) f18) ?v1) f1)))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 (f39 (f40 ?v0) ?v1) f18) ?v2) f1) (=> (=> (= ?v2 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S17) (?v3 S2) (?v4 S2)) (let ((?v_0 (f39 (f40 ?v2) ?v3))) (=> (not (= (f6 (f7 ?v0) ?v1) f1)) (=> (= (f3 (f4 ?v_0 ?v1) ?v4) f1) (= (f3 (f4 ?v_0 (f4 (f19 ?v0) ?v1)) (f41 (f42 ?v2 ?v0) ?v4)) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (= (= (f31 (f32 f33 ?v0) ?v1) (f31 (f32 f33 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S3) (?v3 S2)) (=> (= (f3 (f4 (f34 ?v0) (f4 (f19 ?v1) ?v2)) ?v3) f1) (=> (forall ((?v4 S2) (?v5 S3)) (=> (= (f4 (f19 ?v1) ?v2) (f4 (f19 ?v4) ?v5)) (=> (= (f3 (f4 (f39 (f40 ?v0) ?v4) ?v5) ?v3) f1) (=> (not (= (f6 (f7 ?v4) ?v5) f1)) false)))) false))))
(assert (forall ((?v0 S17) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f34 ?v0) ?v1) ?v2) f1) (exists ((?v3 S2) (?v4 S3) (?v5 S2)) (and (= ?v1 (f4 (f19 ?v3) ?v4)) (and (= ?v2 ?v5) (and (= (f3 (f4 (f39 (f40 ?v0) ?v3) ?v4) ?v5) f1) (not (= (f6 (f7 ?v3) ?v4) f1)))))))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S3) (?v3 S2)) (= (= (f3 (f4 (f39 (f40 ?v0) ?v1) ?v2) ?v3) f1) (or (and (= ?v2 f18) (= ?v3 ?v1)) (exists ((?v4 S2) (?v5 S3) (?v6 S2)) (and (= ?v2 (f4 (f19 ?v4) ?v5)) (and (= ?v3 (f41 (f42 ?v0 ?v4) ?v6)) (and (not (= (f6 (f7 ?v4) ?v5) f1)) (= (f3 (f4 (f39 (f40 ?v0) ?v1) ?v5) ?v6) f1)))))))))
(assert (forall ((?v0 S17) (?v1 S13) (?v2 S3) (?v3 S2)) (=> (= (f35 ?v0 ?v1) f1) (=> (= (f43 ?v2) f1) (=> (not (= (f6 (f7 ?v3) ?v2) f1)) (=> (not (= ?v2 f18)) (= (f26 ?v1 (f4 (f19 ?v3) ?v2)) (f41 (f42 ?v0 ?v3) (f26 ?v1 ?v2)))))))))
(assert (forall ((?v0 S17) (?v1 S13) (?v2 S3)) (=> (= (f35 ?v0 ?v1) f1) (=> (= (f43 ?v2) f1) (= (f26 ?v1 ?v2) (f26 (f37 f38 ?v0) ?v2))))))
(assert (forall ((?v0 S17) (?v1 S13) (?v2 S3)) (=> (= (f35 ?v0 ?v1) f1) (=> (= (f43 ?v2) f1) (=> (not (= ?v2 f18)) (=> (forall ((?v3 S2) (?v4 S2)) (= (f6 (f7 (f41 (f42 ?v0 ?v3) ?v4)) (f4 (f19 ?v3) (f4 (f19 ?v4) f18))) f1)) (= (f6 (f7 (f26 ?v1 ?v2)) ?v2) f1)))))))
(assert (= (f43 f18) f1))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f43 ?v0) f1) (= (f43 (f4 (f19 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f43 (f4 (f19 ?v0) ?v1)) f1) (= (f43 ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S17)) (=> (= (f43 ?v0) f1) (=> (not (= ?v0 f18)) (exists ((?v2 S2)) (= (f3 (f4 (f34 ?v1) ?v0) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S5)) (=> (= (f43 ?v0) f1) (=> (= (f6 ?v1 f18) f1) (=> (forall ((?v2 S2) (?v3 S3)) (=> (= (f43 ?v3) f1) (=> (not (= (f6 (f7 ?v2) ?v3) f1)) (=> (= (f6 ?v1 ?v3) f1) (= (f6 ?v1 (f4 (f19 ?v2) ?v3)) f1))))) (= (f6 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S3)) (= (= (f43 ?v0) f1) (or (= ?v0 f18) (exists ((?v1 S3) (?v2 S2)) (and (= ?v0 (f4 (f19 ?v2) ?v1)) (= (f43 ?v1) f1)))))))
(assert (forall ((?v0 S3) (?v1 S17) (?v2 S2)) (=> (= (f43 ?v0) f1) (exists ((?v3 S2)) (= (f3 (f4 (f39 (f40 ?v1) ?v2) ?v0) ?v3) f1)))))
(assert (forall ((?v0 S17) (?v1 S13) (?v2 S3) (?v3 S2)) (=> (= (f44 ?v0 ?v1) f1) (=> (= (f43 ?v2) f1) (=> (not (= ?v2 f18)) (= (f26 ?v1 (f4 (f19 ?v3) ?v2)) (f41 (f42 ?v0 ?v3) (f26 ?v1 ?v2))))))))
(assert (forall ((?v0 S3) (?v1 S5)) (=> (= (f43 ?v0) f1) (=> (not (= ?v0 f18)) (=> (forall ((?v2 S2)) (= (f6 ?v1 (f4 (f19 ?v2) f18)) f1)) (=> (forall ((?v2 S2) (?v3 S3)) (=> (= (f43 ?v3) f1) (=> (not (= ?v3 f18)) (=> (not (= (f6 (f7 ?v2) ?v3) f1)) (=> (= (f6 ?v1 ?v3) f1) (= (f6 ?v1 (f4 (f19 ?v2) ?v3)) f1)))))) (= (f6 ?v1 ?v0) f1)))))))
(assert (forall ((?v0 S17) (?v1 S13) (?v2 S2)) (=> (= (f44 ?v0 ?v1) f1) (= (f41 (f42 ?v0 ?v2) ?v2) ?v2))))
(assert (forall ((?v0 S17) (?v1 S13) (?v2 S3) (?v3 S2)) (let ((?v_0 (f26 ?v1 ?v2))) (=> (= (f44 ?v0 ?v1) f1) (=> (= (f43 ?v2) f1) (=> (= (f6 (f7 ?v3) ?v2) f1) (= (f41 (f42 ?v0 ?v3) ?v_0) ?v_0)))))))
(assert (forall ((?v0 S17) (?v1 S13) (?v2 S3)) (=> (= (f45 ?v0 ?v1) f1) (=> (= (f43 ?v2) f1) (= (f26 ?v1 ?v2) (f26 (f37 f38 ?v0) ?v2))))))
(assert (forall ((?v0 S17) (?v1 S13) (?v2 S3) (?v3 S2)) (let ((?v_0 (f19 ?v3))) (let ((?v_1 (f4 (f46 ?v2) (f4 ?v_0 f18)))) (=> (= (f35 ?v0 ?v1) f1) (=> (= (f43 ?v2) f1) (= (f26 ?v1 (f4 ?v_0 ?v2)) (ite (= ?v_1 f18) ?v3 (f41 (f42 ?v0 ?v3) (f26 ?v1 ?v_1))))))))))
(assert (forall ((?v0 S17) (?v1 S13) (?v2 S3) (?v3 S2)) (let ((?v_0 (f4 (f46 ?v2) (f4 (f19 ?v3) f18)))) (=> (= (f35 ?v0 ?v1) f1) (=> (= (f43 ?v2) f1) (=> (= (f6 (f7 ?v3) ?v2) f1) (= (f26 ?v1 ?v2) (ite (= ?v_0 f18) ?v3 (f41 (f42 ?v0 ?v3) (f26 ?v1 ?v_0))))))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f46 ?v1) ?v2)) f1) (=> (=> (= (f6 ?v_0 ?v1) f1) (=> (not (= (f6 ?v_0 ?v2) f1)) false)) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 ?v1) f1) (=> (not (= (f6 ?v_0 ?v2) f1)) (= (f6 ?v_0 (f4 (f46 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f43 ?v0) f1) (= (f43 (f4 (f46 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S3)) (= (f4 (f46 f18) ?v0) f18)))
(assert (forall ((?v0 S3)) (= (f4 (f46 ?v0) f18) ?v0)))
(assert (forall ((?v0 S3)) (= (f4 (f46 ?v0) ?v0) f18)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f43 ?v0) f1) (= (= (f43 (f4 (f46 ?v1) ?v0)) f1) (= (f43 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f19 ?v0)) (?v_1 (f4 (f46 ?v1) ?v2))) (= (f4 (f46 (f4 ?v_0 ?v1)) ?v2) (ite (= (f6 (f7 ?v0) ?v2) f1) ?v_1 (f4 ?v_0 ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (=> (= (f6 (f7 ?v0) ?v1) f1) (= (f4 (f46 (f4 (f19 ?v0) ?v2)) ?v1) (f4 (f46 ?v2) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f46 ?v1) ?v2)) f1) (=> (= (f6 ?v_0 ?v2) f1) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (= (f6 ?v_0 (f4 (f46 ?v1) ?v2)) f1) (= (f6 ?v_0 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 (f46 ?v0) ?v1))) (= (f4 (f46 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (= (= (f6 ?v_0 (f4 (f46 ?v1) ?v2)) f1) (and (= (f6 ?v_0 ?v1) f1) (not (= (f6 ?v_0 ?v2) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f4 (f46 ?v0) ?v1) (f25 (f4 (f8 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f19 ?v0))) (=> (= (f6 (f7 ?v0) ?v1) f1) (= (f4 ?v_0 (f4 (f46 ?v1) (f4 ?v_0 f18))) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f19 ?v0))) (=> (not (= (f6 (f7 ?v0) ?v1) f1)) (= (f4 (f46 (f4 ?v_0 ?v1)) (f4 ?v_0 f18)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f19 ?v0))) (= (f4 ?v_0 (f4 (f46 ?v1) (f4 ?v_0 f18))) (f4 ?v_0 ?v1)))))
(check-sat)
(exit)