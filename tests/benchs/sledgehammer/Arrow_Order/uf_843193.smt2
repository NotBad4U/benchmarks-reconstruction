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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S5) S1)
(declare-fun f6 (S6 S2) S5)
(declare-fun f7 () S6)
(declare-fun f8 (S7 S5) S5)
(declare-fun f9 (S8 S5) S7)
(declare-fun f10 () S8)
(declare-fun f11 () S5)
(declare-fun f12 () S5)
(declare-fun f13 () S4)
(declare-fun f14 () S4)
(declare-fun f15 () S3)
(declare-fun f16 (S9 S10) S4)
(declare-fun f17 (S4) S9)
(declare-fun f18 () S3)
(declare-fun f19 () S10)
(declare-fun f20 (S11 S10) S9)
(declare-fun f21 (S4) S11)
(declare-fun f22 () S10)
(declare-fun f23 (S4) S9)
(declare-fun f24 (S5) S3)
(declare-fun f25 (S12 S4) S1)
(declare-fun f26 (S10 S10) S12)
(declare-fun f27 () S10)
(declare-fun f28 () S10)
(declare-fun f29 () S10)
(declare-fun f30 (S3 S13) S1)
(declare-fun f31 () S13)
(declare-fun f32 (S14 S5) S2)
(declare-fun f33 (S15 S6) S14)
(declare-fun f34 (S16 S17) S15)
(declare-fun f35 () S16)
(declare-fun f36 () S17)
(declare-fun f37 (S6 S17) S1)
(declare-fun f38 (S4 S18) S1)
(declare-fun f39 () S18)
(declare-fun f40 (S19 S17) S5)
(declare-fun f41 () S19)
(declare-fun f42 (S20 S3) S4)
(declare-fun f43 () S20)
(declare-fun f44 (S5 S5) S1)
(declare-fun f45 (S20) S1)
(declare-fun f46 (S20) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (ite (= (f5 (f6 f7 ?v0) (f8 (f9 f10 f11) f12)) f1) f13 f14))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f6 f7 ?v0)) (?v_1 (f3 f18 ?v0))) (= (f3 f15 ?v0) (ite (= (f5 ?v_0 f11) f1) (f16 (f17 ?v_1) f19) (ite (= ?v_0 f11) (f16 (f20 (f21 ?v_1) f22) f19) (f16 (f23 ?v_1) f19)))))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (f3 (f24 ?v0) ?v1) (ite (= (f5 (f6 f7 ?v1) ?v0) f1) f13 f14))))
(assert (not (forall ((?v0 S2)) (let ((?v_0 (f6 f7 ?v0))) (let ((?v_2 (= (f5 ?v_0 f11) f1)) (?v_1 (f3 f18 ?v0))) (= (= (f25 (f26 f19 f27) (ite ?v_2 (f16 (f17 ?v_1) f19) (ite (= ?v_0 f11) (f16 (f20 (f21 ?v_1) f22) f19) (f16 (f23 ?v_1) f19)))) f1) (= (f25 (f26 f28 f29) (ite ?v_2 f13 f14)) f1)))))))
(assert (distinct f22 f27 f19))
(assert (= (f30 f18 f31) f1))
(assert (= (f25 (f26 f22 f27) (f3 f18 (f32 (f33 (f34 f35 f36) f7) f11))) f1))
(assert (= (f37 f7 f36) f1))
(assert (= (f30 f18 f31) f1))
(assert (= (f37 f7 f36) f1))
(assert (not (= f29 f28)))
(assert (not (= f22 f27)))
(assert (distinct f22 f27 f19))
(assert (= (f38 f13 f39) f1))
(assert (= (f38 f14 f39) f1))
(assert (= (f25 (f26 f29 f28) f13) f1))
(assert (= (f25 (f26 f28 f29) f14) f1))
(assert (= (f25 (f26 f22 f27) (f3 f18 (f32 (f33 (f34 f35 f36) f7) f11))) f1))
(assert (not (= (f25 (f26 f29 f28) f14) f1)))
(assert (not (= (f25 (f26 f28 f29) f13) f1)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f26 f22 f27)) (?v_1 (f3 f18 ?v0)) (?v_2 (f6 f7 ?v0))) (= (= (f25 ?v_0 ?v_1) f1) (= (f25 ?v_0 (ite (= (f5 ?v_2 f11) f1) (f16 (f17 ?v_1) f19) (ite (= ?v_2 f11) (f16 (f20 (f21 ?v_1) f22) f19) (f16 (f23 ?v_1) f19)))) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S4) (?v3 S10)) (let ((?v_0 (f26 ?v0 ?v1))) (= (= (f25 ?v_0 (f16 (f23 ?v2) ?v3)) f1) (and (not (= ?v1 ?v3)) (ite (= ?v0 ?v3) (not (= ?v0 ?v1)) (= (f25 ?v_0 ?v2) f1)))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S4) (?v3 S10)) (let ((?v_0 (f26 ?v0 ?v1))) (= (= (f25 ?v_0 (f16 (f17 ?v2) ?v3)) f1) (and (not (= ?v0 ?v3)) (ite (= ?v1 ?v3) (not (= ?v0 ?v1)) (= (f25 ?v_0 ?v2) f1)))))))
(assert (=> (forall ((?v0 S10)) (=> (distinct f22 f27 ?v0) false)) false))
(assert (= (f5 f11 (f40 f41 f36)) f1))
(assert (forall ((?v0 S2)) (let ((?v_0 (f6 f7 ?v0)) (?v_1 (f3 f18 ?v0))) (= (= (f25 (f26 f22 f19) (ite (= (f5 ?v_0 f11) f1) (f16 (f17 ?v_1) f19) (ite (= ?v_0 f11) (f16 (f20 (f21 ?v_1) f22) f19) (f16 (f23 ?v_1) f19)))) f1) (= (f25 (f26 f29 f28) (ite (= (f5 ?v_0 (f8 (f9 f10 f11) f12)) f1) f13 f14)) f1)))))
(assert (=> (forall ((?v0 S4)) (=> (= (f25 (f26 f29 f28) ?v0) f1) (=> (= (f38 ?v0 f39) f1) false))) false))
(assert (=> (forall ((?v0 S4)) (=> (= (f25 (f26 f28 f29) ?v0) f1) (=> (= (f38 ?v0 f39) f1) false))) false))
(assert (= (f30 f15 f31) f1))
(assert (let ((?v_0 (f26 f22 f27))) (= (= (f25 ?v_0 (f42 f43 f18)) f1) (= (f25 ?v_0 (f42 f43 f15)) f1))))
(assert (= (f25 (f26 f22 f19) (f42 f43 f15)) f1))
(assert (= (= (f25 (f26 f22 f19) (f42 f43 f15)) f1) (= (f25 (f26 f29 f28) (f42 f43 f4)) f1)))
(assert (forall ((?v0 S5)) (=> (= (f44 ?v0 f11) f1) (= (f25 (f26 f28 f29) (f42 f43 (f24 ?v0))) f1))))
(assert (forall ((?v0 S5)) (= (f30 (f24 ?v0) f31) f1)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S4) (?v3 S10) (?v4 S10)) (let ((?v_0 (f26 ?v3 ?v4))) (=> (not (= ?v0 ?v1)) (=> (= (f38 ?v2 f39) f1) (= (= (f25 ?v_0 (f16 (f20 (f21 ?v2) ?v0) ?v1)) f1) (and (not (= ?v3 ?v4)) (ite (= ?v3 ?v1) (= (f25 (f26 ?v0 ?v4) ?v2) f1) (ite (= ?v4 ?v1) (or (= ?v3 ?v0) (= (f25 (f26 ?v3 ?v0) ?v2) f1)) (= (f25 ?v_0 ?v2) f1))))))))))
(assert (= (f45 f43) f1))
(assert (= (f46 f43) f1))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S3) (?v3 S3)) (=> (not (= ?v0 ?v1)) (=> (= (f30 ?v2 f31) f1) (=> (= (f30 ?v3 f31) f1) (=> (forall ((?v4 S2)) (= (= (f25 (f26 ?v0 ?v1) (f3 ?v2 ?v4)) f1) (= (f25 (f26 ?v1 ?v0) (f3 ?v3 ?v4)) f1))) (= (= (f25 (f26 ?v0 ?v1) (f42 f43 ?v2)) f1) (= (f25 (f26 ?v1 ?v0) (f42 f43 ?v3)) f1))))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10) (?v4 S3) (?v5 S3)) (=> (not (= ?v0 ?v1)) (=> (not (= ?v2 ?v3)) (=> (= (f30 ?v4 f31) f1) (=> (= (f30 ?v5 f31) f1) (=> (forall ((?v6 S2)) (= (= (f25 (f26 ?v0 ?v1) (f3 ?v4 ?v6)) f1) (= (f25 (f26 ?v2 ?v3) (f3 ?v5 ?v6)) f1))) (= (= (f25 (f26 ?v0 ?v1) (f42 f43 ?v4)) f1) (= (f25 (f26 ?v2 ?v3) (f42 f43 ?v5)) f1)))))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S3) (?v4 S3)) (=> (not (= ?v0 ?v1)) (=> (not (= ?v1 ?v2)) (=> (not (= ?v0 ?v2)) (=> (= (f30 ?v3 f31) f1) (=> (= (f30 ?v4 f31) f1) (=> (forall ((?v5 S2)) (= (= (f25 (f26 ?v0 ?v1) (f3 ?v3 ?v5)) f1) (= (f25 (f26 ?v1 ?v2) (f3 ?v4 ?v5)) f1))) (= (= (f25 (f26 ?v0 ?v1) (f42 f43 ?v3)) f1) (= (f25 (f26 ?v1 ?v2) (f42 f43 ?v4)) f1))))))))))
(check-sat)
(exit)