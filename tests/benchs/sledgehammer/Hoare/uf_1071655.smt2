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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S6) S4)
(declare-fun f6 (S7 S8) S5)
(declare-fun f7 (S9 S6) S7)
(declare-fun f8 () S9)
(declare-fun f9 () S6)
(declare-fun f10 (S10 S11) S8)
(declare-fun f11 () S10)
(declare-fun f12 (S2) S11)
(declare-fun f13 (S8) S6)
(declare-fun f14 () S3)
(declare-fun f15 (S12 S2) S8)
(declare-fun f16 () S12)
(declare-fun f17 () S3)
(declare-fun f18 (S14 S13) S1)
(declare-fun f19 (S6 S13) S14)
(declare-fun f20 (S16 S15) S3)
(declare-fun f21 (S17 S15) S16)
(declare-fun f22 () S17)
(declare-fun f23 (S15 S2) S6)
(declare-fun f24 () S17)
(declare-fun f25 (S18 S4) S1)
(declare-fun f26 (S19 S18) S18)
(declare-fun f27 (S18) S19)
(declare-fun f28 (S20 S2) S1)
(declare-fun f29 (S21 S20) S20)
(declare-fun f30 (S20) S21)
(declare-fun f31 (S18 S18) S1)
(declare-fun f32 (S18) S19)
(declare-fun f33 () S18)
(declare-fun f34 (S22 S20) S18)
(declare-fun f35 (S3) S22)
(declare-fun f36 () S20)
(declare-fun f37 (S20) S1)
(declare-fun f38 (S18 S18) S1)
(declare-fun f39 (S18) S1)
(declare-fun f40 (S24 S18) S20)
(declare-fun f41 (S23) S24)
(declare-fun f42 (S20) S20)
(declare-fun f43 (S18) S18)
(declare-fun f44 (S4 S18) S1)
(declare-fun f45 (S2 S20) S1)
(declare-fun f46 (S20) S21)
(declare-fun f47 (S23 S4) S2)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f10 f11 (f12 ?v0)))) (= (f3 f4 ?v0) (f5 (f6 (f7 f8 f9) ?v_0) (f13 ?v_0))))))
(assert (forall ((?v0 S2)) (= (f3 f14 ?v0) (f5 (f6 (f7 f8 f9) (f10 f11 (f12 ?v0))) (f13 (f15 f16 ?v0))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f15 f16 ?v0))) (= (f3 f17 ?v0) (f5 (f6 (f7 f8 f9) ?v_0) (f13 ?v_0))))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f18 (f19 f9 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S2)) (= (f3 (f20 (f21 f22 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f23 ?v0 ?v2)) (f10 f11 (f12 ?v2))) (f23 ?v1 ?v2)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S2)) (= (f3 (f20 (f21 f24 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f23 ?v0 ?v2)) (f15 f16 ?v2)) (f23 ?v1 ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S4)) (= (= (f25 (f26 (f27 ?v0) ?v1) ?v2) f1) (and (= (f25 ?v0 ?v2) f1) (= (f25 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S2)) (= (= (f28 (f29 (f30 ?v0) ?v1) ?v2) f1) (and (= (f28 ?v0 ?v2) f1) (= (f28 ?v1 ?v2) f1)))))
(assert (not (= (f31 (f26 (f32 f33) (f34 (f35 f17) f36)) (f34 (f35 f14) f36)) f1)))
(assert (= (f31 (f26 (f32 f33) (f34 (f35 f17) f36)) (f34 (f35 f4) f36)) f1))
(assert (= (f37 f36) f1))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6) (?v3 S6) (?v4 S8) (?v5 S6)) (= (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f31 ?v0 ?v1) f1) (=> (= (f31 ?v2 ?v0) f1) (= (f31 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S18) (?v1 S15) (?v2 S15) (?v3 S20)) (let ((?v_0 (f34 (f35 (f20 (f21 f24 ?v1) ?v2)) ?v3))) (=> (= (f31 (f26 (f32 ?v0) ?v_0) (f34 (f35 (f20 (f21 f22 ?v1) ?v2)) ?v3)) f1) (= (f31 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S13)) (=> (= (f18 (f19 (f13 (f15 f16 ?v0)) ?v1) ?v2) f1) (=> (=> (= (f18 (f19 (f13 (f10 f11 (f12 ?v0))) ?v1) ?v2) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S13)) (=> (= (f18 (f19 (f13 (f10 f11 (f12 ?v0))) ?v1) ?v2) f1) (= (f18 (f19 (f13 (f15 f16 ?v0)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S18) (?v1 S15) (?v2 S15) (?v3 S20)) (let ((?v_0 (f34 (f35 (f20 (f21 f24 ?v1) ?v2)) ?v3))) (=> (= (f38 (f26 (f32 ?v0) ?v_0) (f34 (f35 (f20 (f21 f22 ?v1) ?v2)) ?v3)) f1) (= (f38 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S20) (?v1 S3)) (=> (= (f37 ?v0) f1) (= (f39 (f34 (f35 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S18) (?v1 S23)) (=> (= (f39 ?v0) f1) (= (f37 (f40 (f41 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S20) (?v1 S20)) (=> (or (= (f37 (f42 ?v0)) f1) (= (f37 (f42 ?v1)) f1)) (= (f37 (f42 (f29 (f30 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (or (= (f39 (f43 ?v0)) f1) (= (f39 (f43 ?v1)) f1)) (= (f39 (f43 (f26 (f27 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S4) (?v1 S18) (?v2 S18)) (=> (= (f44 ?v0 (f26 (f32 ?v1) ?v2)) f1) (=> (=> (= (f44 ?v0 ?v1) f1) false) (=> (=> (= (f44 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S20) (?v2 S20)) (=> (= (f45 ?v0 (f29 (f46 ?v1) ?v2)) f1) (=> (=> (= (f45 ?v0 ?v1) f1) false) (=> (=> (= (f45 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S4)) (=> (= (f25 (f26 (f32 ?v0) ?v1) ?v2) f1) (=> (=> (= (f25 ?v0 ?v2) f1) false) (=> (=> (= (f25 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S2)) (=> (= (f28 (f29 (f46 ?v0) ?v1) ?v2) f1) (=> (=> (= (f28 ?v0 ?v2) f1) false) (=> (=> (= (f28 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S18) (?v1 S4) (?v2 S18)) (=> (=> (not (= (f25 ?v0 ?v1) f1)) (= (f25 ?v2 ?v1) f1)) (= (f25 (f26 (f32 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S20)) (=> (=> (not (= (f28 ?v0 ?v1) f1)) (= (f28 ?v2 ?v1) f1)) (= (f28 (f29 (f46 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S4) (?v1 S18) (?v2 S18)) (=> (=> (not (= (f44 ?v0 ?v1) f1)) (= (f44 ?v0 ?v2) f1)) (= (f44 ?v0 (f26 (f32 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S20) (?v2 S20)) (=> (=> (not (= (f45 ?v0 ?v1) f1)) (= (f45 ?v0 ?v2) f1)) (= (f45 ?v0 (f29 (f46 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S20)) (=> (= ?v0 (f3 ?v1 ?v2)) (=> (= (f45 ?v2 ?v3) f1) (= (f44 ?v0 (f34 (f35 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S4) (?v3 S18)) (=> (= ?v0 (f47 ?v1 ?v2)) (=> (= (f44 ?v2 ?v3) f1) (= (f45 ?v0 (f40 (f41 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f31 ?v0 ?v1) f1) (= (f38 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S20) (?v2 S4) (?v3 S3)) (=> (= (f45 ?v0 ?v1) f1) (=> (= ?v2 (f3 ?v3 ?v0)) (= (f44 ?v2 (f34 (f35 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S18) (?v2 S2) (?v3 S23)) (=> (= (f44 ?v0 ?v1) f1) (=> (= ?v2 (f47 ?v3 ?v0)) (= (f45 ?v2 (f40 (f41 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S20) (?v2 S3)) (=> (= (f45 ?v0 ?v1) f1) (= (f44 (f3 ?v2 ?v0) (f34 (f35 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S18) (?v2 S23)) (=> (= (f44 ?v0 ?v1) f1) (= (f45 (f47 ?v2 ?v0) (f40 (f41 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S20)) (= (= (f44 ?v0 (f34 (f35 ?v1) ?v2)) f1) (exists ((?v3 S2)) (and (= (f45 ?v3 ?v2) f1) (= ?v0 (f3 ?v1 ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S23) (?v2 S18)) (= (= (f45 ?v0 (f40 (f41 ?v1) ?v2)) f1) (exists ((?v3 S4)) (and (= (f44 ?v3 ?v2) f1) (= ?v0 (f47 ?v1 ?v3)))))))
(assert (forall ((?v0 S4) (?v1 S18) (?v2 S18)) (=> (= (f44 ?v0 ?v1) f1) (= (f44 ?v0 (f26 (f32 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S20) (?v2 S20)) (=> (= (f45 ?v0 ?v1) f1) (= (f45 ?v0 (f29 (f46 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S18) (?v2 S18)) (=> (= (f44 ?v0 ?v1) f1) (= (f44 ?v0 (f26 (f32 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S20) (?v2 S20)) (=> (= (f45 ?v0 ?v1) f1) (= (f45 ?v0 (f29 (f46 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S18) (?v1 S4) (?v2 S18)) (=> (= (f25 ?v0 ?v1) f1) (= (f25 (f26 (f32 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S20)) (=> (= (f28 ?v0 ?v1) f1) (= (f28 (f29 (f46 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S18) (?v1 S4) (?v2 S18)) (=> (= (f25 ?v0 ?v1) f1) (= (f25 (f26 (f32 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S20)) (=> (= (f28 ?v0 ?v1) f1) (= (f28 (f29 (f46 ?v0) ?v2) ?v1) f1))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (= (forall ((?v3 S4)) (=> (= (f44 ?v3 (f26 (f32 ?v0) ?v1)) f1) (= (f25 ?v2 ?v3) f1))) (and (forall ((?v3 S4)) (=> (= (f44 ?v3 ?v0) f1) (= (f25 ?v2 ?v3) f1))) (forall ((?v3 S4)) (=> (= (f44 ?v3 ?v1) f1) (= (f25 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S20)) (= (forall ((?v3 S2)) (=> (= (f45 ?v3 (f29 (f46 ?v0) ?v1)) f1) (= (f28 ?v2 ?v3) f1))) (and (forall ((?v3 S2)) (=> (= (f45 ?v3 ?v0) f1) (= (f28 ?v2 ?v3) f1))) (forall ((?v3 S2)) (=> (= (f45 ?v3 ?v1) f1) (= (f28 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (= (exists ((?v3 S4)) (and (= (f44 ?v3 (f26 (f32 ?v0) ?v1)) f1) (= (f25 ?v2 ?v3) f1))) (or (exists ((?v3 S4)) (and (= (f44 ?v3 ?v0) f1) (= (f25 ?v2 ?v3) f1))) (exists ((?v3 S4)) (and (= (f44 ?v3 ?v1) f1) (= (f25 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S20)) (= (exists ((?v3 S2)) (and (= (f45 ?v3 (f29 (f46 ?v0) ?v1)) f1) (= (f28 ?v2 ?v3) f1))) (or (exists ((?v3 S2)) (and (= (f45 ?v3 ?v0) f1) (= (f28 ?v2 ?v3) f1))) (exists ((?v3 S2)) (and (= (f45 ?v3 ?v1) f1) (= (f28 ?v2 ?v3) f1)))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f32 ?v0))) (= (f26 (f32 (f26 ?v_0 ?v1)) ?v2) (f26 ?v_0 (f26 (f32 ?v1) ?v2))))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S20)) (let ((?v_0 (f46 ?v0))) (= (f29 (f46 (f29 ?v_0 ?v1)) ?v2) (f29 ?v_0 (f29 (f46 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S18) (?v2 S18)) (= (= (f44 ?v0 (f26 (f32 ?v1) ?v2)) f1) (or (= (f44 ?v0 ?v1) f1) (= (f44 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S20) (?v2 S20)) (= (= (f45 ?v0 (f29 (f46 ?v1) ?v2)) f1) (or (= (f45 ?v0 ?v1) f1) (= (f45 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_1 (f32 ?v0)) (?v_0 (f32 ?v1))) (= (f26 ?v_1 (f26 ?v_0 ?v2)) (f26 ?v_0 (f26 ?v_1 ?v2))))))
(assert (forall ((?v0 S20) (?v1 S20) (?v2 S20)) (let ((?v_1 (f46 ?v0)) (?v_0 (f46 ?v1))) (= (f29 ?v_1 (f29 ?v_0 ?v2)) (f29 ?v_0 (f29 ?v_1 ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18)) (let ((?v_0 (f32 ?v0))) (let ((?v_1 (f26 ?v_0 ?v1))) (= (f26 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S20) (?v1 S20)) (let ((?v_0 (f46 ?v0))) (let ((?v_1 (f29 ?v_0 ?v1))) (= (f29 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f26 (f32 ?v0) ?v1) (f26 (f32 ?v1) ?v0))))
(assert (forall ((?v0 S20) (?v1 S20)) (= (f29 (f46 ?v0) ?v1) (f29 (f46 ?v1) ?v0))))
(check-sat)
(exit)