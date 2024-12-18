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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () S2)
(declare-fun f4 () S2)
(declare-fun f5 () S3)
(declare-fun f6 () S3)
(declare-fun f7 (S4 S5) S1)
(declare-fun f8 () S5)
(declare-fun f9 (S5 S4) S1)
(declare-fun f10 (S6) S5)
(declare-fun f11 () S6)
(declare-fun f12 (S2 S8) S1)
(declare-fun f13 (S7) S2)
(declare-fun f14 () S8)
(declare-fun f15 () S8)
(declare-fun f16 (S9 S6) S2)
(declare-fun f17 (S10 S8) S9)
(declare-fun f18 (S3) S10)
(declare-fun f19 () S8)
(declare-fun f20 (S11 S3) S3)
(declare-fun f21 (S12 S2) S11)
(declare-fun f22 () S12)
(declare-fun f23 (S5 S5) S1)
(declare-fun f24 (S14 S13) S4)
(declare-fun f25 (S15 S3) S14)
(declare-fun f26 (S16 S13) S15)
(declare-fun f27 () S16)
(declare-fun f28 (S13 S7) S2)
(declare-fun f29 (S17 S6) S6)
(declare-fun f30 () S17)
(declare-fun f31 () S3)
(declare-fun f32 (S18 S3) S11)
(declare-fun f33 () S18)
(declare-fun f34 (S3) S1)
(declare-fun f35 (S19 S2) S18)
(declare-fun f36 () S19)
(declare-fun f37 (S22 S21) S3)
(declare-fun f38 (S23 S20) S22)
(declare-fun f39 () S23)
(declare-fun f40 (S25 S21) S11)
(declare-fun f41 (S26 S24) S25)
(declare-fun f42 () S26)
(assert (not (= f1 f2)))
(assert (not (=> (and (= f3 f4) (= f5 f6)) (=> (forall ((?v0 S4)) (=> (= (f7 ?v0 f8) f1) (= (f9 (f10 f11) ?v0) f1))) (forall ((?v0 S7)) (let ((?v_0 (f13 ?v0))) (=> (= (f12 ?v_0 f14) f1) (and (= (f12 ?v_0 f15) f1) (not (= (f12 f4 f15) f1))))))))))
(assert (forall ((?v0 S6)) (=> (forall ((?v1 S4)) (=> (= (f7 ?v1 f8) f1) (= (f9 (f10 ?v0) ?v1) f1))) (forall ((?v1 S7) (?v2 S8)) (=> (and (= (f12 (f13 ?v1) ?v2) f1) (= (f12 f4 ?v2) f1)) (forall ((?v3 S8)) (=> (= (f12 (f16 (f17 (f18 f6) ?v2) ?v0) ?v3) f1) (= (f12 (f13 ?v1) ?v3) f1))))))))
(assert (= (f12 f3 f14) f1))
(assert (= (f12 (f16 (f17 (f18 f5) f14) f11) f19) f1))
(assert (=> (= f5 (f20 (f21 f22 f4) f6)) (=> (forall ((?v0 S4)) (=> (= (f7 ?v0 f8) f1) (= (f9 (f10 f11) ?v0) f1))) (forall ((?v0 S7)) (let ((?v_0 (f13 ?v0))) (=> (= (f12 ?v_0 f14) f1) (and (= (f12 ?v_0 f19) f1) (not (= (f12 f4 f19) f1)))))))))
(assert (= (f12 (f16 (f17 (f18 (f20 (f21 f22 f3) f5)) f19) f11) f15) f1))
(assert (=> (= (f20 (f21 f22 f3) f5) (f20 (f21 f22 f4) f6)) (=> (forall ((?v0 S4)) (=> (= (f7 ?v0 f8) f1) (= (f9 (f10 f11) ?v0) f1))) (forall ((?v0 S7)) (let ((?v_0 (f13 ?v0))) (=> (= (f12 ?v_0 f19) f1) (and (= (f12 ?v_0 f15) f1) (not (= (f12 f4 f15) f1)))))))))
(assert (forall ((?v0 S2) (?v1 S8) (?v2 S3) (?v3 S6)) (=> (not (= (f12 ?v0 ?v1) f1)) (= (f12 (f16 (f17 (f18 (f20 (f21 f22 ?v0) ?v2)) ?v1) ?v3) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S8) (?v2 S3) (?v3 S6) (?v4 S8) (?v5 S8)) (let ((?v_0 (f18 (f20 (f21 f22 ?v0) ?v2)))) (=> (= (f12 ?v0 ?v1) f1) (=> (= (f12 (f16 (f17 (f18 ?v2) ?v1) ?v3) ?v4) f1) (=> (= (f12 (f16 (f17 ?v_0 ?v4) ?v3) ?v5) f1) (= (f12 (f16 (f17 ?v_0 ?v1) ?v3) ?v5) f1)))))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f23 ?v0 ?v1) f1) (forall ((?v2 S6)) (=> (forall ((?v3 S4)) (=> (= (f7 ?v3 ?v0) f1) (= (f9 (f10 ?v2) ?v3) f1))) (forall ((?v3 S4)) (=> (= (f7 ?v3 ?v1) f1) (= (f9 (f10 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S3)) (= (= (f20 (f21 f22 ?v0) ?v1) (f20 (f21 f22 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S8) (?v3 S6) (?v4 S8)) (=> (= (f12 (f16 (f17 (f18 (f20 (f21 f22 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (=> (= ?v4 ?v2) (=> (not (= (f12 ?v0 ?v2) f1)) false)) (=> (forall ((?v5 S8)) (=> (= (f12 ?v0 ?v2) f1) (=> (= (f12 (f16 (f17 (f18 ?v1) ?v2) ?v3) ?v5) f1) (=> (= (f12 (f16 (f17 (f18 (f20 (f21 f22 ?v0) ?v1)) ?v5) ?v3) ?v4) f1) false)))) false)))))
(assert (forall ((?v0 S6) (?v1 S13) (?v2 S3) (?v3 S13)) (= (= (f9 (f10 ?v0) (f24 (f25 (f26 f27 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S7) (?v5 S8)) (=> (= (f12 (f28 ?v1 ?v4) ?v5) f1) (forall ((?v6 S8)) (=> (= (f12 (f16 (f17 (f18 ?v2) ?v5) ?v0) ?v6) f1) (= (f12 (f28 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S6) (?v3 S8) (?v4 S3) (?v5 S8) (?v6 S6) (?v7 S8)) (=> (= (f12 (f16 (f17 (f18 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f12 (f16 (f17 (f18 ?v4) ?v5) ?v6) ?v7) f1) (exists ((?v8 S6)) (and (= (f12 (f16 (f17 (f18 ?v0) ?v1) ?v8) ?v3) f1) (= (f12 (f16 (f17 (f18 ?v4) ?v5) ?v8) ?v7) f1)))))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (forall ((?v2 S4)) (=> (= (f7 ?v2 ?v0) f1) (= (f9 (f10 (f29 f30 ?v1)) ?v2) f1))) (forall ((?v2 S4)) (=> (= (f7 ?v2 ?v0) f1) (= (f9 (f10 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S4)) (=> (= (f9 (f10 (f29 f30 ?v0)) ?v1) f1) (= (f9 (f10 ?v0) ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S6)) (= (f12 (f16 (f17 (f18 f31) ?v0) ?v1) ?v0) f1)))
(assert (forall ((?v0 S8) (?v1 S6) (?v2 S8)) (=> (= (f12 (f16 (f17 (f18 f31) ?v0) ?v1) ?v2) f1) (=> (=> (= ?v2 ?v0) false) false))))
(assert (forall ((?v0 S13) (?v1 S3) (?v2 S13) (?v3 S13) (?v4 S3) (?v5 S13)) (= (= (f24 (f25 (f26 f27 ?v0) ?v1) ?v2) (f24 (f25 (f26 f27 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S6) (?v3 S8)) (let ((?v_0 (f17 (f18 ?v0) ?v1))) (=> (= (f12 (f16 ?v_0 ?v2) ?v3) f1) (= (f12 (f16 ?v_0 (f29 f30 ?v2)) ?v3) f1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f20 (f21 f22 ?v0) ?v1) f31))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f31 (f20 (f21 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S4)) (=> (forall ((?v1 S13) (?v2 S3) (?v3 S13)) (=> (= ?v0 (f24 (f25 (f26 f27 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S6)) (not (= ?v0 (f29 f30 ?v0)))))
(assert (forall ((?v0 S6)) (not (= (f29 f30 ?v0) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f29 f30 ?v0) (f29 f30 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f29 f30 ?v0) (f29 f30 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S6) (?v3 S8) (?v4 S3) (?v5 S8)) (=> (= (f12 (f16 (f17 (f18 ?v0) ?v1) ?v2) ?v3) f1) (=> (= (f12 (f16 (f17 (f18 ?v4) ?v3) ?v2) ?v5) f1) (= (f12 (f16 (f17 (f18 (f20 (f32 f33 ?v0) ?v4)) ?v1) ?v2) ?v5) f1)))))
(assert (=> (= (f34 f31) f1) (=> false false)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3) (?v3 S8) (?v4 S6) (?v5 S8)) (let ((?v_0 (= (f12 ?v0 ?v3) f1))) (=> (= (f12 (f16 (f17 (f18 (f20 (f32 (f35 f36 ?v0) ?v1) ?v2)) ?v3) ?v4) ?v5) f1) (=> (=> ?v_0 (=> (= (f12 (f16 (f17 (f18 ?v1) ?v3) ?v4) ?v5) f1) false)) (=> (=> (not ?v_0) (=> (= (f12 (f16 (f17 (f18 ?v2) ?v3) ?v4) ?v5) f1) false)) false))))))
(assert (forall ((?v0 S2) (?v1 S8) (?v2 S3) (?v3 S6) (?v4 S8) (?v5 S3)) (=> (= (f12 ?v0 ?v1) f1) (=> (= (f12 (f16 (f17 (f18 ?v2) ?v1) ?v3) ?v4) f1) (= (f12 (f16 (f17 (f18 (f20 (f32 (f35 f36 ?v0) ?v2) ?v5)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S2) (?v1 S8) (?v2 S3) (?v3 S6) (?v4 S8) (?v5 S3)) (=> (not (= (f12 ?v0 ?v1) f1)) (=> (= (f12 (f16 (f17 (f18 ?v2) ?v1) ?v3) ?v4) f1) (= (f12 (f16 (f17 (f18 (f20 (f32 (f35 f36 ?v0) ?v5) ?v2)) ?v1) ?v3) ?v4) f1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f34 (f20 (f21 f22 ?v0) ?v1)) f1) (=> (=> (= (f34 ?v1) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (=> (= (f34 (f20 (f32 (f35 f36 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f34 ?v1) f1) (=> (= (f34 ?v2) f1) false)) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f34 (f20 (f32 f33 ?v0) ?v1)) f1) (=> (=> (= (f34 ?v0) f1) (=> (= (f34 ?v1) f1) false)) false))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2) (?v3 S3) (?v4 S3)) (not (= (f20 (f32 f33 ?v0) ?v1) (f20 (f32 (f35 f36 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (not (= (f20 (f32 (f35 f36 ?v0) ?v1) ?v2) (f20 (f32 f33 ?v3) ?v4)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (= (f20 (f32 f33 ?v0) ?v1) (f20 (f32 f33 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3) (?v3 S2) (?v4 S3) (?v5 S3)) (= (= (f20 (f32 (f35 f36 ?v0) ?v1) ?v2) (f20 (f32 (f35 f36 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f34 ?v0) f1) (=> (= (f34 ?v1) f1) (= (f34 (f20 (f32 f33 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f34 ?v0) f1) (=> (= (f34 ?v1) f1) (= (f34 (f20 (f32 (f35 f36 ?v2) ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f34 ?v0) f1) (= (f34 (f20 (f21 f22 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S3) (?v4 S3)) (not (= (f20 (f21 f22 ?v0) ?v1) (f20 (f32 (f35 f36 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3) (?v3 S2) (?v4 S3)) (not (= (f20 (f32 (f35 f36 ?v0) ?v1) ?v2) (f20 (f21 f22 ?v3) ?v4)))))
(assert (= (f34 f31) f1))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2) (?v3 S3)) (not (= (f20 (f32 f33 ?v0) ?v1) (f20 (f21 f22 ?v2) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3) (?v3 S3)) (not (= (f20 (f21 f22 ?v0) ?v1) (f20 (f32 f33 ?v2) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (not (= (f20 (f32 (f35 f36 ?v0) ?v1) ?v2) f31))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (not (= f31 (f20 (f32 (f35 f36 ?v0) ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3)) (not (= (f20 (f32 f33 ?v0) ?v1) f31))))
(assert (forall ((?v0 S3) (?v1 S3)) (not (= f31 (f20 (f32 f33 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S8) (?v3 S6) (?v4 S8)) (=> (= (f12 (f16 (f17 (f18 (f20 (f32 f33 ?v0) ?v1)) ?v2) ?v3) ?v4) f1) (=> (forall ((?v5 S8)) (=> (= (f12 (f16 (f17 (f18 ?v0) ?v2) ?v3) ?v5) f1) (=> (= (f12 (f16 (f17 (f18 ?v1) ?v5) ?v3) ?v4) f1) false))) false))))
(assert (forall ((?v0 S20) (?v1 S21)) (=> (= (f34 (f37 (f38 f39 ?v0) ?v1)) f1) (=> false false))))
(assert (forall ((?v0 S24) (?v1 S21) (?v2 S3)) (=> (= (f34 (f20 (f40 (f41 f42 ?v0) ?v1) ?v2)) f1) (=> (=> (= (f34 ?v2) f1) false) false))))
(assert (forall ((?v0 S24) (?v1 S21) (?v2 S3) (?v3 S24) (?v4 S21) (?v5 S3)) (= (= (f20 (f40 (f41 f42 ?v0) ?v1) ?v2) (f20 (f40 (f41 f42 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(check-sat)
(exit)
