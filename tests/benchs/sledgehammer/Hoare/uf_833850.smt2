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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S3) S3)
(declare-fun f5 (S2) S4)
(declare-fun f6 (S2 S3) S1)
(declare-fun f7 (S2) S4)
(declare-fun f8 () S3)
(declare-fun f9 (S5 S6) S1)
(declare-fun f10 (S7 S6 S8 S6) S1)
(declare-fun f11 () S7)
(declare-fun f12 () S8)
(declare-fun f13 (S5 S6) S1)
(declare-fun f14 (S3 S3) S1)
(declare-fun f15 () S3)
(declare-fun f16 (S2) S4)
(declare-fun f17 (S10 S9) S2)
(declare-fun f18 (S11 S7) S10)
(declare-fun f19 (S12 S9) S11)
(declare-fun f20 () S12)
(declare-fun f21 () S3)
(declare-fun f22 (S8) S3)
(declare-fun f23 (S13 S6) S1)
(declare-fun f24 (S9 S5) S13)
(declare-fun f25 (S3) S3)
(declare-fun f26 (S14 S3) S2)
(declare-fun f27 () S14)
(declare-fun f28 () S1)
(declare-fun f29 () S7)
(declare-fun f30 (S15 S7) S7)
(declare-fun f31 (S16 S7) S15)
(declare-fun f32 () S16)
(declare-fun f33 (S3 S3) S1)
(declare-fun f34 (S17) S4)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f6 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f7 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f8 ?v0) f1) false)))
(assert (not (forall ((?v0 S5) (?v1 S6)) (=> (= (f9 ?v0 ?v1) f1) (forall ((?v2 S6)) (=> (= (f10 f11 ?v1 f12 ?v2) f1) (= (f13 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f9 ?v0 ?v1) f1) (exists ((?v2 S9) (?v3 S9)) (and (= (f14 f15 (f4 (f16 (f17 (f18 (f19 f20 ?v2) f11) ?v3)) f21)) f1) (and (forall ((?v4 S8)) (=> (forall ((?v5 S2)) (=> (= (f6 ?v5 f15) f1) (= (f3 (f22 ?v4) ?v5) f1))) (forall ((?v5 S5) (?v6 S6)) (=> (= (f23 (f24 ?v2 ?v5) ?v6) f1) (forall ((?v7 S6)) (=> (= (f10 f11 ?v6 ?v4 ?v7) f1) (= (f23 (f24 ?v3 ?v5) ?v7) f1))))))) (forall ((?v4 S6)) (=> (forall ((?v5 S5)) (=> (= (f23 (f24 ?v2 ?v5) ?v1) f1) (= (f23 (f24 ?v3 ?v5) ?v4) f1))) (= (f13 ?v0 ?v4) f1)))))))))
(assert (forall ((?v0 S2)) (=> (= (f6 ?v0 f15) f1) (= (f3 (f22 f12) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f14 ?v0 f21) f1)))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S7) (?v3 S9)) (= (= (f3 (f22 ?v0) (f17 (f18 (f19 f20 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S5) (?v5 S6)) (=> (= (f23 (f24 ?v1 ?v4) ?v5) f1) (forall ((?v6 S6)) (=> (= (f10 ?v2 ?v5 ?v0 ?v6) f1) (= (f23 (f24 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S9) (?v1 S7) (?v2 S9) (?v3 S9) (?v4 S7) (?v5 S9)) (= (= (f17 (f18 (f19 f20 ?v0) ?v1) ?v2) (f17 (f18 (f19 f20 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f14 ?v0 ?v1) f1) (=> (= (f14 ?v2 ?v0) f1) (= (f14 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f16 ?v1))) (=> (= (f14 ?v0 (f4 ?v_0 f21)) f1) (=> (= (f14 ?v0 ?v2) f1) (= (f14 ?v0 (f4 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f16 ?v1))) (=> (= (f14 ?v0 (f4 ?v_0 ?v2)) f1) (and (= (f14 ?v0 (f4 ?v_0 f21)) f1) (= (f14 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S7) (?v3 S9) (?v4 S9)) (let ((?v_0 (f18 (f19 f20 ?v1) ?v2))) (=> (= (f14 ?v0 (f4 (f16 (f17 ?v_0 ?v3)) f21)) f1) (=> (forall ((?v5 S5) (?v6 S6)) (=> (= (f23 (f24 ?v3 ?v5) ?v6) f1) (= (f23 (f24 ?v4 ?v5) ?v6) f1))) (= (f14 ?v0 (f4 (f16 (f17 ?v_0 ?v4)) f21)) f1))))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S7) (?v3 S9) (?v4 S9)) (=> (= (f14 ?v0 (f4 (f16 (f17 (f18 (f19 f20 ?v1) ?v2) ?v3)) f21)) f1) (=> (forall ((?v5 S5) (?v6 S6)) (=> (= (f23 (f24 ?v4 ?v5) ?v6) f1) (= (f23 (f24 ?v1 ?v5) ?v6) f1))) (= (f14 ?v0 (f4 (f16 (f17 (f18 (f19 f20 ?v4) ?v2) ?v3)) f21)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f6 ?v0 (f4 (f16 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f6 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (=> (not (= (f6 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f6 ?v0 (f4 (f16 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S7) (?v3 S9) (?v4 S9) (?v5 S9)) (=> (= (f14 ?v0 (f4 (f16 (f17 (f18 (f19 f20 ?v1) ?v2) ?v3)) f21)) f1) (=> (forall ((?v6 S5) (?v7 S6)) (=> (= (f23 (f24 ?v4 ?v6) ?v7) f1) (forall ((?v8 S6)) (=> (forall ((?v9 S5)) (=> (= (f23 (f24 ?v1 ?v9) ?v7) f1) (= (f23 (f24 ?v3 ?v9) ?v8) f1))) (= (f23 (f24 ?v5 ?v6) ?v8) f1))))) (= (f14 ?v0 (f4 (f16 (f17 (f18 (f19 f20 ?v4) ?v2) ?v5)) f21)) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f6 ?v0 f21) f1) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f21 (f4 (f16 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f4 (f16 ?v0) ?v1) f21))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f6 ?v0 (f4 (f16 ?v1) f21)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f4 (f16 ?v0) (f4 (f16 ?v1) f21)) (f4 (f16 ?v2) (f4 (f16 ?v3) f21))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f21) (not (= (f6 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f25 ?v0) f21) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f6 ?v0 f21) f1) false)))
(assert (forall ((?v0 S3)) (= (= f21 (f25 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f6 ?v1 f21) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f6 ?v1 f21) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f6 ?v1 ?v0) f1)) (not (= ?v0 f21)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f6 ?v1 ?v0) f1))) (= ?v0 f21))))
(assert (= f21 (f25 f8)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 ?v0 ?v1) f1) (= (f4 (f16 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (= (f6 ?v0 ?v1) f1) (= (f6 ?v0 (f4 (f16 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 ?v0))) (=> (not (= (f6 ?v0 ?v1) f1)) (=> (not (= (f6 ?v0 ?v2) f1)) (= (= (f4 ?v_0 ?v1) (f4 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f16 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (= (f6 ?v0 (f4 (f16 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f6 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f16 ?v0)) (?v_0 (f16 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f16 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f16 ?v0) (f25 ?v1)) (f25 (f4 (f7 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f16 ?v0) ?v1) (f25 (f4 (f5 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f6 ?v0 (f4 (f16 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f16 ?v0) f21) (f4 (f16 ?v1) f21)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f6 ?v0 (f4 (f16 ?v1) f21)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2)) (= (f26 f27 (f4 (f16 ?v0) f21)) ?v0)))
(assert (forall ((?v0 S2)) (= (= (f3 f21 ?v0) f1) (= f28 f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f21 ?v0) f1) (= f28 f1))))
(assert (forall ((?v0 S3) (?v1 S9)) (= (f14 ?v0 (f4 (f16 (f17 (f18 (f19 f20 ?v1) f29) ?v1)) f21)) f1)))
(assert (forall ((?v0 S3) (?v1 S9) (?v2 S7) (?v3 S9) (?v4 S7) (?v5 S9)) (let ((?v_0 (f19 f20 ?v1))) (=> (= (f14 ?v0 (f4 (f16 (f17 (f18 ?v_0 ?v2) ?v3)) f21)) f1) (=> (= (f14 ?v0 (f4 (f16 (f17 (f18 (f19 f20 ?v3) ?v4) ?v5)) f21)) f1) (= (f14 ?v0 (f4 (f16 (f17 (f18 ?v_0 (f30 (f31 f32 ?v2) ?v4)) ?v5)) f21)) f1))))))
(assert (forall ((?v0 S2)) (=> (forall ((?v1 S9) (?v2 S7) (?v3 S9)) (=> (= ?v0 (f17 (f18 (f19 f20 ?v1) ?v2) ?v3)) false)) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 ?v0 ?v1) f1) (=> (forall ((?v2 S3)) (=> (= ?v1 (f4 (f16 ?v0) ?v2)) (=> (not (= (f6 ?v0 ?v2) f1)) false))) false))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 ?v0 ?v1) f1) (exists ((?v2 S3)) (and (= ?v1 (f4 (f16 ?v0) ?v2)) (not (= (f6 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2)) (=> (= (f6 ?v1 ?v0) f1) false)) (= ?v0 f21))))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S7) (?v3 S9)) (=> (forall ((?v4 S5) (?v5 S6)) (=> (= (f23 (f24 ?v0 ?v4) ?v5) f1) (exists ((?v6 S9) (?v7 S9)) (and (= (f14 ?v1 (f4 (f16 (f17 (f18 (f19 f20 ?v6) ?v2) ?v7)) f21)) f1) (forall ((?v8 S6)) (=> (forall ((?v9 S5)) (=> (= (f23 (f24 ?v6 ?v9) ?v5) f1) (= (f23 (f24 ?v7 ?v9) ?v8) f1))) (= (f23 (f24 ?v3 ?v4) ?v8) f1))))))) (= (f14 ?v1 (f4 (f16 (f17 (f18 (f19 f20 ?v0) ?v2) ?v3)) f21)) f1))))
(assert (forall ((?v0 S6) (?v1 S8)) (= (f10 f29 ?v0 ?v1 ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6)) (=> (= (f10 f29 ?v0 ?v1 ?v2) f1) (=> (=> (= ?v2 ?v0) false) false))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S7) (?v5 S6)) (=> (= (f10 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f10 ?v4 ?v3 ?v2 ?v5) f1) (= (f10 (f30 (f31 f32 ?v0) ?v4) ?v1 ?v2 ?v5) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (not (= (f30 (f31 f32 ?v0) ?v1) f29))))
(assert (forall ((?v0 S7) (?v1 S7)) (not (= f29 (f30 (f31 f32 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S6) (?v3 S8) (?v4 S6)) (=> (= (f10 (f30 (f31 f32 ?v0) ?v1) ?v2 ?v3 ?v4) f1) (=> (forall ((?v5 S6)) (=> (= (f10 ?v0 ?v2 ?v3 ?v5) f1) (=> (= (f10 ?v1 ?v5 ?v3 ?v4) f1) false))) false))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (= (= (f30 (f31 f32 ?v0) ?v1) (f30 (f31 f32 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f33 ?v0 ?v1) f1) (forall ((?v2 S8)) (=> (forall ((?v3 S2)) (=> (= (f6 ?v3 ?v0) f1) (= (f3 (f22 ?v2) ?v3) f1))) (forall ((?v3 S2)) (=> (= (f6 ?v3 ?v1) f1) (= (f3 (f22 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S7) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S7) (?v5 S6) (?v6 S8) (?v7 S6)) (=> (= (f10 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f10 ?v4 ?v5 ?v6 ?v7) f1) (exists ((?v8 S8)) (and (= (f10 ?v0 ?v1 ?v8 ?v3) f1) (= (f10 ?v4 ?v5 ?v8 ?v7) f1)))))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f21)) (exists ((?v1 S2) (?v2 S3)) (and (= ?v0 (f4 (f16 ?v1) ?v2)) (not (= (f6 ?v1 ?v2) f1)))))))
(assert (forall ((?v0 S2)) (= (= (f3 f21 ?v0) f1) (= (f6 ?v0 f21) f1))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f34 ?v0) (f4 (f16 ?v1) f21)) ?v2) f1) (= ?v1 ?v2))))
(check-sat)
(exit)