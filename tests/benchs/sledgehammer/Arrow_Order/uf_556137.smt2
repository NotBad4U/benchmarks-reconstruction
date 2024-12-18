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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () S2)
(declare-fun f4 () S2)
(declare-fun f5 () S3)
(declare-fun f6 (S4 S3) S3)
(declare-fun f7 (S5 S2) S4)
(declare-fun f8 () S5)
(declare-fun f9 () S7)
(declare-fun f10 (S8 S7) S7)
(declare-fun f11 (S9 S6) S8)
(declare-fun f12 () S9)
(declare-fun f13 () S10)
(declare-fun f14 (S11 S10) S10)
(declare-fun f15 (S12 S7) S11)
(declare-fun f16 () S12)
(declare-fun f17 (S13 S3) S4)
(declare-fun f18 () S13)
(declare-fun f19 (S14 S7) S8)
(declare-fun f20 () S14)
(declare-fun f21 (S15 S10) S11)
(declare-fun f22 () S15)
(declare-fun f23 () S5)
(declare-fun f24 () S9)
(declare-fun f25 () S12)
(declare-fun f26 (S16 S3) S1)
(declare-fun f27 (S17 S7) S1)
(declare-fun f28 (S18 S10) S1)
(declare-fun f29 (S19 S3) S2)
(declare-fun f30 () S19)
(declare-fun f31 (S20 S7) S6)
(declare-fun f32 () S20)
(declare-fun f33 (S21 S10) S7)
(declare-fun f34 () S21)
(declare-fun f35 (S3) S1)
(declare-fun f36 (S7) S1)
(declare-fun f37 (S10) S1)
(declare-fun f38 () S13)
(declare-fun f39 () S14)
(declare-fun f40 () S15)
(assert (not (= f1 f2)))
(assert (not (exists ((?v0 S2)) (distinct f3 f4 ?v0))))
(assert (not (= f3 f4)))
(assert (exists ((?v0 S2) (?v1 S2) (?v2 S2)) (distinct ?v0 ?v1 ?v2)))
(assert (exists ((?v0 S2) (?v1 S2) (?v2 S2)) (distinct ?v0 ?v1 ?v2)))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f5 (f6 (f7 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (not (= f9 (f10 (f11 f12 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S10)) (not (= f13 (f14 (f15 f16 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f6 (f7 f8 ?v0) ?v1) f5))))
(assert (forall ((?v0 S6) (?v1 S7)) (not (= (f10 (f11 f12 ?v0) ?v1) f9))))
(assert (forall ((?v0 S7) (?v1 S10)) (not (= (f14 (f15 f16 ?v0) ?v1) f13))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f5)) (exists ((?v1 S2) (?v2 S3)) (= ?v0 (f6 (f7 f8 ?v1) ?v2))))))
(assert (forall ((?v0 S7)) (= (not (= ?v0 f9)) (exists ((?v1 S6) (?v2 S7)) (= ?v0 (f10 (f11 f12 ?v1) ?v2))))))
(assert (forall ((?v0 S10)) (= (not (= ?v0 f13)) (exists ((?v1 S7) (?v2 S10)) (= ?v0 (f14 (f15 f16 ?v1) ?v2))))))
(assert (forall ((?v0 S3)) (=> (=> (= ?v0 f5) false) (=> (forall ((?v1 S2) (?v2 S3)) (=> (= ?v0 (f6 (f7 f8 ?v1) ?v2)) false)) false))))
(assert (forall ((?v0 S7)) (=> (=> (= ?v0 f9) false) (=> (forall ((?v1 S6) (?v2 S7)) (=> (= ?v0 (f10 (f11 f12 ?v1) ?v2)) false)) false))))
(assert (forall ((?v0 S10)) (=> (=> (= ?v0 f13) false) (=> (forall ((?v1 S7) (?v2 S10)) (=> (= ?v0 (f14 (f15 f16 ?v1) ?v2)) false)) false))))
(assert (forall ((?v0 S3) (?v1 S2)) (not (= ?v0 (f6 (f7 f8 ?v1) ?v0)))))
(assert (forall ((?v0 S10) (?v1 S7)) (not (= ?v0 (f14 (f15 f16 ?v1) ?v0)))))
(assert (forall ((?v0 S7) (?v1 S6)) (not (= ?v0 (f10 (f11 f12 ?v1) ?v0)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f6 (f7 f8 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S7) (?v1 S10)) (not (= (f14 (f15 f16 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S6) (?v1 S7)) (not (= (f10 (f11 f12 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S3)) (= (= (f6 (f7 f8 ?v0) ?v1) (f6 (f7 f8 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S7) (?v1 S10) (?v2 S7) (?v3 S10)) (= (= (f14 (f15 f16 ?v0) ?v1) (f14 (f15 f16 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S6) (?v3 S7)) (= (= (f10 (f11 f12 ?v0) ?v1) (f10 (f11 f12 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f6 (f7 f8 ?v0) ?v1))) (= (f6 (f17 f18 ?v_0) f5) ?v_0))))
(assert (forall ((?v0 S6) (?v1 S7)) (let ((?v_0 (f10 (f11 f12 ?v0) ?v1))) (= (f10 (f19 f20 ?v_0) f9) ?v_0))))
(assert (forall ((?v0 S7) (?v1 S10)) (let ((?v_0 (f14 (f15 f16 ?v0) ?v1))) (= (f14 (f21 f22 ?v_0) f13) ?v_0))))
(assert (forall ((?v0 S2)) (= (f6 (f7 f23 ?v0) f5) (f6 (f7 f8 ?v0) f5))))
(assert (forall ((?v0 S6)) (= (f10 (f11 f24 ?v0) f9) (f10 (f11 f12 ?v0) f9))))
(assert (forall ((?v0 S7)) (= (f14 (f15 f25 ?v0) f13) (f14 (f15 f16 ?v0) f13))))
(assert (forall ((?v0 S3) (?v1 S16)) (=> (not (= ?v0 f5)) (=> (forall ((?v2 S2)) (= (f26 ?v1 (f6 (f7 f8 ?v2) f5)) f1)) (=> (forall ((?v2 S2) (?v3 S3)) (=> (not (= ?v3 f5)) (=> (= (f26 ?v1 ?v3) f1) (= (f26 ?v1 (f6 (f7 f8 ?v2) ?v3)) f1)))) (= (f26 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S7) (?v1 S17)) (=> (not (= ?v0 f9)) (=> (forall ((?v2 S6)) (= (f27 ?v1 (f10 (f11 f12 ?v2) f9)) f1)) (=> (forall ((?v2 S6) (?v3 S7)) (=> (not (= ?v3 f9)) (=> (= (f27 ?v1 ?v3) f1) (= (f27 ?v1 (f10 (f11 f12 ?v2) ?v3)) f1)))) (= (f27 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S10) (?v1 S18)) (=> (not (= ?v0 f13)) (=> (forall ((?v2 S7)) (= (f28 ?v1 (f14 (f15 f16 ?v2) f13)) f1)) (=> (forall ((?v2 S7) (?v3 S10)) (=> (not (= ?v3 f13)) (=> (= (f28 ?v1 ?v3) f1) (= (f28 ?v1 (f14 (f15 f16 ?v2) ?v3)) f1)))) (= (f28 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f29 f30 (f6 (f7 f8 ?v0) ?v1)) (ite (= ?v1 f5) ?v0 (f29 f30 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (f31 f32 (f10 (f11 f12 ?v0) ?v1)) (ite (= ?v1 f9) ?v0 (f31 f32 ?v1)))))
(assert (forall ((?v0 S7) (?v1 S10)) (= (f33 f34 (f14 (f15 f16 ?v0) ?v1)) (ite (= ?v1 f13) ?v0 (f33 f34 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S3)) (let ((?v_0 (f7 f8 ?v0)) (?v_1 (f7 f8 ?v2))) (= (f6 (f17 f18 (f6 ?v_0 ?v1)) (f6 ?v_1 ?v3)) (f6 ?v_0 (f6 ?v_1 (f6 (f17 f18 ?v1) ?v3)))))))
(assert (forall ((?v0 S7) (?v1 S10) (?v2 S7) (?v3 S10)) (let ((?v_0 (f15 f16 ?v0)) (?v_1 (f15 f16 ?v2))) (= (f14 (f21 f22 (f14 ?v_0 ?v1)) (f14 ?v_1 ?v3)) (f14 ?v_0 (f14 ?v_1 (f14 (f21 f22 ?v1) ?v3)))))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S6) (?v3 S7)) (let ((?v_0 (f11 f12 ?v0)) (?v_1 (f11 f12 ?v2))) (= (f10 (f19 f20 (f10 ?v_0 ?v1)) (f10 ?v_1 ?v3)) (f10 ?v_0 (f10 ?v_1 (f10 (f19 f20 ?v1) ?v3)))))))
(assert (forall ((?v0 S3)) (= (f6 (f17 f18 ?v0) f5) ?v0)))
(assert (forall ((?v0 S7)) (= (f10 (f19 f20 ?v0) f9) ?v0)))
(assert (forall ((?v0 S10)) (= (f14 (f21 f22 ?v0) f13) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 (f17 f18 f5) ?v0) ?v0)))
(assert (forall ((?v0 S7)) (= (f10 (f19 f20 f9) ?v0) ?v0)))
(assert (forall ((?v0 S10)) (= (f14 (f21 f22 f13) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f5) (= (f29 f30 (f6 (f7 f8 ?v1) ?v0)) ?v1))))
(assert (forall ((?v0 S7) (?v1 S6)) (=> (= ?v0 f9) (= (f31 f32 (f10 (f11 f12 ?v1) ?v0)) ?v1))))
(assert (forall ((?v0 S10) (?v1 S7)) (=> (= ?v0 f13) (= (f33 f34 (f14 (f15 f16 ?v1) ?v0)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (not (= ?v0 f5)) (= (f29 f30 (f6 (f7 f8 ?v1) ?v0)) (f29 f30 ?v0)))))
(assert (forall ((?v0 S7) (?v1 S6)) (=> (not (= ?v0 f9)) (= (f31 f32 (f10 (f11 f12 ?v1) ?v0)) (f31 f32 ?v0)))))
(assert (forall ((?v0 S10) (?v1 S7)) (=> (not (= ?v0 f13)) (= (f33 f34 (f14 (f15 f16 ?v1) ?v0)) (f33 f34 ?v0)))))
(assert (forall ((?v0 S3)) (= (= ?v0 f5) (= (f35 ?v0) f1))))
(assert (forall ((?v0 S7)) (= (= ?v0 f9) (= (f36 ?v0) f1))))
(assert (forall ((?v0 S10)) (= (= ?v0 f13) (= (f37 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (= (f35 ?v0) f1) (= ?v0 f5))))
(assert (forall ((?v0 S7)) (= (= (f36 ?v0) f1) (= ?v0 f9))))
(assert (forall ((?v0 S10)) (= (= (f37 ?v0) f1) (= ?v0 f13))))
(assert (= (= (f35 f5) f1) true))
(assert (= (= (f36 f9) f1) true))
(assert (= (= (f37 f13) f1) true))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f29 f30 (f6 (f17 f38 ?v0) (f6 (f7 f8 ?v1) f5))) ?v1)))
(assert (forall ((?v0 S7) (?v1 S6)) (= (f31 f32 (f10 (f19 f39 ?v0) (f10 (f11 f12 ?v1) f9))) ?v1)))
(assert (forall ((?v0 S10) (?v1 S7)) (= (f33 f34 (f14 (f21 f40 ?v0) (f14 (f15 f16 ?v1) f13))) ?v1)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f35 (f6 (f7 f8 ?v0) ?v1)) f1) false)))
(assert (forall ((?v0 S7) (?v1 S10)) (= (= (f37 (f14 (f15 f16 ?v0) ?v1)) f1) false)))
(assert (forall ((?v0 S6) (?v1 S7)) (= (= (f36 (f10 (f11 f12 ?v0) ?v1)) f1) false)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (let ((?v_0 (f21 f40 ?v0))) (= (f14 (f21 f40 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f21 f40 ?v1) ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f19 f39 ?v0))) (= (f10 (f19 f39 (f10 ?v_0 ?v1)) ?v2) (f10 ?v_0 (f10 (f19 f39 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f17 f38 ?v0))) (= (f6 (f17 f38 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f17 f38 ?v1) ?v2))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (= (= (f14 (f21 f40 ?v0) ?v1) (f14 (f21 f40 ?v2) ?v3)) (exists ((?v4 S10)) (let ((?v_0 (f21 f40 ?v4))) (or (and (= ?v0 (f14 (f21 f40 ?v2) ?v4)) (= (f14 ?v_0 ?v1) ?v3)) (and (= (f14 (f21 f40 ?v0) ?v4) ?v2) (= ?v1 (f14 ?v_0 ?v3)))))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (= (= (f10 (f19 f39 ?v0) ?v1) (f10 (f19 f39 ?v2) ?v3)) (exists ((?v4 S7)) (let ((?v_0 (f19 f39 ?v4))) (or (and (= ?v0 (f10 (f19 f39 ?v2) ?v4)) (= (f10 ?v_0 ?v1) ?v3)) (and (= (f10 (f19 f39 ?v0) ?v4) ?v2) (= ?v1 (f10 ?v_0 ?v3)))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (= (f6 (f17 f38 ?v0) ?v1) (f6 (f17 f38 ?v2) ?v3)) (exists ((?v4 S3)) (let ((?v_0 (f17 f38 ?v4))) (or (and (= ?v0 (f6 (f17 f38 ?v2) ?v4)) (= (f6 ?v_0 ?v1) ?v3)) (and (= (f6 (f17 f38 ?v0) ?v4) ?v2) (= ?v1 (f6 ?v_0 ?v3)))))))))
(check-sat)
(exit)
