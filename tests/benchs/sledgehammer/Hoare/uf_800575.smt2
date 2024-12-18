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
(declare-sort S25 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S3) S3)
(declare-fun f5 (S5 S2) S4)
(declare-fun f6 () S5)
(declare-fun f7 (S6 S3) S1)
(declare-fun f8 (S7 S2) S6)
(declare-fun f9 () S7)
(declare-fun f10 () S5)
(declare-fun f11 () S3)
(declare-fun f12 (S8 S3) S6)
(declare-fun f13 () S8)
(declare-fun f14 () S3)
(declare-fun f15 () S3)
(declare-fun f16 () S8)
(declare-fun f17 (S10 S9) S3)
(declare-fun f18 () S10)
(declare-fun f19 () S3)
(declare-fun f20 () S8)
(declare-fun f21 () S5)
(declare-fun f22 () S1)
(declare-fun f23 (S12 S6) S1)
(declare-fun f24 (S13 S6) S12)
(declare-fun f25 () S13)
(declare-fun f26 () S6)
(declare-fun f27 (S14 S6) S6)
(declare-fun f28 (S15 S3) S14)
(declare-fun f29 () S15)
(declare-fun f30 (S16 S3) S12)
(declare-fun f31 () S16)
(declare-fun f32 (S17 S1) S1)
(declare-fun f33 (S18 S1) S17)
(declare-fun f34 () S18)
(declare-fun f35 () S4)
(declare-fun f36 () S1)
(declare-fun f37 (S19 S3) S2)
(declare-fun f38 () S19)
(declare-fun f39 () S14)
(declare-fun f40 (S20 S6) S3)
(declare-fun f41 (S21 S1) S3)
(declare-fun f42 (S22 S12) S1)
(declare-fun f43 (S23 S12) S22)
(declare-fun f44 () S23)
(declare-fun f45 () S13)
(declare-fun f46 () S8)
(declare-fun f47 (S25 S24) S4)
(declare-fun f48 () S25)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 f6 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f7 (f8 f9 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 f10 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f11 ?v0) f1) false)))
(assert (not (= (f7 (f12 f13 f14) f15) f1)))
(assert (= (f7 (f12 f16 f14) f15) f1))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f16 ?v2))) (=> (= (f7 (f12 f16 ?v0) ?v1) f1) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f7 (f12 f13 ?v0) ?v1) f1) (forall ((?v2 S9)) (=> (forall ((?v3 S2)) (=> (= (f7 (f8 f9 ?v3) ?v0) f1) (= (f3 (f17 f18 ?v2) ?v3) f1))) (forall ((?v3 S2)) (=> (= (f7 (f8 f9 ?v3) ?v1) f1) (= (f3 (f17 f18 ?v2) ?v3) f1))))))))
(assert (forall ((?v0 S3)) (= (f7 (f12 f16 ?v0) f19) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (= (f7 (f12 f16 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f16 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (=> (= (f7 (f12 f20 ?v2) ?v1) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f7 (f12 f16 ?v0) ?v1) f1) (=> (= (f7 (f12 f20 ?v0) ?v2) f1) (= (f7 (f12 f16 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f12 f16 ?v0)) (?v_1 (f5 f21 ?v1))) (=> (= (f7 ?v_0 (f4 ?v_1 f19)) f1) (=> (= (f7 ?v_0 ?v2) f1) (= (f7 ?v_0 (f4 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f12 f16 ?v0)) (?v_1 (f5 f21 ?v1))) (=> (= (f7 ?v_0 (f4 ?v_1 ?v2)) f1) (and (= (f7 ?v_0 (f4 ?v_1 f19)) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (= (= f22 f1) (exists ((?v0 S11) (?v1 S11)) (not (= ?v0 ?v1)))))
(assert (=> (= f22 f1) (forall ((?v0 S11)) (=> (forall ((?v1 S11)) (= ?v1 ?v0)) false))))
(assert (forall ((?v0 S6)) (= (f23 (f24 f25 f26) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f7 (f12 f20 f19) ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S3)) (let ((?v_0 (f27 (f28 f29 ?v1) f26))) (=> (= (f23 (f24 f25 ?v0) ?v_0) f1) (or (= ?v0 f26) (= ?v0 ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S2)) (let ((?v_0 (f4 (f5 f21 ?v1) f19))) (=> (= (f7 (f12 f20 ?v0) ?v_0) f1) (or (= ?v0 f19) (= ?v0 ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (let ((?v_0 (f30 f31 ?v2))) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f8 f9 ?v2))) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 (f24 f25 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f7 (f12 f20 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (=> (= (f7 ?v_0 (f4 (f5 f21 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f7 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f8 f9 ?v0))) (=> (=> (not (= (f7 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f7 ?v_0 (f4 (f5 f21 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f7 (f8 f9 ?v0) f19) f1) false)))
(assert (forall ((?v0 S6)) (= (f23 (f24 f25 ?v0) ?v0) f1)))
(assert (forall ((?v0 S1)) (= (f32 (f33 f34 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f7 (f12 f20 ?v0) ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S3)) (= (f23 (f24 f25 ?v0) (f27 (f28 f29 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S2)) (= (f7 (f12 f20 ?v0) (f4 (f5 f21 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (= (= (f23 (f24 f25 (f27 (f28 f29 ?v0) ?v1)) ?v2) f1) (and (= (f23 (f30 f31 ?v0) ?v2) f1) (= (f23 (f24 f25 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (= (= (f7 (f12 f20 (f4 (f5 f21 ?v0) ?v1)) ?v2) f1) (and (= (f7 (f8 f9 ?v0) ?v2) f1) (= (f7 (f12 f20 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (let ((?v_0 (f24 f25 ?v1))) (=> (not (= (f23 (f30 f31 ?v0) ?v1) f1)) (= (= (f23 ?v_0 (f27 (f28 f29 ?v0) ?v2)) f1) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f20 ?v1))) (=> (not (= (f7 (f8 f9 ?v0) ?v1) f1)) (= (= (f7 ?v_0 (f4 (f5 f21 ?v0) ?v2)) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f24 f25 ?v2))) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f33 f34 ?v2))) (=> (= (f32 (f33 f34 ?v0) ?v1) f1) (=> (= (f32 ?v_0 ?v0) f1) (= (f32 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f20 ?v2))) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 (f24 f25 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f32 (f33 f34 ?v0) ?v1) f1) (=> (= (f32 (f33 f34 ?v1) ?v0) f1) (= (= ?v1 f1) (= ?v0 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f7 (f12 f20 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (=> (= (f23 (f24 f25 ?v1) ?v2) f1) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f33 f34 ?v0))) (=> (= (f32 ?v_0 ?v1) f1) (=> (= (f32 (f33 f34 ?v1) ?v2) f1) (= (f32 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f20 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (=> (= (f7 (f12 f20 ?v1) ?v2) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 (f24 f25 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f32 (f33 f34 ?v0) ?v1) f1) (=> (= (f32 (f33 f34 ?v1) ?v0) f1) (= (= ?v0 f1) (= ?v1 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f7 (f12 f20 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f23 (f24 f25 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (f32 (f33 f34 ?v0) ?v1) f1) (=> (= (= ?v0 f1) (= ?v2 f1)) (= (f32 (f33 f34 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f7 (f12 f20 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f33 f34 ?v0))) (=> (= (f32 ?v_0 ?v1) f1) (=> (= (= ?v1 f1) (= ?v2 f1)) (= (f32 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f20 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f24 f25 ?v2))) (=> (= ?v0 ?v1) (=> (= (f23 ?v_0 ?v1) f1) (= (f23 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f33 f34 ?v2))) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f32 ?v_0 ?v1) f1) (= (f32 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f20 ?v2))) (=> (= ?v0 ?v1) (=> (= (f7 ?v_0 ?v1) f1) (= (f7 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= ?v0 ?v1) (=> (= (f23 (f24 f25 ?v1) ?v2) f1) (= (f23 (f24 f25 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f32 (f33 f34 ?v1) ?v2) f1) (= (f32 (f33 f34 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= ?v0 ?v1) (=> (= (f7 (f12 f20 ?v1) ?v2) f1) (= (f7 (f12 f20 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (= (= (f23 (f24 f25 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f32 (f33 f34 ?v0) ?v1) f1) (= (= (f32 (f33 f34 ?v1) ?v0) f1) (= (= ?v1 f1) (= ?v0 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (= (= (f7 (f12 f20 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= ?v0 ?v1) (= (f23 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (= ?v0 f1) (= ?v1 f1)) (= (f32 (f33 f34 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f7 (f12 f20 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= ?v0 ?v1) (and (= (f23 (f24 f25 ?v0) ?v1) f1) (= (f23 (f24 f25 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (= ?v0 f1) (= ?v1 f1)) (and (= (f32 (f33 f34 ?v0) ?v1) f1) (= (f32 (f33 f34 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (and (= (f7 (f12 f20 ?v0) ?v1) f1) (= (f7 (f12 f20 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f19) (not (= (f7 (f8 f9 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f4 f35 ?v0) f19) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f7 (f8 f9 ?v0) f19) f1) false)))
(assert (forall ((?v0 S3)) (= (= f19 (f4 f35 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f7 (f8 f9 ?v1) f19) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f7 (f8 f9 ?v1) f19) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f7 (f8 f9 ?v1) ?v0) f1)) (not (= ?v0 f19)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f7 (f8 f9 ?v1) ?v0) f1))) (= ?v0 f19))))
(assert (= f19 (f4 f35 f11)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f7 (f8 f9 ?v0) ?v1) f1) (= (f4 (f5 f21 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f8 f9 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (= (f7 ?v_0 (f4 (f5 f21 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0)) (?v_1 (f5 f21 ?v0))) (=> (not (= (f7 ?v_0 ?v1) f1)) (=> (not (= (f7 ?v_0 ?v2) f1)) (= (= (f4 ?v_1 ?v1) (f4 ?v_1 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 f21 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (= (f7 ?v_0 (f4 (f5 f21 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f5 f21 ?v0)) (?v_0 (f5 f21 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f5 f21 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f5 f21 ?v0) (f4 f35 ?v1)) (f4 f35 (f4 (f5 f10 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f5 f21 ?v0) ?v1) (f4 f35 (f4 (f5 f6 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f7 (f8 f9 ?v0) (f4 (f5 f21 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= ?v0 ?v1) (=> (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 (f24 f25 ?v1) ?v0) f1) false)) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (=> (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f7 (f12 f20 ?v1) ?v0) f1) false)) false))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (=> (= (f23 (f24 f25 ?v1) ?v2) f1) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f20 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (=> (= (f7 (f12 f20 ?v1) ?v2) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (let ((?v_0 (f30 f31 ?v2))) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f8 f9 ?v2))) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (let ((?v_0 (f30 f31 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (=> (= (f23 (f24 f25 ?v1) ?v2) f1) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (=> (= (f7 (f12 f20 ?v1) ?v2) f1) (= (f7 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (let ((?v_0 (f30 f31 ?v2))) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f8 f9 ?v2))) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= ?v0 ?v1) (= (f23 (f24 f25 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f7 (f12 f20 ?v1) ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= ?v0 ?v1) (= (f23 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f7 (f12 f20 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= ?v0 ?v1) (and (= (f23 (f24 f25 ?v0) ?v1) f1) (= (f23 (f24 f25 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (and (= (f7 (f12 f20 ?v0) ?v1) f1) (= (f7 (f12 f20 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S6)) (= (f23 (f24 f25 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f7 (f12 f20 ?v0) ?v0) f1)))
(assert (forall ((?v0 S1)) (=> (= (f32 (f33 f34 ?v0) f36) f1) (= (= ?v0 f1) (= f36 f1)))))
(assert (forall ((?v0 S6)) (=> (= (f23 (f24 f25 ?v0) f26) f1) (= ?v0 f26))))
(assert (forall ((?v0 S3)) (=> (= (f7 (f12 f20 ?v0) f19) f1) (= ?v0 f19))))
(assert (forall ((?v0 S1)) (= (= (f32 (f33 f34 ?v0) f36) f1) (= (= ?v0 f1) (= f36 f1)))))
(assert (forall ((?v0 S6)) (= (= (f23 (f24 f25 ?v0) f26) f1) (= ?v0 f26))))
(assert (forall ((?v0 S3)) (= (= (f7 (f12 f20 ?v0) f19) f1) (= ?v0 f19))))
(assert (forall ((?v0 S1)) (= (f32 (f33 f34 f36) ?v0) f1)))
(assert (forall ((?v0 S6)) (= (f23 (f24 f25 f26) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f7 (f12 f20 f19) ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (=> (= (f32 (f33 f34 (f7 ?v0 ?v2)) (f7 ?v1 ?v2)) f1) false) false))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (=> (= (f32 (f33 f34 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1) false) false))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (= (f32 (f33 f34 (f7 ?v0 ?v2)) (f7 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (= (f32 (f33 f34 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f23 (f24 f25 ?v0) ?v1) f1) (forall ((?v2 S3)) (= (f32 (f33 f34 (f7 ?v0 ?v2)) (f7 ?v1 ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f7 (f12 f20 ?v0) ?v1) f1) (forall ((?v2 S2)) (= (f32 (f33 f34 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f19 ?v0) f1) (= f36 f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f19 ?v0) f1) (= f36 f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f5 f21 ?v0) f19) (f4 (f5 f21 ?v1) f19)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f7 (f8 f9 ?v0) (f4 (f5 f21 ?v1) f19)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f4 (f5 f21 ?v0) (f4 (f5 f21 ?v1) f19)) (f4 (f5 f21 ?v2) (f4 (f5 f21 ?v3) f19))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f7 (f8 f9 ?v0) ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f4 f35 ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f7 (f8 f9 ?v0) (f4 (f5 f21 ?v1) f19)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f4 (f5 f21 ?v0) ?v1) f19))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f19 (f4 (f5 f21 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (= (f23 (f24 f25 ?v0) f26) f1) (= ?v0 f26))))
(assert (forall ((?v0 S3)) (= (= (f7 (f12 f20 ?v0) f19) f1) (= ?v0 f19))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (let ((?v_0 (f28 f29 ?v2))) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (= (f23 (f24 f25 (f27 ?v_0 ?v0)) (f27 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f5 f21 ?v2))) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (= (f7 (f12 f20 (f4 ?v_0 ?v0)) (f4 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (= (f23 ?v_0 (f27 (f28 f29 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f12 f20 ?v0))) (=> (= (f7 ?v_0 ?v1) f1) (= (f7 ?v_0 (f4 (f5 f21 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (forall ((?v2 S3)) (let ((?v_0 (f30 f31 ?v2))) (=> (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 ?v1) f1)))) (= (f23 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S2)) (let ((?v_0 (f8 f9 ?v2))) (=> (= (f7 ?v_0 ?v0) f1) (= (f7 ?v_0 ?v1) f1)))) (= (f7 (f12 f20 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2)) (= (f37 f38 (f4 (f5 f21 ?v0) f19)) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (forall ((?v2 S3)) (= (f32 (f33 f34 (f7 ?v0 ?v2)) (f7 ?v1 ?v2)) f1)) (= (f23 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S2)) (= (f32 (f33 f34 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1)) (= (f7 (f12 f20 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (forall ((?v2 S3)) (=> (= (f7 ?v0 ?v2) f1) (= (f7 ?v1 ?v2) f1))) (= (f23 (f24 f25 (f27 f39 ?v0)) (f27 f39 ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S2)) (=> (= (f3 ?v0 ?v2) f1) (= (f3 ?v1 ?v2) f1))) (= (f7 (f12 f20 (f4 f35 ?v0)) (f4 f35 ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f7 (f8 f9 ?v0) ?v1) f1) (=> (forall ((?v2 S3)) (=> (= ?v1 (f4 (f5 f21 ?v0) ?v2)) (=> (not (= (f7 (f8 f9 ?v0) ?v2) f1)) false))) false))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f7 (f8 f9 ?v0) ?v1) f1) (exists ((?v2 S3)) (and (= ?v1 (f4 (f5 f21 ?v0) ?v2)) (not (= (f7 (f8 f9 ?v0) ?v2) f1)))))))
(assert (forall ((?v0 S3)) (=> (forall ((?v1 S2)) (=> (= (f7 (f8 f9 ?v1) ?v0) f1) false)) (= ?v0 f19))))
(assert (forall ((?v0 S20) (?v1 S6) (?v2 S3) (?v3 S6)) (=> (= (f7 (f12 f20 (f40 ?v0 ?v1)) ?v2) f1) (=> (= (f23 (f24 f25 ?v3) ?v1) f1) (=> (forall ((?v4 S6) (?v5 S6)) (=> (= (f23 (f24 f25 ?v5) ?v4) f1) (= (f7 (f12 f20 (f40 ?v0 ?v5)) (f40 ?v0 ?v4)) f1))) (= (f7 (f12 f20 (f40 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S21) (?v1 S1) (?v2 S3) (?v3 S1)) (=> (= (f7 (f12 f20 (f41 ?v0 ?v1)) ?v2) f1) (=> (= (f32 (f33 f34 ?v3) ?v1) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f32 (f33 f34 ?v5) ?v4) f1) (= (f7 (f12 f20 (f41 ?v0 ?v5)) (f41 ?v0 ?v4)) f1))) (= (f7 (f12 f20 (f41 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S6) (?v3 S3)) (=> (= (f23 (f24 f25 (f12 ?v0 ?v1)) ?v2) f1) (=> (= (f7 (f12 f20 ?v3) ?v1) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v5) ?v4) f1) (= (f23 (f24 f25 (f12 ?v0 ?v5)) (f12 ?v0 ?v4)) f1))) (= (f23 (f24 f25 (f12 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S3) (?v2 S1) (?v3 S3)) (=> (= (f32 (f33 f34 (f7 ?v0 ?v1)) ?v2) f1) (=> (= (f7 (f12 f20 ?v3) ?v1) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v5) ?v4) f1) (= (f32 (f33 f34 (f7 ?v0 ?v5)) (f7 ?v0 ?v4)) f1))) (= (f32 (f33 f34 (f7 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S14) (?v2 S6) (?v3 S6)) (=> (= ?v0 (f27 ?v1 ?v2)) (=> (= (f23 (f24 f25 ?v3) ?v2) f1) (=> (forall ((?v4 S6) (?v5 S6)) (=> (= (f23 (f24 f25 ?v5) ?v4) f1) (= (f23 (f24 f25 (f27 ?v1 ?v5)) (f27 ?v1 ?v4)) f1))) (= (f23 (f24 f25 (f27 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S1) (?v1 S17) (?v2 S1) (?v3 S1)) (=> (= (= ?v0 f1) (= (f32 ?v1 ?v2) f1)) (=> (= (f32 (f33 f34 ?v3) ?v2) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f32 (f33 f34 ?v5) ?v4) f1) (= (f32 (f33 f34 (f32 ?v1 ?v5)) (f32 ?v1 ?v4)) f1))) (= (f32 (f33 f34 (f32 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S3) (?v3 S3)) (=> (= ?v0 (f4 ?v1 ?v2)) (=> (= (f7 (f12 f20 ?v3) ?v2) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v5) ?v4) f1) (= (f7 (f12 f20 (f4 ?v1 ?v5)) (f4 ?v1 ?v4)) f1))) (= (f7 (f12 f20 (f4 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S20) (?v2 S6) (?v3 S6)) (let ((?v_0 (f12 f20 ?v0))) (=> (= (f7 ?v_0 (f40 ?v1 ?v2)) f1) (=> (= (f23 (f24 f25 ?v2) ?v3) f1) (=> (forall ((?v4 S6) (?v5 S6)) (=> (= (f23 (f24 f25 ?v4) ?v5) f1) (= (f7 (f12 f20 (f40 ?v1 ?v4)) (f40 ?v1 ?v5)) f1))) (= (f7 ?v_0 (f40 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S21) (?v2 S1) (?v3 S1)) (let ((?v_0 (f12 f20 ?v0))) (=> (= (f7 ?v_0 (f41 ?v1 ?v2)) f1) (=> (= (f32 (f33 f34 ?v2) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f32 (f33 f34 ?v4) ?v5) f1) (= (f7 (f12 f20 (f41 ?v1 ?v4)) (f41 ?v1 ?v5)) f1))) (= (f7 ?v_0 (f41 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S3) (?v3 S3)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f23 ?v_0 (f12 ?v1 ?v2)) f1) (=> (= (f7 (f12 f20 ?v2) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v4) ?v5) f1) (= (f23 (f24 f25 (f12 ?v1 ?v4)) (f12 ?v1 ?v5)) f1))) (= (f23 ?v_0 (f12 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S1) (?v1 S6) (?v2 S3) (?v3 S3)) (let ((?v_0 (f33 f34 ?v0))) (=> (= (f32 ?v_0 (f7 ?v1 ?v2)) f1) (=> (= (f7 (f12 f20 ?v2) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v4) ?v5) f1) (= (f32 (f33 f34 (f7 ?v1 ?v4)) (f7 ?v1 ?v5)) f1))) (= (f32 ?v_0 (f7 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6) (?v3 S8)) (let ((?v_0 (f24 f25 ?v2))) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f23 ?v_0 (f12 ?v3 ?v0)) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v5) ?v4) f1) (= (f23 (f24 f25 (f12 ?v3 ?v5)) (f12 ?v3 ?v4)) f1))) (= (f23 ?v_0 (f12 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S1) (?v3 S6)) (let ((?v_0 (f33 f34 ?v2))) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f32 ?v_0 (f7 ?v3 ?v0)) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v5) ?v4) f1) (= (f32 (f33 f34 (f7 ?v3 ?v5)) (f7 ?v3 ?v4)) f1))) (= (f32 ?v_0 (f7 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3) (?v3 S20)) (let ((?v_0 (f12 f20 ?v2))) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f7 ?v_0 (f40 ?v3 ?v0)) f1) (=> (forall ((?v4 S6) (?v5 S6)) (=> (= (f23 (f24 f25 ?v5) ?v4) f1) (= (f7 (f12 f20 (f40 ?v3 ?v5)) (f40 ?v3 ?v4)) f1))) (= (f7 ?v_0 (f40 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S3) (?v3 S21)) (let ((?v_0 (f12 f20 ?v2))) (=> (= (f32 (f33 f34 ?v0) ?v1) f1) (=> (= (f7 ?v_0 (f41 ?v3 ?v0)) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f32 (f33 f34 ?v5) ?v4) f1) (= (f7 (f12 f20 (f41 ?v3 ?v5)) (f41 ?v3 ?v4)) f1))) (= (f7 ?v_0 (f41 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S14) (?v3 S6)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f27 ?v2 ?v0) ?v3) (=> (forall ((?v4 S6) (?v5 S6)) (=> (= (f23 (f24 f25 ?v5) ?v4) f1) (= (f23 (f24 f25 (f27 ?v2 ?v5)) (f27 ?v2 ?v4)) f1))) (= (f23 (f24 f25 ?v3) (f27 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S17) (?v3 S1)) (=> (= (f32 (f33 f34 ?v0) ?v1) f1) (=> (= (= (f32 ?v2 ?v0) f1) (= ?v3 f1)) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f32 (f33 f34 ?v5) ?v4) f1) (= (f32 (f33 f34 (f32 ?v2 ?v5)) (f32 ?v2 ?v4)) f1))) (= (f32 (f33 f34 ?v3) (f32 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S4) (?v3 S3)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f4 ?v2 ?v0) ?v3) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v5) ?v4) f1) (= (f7 (f12 f20 (f4 ?v2 ?v5)) (f4 ?v2 ?v4)) f1))) (= (f7 (f12 f20 ?v3) (f4 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S8) (?v3 S6)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f12 ?v2 ?v1) ?v3) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v4) ?v5) f1) (= (f23 (f24 f25 (f12 ?v2 ?v4)) (f12 ?v2 ?v5)) f1))) (= (f23 (f24 f25 (f12 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6) (?v3 S1)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (= (f7 ?v2 ?v1) f1) (= ?v3 f1)) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v4) ?v5) f1) (= (f32 (f33 f34 (f7 ?v2 ?v4)) (f7 ?v2 ?v5)) f1))) (= (f32 (f33 f34 (f7 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S20) (?v3 S3)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f40 ?v2 ?v1) ?v3) (=> (forall ((?v4 S6) (?v5 S6)) (=> (= (f23 (f24 f25 ?v4) ?v5) f1) (= (f7 (f12 f20 (f40 ?v2 ?v4)) (f40 ?v2 ?v5)) f1))) (= (f7 (f12 f20 (f40 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S21) (?v3 S3)) (=> (= (f32 (f33 f34 ?v0) ?v1) f1) (=> (= (f41 ?v2 ?v1) ?v3) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f32 (f33 f34 ?v4) ?v5) f1) (= (f7 (f12 f20 (f41 ?v2 ?v4)) (f41 ?v2 ?v5)) f1))) (= (f7 (f12 f20 (f41 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S8) (?v3 S6)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f23 (f24 f25 (f12 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v4) ?v5) f1) (= (f23 (f24 f25 (f12 ?v2 ?v4)) (f12 ?v2 ?v5)) f1))) (= (f23 (f24 f25 (f12 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6) (?v3 S1)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f32 (f33 f34 (f7 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v4) ?v5) f1) (= (f32 (f33 f34 (f7 ?v2 ?v4)) (f7 ?v2 ?v5)) f1))) (= (f32 (f33 f34 (f7 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S20) (?v3 S3)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f7 (f12 f20 (f40 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S6) (?v5 S6)) (=> (= (f23 (f24 f25 ?v4) ?v5) f1) (= (f7 (f12 f20 (f40 ?v2 ?v4)) (f40 ?v2 ?v5)) f1))) (= (f7 (f12 f20 (f40 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S21) (?v3 S3)) (=> (= (f32 (f33 f34 ?v0) ?v1) f1) (=> (= (f7 (f12 f20 (f41 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f32 (f33 f34 ?v4) ?v5) f1) (= (f7 (f12 f20 (f41 ?v2 ?v4)) (f41 ?v2 ?v5)) f1))) (= (f7 (f12 f20 (f41 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S3) (?v3 S3)) (=> (= ?v0 (f12 ?v1 ?v2)) (=> (= (f7 (f12 f20 ?v2) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v4) ?v5) f1) (= (f23 (f24 f25 (f12 ?v1 ?v4)) (f12 ?v1 ?v5)) f1))) (= (f23 (f24 f25 ?v0) (f12 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S1) (?v1 S6) (?v2 S3) (?v3 S3)) (=> (= (= ?v0 f1) (= (f7 ?v1 ?v2) f1)) (=> (= (f7 (f12 f20 ?v2) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f7 (f12 f20 ?v4) ?v5) f1) (= (f32 (f33 f34 (f7 ?v1 ?v4)) (f7 ?v1 ?v5)) f1))) (= (f32 (f33 f34 ?v0) (f7 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S3) (?v1 S20) (?v2 S6) (?v3 S6)) (=> (= ?v0 (f40 ?v1 ?v2)) (=> (= (f23 (f24 f25 ?v2) ?v3) f1) (=> (forall ((?v4 S6) (?v5 S6)) (=> (= (f23 (f24 f25 ?v4) ?v5) f1) (= (f7 (f12 f20 (f40 ?v1 ?v4)) (f40 ?v1 ?v5)) f1))) (= (f7 (f12 f20 ?v0) (f40 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S3) (?v1 S21) (?v2 S1) (?v3 S1)) (=> (= ?v0 (f41 ?v1 ?v2)) (=> (= (f32 (f33 f34 ?v2) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f32 (f33 f34 ?v4) ?v5) f1) (= (f7 (f12 f20 (f41 ?v1 ?v4)) (f41 ?v1 ?v5)) f1))) (= (f7 (f12 f20 ?v0) (f41 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f7 ?v0 ?v2) f1) (= (f7 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (=> (= (f3 ?v0 ?v2) f1) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f19 ?v0) f1) (= (f7 (f8 f9 ?v0) f19) f1))))
(assert (forall ((?v0 S6) (?v1 S3) (?v2 S6)) (=> (= (f7 ?v0 ?v1) f1) (=> (= (f23 (f24 f25 ?v0) ?v2) f1) (= (f7 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f7 (f12 f20 ?v0) ?v2) f1) (= (f3 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (forall ((?v2 S3)) (=> (= (f7 ?v0 ?v2) f1) (= (f7 ?v1 ?v2) f1))) (= (f23 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S2)) (=> (= (f3 ?v0 ?v2) f1) (= (f3 ?v1 ?v2) f1))) (= (f7 (f12 f20 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (= (f42 (f43 f44 (f24 f45 ?v0)) (f24 f45 ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f7 (f12 f20 ?v0) ?v1) f1) (= (f23 (f24 f25 (f12 f46 ?v0)) (f12 f46 ?v1)) f1))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f19)) (exists ((?v1 S2) (?v2 S3)) (and (= ?v0 (f4 (f5 f21 ?v1) ?v2)) (not (= (f7 (f8 f9 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S24) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f47 f48 ?v0) (f4 (f5 f21 ?v1) f19)) ?v2) f1) (= ?v1 ?v2))))
(assert (forall ((?v0 S24) (?v1 S2)) (=> (= (f3 (f4 (f47 f48 ?v0) f19) ?v1) f1) false)))
(assert (forall ((?v0 S24) (?v1 S3) (?v2 S2)) (=> (= (f3 (f4 (f47 f48 ?v0) ?v1) ?v2) f1) (not (= ?v1 f19)))))
(check-sat)
(exit)
