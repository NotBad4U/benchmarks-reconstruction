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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 () S4)
(declare-fun f7 (S7 S5) S1)
(declare-fun f8 (S8 S6) S7)
(declare-fun f9 (S9 S5) S8)
(declare-fun f10 () S9)
(declare-fun f11 () S8)
(declare-fun f12 (S10 S3) S3)
(declare-fun f13 (S11 S2) S10)
(declare-fun f14 () S11)
(declare-fun f15 () S11)
(declare-fun f16 () S9)
(declare-fun f17 (S12 S6) S8)
(declare-fun f18 (S13 S8) S12)
(declare-fun f19 () S13)
(declare-fun f20 (S14 S8) S8)
(declare-fun f21 (S15 S8) S14)
(declare-fun f22 () S15)
(declare-fun f23 (S16 S1) S14)
(declare-fun f24 () S16)
(declare-fun f25 () S8)
(declare-fun f26 () S8)
(declare-fun f27 () S3)
(declare-fun f28 (S17 S3) S1)
(declare-fun f29 (S18 S3) S17)
(declare-fun f30 () S18)
(declare-fun f31 () S3)
(declare-fun f32 () S11)
(declare-fun f33 (S19 S8) S2)
(declare-fun f34 (S20 S21) S19)
(declare-fun f35 (S22 S8) S20)
(declare-fun f36 () S22)
(declare-fun f37 () S21)
(declare-fun f38 () S8)
(declare-fun f39 () S3)
(declare-fun f40 (S23 S2) S17)
(declare-fun f41 () S23)
(declare-fun f42 () S10)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f6 ?v0) ?v1) f1) (= ?v1 ?v0))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f7 (f8 (f9 f10 ?v0) ?v1) ?v2) f1) (and (= ?v0 ?v2) (= (f7 (f8 f11 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f12 (f13 f14 ?v0) ?v1) ?v2) f1) (and (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f12 (f13 f15 ?v0) ?v1) ?v2) f1) (and (= ?v2 ?v0) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f7 (f8 (f9 f16 ?v0) ?v1) ?v2) f1) (= ?v2 ?v0))))
(assert (forall ((?v0 S8) (?v1 S6) (?v2 S6)) (= (f8 (f17 (f18 f19 ?v0) ?v1) ?v2) (f8 ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S6) (?v3 S5)) (= (= (f7 (f8 (f20 (f21 f22 ?v0) ?v1) ?v2) ?v3) f1) (or (= (f7 (f8 ?v0 ?v2) ?v3) f1) (= (f7 (f8 ?v1 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S1) (?v1 S8) (?v2 S6) (?v3 S5)) (= (= (f7 (f8 (f20 (f23 f24 ?v0) ?v1) ?v2) ?v3) f1) (and (= (f7 (f8 ?v1 ?v2) ?v3) f1) (= ?v0 f1)))))
(assert (forall ((?v0 S6) (?v1 S5)) (= (= (f7 (f8 f25 ?v0) ?v1) f1) false)))
(assert (forall ((?v0 S6) (?v1 S5)) (= (= (f7 (f8 f26 ?v0) ?v1) f1) true)))
(assert (forall ((?v0 S2)) (= (= (f3 f27 ?v0) f1) false)))
(assert (not (= (f28 (f29 f30 f31) (f12 (f13 f32 (f33 (f34 (f35 f36 f11) f37) f38)) f39)) f1)))
(assert (forall ((?v0 S5)) (= (f28 (f29 f30 f31) (f12 (f13 f32 (f33 (f34 (f35 f36 (f9 f10 ?v0)) f37) f38)) f39)) f1)))
(assert (forall ((?v0 S3)) (= (f28 (f29 f30 ?v0) f39) f1)))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S21)) (= (f28 (f29 f30 ?v0) (f12 (f13 f32 (f33 (f34 (f35 f36 ?v1) ?v2) f26)) f39)) f1)))
(assert (forall ((?v0 S3) (?v1 S21) (?v2 S8)) (= (f28 (f29 f30 ?v0) (f12 (f13 f32 (f33 (f34 (f35 f36 f25) ?v1) ?v2)) f39)) f1)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f12 (f13 f32 ?v0) f39))) (= (f28 (f29 f30 ?v_0) ?v_0) f1))))
(assert (forall ((?v0 S8) (?v1 S21) (?v2 S8) (?v3 S8) (?v4 S21) (?v5 S8)) (= (= (f33 (f34 (f35 f36 ?v0) ?v1) ?v2) (f33 (f34 (f35 f36 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f29 f30 ?v2))) (=> (= (f28 (f29 f30 ?v0) ?v1) f1) (=> (= (f28 ?v_0 ?v0) f1) (= (f28 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f29 f30 ?v0)) (?v_1 (f13 f32 ?v1))) (=> (= (f28 ?v_0 (f12 ?v_1 f39)) f1) (=> (= (f28 ?v_0 ?v2) f1) (= (f28 ?v_0 (f12 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f29 f30 ?v0)) (?v_1 (f13 f32 ?v1))) (=> (= (f28 ?v_0 (f12 ?v_1 ?v2)) f1) (and (= (f28 ?v_0 (f12 ?v_1 f39)) f1) (= (f28 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S21) (?v3 S8) (?v4 S8) (?v5 S8)) (let ((?v_0 (f29 f30 ?v0))) (=> (= (f28 ?v_0 (f12 (f13 f32 (f33 (f34 (f35 f36 ?v1) ?v2) ?v3)) f39)) f1) (=> (= (f28 ?v_0 (f12 (f13 f32 (f33 (f34 (f35 f36 ?v4) ?v2) ?v5)) f39)) f1) (= (f28 ?v_0 (f12 (f13 f32 (f33 (f34 (f35 f36 (f20 (f21 f22 ?v1) ?v4)) ?v2) (f20 (f21 f22 ?v3) ?v5))) f39)) f1))))))
(assert (forall ((?v0 S1) (?v1 S3) (?v2 S8) (?v3 S21) (?v4 S8)) (let ((?v_0 (f29 f30 ?v1))) (=> (=> (= ?v0 f1) (= (f28 ?v_0 (f12 (f13 f32 (f33 (f34 (f35 f36 ?v2) ?v3) ?v4)) f39)) f1)) (= (f28 ?v_0 (f12 (f13 f32 (f33 (f34 (f35 f36 (f20 (f23 f24 ?v0) ?v2)) ?v3) ?v4)) f39)) f1)))))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S21) (?v3 S8)) (=> (forall ((?v4 S6) (?v5 S5)) (=> (= (f7 (f8 ?v0 ?v4) ?v5) f1) (= (f28 (f29 f30 ?v1) (f12 (f13 f32 (f33 (f34 (f35 f36 (f9 f16 ?v5)) ?v2) (f17 (f18 f19 ?v3) ?v4))) f39)) f1))) (= (f28 (f29 f30 ?v1) (f12 (f13 f32 (f33 (f34 (f35 f36 ?v0) ?v2) ?v3)) f39)) f1))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S21) (?v3 S8) (?v4 S8)) (let ((?v_0 (f29 f30 ?v0)) (?v_1 (f34 (f35 f36 ?v1) ?v2))) (=> (= (f28 ?v_0 (f12 (f13 f32 (f33 ?v_1 ?v3)) f39)) f1) (=> (forall ((?v5 S6) (?v6 S5)) (=> (= (f7 (f8 ?v3 ?v5) ?v6) f1) (= (f7 (f8 ?v4 ?v5) ?v6) f1))) (= (f28 ?v_0 (f12 (f13 f32 (f33 ?v_1 ?v4)) f39)) f1))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S21) (?v3 S8) (?v4 S8)) (let ((?v_0 (f29 f30 ?v0))) (=> (= (f28 ?v_0 (f12 (f13 f32 (f33 (f34 (f35 f36 ?v1) ?v2) ?v3)) f39)) f1) (=> (forall ((?v5 S6) (?v6 S5)) (=> (= (f7 (f8 ?v4 ?v5) ?v6) f1) (= (f7 (f8 ?v1 ?v5) ?v6) f1))) (= (f28 ?v_0 (f12 (f13 f32 (f33 (f34 (f35 f36 ?v4) ?v2) ?v3)) f39)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f40 f41 ?v0))) (=> (= (f28 ?v_0 (f12 (f13 f32 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f28 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f40 f41 ?v0))) (=> (=> (not (= (f28 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f28 ?v_0 (f12 (f13 f32 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f28 (f40 f41 ?v0) f39) f1) false)))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S21) (?v3 S8) (?v4 S8) (?v5 S8)) (let ((?v_0 (f29 f30 ?v0))) (=> (= (f28 ?v_0 (f12 (f13 f32 (f33 (f34 (f35 f36 ?v1) ?v2) ?v3)) f39)) f1) (=> (forall ((?v6 S6) (?v7 S5)) (=> (= (f7 (f8 ?v4 ?v6) ?v7) f1) (forall ((?v8 S5)) (=> (forall ((?v9 S6)) (=> (= (f7 (f8 ?v1 ?v9) ?v7) f1) (= (f7 (f8 ?v3 ?v9) ?v8) f1))) (= (f7 (f8 ?v5 ?v6) ?v8) f1))))) (= (f28 ?v_0 (f12 (f13 f32 (f33 (f34 (f35 f36 ?v4) ?v2) ?v5)) f39)) f1))))))
(assert (forall ((?v0 S2)) (= (f12 f42 (f4 f5 ?v0)) (f12 (f13 f32 ?v0) f39))))
(assert (forall ((?v0 S2)) (= (f12 f42 (f4 f6 ?v0)) (f12 (f13 f32 ?v0) f39))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f12 f42 (f12 (f13 f14 ?v0) ?v1)) (ite (= (f3 ?v1 ?v0) f1) (f12 (f13 f32 ?v0) f39) f39))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f12 f42 (f12 (f13 f15 ?v0) ?v1)) (ite (= (f3 ?v1 ?v0) f1) (f12 (f13 f32 ?v0) f39) f39))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f39) (not (= (f28 (f40 f41 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f12 f42 ?v0) f39) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f28 (f40 f41 ?v0) f39) f1) false)))
(assert (forall ((?v0 S3)) (= (= f39 (f12 f42 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f28 (f40 f41 ?v1) f39) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f28 (f40 f41 ?v1) f39) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f28 (f40 f41 ?v1) ?v0) f1)) (not (= ?v0 f39)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f28 (f40 f41 ?v1) ?v0) f1))) (= ?v0 f39))))
(assert (= f39 (f12 f42 f27)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f28 (f40 f41 ?v0) ?v1) f1) (= (f12 (f13 f32 ?v0) ?v1) ?v1))))
(check-sat)
(exit)
