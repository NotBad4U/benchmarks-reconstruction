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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 () S4)
(declare-fun f7 () S2)
(declare-fun f8 () S2)
(declare-fun f9 (S6 S5) S1)
(declare-fun f10 (S7 S5) S6)
(declare-fun f11 () S7)
(declare-fun f12 (S8 S2) S2)
(declare-fun f13 (S9 S2) S8)
(declare-fun f14 () S9)
(declare-fun f15 (S10 S5) S5)
(declare-fun f16 () S8)
(declare-fun f17 () S9)
(declare-fun f18 (S12 S3) S1)
(declare-fun f19 (S13 S11) S12)
(declare-fun f20 () S13)
(declare-fun f21 () S5)
(declare-fun f22 () S3)
(declare-fun f23 () S12)
(declare-fun f24 (S14 S2) S12)
(declare-fun f25 () S14)
(declare-fun f26 () S8)
(declare-fun f27 () S4)
(declare-fun f28 () S9)
(declare-fun f29 (S15 S3) S2)
(declare-fun f30 (S16 S8) S15)
(declare-fun f31 () S16)
(declare-fun f32 () S2)
(declare-fun f33 () S5)
(declare-fun f34 () S2)
(declare-fun f35 () S4)
(declare-fun f36 () S5)
(declare-fun f37 (S17 S5) S10)
(declare-fun f38 () S17)
(declare-fun f39 (S11 S2) S5)
(declare-fun f40 () S11)
(declare-fun f41 () S7)
(declare-fun f42 () S5)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (not (= (f3 (f4 f6 f7) f8) f1)))
(assert (not (= f8 f7)))
(assert (forall ((?v0 S2)) (= (f3 (f4 f6 ?v0) ?v0) f1)))
(assert (forall ((?v0 S5)) (= (f9 (f10 f11 ?v0) ?v0) f1)))
(assert (= (f3 (f4 f6 f7) f7) f1))
(assert (forall ((?v0 S2) (?v1 S1) (?v2 S1)) (let ((?v_0 (= (f3 (f4 f6 f7) ?v0) f1)) (?v_1 (= ?v1 f1)) (?v_2 (= ?v2 f1))) (=> (=> ?v_0 (= ?v_1 ?v_2)) (= (and ?v_0 ?v_1) (and ?v_0 ?v_2))))))
(assert (forall ((?v0 S2) (?v1 S1) (?v2 S1)) (let ((?v_0 (= (f3 (f4 f6 f7) ?v0) f1)) (?v_1 (= ?v1 f1)) (?v_2 (= ?v2 f1))) (=> (=> ?v_0 (= ?v_1 ?v_2)) (= (=> ?v_0 ?v_1) (=> ?v_0 ?v_2))))))
(assert (forall ((?v0 S2)) (= (f3 (f4 f6 ?v0) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f6 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f6 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f6 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 (f4 f6 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f6 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (or (= (f9 (f10 f11 ?v0) ?v1) f1) (= (f9 (f10 f11 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 ?v1) (and (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f6 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= ?v0 ?v1) (and (= (f9 (f10 f11 ?v0) ?v1) f1) (= (f9 (f10 f11 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= ?v0 ?v1) (= (f3 (f4 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= ?v0 ?v1) (= (f9 (f10 f11 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f3 (f4 f6 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f6 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (=> (= (f9 (f10 f11 ?v0) ?v1) f1) false) (=> (=> (= (f9 (f10 f11 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f6 ?v2))) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f10 f11 ?v2))) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (=> (= (f9 ?v_0 ?v0) f1) (= (f9 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 (f4 f6 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (=> (= (f9 (f10 f11 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f6 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f6 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f10 f11 ?v0))) (=> (= (f9 ?v_0 ?v1) f1) (=> (= (f9 (f10 f11 ?v1) ?v2) f1) (= (f9 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 (f4 f6 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (=> (= (f9 (f10 f11 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f3 (f4 f6 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f9 (f10 f11 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f6 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f10 f11 ?v0))) (=> (= (f9 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f9 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f6 ?v2))) (=> (= ?v0 ?v1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f10 f11 ?v2))) (=> (= ?v0 ?v1) (=> (= (f9 ?v_0 ?v1) f1) (= (f9 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f3 (f4 f6 ?v1) ?v2) f1) (= (f3 (f4 f6 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= ?v0 ?v1) (=> (= (f9 (f10 f11 ?v1) ?v2) f1) (= (f9 (f10 f11 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (= (= (f3 (f4 f6 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (= (= (f9 (f10 f11 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f6 f7))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f12 (f13 f14 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S8) (?v2 S2) (?v3 S2)) (=> (= ?v0 (f12 ?v1 ?v2)) (=> (= (f3 (f4 f6 ?v3) ?v2) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f4 f6 ?v5) ?v4) f1) (= (f3 (f4 f6 (f12 ?v1 ?v5)) (f12 ?v1 ?v4)) f1))) (= (f3 (f4 f6 (f12 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S5) (?v1 S10) (?v2 S5) (?v3 S5)) (=> (= ?v0 (f15 ?v1 ?v2)) (=> (= (f9 (f10 f11 ?v3) ?v2) f1) (=> (forall ((?v4 S5) (?v5 S5)) (=> (= (f9 (f10 f11 ?v5) ?v4) f1) (= (f9 (f10 f11 (f15 ?v1 ?v5)) (f15 ?v1 ?v4)) f1))) (= (f9 (f10 f11 (f15 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S8) (?v3 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f12 ?v2 ?v0) ?v3) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f4 f6 ?v5) ?v4) f1) (= (f3 (f4 f6 (f12 ?v2 ?v5)) (f12 ?v2 ?v4)) f1))) (= (f3 (f4 f6 ?v3) (f12 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S10) (?v3 S5)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (=> (= (f15 ?v2 ?v0) ?v3) (=> (forall ((?v4 S5) (?v5 S5)) (=> (= (f9 (f10 f11 ?v5) ?v4) f1) (= (f9 (f10 f11 (f15 ?v2 ?v5)) (f15 ?v2 ?v4)) f1))) (= (f9 (f10 f11 ?v3) (f15 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f6 (f12 f16 ?v0)) f7) f1) (= (f3 (f4 f6 ?v0) f7) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f12 f16 ?v0) (f12 f16 ?v1)) (= ?v0 ?v1))))
(assert (= (f12 f16 f7) f7))
(assert (forall ((?v0 S2)) (= (= f7 (f12 f16 ?v0)) (= ?v0 f7))))
(assert (forall ((?v0 S2)) (= (= (f12 f16 ?v0) f7) (= ?v0 f7))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f6 (f12 f16 ?v0)) (f12 f16 ?v1)) f1) (= (f3 (f4 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f4 f6 f7))) (= (= (f3 ?v_0 (f12 f16 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f12 (f13 f14 ?v0) ?v1) (ite (= (f3 (f4 f6 ?v1) ?v0) f1) (f12 (f13 f17 ?v0) ?v1) f7))))
(assert (forall ((?v0 S11) (?v1 S3)) (= (f18 (f19 f20 ?v0) ?v1) f1)))
(assert (forall ((?v0 S2)) (= (= f7 ?v0) (= ?v0 f7))))
(assert (forall ((?v0 S5)) (= (= f21 ?v0) (= ?v0 f21))))
(assert (forall ((?v0 S2)) (= (= (f3 f22 ?v0) f1) (= (f3 (f4 f6 f7) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (= (f18 f23 ?v0) f1) (forall ((?v1 S2)) (=> (= (f18 (f24 f25 ?v1) ?v0) f1) (= (f3 (f4 f6 f7) ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f18 f23 ?v0) f1) (=> (= (f18 (f24 f25 ?v1) ?v0) f1) (= (f3 (f4 f6 f7) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f12 f16 (f12 (f13 f17 ?v0) ?v1)) (f12 (f13 f17 (f12 f16 ?v0)) (f12 f16 ?v1)))))
(assert (forall ((?v0 S2)) (= (f12 (f13 f17 ?v0) f7) ?v0)))
(assert (forall ((?v0 S2)) (= (f12 (f13 f17 ?v0) ?v0) f7)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 ?v1) (= (f12 (f13 f17 ?v0) ?v1) f7))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f12 (f13 f17 ?v0) ?v1) f7) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f12 (f13 f17 ?v0) ?v1) (f12 (f13 f17 ?v2) ?v3)) (= (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f6 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f12 (f13 f17 ?v0) ?v1) (f12 (f13 f17 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f18 f23 ?v0) f1) (=> (= (f18 (f24 f25 ?v1) ?v0) f1) (= (f3 f22 ?v1) f1)))))
(assert (forall ((?v0 S11) (?v1 S3)) (= (= (f18 (f19 f20 ?v0) ?v1) f1) true)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f6 (f12 (f13 f17 ?v0) ?v1)) f7) f1))))
(assert (= (f3 f22 f7) f1))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f22 ?v0) f1) (=> (= (f3 f22 ?v1) f1) (= (f3 f22 (f12 (f13 f14 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f18 (f24 f25 ?v0) ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f12 (f13 f14 ?v1) ?v0) (f12 (f13 f17 ?v1) ?v0)))))
(assert (forall ((?v0 S2)) (=> (= (f3 f22 ?v0) f1) (= (f3 (f4 f6 f7) (f12 f26 ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f27 ?v0) ?v1) f1) (= (f12 (f13 f17 ?v0) ?v1) f7))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f22 ?v0) f1) (=> (= (f3 f22 ?v1) f1) (= (f3 (f4 f6 f7) (f12 (f13 f28 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S8)) (=> (= (f18 f23 ?v0) f1) (=> (forall ((?v2 S2)) (let ((?v_0 (f4 f6 f7))) (=> (= (f3 ?v_0 ?v2) f1) (= (f3 ?v_0 (f12 ?v1 ?v2)) f1)))) (= (f3 (f4 f6 f7) (f29 (f30 f31 ?v1) ?v0)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f6 (f12 f26 ?v0)) (f12 f26 ?v1)) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f27 ?v0) ?v0) f1) true)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f13 f28 ?v0))) (= (f12 (f13 f28 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f13 f28 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f13 f28 ?v0)) (?v_0 (f13 f28 ?v1))) (= (f12 ?v_1 (f12 ?v_0 ?v2)) (f12 ?v_0 (f12 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f12 (f13 f28 ?v0) ?v1) (f12 (f13 f28 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f12 (f13 f28 ?v0) ?v1) f7) (or (= ?v0 f7) (= ?v1 f7)))))
(assert (forall ((?v0 S2)) (= (f12 (f13 f28 ?v0) f7) f7)))
(assert (forall ((?v0 S2)) (= (f12 (f13 f28 f7) ?v0) f7)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f3 (f4 f6 f7) (f12 (f13 f28 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f6 f7))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f12 (f13 f28 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S2)) (= (f3 (f4 f6 f7) (f12 f26 ?v0)) f1)))
(assert (forall ((?v0 S2)) (=> (= (f3 (f4 f6 f7) ?v0) f1) (not (= (f12 f26 ?v0) f7)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f4 f6 f7))) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 (f12 f26 ?v0)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S8) (?v3 S8)) (=> (= ?v0 ?v1) (=> (= (f18 f23 ?v1) f1) (=> (forall ((?v4 S2)) (=> (= (f3 (f4 f6 f7) ?v4) f1) (= (f12 ?v2 ?v4) (f12 ?v3 ?v4)))) (= (f29 (f30 f31 ?v2) ?v0) (f29 (f30 f31 ?v3) ?v1)))))))
(assert (forall ((?v0 S3) (?v1 S8)) (=> (forall ((?v2 S2)) (=> (= (f18 (f24 f25 ?v2) ?v0) f1) (= (f3 (f4 f6 f7) (f12 ?v1 ?v2)) f1))) (= (f3 (f4 f6 f7) (f29 (f30 f31 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S8)) (=> (forall ((?v2 S2)) (=> (= (f18 (f24 f25 ?v2) ?v0) f1) (= (f3 (f4 f6 (f12 ?v1 ?v2)) f7) f1))) (= (f3 (f4 f6 (f29 (f30 f31 ?v1) ?v0)) f7) f1))))
(assert (= f5 f27))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f27 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f27 ?v0) ?v0) f1) true)))
(assert (= f27 f5))
(assert (forall ((?v0 S3) (?v1 S8)) (=> (forall ((?v2 S2)) (=> (= (f18 (f24 f25 ?v2) ?v0) f1) (= (f12 ?v1 ?v2) f7))) (= (f29 (f30 f31 ?v1) ?v0) f7))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8)) (=> (forall ((?v3 S2)) (=> (= (f18 (f24 f25 ?v3) ?v0) f1) (= (f12 ?v1 ?v3) (f12 ?v2 ?v3)))) (= (f29 (f30 f31 ?v1) ?v0) (f29 (f30 f31 ?v2) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S8) (?v3 S8)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S2)) (=> (= (f18 (f24 f25 ?v4) ?v1) f1) (= (f12 ?v2 ?v4) (f12 ?v3 ?v4)))) (= (f29 (f30 f31 ?v2) ?v0) (f29 (f30 f31 ?v3) ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S8) (?v3 S8)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S2)) (=> (= (f18 (f24 f25 ?v4) ?v1) f1) (= (f12 ?v2 ?v4) (f12 ?v3 ?v4)))) (= (f29 (f30 f31 ?v2) ?v0) (f29 (f30 f31 ?v3) ?v1))))))
(assert (forall ((?v0 S2)) (=> (= (f3 (f4 f6 f7) ?v0) f1) (= (f3 (f4 f6 f32) (f12 f26 ?v0)) f1))))
(assert (not (= f7 f32)))
(assert (forall ((?v0 S2)) (= (= f32 ?v0) (= ?v0 f32))))
(assert (forall ((?v0 S5)) (= (= f33 ?v0) (= ?v0 f33))))
(assert (= (f12 f16 f32) f32))
(assert (= (f3 f22 f32) f1))
(assert (= (f12 f26 f32) f32))
(assert (= (f3 (f4 f6 f7) f32) f1))
(assert (= (f12 f26 f7) f32))
(assert (= (f3 (f4 f6 f32) f34) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 ?v2 ?v1) f1) (=> (forall ((?v3 S2)) (=> (= (f3 (f4 f6 ?v3) ?v1) f1) (=> (= (f3 ?v2 ?v3) f1) (= (f3 ?v2 (f12 (f13 f17 ?v3) f32)) f1)))) (= (f3 ?v2 ?v0) f1))))))
(assert (not (= (f3 (f4 f6 f32) f7) f1)))
(assert (not (= (f9 (f10 f11 f33) f21) f1)))
(assert (= (f3 (f4 f6 f7) f32) f1))
(assert (= (f9 (f10 f11 f21) f33) f1))
(assert (= (f3 (f4 f35 f32) f34) f1))
(assert (not (= f32 f7)))
(assert (not (= f33 f21)))
(assert (not (= f7 f32)))
(assert (not (= f21 f33)))
(assert (= f36 (f15 (f37 f38 (f39 f40 f34)) f33)))
(assert (= (f9 (f10 f41 f21) f36) f1))
(assert (= (f9 (f10 f41 f21) f42) f1))
(assert (=> (forall ((?v0 S5)) (=> (= ?v0 (f15 (f37 f38 (f39 f40 f34)) f33)) (=> (= (f9 (f10 f41 f21) ?v0) f1) false))) false))
(assert (= f33 (f39 f40 f32)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 (f4 f35 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f35 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f35 (f12 f16 ?v0)) f7) f1) (= (f3 (f4 f35 ?v0) f7) f1))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f4 f35 f7))) (= (= (f3 ?v_0 (f12 f16 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (= f21 (f39 f40 f7)))
(assert (= (f39 f40 f7) f21))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f35 ?v2))) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f10 f41 ?v2))) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (=> (= (f9 ?v_0 ?v0) f1) (= (f9 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 (f4 f35 ?v1) ?v2) f1) (= (f3 (f4 f35 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (=> (= (f9 (f10 f41 ?v1) ?v2) f1) (= (f9 (f10 f41 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (=> (= (f3 (f4 f6 ?v2) ?v0) f1) (= (f3 (f4 f35 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (=> (= (f9 (f10 f11 ?v2) ?v0) f1) (= (f9 (f10 f41 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f35 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f6 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f10 f41 ?v0))) (=> (= (f9 ?v_0 ?v1) f1) (=> (= (f9 (f10 f11 ?v1) ?v2) f1) (= (f9 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (not (= ?v1 ?v0)) (= (f3 (f4 f35 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (=> (not (= ?v1 ?v0)) (= (f9 (f10 f41 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f3 (f4 f35 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f9 (f10 f41 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (or (= (f3 (f4 f35 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (or (= (f9 (f10 f41 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (= (not (= (f3 (f4 f35 ?v0) ?v1) f1)) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (= (not (= (f9 (f10 f41 ?v0) ?v1) f1)) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (= (f3 (f4 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (= (f9 (f10 f11 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (not (= (f3 (f4 f35 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (not (= (f9 (f10 f41 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (= (f3 (f4 f6 ?v1) ?v0) f1) (= (f3 (f4 f35 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= ?v0 ?v1)) (=> (= (f9 (f10 f11 ?v1) ?v0) f1) (= (f9 (f10 f41 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f35 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= ?v0 ?v1)) (=> (= (f9 (f10 f11 ?v0) ?v1) f1) (= (f9 (f10 f41 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f4 f35 ?v0) ?v1) f1)) (= (= (f3 (f4 f6 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= (f9 (f10 f41 ?v0) ?v1) f1)) (= (= (f9 (f10 f11 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f4 f6 ?v0) ?v1) f1)) (= (f3 (f4 f35 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= (f9 (f10 f11 ?v0) ?v1) f1)) (= (f9 (f10 f41 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f4 f35 ?v0) ?v1) f1)) (= (f3 (f4 f6 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= (f9 (f10 f41 ?v0) ?v1) f1)) (= (f9 (f10 f11 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f6 ?v0) ?v1) f1) (or (= (f3 (f4 f35 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f9 (f10 f11 ?v0) ?v1) f1) (or (= (f9 (f10 f41 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f35 ?v0) ?v1) f1) (and (= (f3 (f4 f6 ?v0) ?v1) f1) (not (= (f3 (f4 f6 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f9 (f10 f41 ?v0) ?v1) f1) (and (= (f9 (f10 f11 ?v0) ?v1) f1) (not (= (f9 (f10 f11 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f35 ?v0) ?v1) f1) (and (= (f3 (f4 f6 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f9 (f10 f41 ?v0) ?v1) f1) (and (= (f9 (f10 f11 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f35 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (or (= (f9 (f10 f11 ?v0) ?v1) f1) (= (f9 (f10 f41 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f4 f6 ?v0) ?v1) f1)) (= (f3 (f4 f35 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (not (= (f9 (f10 f11 ?v0) ?v1) f1)) (= (f9 (f10 f41 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f4 f35 ?v0) ?v1) f1)) (= (f3 (f4 f6 ?v1) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (not (= (f9 (f10 f41 ?v0) ?v1) f1)) (= (f9 (f10 f11 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f12 (f13 f17 ?v0) ?v1) (f12 (f13 f17 ?v2) ?v3)) (= (= (f3 (f4 f35 ?v0) ?v1) f1) (= (f3 (f4 f35 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f35 ?v0) ?v1) f1) (and (= (f3 (f4 f6 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S2)) (not (= (f3 (f4 f35 ?v0) ?v0) f1))))
(assert (forall ((?v0 S5)) (not (= (f9 (f10 f41 ?v0) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= ?v0 ?v1)) (or (= (f3 (f4 f35 ?v0) ?v1) f1) (= (f3 (f4 f35 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (not (= ?v0 ?v1)) (or (= (f9 (f10 f41 ?v0) ?v1) f1) (= (f9 (f10 f41 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f4 f35 ?v0) ?v1) f1)) (or (= (f3 (f4 f35 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (not (= (f9 (f10 f41 ?v0) ?v1) f1)) (or (= (f9 (f10 f41 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f35 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f4 f35 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (or (= (f9 (f10 f41 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f9 (f10 f41 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f35 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f4 f35 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S1) (?v1 S2) (?v2 S2)) (let ((?v_0 (= ?v0 f1))) (= (ite ?v_0 (f39 f40 ?v1) (f39 f40 ?v2)) (f39 f40 (ite ?v_0 ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f4 f35 ?v0) ?v1) f1)) (= (not (= (f3 (f4 f35 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= (f9 (f10 f41 ?v0) ?v1) f1)) (= (not (= (f9 (f10 f41 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 (f4 f35 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f35 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f9 (f10 f41 ?v0) ?v1) f1) false) (=> (=> (= (f9 (f10 f41 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (not (= (f3 (f4 f35 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (not (= (f9 (f10 f41 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (= (not (= (f3 (f4 f35 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (= (not (= (f9 (f10 f41 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S1)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (= (=> (= (f3 (f4 f35 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S1)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (= (=> (= (f9 (f10 f41 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (=> (= (f3 (f4 f35 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (=> (= (f9 (f10 f41 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (=> (= (f3 (f4 f35 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (=> (= (f9 (f10 f41 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f3 (f4 f35 ?v1) ?v2) f1) (= (f3 (f4 f35 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= ?v0 ?v1) (=> (= (f9 (f10 f41 ?v1) ?v2) f1) (= (f9 (f10 f41 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f35 ?v2))) (=> (= ?v0 ?v1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f10 f41 ?v2))) (=> (= ?v0 ?v1) (=> (= (f9 ?v_0 ?v1) f1) (= (f9 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f35 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f10 f41 ?v0))) (=> (= (f9 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f9 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f3 (f4 f35 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f9 (f10 f41 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f35 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f35 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f10 f41 ?v0))) (=> (= (f9 ?v_0 ?v1) f1) (=> (= (f9 (f10 f41 ?v1) ?v2) f1) (= (f9 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f35 ?v2))) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f10 f41 ?v2))) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (=> (= (f9 ?v_0 ?v0) f1) (= (f9 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (=> (=> (not false) (= (f3 (f4 f35 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (=> (=> (not false) (= (f9 (f10 f41 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f3 (f4 f35 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f3 (f4 f35 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (=> (= (f9 (f10 f41 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f9 (f10 f41 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f6 f7))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (= (f9 (f10 f41 (f39 f40 ?v0)) (f39 f40 ?v1)) f1) (= (f3 (f4 f35 ?v0) ?v1) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 f7) ?v0) f1) (= (= (f9 (f10 f41 (f39 f40 ?v0)) (f39 f40 ?v1)) f1) (= (f3 (f4 f35 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f35 f7) ?v0) f1) (= (= (f9 (f10 f41 (f39 f40 ?v1)) (f39 f40 ?v0)) f1) (= (f3 (f4 f35 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f9 (f10 f41 (f39 f40 ?v0)) (f39 f40 ?v1)) f1) (and (= (f3 (f4 f35 f7) ?v1) f1) (= (f3 (f4 f35 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f35 (f12 f16 ?v0)) (f12 f16 ?v1)) f1) (= (f3 (f4 f35 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2)) (= (= (f9 (f10 f41 f21) (f39 f40 ?v0)) f1) (= (f3 (f4 f35 f7) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (or (= (f3 (f4 f35 f7) ?v0) f1) (= (f3 (f4 f6 f7) ?v1) f1)) (= (= (f9 (f10 f11 (f39 f40 ?v0)) (f39 f40 ?v1)) f1) (= (f3 (f4 f6 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2)) (= (= (f39 f40 ?v0) f21) (= (f3 (f4 f6 ?v0) f7) f1))))
(assert (forall ((?v0 S2)) (=> (= (f3 (f4 f6 ?v0) f7) f1) (= (f39 f40 ?v0) f21))))
(assert (forall ((?v0 S6)) (= (exists ((?v1 S5)) (= (f9 ?v0 ?v1) f1)) (exists ((?v1 S2)) (and (= (f3 (f4 f6 f7) ?v1) f1) (= (f9 ?v0 (f39 f40 ?v1)) f1))))))
(assert (forall ((?v0 S6)) (= (forall ((?v1 S5)) (= (f9 ?v0 ?v1) f1)) (forall ((?v1 S2)) (=> (= (f3 (f4 f6 f7) ?v1) f1) (= (f9 ?v0 (f39 f40 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f6 f7))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (= (f39 f40 ?v0) (f39 f40 ?v1)) (= ?v0 ?v1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f6 f7))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (= (f39 f40 ?v0) (f39 f40 ?v1)) (= ?v0 ?v1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f6 f7))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (= (f9 (f10 f11 (f39 f40 ?v0)) (f39 f40 ?v1)) f1) (= (f3 (f4 f6 ?v0) ?v1) f1)))))))
(assert (= (f18 (f19 f20 f40) (f4 f6 f7)) f1))
(assert (= (f3 (f4 f35 f7) f32) f1))
(assert (= (f9 (f10 f41 f21) f33) f1))
(assert (not (= (f3 (f4 f35 f32) f7) f1)))
(assert (not (= (f9 (f10 f41 f33) f21) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f35 ?v0) ?v1) f1) (= (f3 (f4 f35 (f12 (f13 f17 ?v0) ?v1)) f7) f1))))
(assert (= (f3 (f4 f35 f7) f32) f1))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f35 ?v0) ?v1) f1) (= (f3 (f4 f35 (f12 (f13 f17 ?v0) ?v1)) f7) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 f7)) (=> (not (= ?v1 f7)) (= (f3 (f4 f35 f7) (f12 (f13 f28 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f35 f7) ?v0) f1) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (= (f3 (f4 f35 (f12 f26 ?v0)) (f12 f26 ?v1)) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f3 (f4 f35 ?v0) f7) f1) (= (f12 f26 ?v0) f7))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 f7) ?v0) f1) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f39 f40 (f12 (f13 f17 ?v1) ?v0)) (f15 (f37 f38 (f39 f40 ?v1)) (f39 f40 ?v0)))))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f6 f32) ?v0) f1) (= (f3 (f4 f35 f7) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f6 ?v0) (f12 (f13 f17 ?v1) f32)) f1) (= (f3 (f4 f35 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2)) (=> (= (f3 (f4 f6 f7) ?v0) f1) (= (f3 (f4 f35 f7) (f12 f26 ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f6 f7))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f15 (f37 f38 (f39 f40 ?v0)) (f39 f40 ?v1)) (f39 f40 (f12 (f13 f14 ?v0) ?v1))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) (f12 (f13 f17 ?v1) f32)) f1) (= (f3 (f4 f35 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f35 ?v0)) (?v_1 (f12 (f13 f17 ?v1) f32))) (=> (= (f3 (f4 f35 f7) ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (=> (not (= ?v0 ?v_1)) (= (f3 ?v_0 ?v_1) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (=> (= (f3 ?v2 (f12 (f13 f17 ?v1) f32)) f1) (=> (forall ((?v3 S2)) (=> (= (f3 (f4 f35 ?v3) ?v1) f1) (=> (= (f3 ?v2 ?v3) f1) (= (f3 ?v2 (f12 (f13 f17 ?v3) f32)) f1)))) (= (f3 ?v2 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f35 ?v0) ?v1) f1) (=> (= (f3 (f4 f35 ?v2) ?v1) f1) (or (= (f3 (f4 f6 ?v0) ?v2) f1) (= (f3 (f4 f6 ?v2) ?v0) f1))))))
(assert (forall ((?v0 S5)) (= (f9 (f10 f11 f21) ?v0) f1)))
(assert (forall ((?v0 S5)) (=> (= (f9 (f10 f41 ?v0) f21) f1) false)))
(assert (forall ((?v0 S5)) (not (= (f9 (f10 f41 ?v0) ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (not (= ?v0 ?v1)) (or (= (f9 (f10 f41 ?v0) ?v1) f1) (= (f9 (f10 f41 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f9 (f10 f41 ?v0) ?v1) f1) false) (=> (=> (= (f9 (f10 f41 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S5)) (=> (= (f9 (f10 f41 ?v0) ?v0) f1) false)))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (not (= ?v1 ?v0)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f9 (f10 f41 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S7)) (let ((?v_0 (= (f9 (f10 ?v2 ?v1) ?v0) f1))) (=> (=> (= (f9 (f10 f41 ?v0) ?v1) f1) ?v_0) (=> (=> (= ?v0 ?v1) ?v_0) (=> (=> (= (f9 (f10 f41 ?v1) ?v0) f1) ?v_0) ?v_0))))))
(assert (forall ((?v0 S5)) (= (f9 (f10 f11 ?v0) ?v0) f1)))
(check-sat)
(exit)