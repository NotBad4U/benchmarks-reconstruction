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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 (S5 S3) S2)
(declare-fun f5 () S5)
(declare-fun f6 (S6 S3) S3)
(declare-fun f7 (S7 S3) S6)
(declare-fun f8 () S7)
(declare-fun f9 () S6)
(declare-fun f10 () S6)
(declare-fun f11 () S3)
(declare-fun f12 () S7)
(declare-fun f13 () S3)
(declare-fun f14 () S3)
(declare-fun f15 () S6)
(declare-fun f16 (S9 S8) S8)
(declare-fun f17 () S9)
(declare-fun f18 () S9)
(declare-fun f19 (S10 S8) S9)
(declare-fun f20 () S10)
(declare-fun f21 () S10)
(declare-fun f22 (S11 S4) S4)
(declare-fun f23 () S11)
(declare-fun f24 (S12 S4) S11)
(declare-fun f25 () S12)
(declare-fun f26 () S12)
(declare-fun f27 (S3 S3) S1)
(declare-fun f28 (S8 S8) S1)
(declare-fun f29 () S3)
(declare-fun f30 () S8)
(declare-fun f31 () S4)
(assert (not (= f1 f2)))
(assert (let ((?v_1 (f6 f10 f11))) (let ((?v_0 (f6 f9 ?v_1))) (not (= (f3 (f4 f5 (f6 (f7 f8 ?v_0) ?v_0)) (f6 (f7 f12 f13) f14)) (f3 (f4 f5 (f6 f15 ?v_1)) f14))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 f10 (f6 (f7 f12 ?v0) (f6 f15 ?v1))) (f6 f10 (f6 (f7 f12 ?v1) (f6 f15 ?v0))))))
(assert (forall ((?v0 S3)) (= (f6 f9 (f6 (f7 f8 ?v0) ?v0)) (f6 f10 ?v0))))
(assert (forall ((?v0 S3)) (= (f6 f9 (f6 f15 ?v0)) (f6 f15 (f6 f9 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 f9 (f6 (f7 f8 ?v0) ?v1)) (f6 (f7 f8 (f6 f9 ?v0)) (f6 f9 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f6 (f7 f8 (f6 (f7 f12 ?v0) ?v1)) ?v2) (f6 (f7 f12 (f6 (f7 f8 ?v0) ?v2)) (f6 (f7 f8 ?v1) ?v2)))))
(assert (forall ((?v0 S8)) (= (f16 f17 (f16 f18 ?v0)) (f16 f17 ?v0))))
(assert (forall ((?v0 S3)) (= (f6 f10 (f6 f15 ?v0)) (f6 f10 ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f16 (f19 f20 (f16 f17 ?v0)) (f16 f17 ?v1)))) (= (f16 f17 ?v_0) ?v_0))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f6 (f7 f12 (f6 f10 ?v0)) (f6 f10 ?v1)))) (= (f6 f10 ?v_0) ?v_0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f16 f17 (f16 (f19 f21 ?v0) ?v1)) (f16 (f19 f21 (f16 f17 ?v0)) (f16 f17 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 f10 (f6 (f7 f8 ?v0) ?v1)) (f6 (f7 f8 (f6 f10 ?v0)) (f6 f10 ?v1)))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f16 f17 ?v0))) (= (f16 (f19 f21 ?v_0) ?v_0) (f16 (f19 f21 ?v0) ?v0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f6 f10 ?v0))) (= (f6 (f7 f8 ?v_0) ?v_0) (f6 (f7 f8 ?v0) ?v0)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f22 f23 (f22 (f24 f25 ?v0) ?v1)) (f22 (f24 f25 (f22 f23 ?v0)) (f22 f23 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f16 f18 (f16 (f19 f20 ?v0) ?v1)) (f16 (f19 f20 (f16 f18 ?v0)) (f16 f18 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 f15 (f6 (f7 f12 ?v0) ?v1)) (f6 (f7 f12 (f6 f15 ?v0)) (f6 f15 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f22 f23 (f22 (f24 f25 ?v0) ?v1)) (f22 (f24 f25 (f22 f23 ?v1)) (f22 f23 ?v0)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f16 f18 (f16 (f19 f20 ?v0) ?v1)) (f16 (f19 f20 (f16 f18 ?v1)) (f16 f18 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 f15 (f6 (f7 f12 ?v0) ?v1)) (f6 (f7 f12 (f6 f15 ?v1)) (f6 f15 ?v0)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f22 (f24 f25 ?v0) (f22 (f24 f25 (f22 f23 ?v0)) ?v1)) ?v1)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f16 (f19 f20 ?v0) (f16 (f19 f20 (f16 f18 ?v0)) ?v1)) ?v1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f12 ?v0) (f6 (f7 f12 (f6 f15 ?v0)) ?v1)) ?v1)))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f21 ?v0))) (= (f16 (f19 f21 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f19 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 (f7 f8 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f7 f8 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f26 ?v0))) (= (f22 (f24 f26 (f22 ?v_0 ?v1)) ?v2) (f22 ?v_0 (f22 (f24 f26 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (=> (= (f22 (f24 f25 ?v0) ?v1) (f22 (f24 f25 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (=> (= (f16 (f19 f20 ?v0) ?v1) (f16 (f19 f20 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f6 (f7 f12 ?v0) ?v1) (f6 (f7 f12 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f22 ?v_0 ?v1) (f22 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f12 ?v0))) (=> (= (f6 ?v_0 ?v1) (f6 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f22 ?v_0 ?v1) (f22 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f12 ?v0))) (=> (= (f6 ?v_0 ?v1) (f6 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (= (f22 (f24 f25 ?v0) ?v1) (f22 (f24 f25 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (= (f16 (f19 f20 ?v0) ?v1) (f16 (f19 f20 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f6 (f7 f12 ?v0) ?v1) (f6 (f7 f12 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f25 ?v0))) (= (= (f22 ?v_0 ?v1) (f22 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f20 ?v0))) (= (= (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f12 ?v0))) (= (= (f6 ?v_0 ?v1) (f6 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f25 ?v0))) (= (f22 (f24 f25 (f22 ?v_0 ?v1)) ?v2) (f22 ?v_0 (f22 (f24 f25 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f20 ?v0))) (= (f16 (f19 f20 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f19 f20 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f12 ?v0))) (= (f6 (f7 f12 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f7 f12 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f16 f18 ?v0) (f16 f18 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f22 f23 ?v0) (f22 f23 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 f15 ?v0) (f6 f15 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f16 f18 ?v0) ?v1) (= (f16 f18 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f22 f23 ?v0) ?v1) (= (f22 f23 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 f15 ?v0) ?v1) (= (f6 f15 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= ?v0 (f16 f18 ?v1)) (= ?v1 (f16 f18 ?v0)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= ?v0 (f22 f23 ?v1)) (= ?v1 (f22 f23 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 (f6 f15 ?v1)) (= ?v1 (f6 f15 ?v0)))))
(assert (forall ((?v0 S8)) (= (f16 f18 (f16 f18 ?v0)) ?v0)))
(assert (forall ((?v0 S4)) (= (f22 f23 (f22 f23 ?v0)) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 f15 (f6 f15 ?v0)) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 (f7 f8 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f7 f8 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f8 ?v0) ?v1) (f6 (f7 f8 ?v1) ?v0))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f16 f17 ?v0))) (= (f16 f17 ?v_0) ?v_0))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f6 f10 ?v0))) (= (f6 f10 ?v_0) ?v_0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 f9 ?v0) (f6 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (= (f16 (f19 f20 (f16 (f19 f21 ?v0) ?v1)) (f16 (f19 f20 (f16 (f19 f21 ?v2) ?v1)) ?v3)) (f16 (f19 f20 (f16 (f19 f21 (f16 (f19 f20 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (= (f22 (f24 f25 (f22 (f24 f26 ?v0) ?v1)) (f22 (f24 f25 (f22 (f24 f26 ?v2) ?v1)) ?v3)) (f22 (f24 f25 (f22 (f24 f26 (f22 (f24 f25 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (f6 (f7 f12 (f6 (f7 f8 ?v0) ?v1)) (f6 (f7 f12 (f6 (f7 f8 ?v2) ?v1)) ?v3)) (f6 (f7 f12 (f6 (f7 f8 (f6 (f7 f12 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (f16 (f19 f21 (f16 (f19 f20 ?v0) ?v1)) ?v2) (f16 (f19 f20 (f16 (f19 f21 ?v0) ?v2)) (f16 (f19 f21 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f22 (f24 f26 (f22 (f24 f25 ?v0) ?v1)) ?v2) (f22 (f24 f25 (f22 (f24 f26 ?v0) ?v2)) (f22 (f24 f26 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f6 (f7 f8 (f6 (f7 f12 ?v0) ?v1)) ?v2) (f6 (f7 f12 (f6 (f7 f8 ?v0) ?v2)) (f6 (f7 f8 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f16 (f19 f21 ?v0) ?v0) (f16 (f19 f21 ?v1) ?v1)) (or (= ?v0 ?v1) (= ?v0 (f16 f18 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 (f7 f8 ?v0) ?v0) (f6 (f7 f8 ?v1) ?v1)) (or (= ?v0 ?v1) (= ?v0 (f6 f15 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f22 (f24 f26 ?v0) ?v0) (f22 (f24 f26 ?v1) ?v1)) (or (= ?v0 ?v1) (= ?v0 (f22 f23 ?v1))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f16 (f19 f21 (f16 f18 ?v0)) (f16 f18 ?v1)) (f16 (f19 f21 ?v0) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f8 (f6 f15 ?v0)) (f6 f15 ?v1)) (f6 (f7 f8 ?v0) ?v1))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f22 (f24 f26 (f22 f23 ?v0)) (f22 f23 ?v1)) (f22 (f24 f26 ?v0) ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f16 (f19 f21 (f16 f18 ?v0)) ?v1) (f16 (f19 f21 ?v0) (f16 f18 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f8 (f6 f15 ?v0)) ?v1) (f6 (f7 f8 ?v0) (f6 f15 ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f22 (f24 f26 (f22 f23 ?v0)) ?v1) (f22 (f24 f26 ?v0) (f22 f23 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f16 f18 (f16 (f19 f21 ?v0) ?v1)) (f16 (f19 f21 (f16 f18 ?v0)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 f15 (f6 (f7 f8 ?v0) ?v1)) (f6 (f7 f8 (f6 f15 ?v0)) ?v1))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f22 f23 (f22 (f24 f26 ?v0) ?v1)) (f22 (f24 f26 (f22 f23 ?v0)) ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f19 f21 ?v0))) (= (f16 f18 (f16 ?v_0 ?v1)) (f16 ?v_0 (f16 f18 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 f15 (f6 ?v_0 ?v1)) (f6 ?v_0 (f6 f15 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_0 (f24 f26 ?v0))) (= (f22 f23 (f22 ?v_0 ?v1)) (f22 ?v_0 (f22 f23 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f22 (f24 f25 (f22 f23 ?v0)) (f22 (f24 f25 ?v0) ?v1)) ?v1)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f16 (f19 f20 (f16 f18 ?v0)) (f16 (f19 f20 ?v0) ?v1)) ?v1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f12 (f6 f15 ?v0)) (f6 (f7 f12 ?v0) ?v1)) ?v1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (f22 (f24 f26 (f3 (f4 f5 ?v0) ?v1)) (f3 (f4 f5 ?v2) ?v3)) (f3 (f4 f5 (f6 (f7 f8 ?v0) ?v2)) (f6 (f7 f12 ?v1) ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f8 (f6 f15 ?v0)) ?v1) (f6 f15 (f6 (f7 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f22 (f24 f26 (f22 f23 ?v0)) ?v1) (f22 f23 (f22 (f24 f26 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f8 (f6 f15 ?v0)) ?v1) (f6 f15 (f6 (f7 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f22 (f24 f26 (f22 f23 ?v0)) ?v1) (f22 f23 (f22 (f24 f26 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 ?v_0 (f6 f15 ?v1)) (f6 f15 (f6 ?v_0 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_0 (f24 f26 ?v0))) (= (f22 ?v_0 (f22 f23 ?v1)) (f22 f23 (f22 ?v_0 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 ?v_0 (f6 f15 ?v1)) (f6 f15 (f6 ?v_0 ?v1))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_0 (f24 f26 ?v0))) (= (f22 ?v_0 (f22 f23 ?v1)) (f22 f23 (f22 ?v_0 ?v1))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f19 f21 ?v0)) (?v_1 (f19 f21 ?v2))) (= (= (f16 (f19 f20 (f16 ?v_0 ?v1)) (f16 ?v_1 ?v3)) (f16 (f19 f20 (f16 ?v_0 ?v3)) (f16 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f24 f26 ?v0)) (?v_1 (f24 f26 ?v2))) (= (= (f22 (f24 f25 (f22 ?v_0 ?v1)) (f22 ?v_1 ?v3)) (f22 (f24 f25 (f22 ?v_0 ?v3)) (f22 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f7 f8 ?v0)) (?v_1 (f7 f8 ?v2))) (= (= (f6 (f7 f12 (f6 ?v_0 ?v1)) (f6 ?v_1 ?v3)) (f6 (f7 f12 (f6 ?v_0 ?v3)) (f6 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (f16 (f19 f20 (f16 (f19 f21 ?v0) ?v1)) (f16 (f19 f21 ?v2) ?v1)) (f16 (f19 f21 (f16 (f19 f20 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f22 (f24 f25 (f22 (f24 f26 ?v0) ?v1)) (f22 (f24 f26 ?v2) ?v1)) (f22 (f24 f26 (f22 (f24 f25 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f6 (f7 f12 (f6 (f7 f8 ?v0) ?v1)) (f6 (f7 f8 ?v2) ?v1)) (f6 (f7 f8 (f6 (f7 f12 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f22 (f24 f26 (f22 (f24 f25 ?v0) ?v1)) ?v2) (f22 (f24 f25 (f22 (f24 f26 ?v0) ?v2)) (f22 (f24 f26 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f6 (f7 f8 (f6 (f7 f12 ?v0) ?v1)) ?v2) (f6 (f7 f12 (f6 (f7 f8 ?v0) ?v2)) (f6 (f7 f8 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f22 (f24 f26 (f22 (f24 f25 ?v0) ?v1)) ?v2) (f22 (f24 f25 (f22 (f24 f26 ?v0) ?v2)) (f22 (f24 f26 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f6 (f7 f8 (f6 (f7 f12 ?v0) ?v1)) ?v2) (f6 (f7 f12 (f6 (f7 f8 ?v0) ?v2)) (f6 (f7 f8 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (f16 (f19 f21 (f16 (f19 f20 ?v0) ?v1)) ?v2) (f16 (f19 f20 (f16 (f19 f21 ?v0) ?v2)) (f16 (f19 f21 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f22 (f24 f26 (f22 (f24 f25 ?v0) ?v1)) ?v2) (f22 (f24 f25 (f22 (f24 f26 ?v0) ?v2)) (f22 (f24 f26 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f6 (f7 f8 (f6 (f7 f12 ?v0) ?v1)) ?v2) (f6 (f7 f12 (f6 (f7 f8 ?v0) ?v2)) (f6 (f7 f8 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f19 f21 ?v0)) (?v_1 (f19 f21 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f16 (f19 f20 (f16 ?v_0 ?v2)) (f16 ?v_1 ?v3)) (f16 (f19 f20 (f16 ?v_0 ?v3)) (f16 ?v_1 ?v2))))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f24 f26 ?v0)) (?v_1 (f24 f26 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f22 (f24 f25 (f22 ?v_0 ?v2)) (f22 ?v_1 ?v3)) (f22 (f24 f25 (f22 ?v_0 ?v3)) (f22 ?v_1 ?v2))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f7 f8 ?v0)) (?v_1 (f7 f8 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f6 (f7 f12 (f6 ?v_0 ?v2)) (f6 ?v_1 ?v3)) (f6 (f7 f12 (f6 ?v_0 ?v3)) (f6 ?v_1 ?v2))))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f16 (f19 f21 ?v0) ?v1) (f16 (f19 f21 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f8 ?v0) ?v1) (f6 (f7 f8 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f22 (f24 f26 ?v0) ?v1) (f22 (f24 f26 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f19 f21 ?v0)) (?v_0 (f19 f21 ?v1))) (= (f16 ?v_1 (f16 ?v_0 ?v2)) (f16 ?v_0 (f16 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f7 f8 ?v0)) (?v_0 (f7 f8 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f24 f26 ?v0)) (?v_0 (f24 f26 ?v1))) (= (f22 ?v_1 (f22 ?v_0 ?v2)) (f22 ?v_0 (f22 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f21 ?v0))) (= (f16 ?v_0 (f16 (f19 f21 ?v1) ?v2)) (f16 (f19 f21 (f16 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 ?v_0 (f6 (f7 f8 ?v1) ?v2)) (f6 (f7 f8 (f6 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f26 ?v0))) (= (f22 ?v_0 (f22 (f24 f26 ?v1) ?v2)) (f22 (f24 f26 (f22 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f21 ?v0))) (= (f16 (f19 f21 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f19 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 (f7 f8 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f7 f8 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f26 ?v0))) (= (f22 (f24 f26 (f22 ?v_0 ?v1)) ?v2) (f22 ?v_0 (f22 (f24 f26 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f21 ?v0))) (= (f16 (f19 f21 (f16 ?v_0 ?v1)) ?v2) (f16 (f19 f21 (f16 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 (f7 f8 (f6 ?v_0 ?v1)) ?v2) (f6 (f7 f8 (f6 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f26 ?v0))) (= (f22 (f24 f26 (f22 ?v_0 ?v1)) ?v2) (f22 (f24 f26 (f22 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f19 f21 ?v0)) (?v_1 (f16 (f19 f21 ?v2) ?v3))) (= (f16 (f19 f21 (f16 ?v_0 ?v1)) ?v_1) (f16 ?v_0 (f16 (f19 f21 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f7 f8 ?v0)) (?v_1 (f6 (f7 f8 ?v2) ?v3))) (= (f6 (f7 f8 (f6 ?v_0 ?v1)) ?v_1) (f6 ?v_0 (f6 (f7 f8 ?v1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f24 f26 ?v0)) (?v_1 (f22 (f24 f26 ?v2) ?v3))) (= (f22 (f24 f26 (f22 ?v_0 ?v1)) ?v_1) (f22 ?v_0 (f22 (f24 f26 ?v1) ?v_1))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_1 (f19 f21 (f16 (f19 f21 ?v0) ?v1))) (?v_0 (f19 f21 ?v2))) (= (f16 ?v_1 (f16 ?v_0 ?v3)) (f16 ?v_0 (f16 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f7 f8 (f6 (f7 f8 ?v0) ?v1))) (?v_0 (f7 f8 ?v2))) (= (f6 ?v_1 (f6 ?v_0 ?v3)) (f6 ?v_0 (f6 ?v_1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_1 (f24 f26 (f22 (f24 f26 ?v0) ?v1))) (?v_0 (f24 f26 ?v2))) (= (f22 ?v_1 (f22 ?v_0 ?v3)) (f22 ?v_0 (f22 ?v_1 ?v3))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f19 f21 ?v0))) (= (f16 (f19 f21 (f16 ?v_0 ?v1)) (f16 (f19 f21 ?v2) ?v3)) (f16 (f19 f21 (f16 ?v_0 ?v2)) (f16 (f19 f21 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 (f7 f8 (f6 ?v_0 ?v1)) (f6 (f7 f8 ?v2) ?v3)) (f6 (f7 f8 (f6 ?v_0 ?v2)) (f6 (f7 f8 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f24 f26 ?v0))) (= (f22 (f24 f26 (f22 ?v_0 ?v1)) (f22 (f24 f26 ?v2) ?v3)) (f22 (f24 f26 (f22 ?v_0 ?v2)) (f22 (f24 f26 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f22 (f24 f25 ?v0) ?v1) (f22 (f24 f25 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f16 (f19 f20 ?v0) ?v1) (f16 (f19 f20 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f12 ?v0) ?v1) (f6 (f7 f12 ?v1) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f24 f25 ?v0)) (?v_0 (f24 f25 ?v1))) (= (f22 ?v_1 (f22 ?v_0 ?v2)) (f22 ?v_0 (f22 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_1 (f19 f20 ?v0)) (?v_0 (f19 f20 ?v1))) (= (f16 ?v_1 (f16 ?v_0 ?v2)) (f16 ?v_0 (f16 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f7 f12 ?v0)) (?v_0 (f7 f12 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f25 ?v0))) (= (f22 ?v_0 (f22 (f24 f25 ?v1) ?v2)) (f22 (f24 f25 (f22 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f20 ?v0))) (= (f16 ?v_0 (f16 (f19 f20 ?v1) ?v2)) (f16 (f19 f20 (f16 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f12 ?v0))) (= (f6 ?v_0 (f6 (f7 f12 ?v1) ?v2)) (f6 (f7 f12 (f6 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f25 ?v0))) (= (f22 (f24 f25 (f22 ?v_0 ?v1)) ?v2) (f22 ?v_0 (f22 (f24 f25 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f20 ?v0))) (= (f16 (f19 f20 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f19 f20 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f12 ?v0))) (= (f6 (f7 f12 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f7 f12 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f25 ?v0))) (= (f22 (f24 f25 (f22 ?v_0 ?v1)) ?v2) (f22 (f24 f25 (f22 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f20 ?v0))) (= (f16 (f19 f20 (f16 ?v_0 ?v1)) ?v2) (f16 (f19 f20 (f16 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f12 ?v0))) (= (f6 (f7 f12 (f6 ?v_0 ?v1)) ?v2) (f6 (f7 f12 (f6 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f24 f25 ?v0))) (= (f22 (f24 f25 (f22 ?v_0 ?v1)) (f22 (f24 f25 ?v2) ?v3)) (f22 (f24 f25 (f22 ?v_0 ?v2)) (f22 (f24 f25 ?v1) ?v3))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f19 f20 ?v0))) (= (f16 (f19 f20 (f16 ?v_0 ?v1)) (f16 (f19 f20 ?v2) ?v3)) (f16 (f19 f20 (f16 ?v_0 ?v2)) (f16 (f19 f20 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f7 f12 ?v0))) (= (f6 (f7 f12 (f6 ?v_0 ?v1)) (f6 (f7 f12 ?v2) ?v3)) (f6 (f7 f12 (f6 ?v_0 ?v2)) (f6 (f7 f12 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f26 ?v0))) (= (f22 ?v_0 (f22 (f24 f25 ?v1) ?v2)) (f22 (f24 f25 (f22 ?v_0 ?v1)) (f22 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 ?v_0 (f6 (f7 f12 ?v1) ?v2)) (f6 (f7 f12 (f6 ?v_0 ?v1)) (f6 ?v_0 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f21 ?v0))) (= (f16 ?v_0 (f16 (f19 f20 ?v1) ?v2)) (f16 (f19 f20 (f16 ?v_0 ?v1)) (f16 ?v_0 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f26 ?v0))) (= (f22 ?v_0 (f22 (f24 f25 ?v1) ?v2)) (f22 (f24 f25 (f22 ?v_0 ?v1)) (f22 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 ?v_0 (f6 (f7 f12 ?v1) ?v2)) (f6 (f7 f12 (f6 ?v_0 ?v1)) (f6 ?v_0 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f24 f26 ?v0))) (= (f22 ?v_0 (f22 (f24 f25 ?v1) ?v2)) (f22 (f24 f25 (f22 ?v_0 ?v1)) (f22 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 ?v_0 (f6 (f7 f12 ?v1) ?v2)) (f6 (f7 f12 (f6 ?v_0 ?v1)) (f6 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f7 f12 ?v0)) (?v_1 (f6 f15 ?v2)) (?v_2 (f6 f15 ?v3))) (= (f27 (f6 f10 (f6 (f7 f12 (f6 ?v_0 ?v1)) (f6 (f7 f12 ?v_1) ?v_2))) (f6 (f7 f12 (f6 f10 (f6 ?v_0 ?v_1))) (f6 f10 (f6 (f7 f12 ?v1) ?v_2)))) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f27 ?v0 (f6 f9 (f6 (f7 f12 (f6 (f7 f8 ?v0) ?v0)) (f6 (f7 f8 ?v1) ?v1)))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f27 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f27 ?v1 ?v2) f1) (= (f27 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f27 ?v0 ?v1) f1) (= (f27 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f27 ?v0 ?v0) f1)))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f28 (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) f1) (= (f28 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f12 ?v0))) (=> (= (f27 (f6 ?v_0 ?v1) (f6 ?v_0 ?v2)) f1) (= (f27 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (=> (= (f28 (f16 (f19 f20 ?v0) ?v1) (f16 (f19 f20 ?v2) ?v1)) f1) (= (f28 ?v0 ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f27 (f6 (f7 f12 ?v0) ?v1) (f6 (f7 f12 ?v2) ?v1)) f1) (= (f27 ?v0 ?v2) f1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (=> (= (f28 ?v0 ?v1) f1) (=> (= (f28 ?v2 ?v3) f1) (= (f28 (f16 (f19 f20 ?v0) ?v2) (f16 (f19 f20 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f27 ?v2 ?v3) f1) (= (f27 (f6 (f7 f12 ?v0) ?v2) (f6 (f7 f12 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f20 ?v2))) (=> (= (f28 ?v0 ?v1) f1) (= (f28 (f16 ?v_0 ?v0) (f16 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f12 ?v2))) (=> (= (f27 ?v0 ?v1) f1) (= (f27 (f6 ?v_0 ?v0) (f6 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (=> (= (f28 ?v0 ?v1) f1) (= (f28 (f16 (f19 f20 ?v0) ?v2) (f16 (f19 f20 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f27 ?v0 ?v1) f1) (= (f27 (f6 (f7 f12 ?v0) ?v2) (f6 (f7 f12 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f19 f20 ?v0))) (= (= (f28 (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) f1) (= (f28 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f12 ?v0))) (= (= (f27 (f6 ?v_0 ?v1) (f6 ?v_0 ?v2)) f1) (= (f27 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (= (f28 (f16 (f19 f20 ?v0) ?v1) (f16 (f19 f20 ?v2) ?v1)) f1) (= (f28 ?v0 ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f27 (f6 (f7 f12 ?v0) ?v1) (f6 (f7 f12 ?v2) ?v1)) f1) (= (f27 ?v0 ?v2) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f28 ?v0 ?v1) f1) (= (f28 (f16 f18 ?v1) (f16 f18 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f27 ?v0 ?v1) f1) (= (f27 (f6 f15 ?v1) (f6 f15 ?v0)) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f28 (f16 f18 ?v0) (f16 f18 ?v1)) f1) (= (f28 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f27 (f6 f15 ?v0) (f6 f15 ?v1)) f1) (= (f27 ?v1 ?v0) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f28 (f16 f18 ?v0) ?v1) f1) (= (f28 (f16 f18 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f27 (f6 f15 ?v0) ?v1) f1) (= (f27 (f6 f15 ?v1) ?v0) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f28 ?v0 (f16 f18 ?v1)) f1) (= (f28 ?v1 (f16 f18 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f27 ?v0 (f6 f15 ?v1)) f1) (= (f27 ?v1 (f6 f15 ?v0)) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f28 (f16 f17 ?v0) ?v1) f1) (= (f28 ?v0 ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f27 (f6 f10 ?v0) ?v1) f1) (= (f27 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8)) (= (f28 ?v0 (f16 f17 ?v0)) f1)))
(assert (forall ((?v0 S3)) (= (f27 ?v0 (f6 f10 ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f12 ?v2))) (=> (= (f27 ?v0 ?v1) f1) (= (f27 (f6 ?v_0 ?v0) (f6 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f27 ?v0 ?v1) f1) (= (f27 (f6 f9 ?v0) (f6 f9 ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f27 (f6 f9 ?v0) (f6 f9 ?v1)) f1) (= (f27 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f28 (f16 f17 (f16 (f19 f20 ?v0) ?v1)) (f16 (f19 f20 (f16 f17 ?v0)) (f16 f17 ?v1))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f27 (f6 f10 (f6 (f7 f12 ?v0) ?v1)) (f6 (f7 f12 (f6 f10 ?v0)) (f6 f10 ?v1))) f1)))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f28 (f16 f17 ?v0) ?v1) f1) (= (f28 (f16 f18 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f27 (f6 f10 ?v0) ?v1) f1) (= (f27 (f6 f15 ?v0) ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f28 ?v0 ?v1) f1) (=> (= (f28 (f16 f18 ?v0) ?v1) f1) (= (f28 (f16 f17 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f27 (f6 f15 ?v0) ?v1) f1) (= (f27 (f6 f10 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f28 (f16 f17 ?v0) ?v1) f1) (and (= (f28 ?v0 ?v1) f1) (= (f28 (f16 f18 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f27 (f6 f10 ?v0) ?v1) f1) (and (= (f27 ?v0 ?v1) f1) (= (f27 (f6 f15 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S8)) (= (f28 (f16 f18 ?v0) (f16 f17 ?v0)) f1)))
(assert (forall ((?v0 S3)) (= (f27 (f6 f15 ?v0) (f6 f10 ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f27 (f6 f15 (f6 (f7 f8 ?v0) ?v0)) (f6 (f7 f8 ?v1) ?v1)) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f27 (f6 f10 ?v0) ?v1) f1) (and (= (f27 (f6 f15 ?v1) ?v0) f1) (= (f27 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S8)) (= (f28 ?v0 ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f27 ?v0 ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f27 f29 (f6 f9 (f6 (f7 f12 (f6 (f7 f8 ?v0) ?v0)) (f6 (f7 f8 ?v1) ?v1)))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f27 (f6 (f7 f12 ?v0) ?v1) f29) f1) (= (f27 ?v1 (f6 f15 ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f27 f29 (f6 (f7 f12 ?v0) ?v1)) f1) (= (f27 (f6 f15 ?v0) ?v1) f1))))
(assert (forall ((?v0 S8)) (=> (= (f28 ?v0 f30) f1) (= (f16 f17 ?v0) (f16 f18 ?v0)))))
(assert (forall ((?v0 S3)) (=> (= (f27 ?v0 f29) f1) (= (f6 f10 ?v0) (f6 f15 ?v0)))))
(assert (forall ((?v0 S8)) (= (f28 (f16 f18 (f16 f17 ?v0)) f30) f1)))
(assert (forall ((?v0 S3)) (= (f27 (f6 f15 (f6 f10 ?v0)) f29) f1)))
(assert (forall ((?v0 S8)) (= (= f30 ?v0) (= ?v0 f30))))
(assert (forall ((?v0 S3)) (= (= f29 ?v0) (= ?v0 f29))))
(assert (forall ((?v0 S4)) (= (= f31 ?v0) (= ?v0 f31))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f29) ?v0) f31)))
(assert (forall ((?v0 S8)) (= (f16 (f19 f21 f30) ?v0) f30)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 f29) ?v0) f29)))
(assert (forall ((?v0 S4)) (= (f22 (f24 f26 f31) ?v0) f31)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 f29) ?v0) f29)))
(assert (forall ((?v0 S4)) (= (f22 (f24 f26 f31) ?v0) f31)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 f29) ?v0) f29)))
(assert (forall ((?v0 S4)) (= (f22 (f24 f26 f31) ?v0) f31)))
(assert (forall ((?v0 S8)) (= (f16 (f19 f21 ?v0) f30) f30)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 ?v0) f29) f29)))
(assert (forall ((?v0 S4)) (= (f22 (f24 f26 ?v0) f31) f31)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 ?v0) f29) f29)))
(assert (forall ((?v0 S4)) (= (f22 (f24 f26 ?v0) f31) f31)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 ?v0) f29) f29)))
(assert (forall ((?v0 S4)) (= (f22 (f24 f26 ?v0) f31) f31)))
(assert (forall ((?v0 S8)) (= (f16 (f19 f21 f30) ?v0) f30)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 f29) ?v0) f29)))
(assert (forall ((?v0 S4)) (= (f22 (f24 f26 f31) ?v0) f31)))
(assert (forall ((?v0 S8)) (= (f16 (f19 f21 ?v0) f30) f30)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 ?v0) f29) f29)))
(assert (forall ((?v0 S4)) (= (f22 (f24 f26 ?v0) f31) f31)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f16 (f19 f21 ?v0) ?v1) f30) (or (= ?v0 f30) (= ?v1 f30)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 (f7 f8 ?v0) ?v1) f29) (or (= ?v0 f29) (= ?v1 f29)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f22 (f24 f26 ?v0) ?v1) f31) (or (= ?v0 f31) (= ?v1 f31)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (not (= ?v0 f30)) (=> (not (= ?v1 f30)) (not (= (f16 (f19 f21 ?v0) ?v1) f30))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 f29)) (=> (not (= ?v1 f29)) (not (= (f6 (f7 f8 ?v0) ?v1) f29))))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (not (= ?v0 f31)) (=> (not (= ?v1 f31)) (not (= (f22 (f24 f26 ?v0) ?v1) f31))))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f16 (f19 f21 ?v0) ?v1) f30) (or (= ?v0 f30) (= ?v1 f30)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f6 (f7 f8 ?v0) ?v1) f29) (or (= ?v0 f29) (= ?v1 f29)))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (= (f22 (f24 f26 ?v0) ?v1) f31) (or (= ?v0 f31) (= ?v1 f31)))))
(assert (forall ((?v0 S8)) (= (f16 (f19 f20 f30) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f22 (f24 f25 f31) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f12 f29) ?v0) ?v0)))
(assert (forall ((?v0 S8)) (= (f16 (f19 f20 ?v0) f30) ?v0)))
(assert (forall ((?v0 S4)) (= (f22 (f24 f25 ?v0) f31) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f12 ?v0) f29) ?v0)))
(check-sat)
(exit)