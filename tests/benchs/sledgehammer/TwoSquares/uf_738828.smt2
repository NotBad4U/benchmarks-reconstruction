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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S6) S3)
(declare-fun f7 (S7 S3) S5)
(declare-fun f8 () S7)
(declare-fun f9 () S4)
(declare-fun f10 () S3)
(declare-fun f11 () S3)
(declare-fun f12 () S3)
(declare-fun f13 () S3)
(declare-fun f14 () S3)
(declare-fun f15 (S8 S3) S6)
(declare-fun f16 () S8)
(declare-fun f17 () S2)
(declare-fun f18 () S2)
(declare-fun f19 () S3)
(declare-fun f20 () S4)
(declare-fun f21 () S2)
(declare-fun f22 () S3)
(declare-fun f23 () S3)
(declare-fun f24 (S3) S1)
(declare-fun f25 (S9 S6) S6)
(declare-fun f26 (S10 S6) S9)
(declare-fun f27 () S10)
(declare-fun f28 () S10)
(declare-fun f29 () S10)
(declare-fun f30 () S3)
(declare-fun f31 () S3)
(declare-fun f32 () S6)
(declare-fun f33 (S3 S3) S1)
(declare-fun f34 (S3) S1)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f4 f9 f10)) (?v_1 (f4 f9 f12)) (?v_3 (f3 f17 (f3 f18 f19)))) (let ((?v_2 (f15 f16 ?v_3))) (not (= (f3 (f4 f5 (f6 (f7 f8 (f3 (f4 f5 (f3 (f4 f5 (f3 ?v_0 f11)) (f3 ?v_1 f13))) f14)) ?v_2)) (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_0 f13)) (f3 ?v_1 f11))) ?v_2)) (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_3))) f22)) f23)) f14))))))
(assert (= (f24 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 (f3 f17 (f3 f18 f19))))) f22)) f23)) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f6 (f7 f8 (f3 (f4 f20 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f20 (f6 (f7 f8 ?v0) ?v_0)) (f3 (f4 f9 (f3 (f4 f9 (f3 f21 ?v_1)) ?v0)) ?v1))) (f6 (f7 f8 ?v1) ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_3 (f3 f18 f19))) (let ((?v_5 (f15 f16 (f3 f17 ?v_3))) (?v_1 (f3 f18 ?v_3))) (let ((?v_0 (f15 f16 ?v_1)) (?v_2 (f7 f8 ?v0)) (?v_4 (f4 f9 (f3 f21 ?v_1))) (?v_6 (f7 f8 ?v1))) (= (f6 (f7 f8 (f3 (f4 f20 ?v0) ?v1)) ?v_0) (f3 (f4 f20 (f3 (f4 f5 (f3 (f4 f20 (f6 ?v_2 ?v_0)) (f3 (f4 f9 (f3 ?v_4 (f6 ?v_2 ?v_5))) ?v1))) (f3 (f4 f9 (f3 ?v_4 ?v0)) (f6 ?v_6 ?v_5)))) (f6 ?v_6 ?v_0))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f6 (f7 f8 (f3 (f4 f20 ?v0) ?v1)) ?v_0) (f3 (f4 f20 (f3 (f4 f5 (f6 (f7 f8 ?v0) ?v_0)) (f6 (f7 f8 ?v1) ?v_0))) (f3 (f4 f9 (f3 (f4 f9 (f3 f21 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f15 f16 (f3 f17 (f3 f18 f19))))) (= (f3 (f4 f9 (f3 (f4 f5 ?v0) ?v1)) (f3 (f4 f20 ?v0) ?v1)) (f3 (f4 f20 (f6 (f7 f8 ?v0) ?v_0)) (f6 (f7 f8 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f6 (f7 f8 (f3 (f4 f5 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f5 (f6 (f7 f8 ?v0) ?v_0)) (f3 (f4 f9 (f3 (f4 f9 (f3 f21 ?v_1)) ?v0)) ?v1))) (f6 (f7 f8 ?v1) ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_3 (f3 f18 f19))) (let ((?v_5 (f15 f16 (f3 f17 ?v_3))) (?v_1 (f3 f18 ?v_3))) (let ((?v_0 (f15 f16 ?v_1)) (?v_4 (f4 f9 (f3 f21 ?v_1))) (?v_2 (f7 f8 ?v0)) (?v_6 (f7 f8 ?v1))) (= (f6 (f7 f8 (f3 (f4 f5 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f5 (f3 (f4 f5 (f6 ?v_2 ?v_0)) (f3 (f4 f9 (f3 ?v_4 (f6 ?v_2 ?v_5))) ?v1))) (f3 (f4 f9 (f3 ?v_4 ?v0)) (f6 ?v_6 ?v_5)))) (f6 ?v_6 ?v_0))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f6 (f7 f8 (f3 (f4 f5 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f5 (f6 (f7 f8 ?v0) ?v_0)) (f6 (f7 f8 ?v1) ?v_0))) (f3 (f4 f9 (f3 (f4 f9 (f3 f21 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f15 f16 (f3 f17 (f3 f18 f19))))) (= (f25 (f26 f27 (f25 (f26 f28 ?v0) ?v1)) ?v_0) (f25 (f26 f28 (f25 (f26 f28 (f25 (f26 f27 ?v0) ?v_0)) (f25 (f26 f27 ?v1) ?v_0))) (f25 (f26 f29 (f25 (f26 f29 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f15 f16 ?v0))) (= (f25 (f26 f27 ?v_0) (f15 f16 (f3 f17 (f3 f18 f19)))) (f25 (f26 f29 ?v_0) ?v_0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f3 f21 ?v0))) (= (f6 (f7 f8 ?v_0) (f15 f16 (f3 f17 (f3 f18 f19)))) (f3 (f4 f9 ?v_0) ?v_0)))))
(assert (let ((?v_0 (f3 f17 (f3 f18 f19)))) (= (f3 (f4 f5 (f6 (f7 f8 f30) (f15 f16 ?v_0))) f23) (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_0))) f22)) f23)) f31))))
(assert (forall ((?v0 S3)) (let ((?v_1 (f3 f18 f19)) (?v_0 (f7 f8 ?v0))) (= (f3 (f4 f9 ?v0) (f6 ?v_0 (f15 f16 (f3 f17 ?v_1)))) (f6 ?v_0 (f15 f16 (f3 f18 ?v_1)))))))
(assert (= (f6 (f7 f8 f23) (f15 f16 (f3 f17 (f3 f18 f19)))) f23))
(assert (= (f25 (f26 f27 f32) (f15 f16 (f3 f17 (f3 f18 f19)))) f32))
(assert (forall ((?v0 S6)) (= (f25 (f26 f29 ?v0) ?v0) (f25 (f26 f27 ?v0) (f15 f16 (f3 f17 (f3 f18 f19)))))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 ?v0) ?v0) (f6 (f7 f8 ?v0) (f15 f16 (f3 f17 (f3 f18 f19)))))))
(assert (= (f33 f23 f31) f1))
(assert (=> (forall ((?v0 S3)) (let ((?v_0 (f3 f17 (f3 f18 f19)))) (=> (= (f3 (f4 f5 (f6 (f7 f8 f30) (f15 f16 ?v_0))) f23) (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_0))) f22)) f23)) ?v0)) false))) false))
(assert (= (f34 (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 (f3 f17 (f3 f18 f19))))) f22)) f23)) f31)) f1))
(assert (=> (= f31 f23) (exists ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f3 (f4 f5 (f6 (f7 f8 ?v0) ?v_0)) (f6 (f7 f8 ?v1) ?v_0)) (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_1))) f22)) f23)))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f26 f27 ?v0))) (= (f25 (f26 f27 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f26 f29 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (let ((?v_0 (f7 f8 ?v0))) (= (f6 (f7 f8 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f25 (f26 f29 ?v1) ?v2))))))
(assert (forall ((?v0 S6)) (= (f25 (f26 f27 ?v0) f32) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 ?v0) f32) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f26 f27 ?v0))) (= (f25 (f26 f29 (f25 ?v_0 ?v1)) (f25 ?v_0 ?v2)) (f25 ?v_0 (f25 (f26 f28 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (let ((?v_0 (f7 f8 ?v0))) (= (f3 (f4 f9 (f6 ?v_0 ?v1)) (f6 ?v_0 ?v2)) (f6 ?v_0 (f25 (f26 f28 ?v1) ?v2))))))
(assert (forall ((?v0 S6)) (= (f25 (f26 f29 (f15 f16 (f3 f17 (f3 f18 f19)))) ?v0) (f25 (f26 f28 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f25 (f26 f29 ?v0) (f15 f16 (f3 f17 (f3 f18 f19)))) (f25 (f26 f28 ?v0) ?v0))))
(assert (= (f25 (f26 f28 f32) f32) (f15 f16 (f3 f17 (f3 f18 f19)))))
(assert (= (f15 f16 (f3 f18 f19)) f32))
(assert (= f32 (f15 f16 (f3 f18 f19))))
(assert (= (f24 (f3 f21 (f3 f17 (f3 f18 f19)))) f1))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f9 ?v0))) (= (f3 (f4 f9 (f3 ?v_0 ?v1)) (f3 (f4 f9 ?v2) ?v3)) (f3 (f4 f9 (f3 ?v_0 ?v2)) (f3 (f4 f9 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f26 f29 ?v0))) (= (f25 (f26 f29 (f25 ?v_0 ?v1)) (f25 (f26 f29 ?v2) ?v3)) (f25 (f26 f29 (f25 ?v_0 ?v2)) (f25 (f26 f29 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f4 f9 (f3 (f4 f9 ?v0) ?v1))) (?v_0 (f4 f9 ?v2))) (= (f3 ?v_1 (f3 ?v_0 ?v3)) (f3 ?v_0 (f3 ?v_1 ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_1 (f26 f29 (f25 (f26 f29 ?v0) ?v1))) (?v_0 (f26 f29 ?v2))) (= (f25 ?v_1 (f25 ?v_0 ?v3)) (f25 ?v_0 (f25 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f9 ?v0)) (?v_1 (f3 (f4 f9 ?v2) ?v3))) (= (f3 (f4 f9 (f3 ?v_0 ?v1)) ?v_1) (f3 ?v_0 (f3 (f4 f9 ?v1) ?v_1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f26 f29 ?v0)) (?v_1 (f25 (f26 f29 ?v2) ?v3))) (= (f25 (f26 f29 (f25 ?v_0 ?v1)) ?v_1) (f25 ?v_0 (f25 (f26 f29 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v0))) (= (f3 (f4 f9 (f3 ?v_0 ?v1)) ?v2) (f3 (f4 f9 (f3 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f26 f29 ?v0))) (= (f25 (f26 f29 (f25 ?v_0 ?v1)) ?v2) (f25 (f26 f29 (f25 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v0))) (= (f3 (f4 f9 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f26 f29 ?v0))) (= (f25 (f26 f29 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f26 f29 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f9 ?v0))) (= (f3 ?v_0 (f3 (f4 f9 ?v1) ?v2)) (f3 (f4 f9 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f26 f29 ?v0))) (= (f25 ?v_0 (f25 (f26 f29 ?v1) ?v2)) (f25 (f26 f29 (f25 ?v_0 ?v1)) ?v2)))))
(check-sat)
(exit)
