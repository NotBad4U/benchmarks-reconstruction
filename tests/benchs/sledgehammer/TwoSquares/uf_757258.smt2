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
(declare-fun f24 () S5)
(declare-fun f25 () S6)
(declare-fun f26 () S3)
(declare-fun f27 (S3) S1)
(declare-fun f28 (S9 S6) S6)
(declare-fun f29 (S10 S6) S9)
(declare-fun f30 () S10)
(declare-fun f31 () S10)
(declare-fun f32 () S10)
(declare-fun f33 () S3)
(declare-fun f34 () S3)
(declare-fun f35 (S3 S3) S1)
(declare-fun f36 (S3) S1)
(declare-fun f37 () S6)
(declare-fun f38 () S6)
(declare-fun f39 () S3)
(declare-fun f40 () S3)
(declare-fun f41 (S3 S3) S1)
(declare-fun f42 () S3)
(declare-fun f43 (S6 S6) S1)
(declare-fun f44 () S4)
(declare-fun f45 () S10)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f4 f9 f10)) (?v_1 (f4 f9 f12)) (?v_3 (f3 f17 (f3 f18 f19)))) (let ((?v_2 (f15 f16 ?v_3))) (not (= (f3 (f4 f5 (f6 (f7 f8 (f3 (f4 f5 (f3 (f4 f5 (f3 ?v_0 f11)) (f3 ?v_1 f13))) f14)) ?v_2)) (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_0 f13)) (f3 ?v_1 f11))) ?v_2)) (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_3))) f22)) f23)) f14))))))
(assert (let ((?v_2 (f4 f9 f10)) (?v_3 (f4 f9 f12)) (?v_0 (f3 f17 (f3 f18 f19)))) (let ((?v_1 (f15 f16 ?v_0))) (= (f3 (f4 f9 (f6 (f7 f8 (f3 (f4 f5 f23) (f6 f24 f25))) ?v_1)) (f3 (f4 f20 (f3 (f4 f20 (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_0))) f22)) f23)) f14)) (f6 (f7 f8 (f3 (f4 f5 (f3 (f4 f5 (f3 ?v_2 f11)) (f3 ?v_3 f13))) f14)) ?v_1))) (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_2 f13)) (f3 ?v_3 f11))) ?v_1))) f26))))
(assert (not (= (f6 (f7 f8 (f3 (f4 f5 f23) (f6 f24 f25))) (f15 f16 (f3 f17 (f3 f18 f19)))) f26)))
(assert (not (= (f6 (f7 f8 (f3 (f4 f5 f23) (f6 f24 f25))) (f15 f16 (f3 f17 (f3 f18 f19)))) f26)))
(assert (let ((?v_0 (f15 f16 (f3 f17 (f3 f18 f19))))) (= (f3 (f4 f5 (f6 (f7 f8 f11) ?v_0)) (f6 (f7 f8 f13) ?v_0)) (f3 (f4 f9 (f3 (f4 f5 f23) (f6 f24 f25))) f14))))
(assert (let ((?v_2 (f4 f9 f10)) (?v_3 (f4 f9 f12)) (?v_0 (f3 f17 (f3 f18 f19)))) (let ((?v_1 (f15 f16 ?v_0))) (= (f3 (f4 f9 (f6 (f7 f8 (f3 (f4 f5 f23) (f6 f24 f25))) ?v_1)) (f3 (f4 f20 (f3 (f4 f20 (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_0))) f22)) f23)) f14)) (f6 (f7 f8 (f3 (f4 f5 (f3 (f4 f5 (f3 ?v_2 f11)) (f3 ?v_3 f13))) f14)) ?v_1))) (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_2 f13)) (f3 ?v_3 f11))) ?v_1))) f26))))
(assert (= (f27 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 (f3 f17 (f3 f18 f19))))) f22)) f23)) f1))
(assert (let ((?v_4 (f4 f9 f10)) (?v_6 (f4 f9 f12)) (?v_3 (f15 f16 (f3 f17 (f3 f18 f19)))) (?v_0 (f3 (f4 f5 f23) (f6 f24 f25)))) (let ((?v_5 (f4 f9 ?v_0)) (?v_1 (f4 f9 (f3 (f4 f5 (f3 ?v_4 ?v_0)) f11))) (?v_2 (f4 f9 (f3 (f4 f5 (f3 ?v_6 ?v_0)) f13)))) (= (f3 (f4 f5 (f6 (f7 f8 (f3 (f4 f5 (f3 ?v_1 f11)) (f3 ?v_2 f13))) ?v_3)) (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_1 f13)) (f3 ?v_2 f11))) ?v_3)) (f3 (f4 f5 (f6 (f7 f8 (f3 (f4 f5 (f3 (f4 f5 (f3 ?v_5 (f3 ?v_4 f11))) (f3 ?v_5 (f3 ?v_6 f13)))) (f3 (f4 f5 (f6 (f7 f8 f11) ?v_3)) (f6 (f7 f8 f13) ?v_3)))) ?v_3)) (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_5 (f3 ?v_4 f13))) (f3 ?v_5 (f3 ?v_6 f11)))) ?v_3))))))
(assert (let ((?v_2 (f4 f9 f10)) (?v_3 (f4 f9 f12)) (?v_1 (f15 f16 (f3 f17 (f3 f18 f19)))) (?v_0 (f4 f9 (f3 (f4 f5 f23) (f6 f24 f25))))) (let ((?v_4 (f4 f5 (f3 (f4 f5 (f3 ?v_0 (f3 ?v_2 f11))) (f3 ?v_0 (f3 ?v_3 f13))))) (?v_5 (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_0 (f3 ?v_2 f13))) (f3 ?v_0 (f3 ?v_3 f11)))) ?v_1))) (= (f3 (f4 f5 (f6 (f7 f8 (f3 ?v_4 (f3 (f4 f5 (f6 (f7 f8 f11) ?v_1)) (f6 (f7 f8 f13) ?v_1)))) ?v_1)) ?v_5) (f3 (f4 f5 (f6 (f7 f8 (f3 ?v_4 (f3 ?v_0 f14))) ?v_1)) ?v_5)))))
(assert (let ((?v_3 (f4 f9 f10)) (?v_4 (f4 f9 f12)) (?v_0 (f3 f17 (f3 f18 f19)))) (let ((?v_2 (f15 f16 ?v_0))) (let ((?v_1 (f4 f9 (f6 (f7 f8 (f3 (f4 f5 f23) (f6 f24 f25))) ?v_2)))) (= (f3 ?v_1 (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_0))) f22)) f23)) f14)) (f3 ?v_1 (f3 (f4 f5 (f6 (f7 f8 (f3 (f4 f5 (f3 (f4 f5 (f3 ?v_3 f11)) (f3 ?v_4 f13))) f14)) ?v_2)) (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_3 f13)) (f3 ?v_4 f11))) ?v_2))))))))
(assert (let ((?v_4 (f4 f9 f10)) (?v_5 (f4 f9 f12)) (?v_0 (f3 f17 (f3 f18 f19)))) (let ((?v_1 (f15 f16 ?v_0)) (?v_2 (f3 (f4 f5 f23) (f6 f24 f25)))) (let ((?v_3 (f4 f9 (f6 (f7 f8 ?v_2) ?v_1)))) (= (f3 (f4 f9 (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_0))) f22)) f23)) ?v_2)) (f3 (f4 f5 (f6 (f7 f8 f11) ?v_1)) (f6 (f7 f8 f13) ?v_1))) (f3 (f4 f5 (f3 ?v_3 (f6 (f7 f8 (f3 (f4 f5 (f3 (f4 f5 (f3 ?v_4 f11)) (f3 ?v_5 f13))) f14)) ?v_1))) (f3 ?v_3 (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_4 f13)) (f3 ?v_5 f11))) ?v_1))))))))
(assert (let ((?v_4 (f4 f9 f10)) (?v_5 (f4 f9 f12)) (?v_0 (f3 f17 (f3 f18 f19)))) (let ((?v_1 (f15 f16 ?v_0)) (?v_2 (f3 (f4 f5 f23) (f6 f24 f25)))) (let ((?v_3 (f4 f9 ?v_2))) (= (f3 (f4 f9 (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_0))) f22)) f23)) ?v_2)) (f3 (f4 f5 (f6 (f7 f8 f11) ?v_1)) (f6 (f7 f8 f13) ?v_1))) (f3 (f4 f5 (f6 (f7 f8 (f3 (f4 f5 (f3 (f4 f5 (f3 ?v_3 (f3 ?v_4 f11))) (f3 ?v_3 (f3 ?v_5 f13)))) (f3 ?v_3 f14))) ?v_1)) (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_3 (f3 ?v_4 f13))) (f3 ?v_3 (f3 ?v_5 f11)))) ?v_1)))))))
(assert (=> (forall ((?v0 S3)) (let ((?v_0 (f15 f16 (f3 f17 (f3 f18 f19))))) (=> (= (f3 (f4 f5 (f6 (f7 f8 f11) ?v_0)) (f6 (f7 f8 f13) ?v_0)) (f3 (f4 f9 (f3 (f4 f5 f23) (f6 f24 f25))) ?v0)) false))) false))
(assert (=> (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_1))) (=> (= (f3 (f4 f5 (f6 (f7 f8 ?v0) ?v_0)) (f6 (f7 f8 ?v1) ?v_0)) (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_1))) f22)) f23)) (f3 (f4 f5 f23) (f6 f24 f25)))) false)))) false))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f6 (f7 f8 (f3 (f4 f20 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f20 (f6 (f7 f8 ?v0) ?v_0)) (f3 (f4 f9 (f3 (f4 f9 (f3 f21 ?v_1)) ?v0)) ?v1))) (f6 (f7 f8 ?v1) ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_3 (f3 f18 f19))) (let ((?v_5 (f15 f16 (f3 f17 ?v_3))) (?v_1 (f3 f18 ?v_3))) (let ((?v_0 (f15 f16 ?v_1)) (?v_2 (f7 f8 ?v0)) (?v_4 (f4 f9 (f3 f21 ?v_1))) (?v_6 (f7 f8 ?v1))) (= (f6 (f7 f8 (f3 (f4 f20 ?v0) ?v1)) ?v_0) (f3 (f4 f20 (f3 (f4 f5 (f3 (f4 f20 (f6 ?v_2 ?v_0)) (f3 (f4 f9 (f3 ?v_4 (f6 ?v_2 ?v_5))) ?v1))) (f3 (f4 f9 (f3 ?v_4 ?v0)) (f6 ?v_6 ?v_5)))) (f6 ?v_6 ?v_0))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f6 (f7 f8 (f3 (f4 f20 ?v0) ?v1)) ?v_0) (f3 (f4 f20 (f3 (f4 f5 (f6 (f7 f8 ?v0) ?v_0)) (f6 (f7 f8 ?v1) ?v_0))) (f3 (f4 f9 (f3 (f4 f9 (f3 f21 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f15 f16 (f3 f17 (f3 f18 f19))))) (= (f3 (f4 f9 (f3 (f4 f5 ?v0) ?v1)) (f3 (f4 f20 ?v0) ?v1)) (f3 (f4 f20 (f6 (f7 f8 ?v0) ?v_0)) (f6 (f7 f8 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f6 (f7 f8 (f3 (f4 f5 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f5 (f6 (f7 f8 ?v0) ?v_0)) (f3 (f4 f9 (f3 (f4 f9 (f3 f21 ?v_1)) ?v0)) ?v1))) (f6 (f7 f8 ?v1) ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_3 (f3 f18 f19))) (let ((?v_5 (f15 f16 (f3 f17 ?v_3))) (?v_1 (f3 f18 ?v_3))) (let ((?v_0 (f15 f16 ?v_1)) (?v_4 (f4 f9 (f3 f21 ?v_1))) (?v_2 (f7 f8 ?v0)) (?v_6 (f7 f8 ?v1))) (= (f6 (f7 f8 (f3 (f4 f5 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f5 (f3 (f4 f5 (f6 ?v_2 ?v_0)) (f3 (f4 f9 (f3 ?v_4 (f6 ?v_2 ?v_5))) ?v1))) (f3 (f4 f9 (f3 ?v_4 ?v0)) (f6 ?v_6 ?v_5)))) (f6 ?v_6 ?v_0))))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f15 f16 (f3 f17 (f3 f18 f19))))) (= (f28 (f29 f30 (f28 (f29 f31 ?v0) ?v1)) ?v_0) (f28 (f29 f31 (f28 (f29 f31 (f28 (f29 f30 ?v0) ?v_0)) (f28 (f29 f30 ?v1) ?v_0))) (f28 (f29 f32 (f28 (f29 f32 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f6 (f7 f8 (f3 (f4 f5 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f5 (f6 (f7 f8 ?v0) ?v_0)) (f6 (f7 f8 ?v1) ?v_0))) (f3 (f4 f9 (f3 (f4 f9 (f3 f21 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f15 f16 ?v0))) (= (f28 (f29 f30 ?v_0) (f15 f16 (f3 f17 (f3 f18 f19)))) (f28 (f29 f32 ?v_0) ?v_0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f3 f21 ?v0))) (= (f6 (f7 f8 ?v_0) (f15 f16 (f3 f17 (f3 f18 f19)))) (f3 (f4 f9 ?v_0) ?v_0)))))
(assert (let ((?v_0 (f3 f17 (f3 f18 f19)))) (= (f3 (f4 f5 (f6 (f7 f8 f33) (f15 f16 ?v_0))) f23) (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_0))) f22)) f23)) f34))))
(assert (forall ((?v0 S3)) (let ((?v_1 (f3 f18 f19)) (?v_0 (f7 f8 ?v0))) (= (f3 (f4 f9 ?v0) (f6 ?v_0 (f15 f16 (f3 f17 ?v_1)))) (f6 ?v_0 (f15 f16 (f3 f18 ?v_1)))))))
(assert (= (f35 f23 f34) f1))
(assert (=> (forall ((?v0 S3)) (let ((?v_0 (f3 f17 (f3 f18 f19)))) (=> (= (f3 (f4 f5 (f6 (f7 f8 f33) (f15 f16 ?v_0))) f23) (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_0))) f22)) f23)) ?v0)) false))) false))
(assert (= (f36 (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 (f3 f17 (f3 f18 f19))))) f22)) f23)) f34)) f1))
(assert (=> (= f34 f23) (exists ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f3 (f4 f5 (f6 (f7 f8 ?v0) ?v_0)) (f6 (f7 f8 ?v1) ?v_0)) (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_1))) f22)) f23)))))))
(assert (forall ((?v0 S6)) (= (f28 (f29 f32 (f15 f16 (f3 f17 (f3 f18 f19)))) ?v0) (f28 (f29 f31 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f28 (f29 f32 ?v0) (f15 f16 (f3 f17 (f3 f18 f19)))) (f28 (f29 f31 ?v0) ?v0))))
(assert (= (f27 (f3 f21 (f3 f17 (f3 f18 f19)))) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f3 (f4 f9 ?v0) ?v0)) (f3 (f4 f9 ?v1) ?v1)) f26) (and (= ?v0 f26) (= ?v1 f26)))))
(assert (= f26 (f3 f21 f19)))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_1 (f15 f16 (f3 f17 (f3 f18 f19)))) (?v_0 (f29 f30 ?v0))) (= (f28 ?v_0 (f28 (f29 f32 ?v_1) ?v1)) (f28 (f29 f30 (f28 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S6)) (let ((?v_1 (f15 f16 (f3 f17 (f3 f18 f19)))) (?v_0 (f7 f8 ?v0))) (= (f6 ?v_0 (f28 (f29 f32 ?v_1) ?v1)) (f6 (f7 f8 (f6 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S3)) (= (= (f6 (f7 f8 ?v0) (f15 f16 (f3 f17 (f3 f18 f19)))) f26) (= ?v0 f26))))
(assert (= (f28 (f29 f30 f37) (f15 f16 (f3 f17 (f3 f18 f19)))) f37))
(assert (= (f6 (f7 f8 f26) (f15 f16 (f3 f17 (f3 f18 f19)))) f26))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f15 f16 (f3 f17 (f3 f18 f19))))) (= (= (f3 (f4 f5 (f6 (f7 f8 ?v0) ?v_0)) (f6 (f7 f8 ?v1) ?v_0)) f26) (and (= ?v0 f26) (= ?v1 f26))))))
(assert (= f23 (f3 f21 (f3 f18 f19))))
(assert (forall ((?v0 S6)) (= (f28 (f29 f30 ?v0) (f15 f16 (f3 f18 (f3 f18 f19)))) (f28 (f29 f32 (f28 (f29 f32 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 ?v0) (f15 f16 (f3 f18 (f3 f18 f19)))) (f3 (f4 f9 (f3 (f4 f9 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S3)) (let ((?v_2 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_2)) (?v_1 (f7 f8 ?v0))) (= (f6 (f7 f8 (f6 ?v_1 ?v_0)) ?v_0) (f6 ?v_1 (f15 f16 (f3 f17 ?v_2))))))))
(assert (forall ((?v0 S6)) (= (f28 (f29 f30 ?v0) (f15 f16 (f3 f17 (f3 f18 f19)))) (f28 (f29 f32 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 ?v0) (f15 f16 (f3 f17 (f3 f18 f19)))) (f3 (f4 f9 ?v0) ?v0))))
(assert (= (f28 (f29 f30 f38) (f15 f16 (f3 f17 (f3 f18 f19)))) f38))
(assert (= (f6 (f7 f8 f23) (f15 f16 (f3 f17 (f3 f18 f19)))) f23))
(assert (not (= (f36 (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 (f3 f17 (f3 f18 f19))))) f22)) f23)) (f3 (f4 f5 f23) (f6 f24 f37)))) f1)))
(assert (let ((?v_0 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 (f3 f17 (f3 f18 f19))))) f22)) f23)) (?v_1 (f3 (f4 f5 f23) (f6 f24 f25)))) (not (=> (= (f35 ?v_1 ?v_0) f1) (not (= (f36 (f3 (f4 f9 ?v_0) ?v_1)) f1))))))
(assert (let ((?v_1 (f3 f17 (f3 f18 f19)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f3 (f4 f5 (f6 (f7 f8 f39) ?v_0)) (f6 (f7 f8 f40) ?v_0)) (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_1))) f22)) f23)) (f3 (f4 f5 f23) (f6 f24 f25)))))))
(assert (let ((?v_0 (f15 f16 (f3 f17 (f3 f18 f19))))) (= (f41 (f3 (f4 f5 f23) (f6 f24 f25)) (f3 (f4 f5 (f6 (f7 f8 f11) ?v_0)) (f6 (f7 f8 f13) ?v_0))) f1)))
(assert (let ((?v_0 (f3 f17 (f3 f18 f19)))) (= (f41 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_0))) f22)) f23) (f3 (f4 f5 (f6 (f7 f8 f33) (f15 f16 ?v_0))) f23)) f1)))
(assert (= (f35 f34 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 (f3 f17 (f3 f18 f19))))) f22)) f23)) f1))
(assert (let ((?v_0 (f6 (f7 f8 f33) (f15 f16 (f3 f17 (f3 f18 f19)))))) (= (f3 (f4 f20 ?v_0) (f3 f21 f42)) (f3 (f4 f5 ?v_0) f23))))
(assert (= (f35 f26 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 (f3 f17 (f3 f18 f19))))) f22)) f23)) f1))
(assert (let ((?v_0 (f3 f17 (f3 f18 f19)))) (= (f3 f21 ?v_0) (f6 f24 (f15 f16 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f29 f30 ?v0))) (let ((?v_1 (f28 ?v_0 ?v1))) (= (f28 ?v_0 (f28 (f29 f32 (f15 f16 (f3 f17 (f3 f18 f19)))) ?v1)) (f28 (f29 f32 ?v_1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S6)) (let ((?v_0 (f7 f8 ?v0))) (let ((?v_1 (f6 ?v_0 ?v1))) (= (f6 ?v_0 (f28 (f29 f32 (f15 f16 (f3 f17 (f3 f18 f19)))) ?v1)) (f3 (f4 f9 ?v_1) ?v_1))))))
(assert (= (f35 f26 (f3 (f4 f5 f23) (f6 f24 f25))) f1))
(assert (= (f35 f14 (f3 (f4 f5 f23) (f6 f24 f25))) f1))
(assert (= (f43 f37 f25) f1))
(assert (let ((?v_0 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 (f3 f17 (f3 f18 f19))))) f22)) f23)) (?v_1 (f3 (f4 f5 f23) (f6 f24 f25)))) (and (= (f35 ?v_1 ?v_0) f1) (= (f36 (f3 (f4 f9 ?v_0) ?v_1)) f1))))
(assert (let ((?v_0 (f15 f16 (f3 f17 (f3 f18 f19)))) (?v_1 (f4 f9 f39)) (?v_2 (f4 f9 f40))) (= (f3 (f4 f9 (f3 (f4 f5 (f6 (f7 f8 f39) ?v_0)) (f6 (f7 f8 f40) ?v_0))) (f3 (f4 f5 (f6 (f7 f8 f11) ?v_0)) (f6 (f7 f8 f13) ?v_0))) (f3 (f4 f5 (f6 (f7 f8 (f3 (f4 f5 (f3 ?v_1 f11)) (f3 ?v_2 f13))) ?v_0)) (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_1 f13)) (f3 ?v_2 f11))) ?v_0)))))
(assert (let ((?v_0 (f3 f17 (f3 f18 f19)))) (= (f41 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_0))) f22)) f23) (f3 (f4 f20 (f6 (f7 f8 f33) (f15 f16 ?v_0))) (f3 f21 f42))) f1)))
(assert (let ((?v_0 (f3 f17 (f3 f18 f19)))) (let ((?v_1 (f15 f16 ?v_0))) (let ((?v_2 (f3 (f4 f5 (f6 (f7 f8 f11) ?v_1)) (f6 (f7 f8 f13) ?v_1)))) (= (f3 (f4 f9 (f3 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 ?v_0))) f22)) f23)) (f3 (f4 f5 f23) (f6 f24 f25)))) ?v_2) (f3 (f4 f9 (f3 (f4 f5 (f6 (f7 f8 f39) ?v_1)) (f6 (f7 f8 f40) ?v_1))) ?v_2))))))
(assert (let ((?v_2 (f15 f16 (f3 f17 (f3 f18 f19)))) (?v_3 (f3 (f4 f5 f23) (f6 f24 f25)))) (let ((?v_4 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 f10) ?v_3)) f11))) (?v_5 (f4 f9 (f3 (f4 f5 (f3 (f4 f9 f12) ?v_3)) f13))) (?v_0 (f4 f9 f39)) (?v_1 (f4 f9 f40))) (= (f3 (f4 f5 (f6 (f7 f8 (f3 (f4 f5 (f3 ?v_0 f11)) (f3 ?v_1 f13))) ?v_2)) (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_0 f13)) (f3 ?v_1 f11))) ?v_2)) (f3 (f4 f5 (f6 (f7 f8 (f3 (f4 f5 (f3 ?v_4 f11)) (f3 ?v_5 f13))) ?v_2)) (f6 (f7 f8 (f3 (f4 f20 (f3 ?v_4 f13)) (f3 ?v_5 f11))) ?v_2))))))
(assert (= (f3 (f4 f44 (f3 f21 f42)) (f3 (f4 f5 (f3 (f4 f9 (f3 f21 (f3 f17 (f3 f17 (f3 f18 f19))))) f22)) f23)) f23))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f29 f30 ?v0))) (= (f28 ?v_0 ?v1) (ite (= ?v1 f37) f38 (f28 (f29 f32 ?v0) (f28 ?v_0 (f28 (f29 f45 ?v1) f38))))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f28 (f29 f32 ?v0) ?v1) (ite (= ?v0 f37) f37 (f28 (f29 f31 ?v1) (f28 (f29 f32 (f28 (f29 f45 ?v0) f38)) ?v1))))))
(assert (forall ((?v0 S6)) (= (f28 (f29 f30 ?v0) f38) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 ?v0) f38) ?v0)))
(assert (forall ((?v0 S6)) (= (f28 (f29 f30 ?v0) f37) f38)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 ?v0) f37) f23)))
(assert (= f23 (f6 f24 f38)))
(check-sat)
(exit)