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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 () S2)
(declare-fun f7 () S2)
(declare-fun f8 () S2)
(declare-fun f9 () S3)
(declare-fun f10 () S4)
(declare-fun f11 () S3)
(declare-fun f12 (S5 S6) S3)
(declare-fun f13 () S5)
(declare-fun f14 () S6)
(declare-fun f15 () S3)
(declare-fun f16 (S7 S3) S5)
(declare-fun f17 () S7)
(declare-fun f18 () S3)
(declare-fun f19 (S8 S3) S6)
(declare-fun f20 () S8)
(declare-fun f21 () S3)
(declare-fun f22 (S9 S3) S1)
(declare-fun f23 (S10 S3) S9)
(declare-fun f24 () S10)
(declare-fun f25 () S10)
(declare-fun f26 (S11 S6) S6)
(declare-fun f27 (S12 S6) S11)
(declare-fun f28 () S12)
(declare-fun f29 () S12)
(declare-fun f30 () S12)
(declare-fun f31 () S6)
(declare-fun f32 () S3)
(assert (not (= f1 f2)))
(assert (let ((?v_1 (f3 f7 (f3 f8 f9)))) (let ((?v_0 (f4 f5 (f3 f6 (f3 f7 ?v_1)))) (?v_2 (f19 f20 ?v_1))) (not (= (f3 (f4 f5 (f3 ?v_0 (f3 (f4 f10 f11) (f12 f13 f14)))) f15) (f3 (f4 f10 (f3 ?v_0 (f12 (f16 f17 f18) ?v_2))) (f3 ?v_0 (f12 (f16 f17 f21) ?v_2))))))))
(assert (let ((?v_0 (f19 f20 (f3 f7 (f3 f8 f9))))) (= (f3 (f4 f10 (f12 (f16 f17 f18) ?v_0)) (f12 (f16 f17 f21) ?v_0)) (f3 (f4 f5 (f3 (f4 f10 f11) (f12 f13 f14))) f15))))
(assert (let ((?v_0 (f19 f20 (f3 f7 (f3 f8 f9))))) (= (f3 (f4 f10 (f12 (f16 f17 f18) ?v_0)) (f12 (f16 f17 f21) ?v_0)) (f3 (f4 f5 (f3 (f4 f10 f11) (f12 f13 f14))) f15))))
(assert (not (= (f22 (f23 f24 f15) (f3 (f4 f10 f11) (f12 f13 f14))) f1)))
(assert (=> (forall ((?v0 S3)) (let ((?v_0 (f19 f20 (f3 f7 (f3 f8 f9))))) (=> (= (f3 (f4 f10 (f12 (f16 f17 f18) ?v_0)) (f12 (f16 f17 f21) ?v_0)) (f3 (f4 f5 (f3 (f4 f10 f11) (f12 f13 f14))) ?v0)) false))) false))
(assert (let ((?v_0 (f19 f20 (f3 f7 (f3 f8 f9))))) (= (f22 (f23 f25 (f3 (f4 f10 f11) (f12 f13 f14))) (f3 (f4 f10 (f12 (f16 f17 f18) ?v_0)) (f12 (f16 f17 f21) ?v_0))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f7 (f3 f8 f9)))) (let ((?v_0 (f19 f20 ?v_1))) (= (f12 (f16 f17 (f3 (f4 f10 ?v0) ?v1)) ?v_0) (f3 (f4 f10 (f3 (f4 f10 (f12 (f16 f17 ?v0) ?v_0)) (f3 (f4 f5 (f3 (f4 f5 (f3 f6 ?v_1)) ?v0)) ?v1))) (f12 (f16 f17 ?v1) ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_3 (f3 f8 f9))) (let ((?v_5 (f19 f20 (f3 f7 ?v_3))) (?v_1 (f3 f8 ?v_3))) (let ((?v_0 (f19 f20 ?v_1)) (?v_2 (f16 f17 ?v0)) (?v_4 (f4 f5 (f3 f6 ?v_1))) (?v_6 (f16 f17 ?v1))) (= (f12 (f16 f17 (f3 (f4 f10 ?v0) ?v1)) ?v_0) (f3 (f4 f10 (f3 (f4 f10 (f3 (f4 f10 (f12 ?v_2 ?v_0)) (f3 (f4 f5 (f3 ?v_4 (f12 ?v_2 ?v_5))) ?v1))) (f3 (f4 f5 (f3 ?v_4 ?v0)) (f12 ?v_6 ?v_5)))) (f12 ?v_6 ?v_0))))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f19 f20 (f3 f7 (f3 f8 f9))))) (= (f26 (f27 f28 (f26 (f27 f29 ?v0) ?v1)) ?v_0) (f26 (f27 f29 (f26 (f27 f29 (f26 (f27 f28 ?v0) ?v_0)) (f26 (f27 f28 ?v1) ?v_0))) (f26 (f27 f30 (f26 (f27 f30 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f7 (f3 f8 f9)))) (let ((?v_0 (f19 f20 ?v_1))) (= (f12 (f16 f17 (f3 (f4 f10 ?v0) ?v1)) ?v_0) (f3 (f4 f10 (f3 (f4 f10 (f12 (f16 f17 ?v0) ?v_0)) (f12 (f16 f17 ?v1) ?v_0))) (f3 (f4 f5 (f3 (f4 f5 (f3 f6 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f19 f20 ?v0))) (= (f26 (f27 f28 ?v_0) (f19 f20 (f3 f7 (f3 f8 f9)))) (f26 (f27 f30 ?v_0) ?v_0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f3 f6 ?v0))) (= (f12 (f16 f17 ?v_0) (f19 f20 (f3 f7 (f3 f8 f9)))) (f3 (f4 f5 ?v_0) ?v_0)))))
(assert (forall ((?v0 S3)) (let ((?v_1 (f3 f8 f9)) (?v_0 (f16 f17 ?v0))) (= (f3 (f4 f5 ?v0) (f12 ?v_0 (f19 f20 (f3 f7 ?v_1)))) (f12 ?v_0 (f19 f20 (f3 f8 ?v_1)))))))
(assert (let ((?v_0 (f3 f7 (f3 f8 f9)))) (= (f3 f6 ?v_0) (f12 f13 (f19 f20 ?v_0)))))
(assert (= (f26 (f27 f28 f31) (f19 f20 (f3 f7 (f3 f8 f9)))) f31))
(assert (= (f12 (f16 f17 f11) (f19 f20 (f3 f7 (f3 f8 f9)))) f11))
(assert (forall ((?v0 S6)) (= (f26 (f27 f30 ?v0) ?v0) (f26 (f27 f28 ?v0) (f19 f20 (f3 f7 (f3 f8 f9)))))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) ?v0) (f12 (f16 f17 ?v0) (f19 f20 (f3 f7 (f3 f8 f9)))))))
(assert (forall ((?v0 S6)) (= (f26 (f27 f28 ?v0) (f19 f20 (f3 f7 (f3 f8 f9)))) (f26 (f27 f30 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f12 (f16 f17 ?v0) (f19 f20 (f3 f7 (f3 f8 f9)))) (f3 (f4 f5 ?v0) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f27 f28 ?v0))) (let ((?v_1 (f26 ?v_0 ?v1))) (= (f26 ?v_0 (f26 (f27 f30 (f19 f20 (f3 f7 (f3 f8 f9)))) ?v1)) (f26 (f27 f30 ?v_1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S6)) (let ((?v_0 (f16 f17 ?v0))) (let ((?v_1 (f12 ?v_0 ?v1))) (= (f12 ?v_0 (f26 (f27 f30 (f19 f20 (f3 f7 (f3 f8 f9)))) ?v1)) (f3 (f4 f5 ?v_1) ?v_1))))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f10 f11) (f3 f6 ?v0)) (f3 f6 (f3 (f4 f10 (f3 f8 f9)) ?v0)))))
(assert (= (f22 (f23 f24 f11) f32) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f22 (f23 f24 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f22 (f23 f24 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f22 (f23 f24 (f3 f6 ?v0)) (f3 f6 ?v1)) f1) (= (f22 (f23 f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f22 (f23 f24 (f3 f8 ?v0)) (f3 f8 ?v1)) f1) (= (f22 (f23 f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f22 (f23 f24 (f3 f8 ?v0)) (f3 f8 ?v1)) f1) (= (f22 (f23 f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f27 f28 ?v0))) (= (f26 (f27 f28 (f26 ?v_0 ?v1)) ?v2) (f26 ?v_0 (f26 (f27 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (let ((?v_0 (f16 f17 ?v0))) (= (f12 (f16 f17 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f26 (f27 f30 ?v1) ?v2))))))
(assert (= (= (f22 (f23 f24 f9) f9) f1) false))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f22 (f23 f24 (f3 f7 ?v0)) (f3 f7 ?v1)) f1) (= (f22 (f23 f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f22 (f23 f24 (f3 f7 ?v0)) (f3 f7 ?v1)) f1) (= (f22 (f23 f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6)) (= (f26 (f27 f28 ?v0) f31) ?v0)))
(assert (forall ((?v0 S3)) (= (f12 (f16 f17 ?v0) f31) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f22 (f23 f24 (f3 f6 ?v0)) (f3 f6 ?v1)) f1) (= (f22 (f23 f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f22 (f23 f24 ?v0) ?v1) f1) (= (f22 (f23 f24 (f3 (f4 f10 ?v0) ?v2)) (f3 (f4 f10 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (let ((?v_0 (f16 f17 ?v0))) (= (f12 (f16 f17 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f26 (f27 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f19 f20 ?v0)) (?v_0 (f19 f20 ?v1))) (= (f26 (f27 f29 ?v_1) ?v_0) (ite (= (f22 (f23 f24 ?v0) f9) f1) ?v_0 (ite (= (f22 (f23 f24 ?v1) f9) f1) ?v_1 (f19 f20 (f3 (f4 f10 ?v0) ?v1))))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f27 f28 ?v0))) (= (f26 (f27 f30 (f26 ?v_0 ?v1)) (f26 ?v_0 ?v2)) (f26 ?v_0 (f26 (f27 f29 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (let ((?v_0 (f16 f17 ?v0))) (= (f3 (f4 f5 (f12 ?v_0 ?v1)) (f12 ?v_0 ?v2)) (f12 ?v_0 (f26 (f27 f29 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f23 f25 ?v0)) (?v_1 (f4 f10 ?v2))) (=> (= (f22 ?v_0 ?v1) f1) (= (= (f22 ?v_0 (f3 ?v_1 ?v3)) f1) (= (f22 ?v_0 (f3 (f4 f10 (f3 ?v_1 (f3 (f4 f5 ?v4) ?v1))) ?v3)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f23 f25 ?v0))) (= (= (f22 ?v_0 (f3 (f4 f10 ?v1) (f3 (f4 f5 ?v0) ?v2))) f1) (= (f22 ?v_0 ?v1) f1)))))
(assert (forall ((?v0 S3)) (= (= (f22 (f23 f24 (f3 f8 ?v0)) f9) f1) (= (f22 (f23 f24 ?v0) f9) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f22 (f23 f24 (f3 f8 ?v0)) (f3 f7 ?v1)) f1) (= (f22 (f23 f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f22 (f23 f24 (f3 f8 ?v0)) (f3 f7 ?v1)) f1) (= (f22 (f23 f24 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f22 (f23 f24 (f3 f7 ?v0)) f9) f1) (= (f22 (f23 f24 ?v0) f9) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f23 f24 f9))) (= (= (f22 ?v_0 (f3 f7 ?v0)) f1) (= (f22 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f23 f24 ?v0))) (= (= (f22 ?v_0 (f3 (f4 f10 ?v1) f11)) f1) (or (= (f22 ?v_0 ?v1) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f12 (f16 f17 (f12 f13 ?v0)) ?v1) (f12 f13 (f26 (f27 f28 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f12 (f16 f17 (f12 f13 ?v0)) ?v1) (f12 f13 (f26 (f27 f28 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f12 f13 (f26 (f27 f28 ?v0) ?v1)) (f12 (f16 f17 (f12 f13 ?v0)) ?v1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (= (f3 (f4 f10 (f12 f13 ?v0)) (f3 (f4 f10 (f12 f13 ?v1)) ?v2)) (f3 (f4 f10 (f12 f13 (f26 (f27 f29 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f3 (f4 f10 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f26 (f27 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f3 (f4 f10 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f26 (f27 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f3 (f4 f5 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f26 (f27 f30 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f3 (f4 f5 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f26 (f27 f30 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f12 f13 (f26 (f27 f30 ?v0) ?v1)) (f3 (f4 f5 (f12 f13 ?v0)) (f12 f13 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (let ((?v_0 (f16 f17 ?v0))) (= (f12 ?v_0 (f26 (f27 f29 ?v1) ?v2)) (f3 (f4 f5 (f12 ?v_0 ?v1)) (f12 ?v_0 ?v2))))))
(assert (= (f12 f13 f31) f11))
(assert (= f11 (f12 f13 f31)))
(assert (forall ((?v0 S3)) (= (= (f22 (f23 f24 (f3 f6 ?v0)) f11) f1) (= (f22 (f23 f24 ?v0) (f3 f8 f9)) f1))))
(assert (forall ((?v0 S3)) (= (= (f22 (f23 f24 f11) (f3 f6 ?v0)) f1) (= (f22 (f23 f24 (f3 f8 f9)) ?v0) f1))))
(assert (forall ((?v0 S6)) (= (f26 (f27 f30 (f19 f20 (f3 f7 (f3 f8 f9)))) ?v0) (f26 (f27 f29 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f26 (f27 f30 ?v0) (f19 f20 (f3 f7 (f3 f8 f9)))) (f26 (f27 f29 ?v0) ?v0))))
(assert (= (f26 (f27 f29 f31) f31) (f19 f20 (f3 f7 (f3 f8 f9)))))
(assert (= (f19 f20 (f3 f8 f9)) f31))
(assert (= f31 (f19 f20 (f3 f8 f9))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f27 f30 ?v0))) (= (f26 (f27 f30 (f26 ?v_0 ?v1)) (f26 (f27 f30 ?v2) ?v3)) (f26 (f27 f30 (f26 ?v_0 ?v2)) (f26 (f27 f30 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) (f3 (f4 f5 ?v2) ?v3)) (f3 (f4 f5 (f3 ?v_0 ?v2)) (f3 (f4 f5 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_1 (f27 f30 (f26 (f27 f30 ?v0) ?v1))) (?v_0 (f27 f30 ?v2))) (= (f26 ?v_1 (f26 ?v_0 ?v3)) (f26 ?v_0 (f26 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f4 f5 (f3 (f4 f5 ?v0) ?v1))) (?v_0 (f4 f5 ?v2))) (= (f3 ?v_1 (f3 ?v_0 ?v3)) (f3 ?v_0 (f3 ?v_1 ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f27 f30 ?v0)) (?v_1 (f26 (f27 f30 ?v2) ?v3))) (= (f26 (f27 f30 (f26 ?v_0 ?v1)) ?v_1) (f26 ?v_0 (f26 (f27 f30 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f5 ?v0)) (?v_1 (f3 (f4 f5 ?v2) ?v3))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v_1) (f3 ?v_0 (f3 (f4 f5 ?v1) ?v_1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f27 f30 ?v0))) (= (f26 (f27 f30 (f26 ?v_0 ?v1)) ?v2) (f26 (f27 f30 (f26 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 (f4 f5 (f3 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f27 f30 ?v0))) (= (f26 (f27 f30 (f26 ?v_0 ?v1)) ?v2) (f26 ?v_0 (f26 (f27 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f27 f30 ?v0))) (= (f26 ?v_0 (f26 (f27 f30 ?v1) ?v2)) (f26 (f27 f30 (f26 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2)) (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f27 f30 ?v0)) (?v_0 (f27 f30 ?v1))) (= (f26 ?v_1 (f26 ?v_0 ?v2)) (f26 ?v_0 (f26 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f4 f5 ?v0)) (?v_0 (f4 f5 ?v1))) (= (f3 ?v_1 (f3 ?v_0 ?v2)) (f3 ?v_0 (f3 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f26 (f27 f30 ?v0) ?v1) (f26 (f27 f30 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f5 ?v0) ?v1) (f3 (f4 f5 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f27 f29 ?v0))) (= (f26 (f27 f29 (f26 ?v_0 ?v1)) (f26 (f27 f29 ?v2) ?v3)) (f26 (f27 f29 (f26 ?v_0 ?v2)) (f26 (f27 f29 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f10 ?v0))) (= (f3 (f4 f10 (f3 ?v_0 ?v1)) (f3 (f4 f10 ?v2) ?v3)) (f3 (f4 f10 (f3 ?v_0 ?v2)) (f3 (f4 f10 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f27 f29 ?v0))) (= (f26 (f27 f29 (f26 ?v_0 ?v1)) ?v2) (f26 (f27 f29 (f26 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f10 ?v0))) (= (f3 (f4 f10 (f3 ?v_0 ?v1)) ?v2) (f3 (f4 f10 (f3 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f27 f29 ?v0))) (= (f26 (f27 f29 (f26 ?v_0 ?v1)) ?v2) (f26 ?v_0 (f26 (f27 f29 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f10 ?v0))) (= (f3 (f4 f10 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f10 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f27 f29 ?v0))) (= (f26 ?v_0 (f26 (f27 f29 ?v1) ?v2)) (f26 (f27 f29 (f26 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f10 ?v0))) (= (f3 ?v_0 (f3 (f4 f10 ?v1) ?v2)) (f3 (f4 f10 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f27 f29 ?v0)) (?v_0 (f27 f29 ?v1))) (= (f26 ?v_1 (f26 ?v_0 ?v2)) (f26 ?v_0 (f26 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f4 f10 ?v0)) (?v_0 (f4 f10 ?v1))) (= (f3 ?v_1 (f3 ?v_0 ?v2)) (f3 ?v_0 (f3 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f26 (f27 f29 ?v0) ?v1) (f26 (f27 f29 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f10 ?v0) ?v1) (f3 (f4 f10 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 f6 ?v0) (f3 f6 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S6)) (let ((?v_0 (f19 f20 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f3 f6 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 f8 ?v0) (f3 f8 ?v1)) (= ?v0 ?v1))))
(assert (= (= f9 f9) true))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 f7 ?v0) (f3 f7 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f5 ?v0) ?v1) (f3 (f4 f5 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 f6 ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f10 ?v0))) (= (f3 (f4 f10 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f10 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f4 f10 ?v0)) (?v_0 (f4 f10 ?v1))) (= (f3 ?v_1 (f3 ?v_0 ?v2)) (f3 ?v_0 (f3 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f10 ?v0) ?v1) (f3 (f4 f10 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S6) (?v2 S6)) (let ((?v_0 (= ?v0 f1))) (= (ite ?v_0 (f12 f13 ?v1) (f12 f13 ?v2)) (f12 f13 (ite ?v_0 ?v1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f12 f13 ?v0) (f12 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f12 f13 ?v0) (f12 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_1 (f19 f20 (f3 f7 (f3 f8 f9)))) (?v_0 (f27 f28 ?v0))) (= (f26 ?v_0 (f26 (f27 f30 ?v_1) ?v1)) (f26 (f27 f28 (f26 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S6)) (let ((?v_1 (f19 f20 (f3 f7 (f3 f8 f9)))) (?v_0 (f16 f17 ?v0))) (= (f12 ?v_0 (f26 (f27 f30 ?v_1) ?v1)) (f12 (f16 f17 (f12 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f27 f30 ?v0)) (?v_1 (f27 f30 ?v2))) (= (= (f26 (f27 f29 (f26 ?v_0 ?v1)) (f26 ?v_1 ?v3)) (f26 (f27 f29 (f26 ?v_0 ?v3)) (f26 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f5 ?v0)) (?v_1 (f4 f5 ?v2))) (= (= (f3 (f4 f10 (f3 ?v_0 ?v1)) (f3 ?v_1 ?v3)) (f3 (f4 f10 (f3 ?v_0 ?v3)) (f3 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f26 (f27 f29 (f26 (f27 f30 ?v0) ?v1)) (f26 (f27 f30 ?v2) ?v1)) (f26 (f27 f30 (f26 (f27 f29 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f10 (f3 (f4 f5 ?v0) ?v1)) (f3 (f4 f5 ?v2) ?v1)) (f3 (f4 f5 (f3 (f4 f10 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f26 (f27 f30 (f26 (f27 f29 ?v0) ?v1)) ?v2) (f26 (f27 f29 (f26 (f27 f30 ?v0) ?v2)) (f26 (f27 f30 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f5 (f3 (f4 f10 ?v0) ?v1)) ?v2) (f3 (f4 f10 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f27 f30 ?v0)) (?v_1 (f27 f30 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f26 (f27 f29 (f26 ?v_0 ?v2)) (f26 ?v_1 ?v3)) (f26 (f27 f29 (f26 ?v_0 ?v3)) (f26 ?v_1 ?v2))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f5 ?v0)) (?v_1 (f4 f5 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f3 (f4 f10 (f3 ?v_0 ?v2)) (f3 ?v_1 ?v3)) (f3 (f4 f10 (f3 ?v_0 ?v3)) (f3 ?v_1 ?v2))))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f27 f30 ?v0))) (= (f26 ?v_0 (f26 (f27 f29 ?v1) ?v2)) (f26 (f27 f29 (f26 ?v_0 ?v1)) (f26 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f3 (f4 f10 ?v1) ?v2)) (f3 (f4 f10 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S6)) (= (f26 (f27 f30 ?v0) f31) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) f11) ?v0)))
(assert (forall ((?v0 S6)) (= (f26 (f27 f30 f31) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f11) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f26 (f27 f28 (f26 (f27 f30 ?v0) ?v1)) ?v2) (f26 (f27 f30 (f26 (f27 f28 ?v0) ?v2)) (f26 (f27 f28 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6)) (= (f12 (f16 f17 (f3 (f4 f5 ?v0) ?v1)) ?v2) (f3 (f4 f5 (f12 (f16 f17 ?v0) ?v2)) (f12 (f16 f17 ?v1) ?v2)))))
(assert (forall ((?v0 S3)) (= (= (f3 f8 ?v0) f9) false)))
(assert (forall ((?v0 S3)) (= (= f9 (f3 f8 ?v0)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 f8 ?v0) (f3 f7 ?v1)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 f7 ?v0) (f3 f8 ?v1)) false)))
(assert (forall ((?v0 S3)) (= (= (f3 f7 ?v0) f9) (= ?v0 f9))))
(assert (forall ((?v0 S3)) (= (= f9 (f3 f7 ?v0)) (= f9 ?v0))))
(assert (= (f3 f7 f9) f9))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f9) ?v0) f9)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f5 (f3 f7 ?v0)) ?v1) (f3 f7 (f3 (f4 f5 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f10 ?v0) f9) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f10 f9) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f10 (f3 f7 ?v0)) (f3 f7 ?v1)) (f3 f7 (f3 (f4 f10 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f3 f7 ?v0) (f3 (f4 f10 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) f11) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f11) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f5 (f3 f6 ?v0)) (f3 f6 ?v1)) (f3 f6 (f3 (f4 f5 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f5 (f3 (f4 f10 ?v0) ?v1)) ?v2) (f3 (f4 f10 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f3 (f4 f10 ?v1) ?v2)) (f3 (f4 f10 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f10 (f3 f6 ?v0)) (f3 f6 ?v1)) (f3 f6 (f3 (f4 f10 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (let ((?v_0 (f19 f20 ?v2))) (= (f26 (f27 f30 (f26 (f27 f29 ?v0) ?v1)) ?v_0) (f26 (f27 f29 (f26 (f27 f30 ?v0) ?v_0)) (f26 (f27 f30 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f3 f6 ?v2))) (= (f3 (f4 f5 (f3 (f4 f10 ?v0) ?v1)) ?v_0) (f3 (f4 f10 (f3 (f4 f5 ?v0) ?v_0)) (f3 (f4 f5 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (let ((?v_0 (f27 f30 (f19 f20 ?v0)))) (= (f26 ?v_0 (f26 (f27 f29 ?v1) ?v2)) (f26 (f27 f29 (f26 ?v_0 ?v1)) (f26 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 (f3 f6 ?v0)))) (= (f3 ?v_0 (f3 (f4 f10 ?v1) ?v2)) (f3 (f4 f10 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f26 (f27 f29 (f26 (f27 f30 ?v0) ?v1)) ?v1) (f26 (f27 f30 (f26 (f27 f29 ?v0) f31)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f10 (f3 (f4 f5 ?v0) ?v1)) ?v1) (f3 (f4 f5 (f3 (f4 f10 ?v0) f11)) ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f26 (f27 f29 ?v0) (f26 (f27 f30 ?v1) ?v0)) (f26 (f27 f30 (f26 (f27 f29 ?v1) f31)) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f10 ?v0) (f3 (f4 f5 ?v1) ?v0)) (f3 (f4 f5 (f3 (f4 f10 ?v1) f11)) ?v0))))
(assert (forall ((?v0 S6)) (= (f26 (f27 f29 ?v0) ?v0) (f26 (f27 f30 (f26 (f27 f29 f31) f31)) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f10 ?v0) ?v0) (f3 (f4 f5 (f3 (f4 f10 f11) f11)) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f10 (f3 f6 f9)) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f10 ?v0) (f3 f6 f9)) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f5 (f3 f6 ?v0)) (f3 (f4 f5 (f3 f6 ?v1)) ?v2)) (f3 (f4 f5 (f3 f6 (f3 (f4 f5 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f5 (f3 f6 ?v0)) (f3 f6 ?v1)) (f3 f6 (f3 (f4 f5 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 f6 (f3 (f4 f5 ?v0) ?v1)) (f3 (f4 f5 (f3 f6 ?v0)) (f3 f6 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f3 (f4 f10 (f3 f6 ?v0)) (f3 (f4 f10 (f3 f6 ?v1)) ?v2)) (f3 (f4 f10 (f3 f6 (f3 (f4 f10 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f10 (f3 f6 ?v0)) (f3 f6 ?v1)) (f3 f6 (f3 (f4 f10 ?v0) ?v1)))))
(check-sat)
(exit)