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
(declare-fun f3 (S2 S2 S2) S1)
(declare-fun f4 (S3 S2) S2)
(declare-fun f5 (S4 S2) S3)
(declare-fun f6 () S4)
(declare-fun f7 () S3)
(declare-fun f8 () S2)
(declare-fun f9 () S4)
(declare-fun f10 () S4)
(declare-fun f11 () S3)
(declare-fun f12 () S3)
(declare-fun f13 () S2)
(declare-fun f14 () S2)
(declare-fun f15 () S2)
(declare-fun f16 (S5 S6) S2)
(declare-fun f17 (S7 S2) S5)
(declare-fun f18 () S7)
(declare-fun f19 (S8 S6) S6)
(declare-fun f20 (S9 S6) S8)
(declare-fun f21 () S9)
(declare-fun f22 (S10 S2) S6)
(declare-fun f23 () S10)
(declare-fun f24 () S10)
(declare-fun f25 () S4)
(declare-fun f26 () S4)
(declare-fun f27 (S2) S1)
(declare-fun f28 () S9)
(declare-fun f29 () S9)
(declare-fun f30 (S2 S2) S1)
(declare-fun f31 () S6)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f4 f7 f8)) (?v_1 (f4 f11 (f4 f12 f13)))) (let ((?v_2 (f4 (f5 f9 (f4 (f5 f10 (f4 f7 (f4 f11 ?v_1))) f14)) f15))) (not (= (f3 (f4 (f5 f6 ?v_0) ?v_2) (f16 (f17 f18 ?v_0) (f19 (f20 f21 (f22 f23 ?v_1)) (f22 f24 f14))) ?v_2) f1)))))
(assert (let ((?v_0 (f4 f7 f8)) (?v_2 (f4 f11 (f4 f12 f13)))) (let ((?v_1 (f4 (f5 f9 (f4 (f5 f10 (f4 f7 (f4 f11 ?v_2))) f14)) f15))) (= (f3 (f4 (f5 f6 ?v_0) ?v_1) (f16 (f17 f18 ?v_0) (f22 f24 (f4 (f5 f25 (f4 (f5 f26 ?v_1) f15)) (f4 f7 ?v_2)))) ?v_1) f1))))
(assert (let ((?v_0 (f4 f7 f8)) (?v_2 (f4 f11 (f4 f12 f13)))) (let ((?v_1 (f4 (f5 f9 (f4 (f5 f10 (f4 f7 (f4 f11 ?v_2))) f14)) f15))) (= (f3 (f4 (f5 f6 ?v_0) ?v_1) (f16 (f17 f18 ?v_0) (f22 f24 (f4 (f5 f25 (f4 (f5 f26 ?v_1) f15)) (f4 f7 ?v_2)))) ?v_1) f1))))
(assert (= (f27 (f4 (f5 f9 (f4 (f5 f10 (f4 f7 (f4 f11 (f4 f11 (f4 f12 f13))))) f14)) f15)) f1))
(assert (forall ((?v0 S6)) (= (f16 (f17 f18 (f4 f7 f8)) (f19 (f20 f21 (f22 f23 (f4 f11 (f4 f12 f13)))) ?v0)) f15)))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f4 f11 (f4 f12 f13)))) (let ((?v_0 (f22 f23 ?v_1))) (= (f16 (f17 f18 (f4 (f5 f9 ?v0) ?v1)) ?v_0) (f4 (f5 f9 (f4 (f5 f9 (f16 (f17 f18 ?v0) ?v_0)) (f4 (f5 f10 (f4 (f5 f10 (f4 f7 ?v_1)) ?v0)) ?v1))) (f16 (f17 f18 ?v1) ?v_0)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_3 (f4 f12 f13))) (let ((?v_5 (f22 f23 (f4 f11 ?v_3))) (?v_1 (f4 f12 ?v_3))) (let ((?v_0 (f22 f23 ?v_1)) (?v_2 (f17 f18 ?v0)) (?v_4 (f5 f10 (f4 f7 ?v_1))) (?v_6 (f17 f18 ?v1))) (= (f16 (f17 f18 (f4 (f5 f9 ?v0) ?v1)) ?v_0) (f4 (f5 f9 (f4 (f5 f9 (f4 (f5 f9 (f16 ?v_2 ?v_0)) (f4 (f5 f10 (f4 ?v_4 (f16 ?v_2 ?v_5))) ?v1))) (f4 (f5 f10 (f4 ?v_4 ?v0)) (f16 ?v_6 ?v_5)))) (f16 ?v_6 ?v_0))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f4 f11 (f4 f12 f13)))) (let ((?v_0 (f22 f23 ?v_1))) (= (f16 (f17 f18 (f4 (f5 f9 ?v0) ?v1)) ?v_0) (f4 (f5 f9 (f4 (f5 f9 (f16 (f17 f18 ?v0) ?v_0)) (f16 (f17 f18 ?v1) ?v_0))) (f4 (f5 f10 (f4 (f5 f10 (f4 f7 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f22 f23 (f4 f11 (f4 f12 f13))))) (= (f19 (f20 f28 (f19 (f20 f29 ?v0) ?v1)) ?v_0) (f19 (f20 f29 (f19 (f20 f29 (f19 (f20 f28 ?v0) ?v_0)) (f19 (f20 f28 ?v1) ?v_0))) (f19 (f20 f21 (f19 (f20 f21 ?v_0) ?v0)) ?v1))))))
(assert (let ((?v_0 (f4 f11 (f4 f12 f13)))) (= (f30 (f4 f7 ?v_0) (f4 (f5 f9 (f4 (f5 f10 (f4 f7 (f4 f11 ?v_0))) f14)) f15)) f1)))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f20 f28 ?v0))) (let ((?v_1 (f19 ?v_0 ?v1))) (= (f19 ?v_0 (f19 (f20 f21 (f22 f23 (f4 f11 (f4 f12 f13)))) ?v1)) (f19 (f20 f21 ?v_1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S6)) (let ((?v_0 (f17 f18 ?v0))) (let ((?v_1 (f16 ?v_0 ?v1))) (= (f16 ?v_0 (f19 (f20 f21 (f22 f23 (f4 f11 (f4 f12 f13)))) ?v1)) (f4 (f5 f10 ?v_1) ?v_1))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f22 f23 ?v0))) (= (f19 (f20 f28 ?v_0) (f22 f23 (f4 f11 (f4 f12 f13)))) (f19 (f20 f21 ?v_0) ?v_0)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f4 f7 ?v0))) (= (f16 (f17 f18 ?v_0) (f22 f23 (f4 f11 (f4 f12 f13)))) (f4 (f5 f10 ?v_0) ?v_0)))))
(assert (forall ((?v0 S2)) (let ((?v_1 (f4 f12 f13)) (?v_0 (f17 f18 ?v0))) (= (f4 (f5 f10 ?v0) (f16 ?v_0 (f22 f23 (f4 f11 ?v_1)))) (f16 ?v_0 (f22 f23 (f4 f12 ?v_1)))))))
(assert (let ((?v_0 (f4 f11 (f4 f12 f13)))) (= (f22 f23 ?v_0) (f22 f24 (f4 f7 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_1 (f22 f23 (f4 f11 (f4 f12 f13)))) (?v_0 (f20 f28 ?v0))) (= (f19 ?v_0 (f19 (f20 f21 ?v_1) ?v1)) (f19 (f20 f28 (f19 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S6)) (let ((?v_1 (f22 f23 (f4 f11 (f4 f12 f13)))) (?v_0 (f17 f18 ?v0))) (= (f16 ?v_0 (f19 (f20 f21 ?v_1) ?v1)) (f16 (f17 f18 (f16 ?v_0 ?v1)) ?v_1)))))
(assert (= (f16 (f17 f18 f15) (f22 f23 (f4 f11 (f4 f12 f13)))) f15))
(assert (= (f19 (f20 f28 f31) (f22 f23 (f4 f11 (f4 f12 f13)))) f31))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 ?v0) ?v0) (f19 (f20 f28 ?v0) (f22 f23 (f4 f11 (f4 f12 f13)))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f10 ?v0) ?v0) (f16 (f17 f18 ?v0) (f22 f23 (f4 f11 (f4 f12 f13)))))))
(assert (forall ((?v0 S6)) (= (f19 (f20 f28 ?v0) f31) ?v0)))
(assert (forall ((?v0 S2)) (= (f16 (f17 f18 ?v0) f31) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f22 f23 ?v0)) (?v_0 (f22 f23 ?v1))) (= (f19 (f20 f29 ?v_1) ?v_0) (ite (= (f30 ?v0 f13) f1) ?v_0 (ite (= (f30 ?v1 f13) f1) ?v_1 (f22 f23 (f4 (f5 f9 ?v0) ?v1))))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f28 ?v0))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) (f19 ?v_0 ?v2)) (f19 ?v_0 (f19 (f20 f29 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (= (f4 (f5 f10 (f16 ?v_0 ?v1)) (f16 ?v_0 ?v2)) (f16 ?v_0 (f19 (f20 f29 ?v1) ?v2))))))
(assert (= f31 (f22 f24 f15)))
(assert (= (f19 (f20 f29 f31) f31) (f22 f23 (f4 f11 (f4 f12 f13)))))
(assert (= (f22 f23 (f4 f12 f13)) f31))
(assert (= f31 (f22 f23 (f4 f12 f13))))
(assert (= (f27 (f4 f7 (f4 f11 (f4 f12 f13)))) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f5 f10 ?v0))) (= (f4 (f5 f10 (f4 ?v_0 ?v1)) (f4 (f5 f10 ?v2) ?v3)) (f4 (f5 f10 (f4 ?v_0 ?v2)) (f4 (f5 f10 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) (f19 (f20 f21 ?v2) ?v3)) (f19 (f20 f21 (f19 ?v_0 ?v2)) (f19 (f20 f21 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_1 (f5 f10 (f4 (f5 f10 ?v0) ?v1))) (?v_0 (f5 f10 ?v2))) (= (f4 ?v_1 (f4 ?v_0 ?v3)) (f4 ?v_0 (f4 ?v_1 ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_1 (f20 f21 (f19 (f20 f21 ?v0) ?v1))) (?v_0 (f20 f21 ?v2))) (= (f19 ?v_1 (f19 ?v_0 ?v3)) (f19 ?v_0 (f19 ?v_1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f5 f10 ?v0)) (?v_1 (f4 (f5 f10 ?v2) ?v3))) (= (f4 (f5 f10 (f4 ?v_0 ?v1)) ?v_1) (f4 ?v_0 (f4 (f5 f10 ?v1) ?v_1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f20 f21 ?v0)) (?v_1 (f19 (f20 f21 ?v2) ?v3))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v_1) (f19 ?v_0 (f19 (f20 f21 ?v1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f10 ?v0))) (= (f4 (f5 f10 (f4 ?v_0 ?v1)) ?v2) (f4 (f5 f10 (f4 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v2) (f19 (f20 f21 (f19 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f10 ?v0))) (= (f4 (f5 f10 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f10 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f20 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f10 ?v0))) (= (f4 ?v_0 (f4 (f5 f10 ?v1) ?v2)) (f4 (f5 f10 (f4 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 ?v_0 (f19 (f20 f21 ?v1) ?v2)) (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f5 f10 ?v0)) (?v_0 (f5 f10 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f20 f21 ?v0)) (?v_0 (f20 f21 ?v1))) (= (f19 ?v_1 (f19 ?v_0 ?v2)) (f19 ?v_0 (f19 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f10 ?v0) ?v1) (f4 (f5 f10 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f19 (f20 f21 ?v0) ?v1) (f19 (f20 f21 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f5 f9 ?v0))) (= (f4 (f5 f9 (f4 ?v_0 ?v1)) (f4 (f5 f9 ?v2) ?v3)) (f4 (f5 f9 (f4 ?v_0 ?v2)) (f4 (f5 f9 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f20 f29 ?v0))) (= (f19 (f20 f29 (f19 ?v_0 ?v1)) (f19 (f20 f29 ?v2) ?v3)) (f19 (f20 f29 (f19 ?v_0 ?v2)) (f19 (f20 f29 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f9 ?v0))) (= (f4 (f5 f9 (f4 ?v_0 ?v1)) ?v2) (f4 (f5 f9 (f4 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f29 ?v0))) (= (f19 (f20 f29 (f19 ?v_0 ?v1)) ?v2) (f19 (f20 f29 (f19 ?v_0 ?v2)) ?v1)))))
(check-sat)
(exit)