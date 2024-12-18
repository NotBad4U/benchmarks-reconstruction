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
(declare-fun f3 () S1)
(declare-fun f4 (S2 S2 S2) S1)
(declare-fun f5 (S3 S4) S2)
(declare-fun f6 (S5 S2) S3)
(declare-fun f7 () S5)
(declare-fun f8 (S6 S2) S4)
(declare-fun f9 () S6)
(declare-fun f10 (S7 S2) S2)
(declare-fun f11 () S7)
(declare-fun f12 () S7)
(declare-fun f13 () S2)
(declare-fun f14 () S7)
(declare-fun f15 () S2)
(declare-fun f16 (S8 S2) S7)
(declare-fun f17 () S8)
(declare-fun f18 () S8)
(declare-fun f19 () S2)
(declare-fun f20 () S2)
(declare-fun f21 (S2 S2) S1)
(declare-fun f22 (S2) S1)
(declare-fun f23 () S8)
(declare-fun f24 (S9 S4) S4)
(declare-fun f25 (S10 S4) S9)
(declare-fun f26 () S10)
(declare-fun f27 () S10)
(declare-fun f28 () S10)
(declare-fun f29 () S4)
(assert (not (= f1 f2)))
(assert (not (= f3 f1)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f10 f11 (f10 f12 f13)))) (=> (= (f4 (f5 (f6 f7 ?v0) (f8 f9 ?v_0)) (f10 f14 f15) (f10 (f16 f17 (f10 (f16 f18 (f10 f14 (f10 f11 ?v_0))) f19)) f20)) f1) (= f3 f1)))))
(assert (= (f21 (f10 (f16 f17 (f10 (f16 f18 (f10 f14 (f10 f11 (f10 f11 (f10 f12 f13))))) f19)) f20) (f10 f14 f15)) f1))
(assert (= (f21 (f10 (f16 f17 (f10 (f16 f18 (f10 f14 (f10 f11 (f10 f11 (f10 f12 f13))))) f19)) f20) (f10 f14 f15)) f1))
(assert (= (f22 (f10 (f16 f17 (f10 (f16 f18 (f10 f14 (f10 f11 (f10 f11 (f10 f12 f13))))) f19)) f20)) f1))
(assert (= (f10 (f16 f23 (f10 f14 f15)) (f10 (f16 f17 (f10 (f16 f18 (f10 f14 (f10 f11 (f10 f11 (f10 f12 f13))))) f19)) f20)) f20))
(assert (let ((?v_0 (f10 f14 f15)) (?v_1 (f10 (f16 f17 (f10 (f16 f18 (f10 f14 (f10 f11 (f10 f11 (f10 f12 f13))))) f19)) f20))) (=> (not (= (f21 ?v_1 ?v_0) f1)) (not (= (f10 (f16 f23 ?v_0) ?v_1) f20)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f10 f11 (f10 f12 f13)))) (let ((?v_0 (f8 f9 ?v_1))) (= (f5 (f6 f7 (f10 (f16 f17 ?v0) ?v1)) ?v_0) (f10 (f16 f17 (f10 (f16 f17 (f5 (f6 f7 ?v0) ?v_0)) (f10 (f16 f18 (f10 (f16 f18 (f10 f14 ?v_1)) ?v0)) ?v1))) (f5 (f6 f7 ?v1) ?v_0)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_3 (f10 f12 f13))) (let ((?v_5 (f8 f9 (f10 f11 ?v_3))) (?v_1 (f10 f12 ?v_3))) (let ((?v_0 (f8 f9 ?v_1)) (?v_2 (f6 f7 ?v0)) (?v_4 (f16 f18 (f10 f14 ?v_1))) (?v_6 (f6 f7 ?v1))) (= (f5 (f6 f7 (f10 (f16 f17 ?v0) ?v1)) ?v_0) (f10 (f16 f17 (f10 (f16 f17 (f10 (f16 f17 (f5 ?v_2 ?v_0)) (f10 (f16 f18 (f10 ?v_4 (f5 ?v_2 ?v_5))) ?v1))) (f10 (f16 f18 (f10 ?v_4 ?v0)) (f5 ?v_6 ?v_5)))) (f5 ?v_6 ?v_0))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f10 f11 (f10 f12 f13)))) (let ((?v_0 (f8 f9 ?v_1))) (= (f5 (f6 f7 (f10 (f16 f17 ?v0) ?v1)) ?v_0) (f10 (f16 f17 (f10 (f16 f17 (f5 (f6 f7 ?v0) ?v_0)) (f5 (f6 f7 ?v1) ?v_0))) (f10 (f16 f18 (f10 (f16 f18 (f10 f14 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_0 (f8 f9 (f10 f11 (f10 f12 f13))))) (= (f24 (f25 f26 (f24 (f25 f27 ?v0) ?v1)) ?v_0) (f24 (f25 f27 (f24 (f25 f27 (f24 (f25 f26 ?v0) ?v_0)) (f24 (f25 f26 ?v1) ?v_0))) (f24 (f25 f28 (f24 (f25 f28 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f24 (f25 f26 ?v_0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f24 (f25 f28 ?v_0) ?v_0)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f10 f14 ?v0))) (= (f5 (f6 f7 ?v_0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f10 (f16 f18 ?v_0) ?v_0)))))
(assert (forall ((?v0 S2)) (let ((?v_1 (f10 f12 f13)) (?v_0 (f6 f7 ?v0))) (= (f10 (f16 f18 ?v0) (f5 ?v_0 (f8 f9 (f10 f11 ?v_1)))) (f5 ?v_0 (f8 f9 (f10 f12 ?v_1)))))))
(assert (= (f5 (f6 f7 f20) (f8 f9 (f10 f11 (f10 f12 f13)))) f20))
(assert (= (f24 (f25 f26 f29) (f8 f9 (f10 f11 (f10 f12 f13)))) f29))
(assert (forall ((?v0 S4)) (= (f24 (f25 f28 ?v0) ?v0) (f24 (f25 f26 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))))))
(assert (forall ((?v0 S2)) (= (f10 (f16 f18 ?v0) ?v0) (f5 (f6 f7 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))))))
(assert (forall ((?v0 S4)) (= (f24 (f25 f26 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f24 (f25 f28 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f10 (f16 f18 ?v0) ?v0))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_0 (f25 f26 ?v0))) (let ((?v_1 (f24 ?v_0 ?v1))) (= (f24 ?v_0 (f24 (f25 f28 (f8 f9 (f10 f11 (f10 f12 f13)))) ?v1)) (f24 (f25 f28 ?v_1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S4)) (let ((?v_0 (f6 f7 ?v0))) (let ((?v_1 (f5 ?v_0 ?v1))) (= (f5 ?v_0 (f24 (f25 f28 (f8 f9 (f10 f11 (f10 f12 f13)))) ?v1)) (f10 (f16 f18 ?v_1) ?v_1))))))
(assert (forall ((?v0 S2)) (= (f10 (f16 f17 f20) (f10 f14 ?v0)) (f10 f14 (f10 (f16 f17 (f10 f12 f13)) ?v0)))))
(assert (forall ((?v0 S2)) (= (f10 (f16 f17 (f10 f14 ?v0)) f20) (f10 f14 (f10 (f16 f17 ?v0) (f10 f12 f13))))))
(assert (= (f10 (f16 f17 f20) f20) (f10 f14 (f10 f11 (f10 f12 f13)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f25 f26 ?v0))) (= (f24 (f25 f26 (f24 ?v_0 ?v1)) ?v2) (f24 ?v_0 (f24 (f25 f28 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f24 (f25 f28 ?v1) ?v2))))))
(assert (forall ((?v0 S4)) (= (f24 (f25 f26 ?v0) f29) ?v0)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 ?v0) f29) ?v0)))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f24 (f25 f28 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f25 f26 ?v0))) (= (f24 (f25 f28 (f24 ?v_0 ?v1)) (f24 ?v_0 ?v2)) (f24 ?v_0 (f24 (f25 f27 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f10 (f16 f18 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2)) (f5 ?v_0 (f24 (f25 f27 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 ?v_0 (f24 (f25 f27 ?v1) ?v2)) (f10 (f16 f18 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S4)) (= (f24 (f25 f28 (f8 f9 (f10 f11 (f10 f12 f13)))) ?v0) (f24 (f25 f27 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f24 (f25 f28 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f24 (f25 f27 ?v0) ?v0))))
(assert (= (f24 (f25 f27 f29) f29) (f8 f9 (f10 f11 (f10 f12 f13)))))
(assert (= (f8 f9 (f10 f12 f13)) f29))
(assert (= f29 (f8 f9 (f10 f12 f13))))
(assert (= (f22 (f10 f14 (f10 f11 (f10 f12 f13)))) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f16 f18 ?v0))) (= (f10 (f16 f18 (f10 ?v_0 ?v1)) (f10 (f16 f18 ?v2) ?v3)) (f10 (f16 f18 (f10 ?v_0 ?v2)) (f10 (f16 f18 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f25 f28 ?v0))) (= (f24 (f25 f28 (f24 ?v_0 ?v1)) (f24 (f25 f28 ?v2) ?v3)) (f24 (f25 f28 (f24 ?v_0 ?v2)) (f24 (f25 f28 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_1 (f16 f18 (f10 (f16 f18 ?v0) ?v1))) (?v_0 (f16 f18 ?v2))) (= (f10 ?v_1 (f10 ?v_0 ?v3)) (f10 ?v_0 (f10 ?v_1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_1 (f25 f28 (f24 (f25 f28 ?v0) ?v1))) (?v_0 (f25 f28 ?v2))) (= (f24 ?v_1 (f24 ?v_0 ?v3)) (f24 ?v_0 (f24 ?v_1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f16 f18 ?v0)) (?v_1 (f10 (f16 f18 ?v2) ?v3))) (= (f10 (f16 f18 (f10 ?v_0 ?v1)) ?v_1) (f10 ?v_0 (f10 (f16 f18 ?v1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f25 f28 ?v0)) (?v_1 (f24 (f25 f28 ?v2) ?v3))) (= (f24 (f25 f28 (f24 ?v_0 ?v1)) ?v_1) (f24 ?v_0 (f24 (f25 f28 ?v1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f18 ?v0))) (= (f10 (f16 f18 (f10 ?v_0 ?v1)) ?v2) (f10 (f16 f18 (f10 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f25 f28 ?v0))) (= (f24 (f25 f28 (f24 ?v_0 ?v1)) ?v2) (f24 (f25 f28 (f24 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 f18 ?v0))) (= (f10 (f16 f18 (f10 ?v_0 ?v1)) ?v2) (f10 ?v_0 (f10 (f16 f18 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f25 f28 ?v0))) (= (f24 (f25 f28 (f24 ?v_0 ?v1)) ?v2) (f24 ?v_0 (f24 (f25 f28 ?v1) ?v2))))))
(check-sat)
(exit)
