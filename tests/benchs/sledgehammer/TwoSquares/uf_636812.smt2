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
(declare-fun f4 (S3 S4) S2)
(declare-fun f5 (S5 S2) S3)
(declare-fun f6 () S5)
(declare-fun f7 () S2)
(declare-fun f8 (S6 S2) S4)
(declare-fun f9 () S6)
(declare-fun f10 (S7 S2) S2)
(declare-fun f11 () S7)
(declare-fun f12 () S7)
(declare-fun f13 () S2)
(declare-fun f14 () S2)
(declare-fun f15 (S8 S2) S7)
(declare-fun f16 () S8)
(declare-fun f17 () S8)
(declare-fun f18 () S7)
(declare-fun f19 () S2)
(declare-fun f20 () S2)
(declare-fun f21 (S2 S2) S1)
(declare-fun f22 () S2)
(declare-fun f23 (S2 S2) S1)
(declare-fun f24 (S2) S1)
(declare-fun f25 () S2)
(declare-fun f26 (S9 S4) S4)
(declare-fun f27 (S10 S4) S9)
(declare-fun f28 () S10)
(declare-fun f29 () S10)
(declare-fun f30 () S10)
(declare-fun f31 () S4)
(declare-fun f32 () S8)
(assert (not (= f1 f2)))
(assert (let ((?v_1 (f10 f11 (f10 f12 f13)))) (let ((?v_0 (f8 f9 ?v_1))) (not (= (f3 (f4 (f5 f6 f7) ?v_0) (f4 (f5 f6 f14) ?v_0) (f10 (f15 f16 (f10 (f15 f17 (f10 f18 (f10 f11 ?v_1))) f19)) f20)) f1)))))
(assert (let ((?v_0 (f10 (f15 f16 (f10 (f15 f17 (f10 f18 (f10 f11 (f10 f11 (f10 f12 f13))))) f19)) f20))) (and (= (f21 f22 f7) f1) (and (= (f23 f7 ?v_0) f1) (= (f3 f14 f7 ?v_0) f1)))))
(assert (let ((?v_0 (f10 (f15 f16 (f10 (f15 f17 (f10 f18 (f10 f11 (f10 f11 (f10 f12 f13))))) f19)) f20))) (and (= (f21 f22 f7) f1) (and (= (f23 f7 ?v_0) f1) (= (f3 f14 f7 ?v_0) f1)))))
(assert (= (f24 (f10 (f15 f16 (f10 (f15 f17 (f10 f18 (f10 f11 (f10 f11 (f10 f12 f13))))) f19)) f20)) f1))
(assert (= (f23 f22 (f10 (f15 f16 (f10 (f15 f17 (f10 f18 (f10 f11 (f10 f11 (f10 f12 f13))))) f19)) f20)) f1))
(assert (let ((?v_0 (f10 f11 (f10 f12 f13)))) (= (f3 (f4 (f5 f6 f14) (f8 f9 ?v_0)) (f10 f18 f25) (f10 (f15 f16 (f10 (f15 f17 (f10 f18 (f10 f11 ?v_0))) f19)) f20)) f1)))
(assert (exists ((?v0 S2)) (let ((?v_0 (f10 (f15 f16 (f10 (f15 f17 (f10 f18 (f10 f11 (f10 f11 (f10 f12 f13))))) f19)) f20))) (and (and (= (f21 f22 ?v0) f1) (and (= (f23 ?v0 ?v_0) f1) (= (f3 f14 ?v0 ?v_0) f1))) (forall ((?v1 S2)) (=> (and (= (f21 f22 ?v1) f1) (and (= (f23 ?v1 ?v_0) f1) (= (f3 f14 ?v1 ?v_0) f1))) (= ?v1 ?v0)))))))
(assert (=> (forall ((?v0 S2)) (let ((?v_0 (f10 (f15 f16 (f10 (f15 f17 (f10 f18 (f10 f11 (f10 f11 (f10 f12 f13))))) f19)) f20))) (=> (and (= (f21 f22 ?v0) f1) (and (= (f23 ?v0 ?v_0) f1) (= (f3 f14 ?v0 ?v_0) f1))) false))) false))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f10 f11 (f10 f12 f13)))) (let ((?v_0 (f8 f9 ?v_1))) (= (f4 (f5 f6 (f10 (f15 f16 ?v0) ?v1)) ?v_0) (f10 (f15 f16 (f10 (f15 f16 (f4 (f5 f6 ?v0) ?v_0)) (f10 (f15 f17 (f10 (f15 f17 (f10 f18 ?v_1)) ?v0)) ?v1))) (f4 (f5 f6 ?v1) ?v_0)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_3 (f10 f12 f13))) (let ((?v_5 (f8 f9 (f10 f11 ?v_3))) (?v_1 (f10 f12 ?v_3))) (let ((?v_0 (f8 f9 ?v_1)) (?v_2 (f5 f6 ?v0)) (?v_4 (f15 f17 (f10 f18 ?v_1))) (?v_6 (f5 f6 ?v1))) (= (f4 (f5 f6 (f10 (f15 f16 ?v0) ?v1)) ?v_0) (f10 (f15 f16 (f10 (f15 f16 (f10 (f15 f16 (f4 ?v_2 ?v_0)) (f10 (f15 f17 (f10 ?v_4 (f4 ?v_2 ?v_5))) ?v1))) (f10 (f15 f17 (f10 ?v_4 ?v0)) (f4 ?v_6 ?v_5)))) (f4 ?v_6 ?v_0))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f10 f11 (f10 f12 f13)))) (let ((?v_0 (f8 f9 ?v_1))) (= (f4 (f5 f6 (f10 (f15 f16 ?v0) ?v1)) ?v_0) (f10 (f15 f16 (f10 (f15 f16 (f4 (f5 f6 ?v0) ?v_0)) (f4 (f5 f6 ?v1) ?v_0))) (f10 (f15 f17 (f10 (f15 f17 (f10 f18 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_0 (f8 f9 (f10 f11 (f10 f12 f13))))) (= (f26 (f27 f28 (f26 (f27 f29 ?v0) ?v1)) ?v_0) (f26 (f27 f29 (f26 (f27 f29 (f26 (f27 f28 ?v0) ?v_0)) (f26 (f27 f28 ?v1) ?v_0))) (f26 (f27 f30 (f26 (f27 f30 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f10 f18 ?v0))) (= (f4 (f5 f6 ?v_0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f10 (f15 f17 ?v_0) ?v_0)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f26 (f27 f28 ?v_0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f26 (f27 f30 ?v_0) ?v_0)))))
(assert (forall ((?v0 S2)) (let ((?v_1 (f10 f12 f13)) (?v_0 (f5 f6 ?v0))) (= (f10 (f15 f17 ?v0) (f4 ?v_0 (f8 f9 (f10 f11 ?v_1)))) (f4 ?v_0 (f8 f9 (f10 f12 ?v_1)))))))
(assert (= (f4 (f5 f6 f20) (f8 f9 (f10 f11 (f10 f12 f13)))) f20))
(assert (= (f26 (f27 f28 f31) (f8 f9 (f10 f11 (f10 f12 f13)))) f31))
(assert (forall ((?v0 S2)) (= (f10 (f15 f17 ?v0) ?v0) (f4 (f5 f6 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))))))
(assert (forall ((?v0 S4)) (= (f26 (f27 f30 ?v0) ?v0) (f26 (f27 f28 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f10 (f15 f17 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f26 (f27 f28 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f26 (f27 f30 ?v0) ?v0))))
(assert (forall ((?v0 S2) (?v1 S4)) (let ((?v_0 (f5 f6 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 (f26 (f27 f30 (f8 f9 (f10 f11 (f10 f12 f13)))) ?v1)) (f10 (f15 f17 ?v_1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S4)) (let ((?v_0 (f27 f28 ?v0))) (let ((?v_1 (f26 ?v_0 ?v1))) (= (f26 ?v_0 (f26 (f27 f30 (f8 f9 (f10 f11 (f10 f12 f13)))) ?v1)) (f26 (f27 f30 ?v_1) ?v_1))))))
(assert (forall ((?v0 S2)) (= (f10 (f15 f16 f20) (f10 f18 ?v0)) (f10 f18 (f10 (f15 f16 (f10 f12 f13)) ?v0)))))
(assert (=> (forall ((?v0 S2)) (let ((?v_0 (f10 f11 (f10 f12 f13)))) (=> (= (f3 (f4 (f5 f6 ?v0) (f8 f9 ?v_0)) (f10 f18 f25) (f10 (f15 f16 (f10 (f15 f17 (f10 f18 (f10 f11 ?v_0))) f19)) f20)) f1) false))) false))
(assert (= (f10 (f15 f32 (f10 f18 f25)) (f10 (f15 f16 (f10 (f15 f17 (f10 f18 (f10 f11 (f10 f11 (f10 f12 f13))))) f19)) f20)) f20))
(assert (forall ((?v0 S2)) (= (f21 ?v0 ?v0) f1)))
(assert (= (= f25 f25) true))
(assert (= (= (f23 f25 f25) f1) false))
(assert (= (= (f23 f25 f22) f1) true))
(assert (= (= (f21 f25 f25) f1) true))
(assert (forall ((?v0 S2)) (= (= (f21 f25 (f10 f11 ?v0)) f1) (= (f23 f25 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f21 ?v0 ?v1) f1) (= (f21 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f23 ?v0 ?v1) f1) (and (= (f21 ?v0 ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f23 ?v0 ?v1) f1) (or (= ?v0 ?v1) (= (f23 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (= (f23 (f10 f11 ?v0) f25) f1) (= (f21 ?v0 f25) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f21 ?v0 ?v1) f1) (=> (= (f21 ?v1 ?v2) f1) (= (f21 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f21 ?v0 ?v1) f1) (=> (= (f21 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2)) (= (= (f23 (f10 f12 ?v0) f25) f1) (= (f23 ?v0 f25) f1))))
(assert (forall ((?v0 S2)) (= (= (f23 f25 (f10 f12 ?v0)) f1) (= (f23 f25 ?v0) f1))))
(check-sat)
(exit)
