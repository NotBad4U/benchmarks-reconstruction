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
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 () S2)
(declare-fun f5 (S3 S2) S2)
(declare-fun f6 (S4 S2) S3)
(declare-fun f7 () S4)
(declare-fun f8 () S4)
(declare-fun f9 () S3)
(declare-fun f10 () S4)
(declare-fun f11 () S2)
(declare-fun f12 () S2)
(declare-fun f13 (S5 S6) S2)
(declare-fun f14 () S5)
(declare-fun f15 (S7 S6) S6)
(declare-fun f16 () S7)
(declare-fun f17 () S7)
(declare-fun f18 () S6)
(declare-fun f19 () S4)
(declare-fun f20 (S8 S9) S2)
(declare-fun f21 () S8)
(declare-fun f22 (S2 S2) S9)
(declare-fun f23 () S2)
(declare-fun f24 (S10 S6) S7)
(declare-fun f25 () S10)
(declare-fun f26 () S7)
(declare-fun f27 () S10)
(declare-fun f28 () S9)
(declare-fun f29 () S2)
(declare-fun f30 () S10)
(declare-fun f31 () S6)
(declare-fun f32 (S6 S6) S1)
(assert (not (= f1 f2)))
(assert (not (= (f3 f4 (f5 (f6 f7 (f5 (f6 f8 (f5 f9 (f5 (f6 f8 (f5 (f6 f10 f11) f11)) (f5 (f6 f10 f12) f12)))) f11)) (f13 f14 (f15 f16 (f15 f17 f18))))) f1)))
(assert (= (f3 f4 (f5 (f6 f19 (f20 f21 (f22 f11 f12))) f11)) f1))
(assert (= (f3 f4 (f5 (f6 f8 (f20 f21 (f22 f11 f12))) f11)) f1))
(assert (not (= f23 f4)))
(assert (= (f3 f4 (f5 (f6 f8 (f20 f21 (f22 f11 f12))) f11)) f1))
(assert (= (f3 f4 (f5 (f6 f19 (f20 f21 (f22 f11 f12))) f11)) f1))
(assert (= (f3 f4 (f5 f9 (f13 f14 (f15 f16 (f15 f17 f18))))) f1))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 (f6 f7 ?v0) (f13 f14 (f15 f16 (f15 f17 f18)))))) (= (f5 (f6 f8 ?v_0) ?v_0) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f6 f7 ?v1)) (?v_0 (f6 f10 (f13 f14 (f15 f16 (f15 f17 f18)))))) (= (= ?v0 (f5 ?v_1 (f5 ?v_0 ?v2))) (= (f5 ?v_0 ?v0) (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S6)) (= (f15 (f24 f25 ?v0) (f15 f26 (f15 f16 (f15 f17 f18)))) (f15 (f24 f27 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f10 ?v0) (f13 f14 (f15 f16 (f15 f17 f18)))) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f15 (f24 f25 ?v0) (f15 f26 (f15 f16 (f15 f17 f18)))) (f15 (f24 f27 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f10 ?v0) (f13 f14 (f15 f16 (f15 f17 f18)))) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f15 (f24 f25 (f15 f26 (f15 f16 (f15 f17 f18)))) ?v0) (f15 (f24 f27 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f10 (f13 f14 (f15 f16 (f15 f17 f18)))) ?v0) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f15 (f24 f25 (f15 f26 (f15 f16 (f15 f17 f18)))) ?v0) (f15 (f24 f27 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f10 (f13 f14 (f15 f16 (f15 f17 f18)))) ?v0) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f3 f4 (f5 f9 (f5 (f6 f8 (f5 (f6 f10 ?v0) ?v0)) (f5 (f6 f10 ?v1) ?v1)))) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f3 ?v0 (f5 f9 (f5 (f6 f8 (f5 (f6 f10 ?v0) ?v0)) (f5 (f6 f10 ?v1) ?v1)))) f1)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 ?v0) (f13 f14 (f15 f17 f18))) ?v0)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 ?v0) (f13 f14 (f15 f17 f18))) ?v0)))
(assert (forall ((?v0 S6)) (= (f15 (f24 f25 ?v0) (f15 f26 (f15 f17 f18))) ?v0)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f10 ?v0) (f13 f14 (f15 f17 f18))) ?v0)))
(assert (= f28 (f22 f29 f23)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f15 f26 (f15 (f24 f30 ?v0) ?v1)) (f15 (f24 f30 (f15 f26 ?v0)) (f15 f26 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f13 f14 (f15 (f24 f30 ?v0) ?v1)) (f5 (f6 f19 (f13 f14 ?v0)) (f13 f14 ?v1)))))
(assert (forall ((?v0 S6)) (= (f15 (f24 f27 ?v0) f18) ?v0)))
(assert (forall ((?v0 S6)) (= (f15 (f24 f27 f18) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f15 (f24 f27 (f15 f16 ?v0)) (f15 f16 ?v1)) (f15 f16 (f15 (f24 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (f15 f16 ?v0) (f15 (f24 f27 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f15 (f24 f25 f18) ?v0) f18)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f15 (f24 f25 (f15 f16 ?v0)) ?v1) (f15 f16 (f15 (f24 f25 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f15 (f24 f25 (f15 f17 ?v0)) ?v1) (f15 (f24 f27 (f15 f16 (f15 (f24 f25 ?v0) ?v1))) ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f15 (f24 f27 (f15 f17 ?v0)) (f15 f16 ?v1)) (f15 f17 (f15 (f24 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f15 (f24 f27 (f15 f16 ?v0)) (f15 f17 ?v1)) (f15 f17 (f15 (f24 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (f15 (f24 f30 (f15 (f24 f27 ?v0) ?v1)) (f15 (f24 f27 ?v2) ?v3)) (f15 (f24 f27 (f15 (f24 f30 ?v0) ?v2)) (f15 (f24 f30 ?v1) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (f5 (f6 f19 (f5 (f6 f8 ?v0) ?v1)) (f5 (f6 f8 ?v2) ?v3)) (f5 (f6 f8 (f5 (f6 f19 ?v0) ?v2)) (f5 (f6 f19 ?v1) ?v3)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f15 f26 ?v0) (f15 f26 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f13 f14 ?v0) (f13 f14 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f15 f26 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S2)) (let ((?v_0 (f13 f14 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f15 f17 ?v0) (f15 f17 ?v1)) (= ?v0 ?v1))))
(assert (= (= f18 f18) true))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f26 ?v2))) (= (f15 (f24 f25 (f15 (f24 f30 ?v0) ?v1)) ?v_0) (f15 (f24 f30 (f15 (f24 f25 ?v0) ?v_0)) (f15 (f24 f25 ?v1) ?v_0))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (let ((?v_0 (f13 f14 ?v2))) (= (f5 (f6 f10 (f5 (f6 f19 ?v0) ?v1)) ?v_0) (f5 (f6 f19 (f5 (f6 f10 ?v0) ?v_0)) (f5 (f6 f10 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f24 f25 (f15 f26 ?v0)))) (= (f15 ?v_0 (f15 (f24 f30 ?v1) ?v2)) (f15 (f24 f30 (f15 ?v_0 ?v1)) (f15 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f10 (f13 f14 ?v0)))) (= (f5 ?v_0 (f5 (f6 f19 ?v1) ?v2)) (f5 (f6 f19 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f15 f16 ?v0) (f15 f16 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f15 (f24 f27 (f15 f26 ?v0)) (f15 (f24 f30 (f15 f26 ?v1)) ?v2)) (f15 (f24 f30 (f15 f26 (f15 (f24 f27 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S2)) (= (f5 (f6 f8 (f13 f14 ?v0)) (f5 (f6 f19 (f13 f14 ?v1)) ?v2)) (f5 (f6 f19 (f13 f14 (f15 (f24 f27 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 ?v0 ?v1)) (?v_1 (f6 f19 (f5 ?v0 ?v2)))) (let ((?v_2 (f6 f10 (f5 (f6 f7 (f5 ?v_1 ?v_0)) (f5 (f6 f19 ?v2) ?v1))))) (= (f5 (f6 f19 ?v_0) (f5 ?v_2 ?v1)) (f5 ?v_1 (f5 ?v_2 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f5 f9 ?v0) (f5 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (let ((?v_0 (f6 f10 ?v0))) (= (f5 (f6 f7 (f5 (f6 f19 (f5 ?v_0 ?v1)) (f5 (f6 f10 ?v2) ?v3))) ?v4) (f5 (f6 f8 (f5 ?v_0 (f5 (f6 f7 (f5 (f6 f19 ?v1) ?v3)) ?v4))) (f5 (f6 f10 (f5 (f6 f7 (f5 (f6 f19 ?v0) ?v2)) ?v4)) ?v3))))))
(assert (forall ((?v0 S6)) (= (= (f15 (f24 f27 ?v0) ?v0) f31) (= ?v0 f31))))
(assert (forall ((?v0 S2)) (= (= (f5 (f6 f8 ?v0) ?v0) f4) (= ?v0 f4))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f32 (f15 f26 ?v0) (f15 f26 ?v1)) f1) (= (f32 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f3 (f13 f14 ?v0) (f13 f14 ?v1)) f1) (= (f32 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f15 (f24 f25 (f15 f26 ?v0)) (f15 (f24 f25 (f15 f26 ?v1)) ?v2)) (f15 (f24 f25 (f15 f26 (f15 (f24 f25 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S2)) (= (f5 (f6 f10 (f13 f14 ?v0)) (f5 (f6 f10 (f13 f14 ?v1)) ?v2)) (f5 (f6 f10 (f13 f14 (f15 (f24 f25 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f15 (f24 f25 (f15 f26 ?v0)) (f15 f26 ?v1)) (f15 f26 (f15 (f24 f25 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f5 (f6 f10 (f13 f14 ?v0)) (f13 f14 ?v1)) (f13 f14 (f15 (f24 f25 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f15 f26 (f15 (f24 f25 ?v0) ?v1)) (f15 (f24 f25 (f15 f26 ?v0)) (f15 f26 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f13 f14 (f15 (f24 f25 ?v0) ?v1)) (f5 (f6 f10 (f13 f14 ?v0)) (f13 f14 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f15 (f24 f27 (f15 f26 ?v0)) (f15 (f24 f27 (f15 f26 ?v1)) ?v2)) (f15 (f24 f27 (f15 f26 (f15 (f24 f27 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S2)) (= (f5 (f6 f8 (f13 f14 ?v0)) (f5 (f6 f8 (f13 f14 ?v1)) ?v2)) (f5 (f6 f8 (f13 f14 (f15 (f24 f27 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f15 (f24 f27 (f15 f26 ?v0)) (f15 f26 ?v1)) (f15 f26 (f15 (f24 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f5 (f6 f8 (f13 f14 ?v0)) (f13 f14 ?v1)) (f13 f14 (f15 (f24 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f15 f26 (f15 (f24 f27 ?v0) ?v1)) (f15 (f24 f27 (f15 f26 ?v0)) (f15 f26 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f13 f14 (f15 (f24 f27 ?v0) ?v1)) (f5 (f6 f8 (f13 f14 ?v0)) (f13 f14 ?v1)))))
(assert (forall ((?v0 S6)) (= (= (f15 f17 ?v0) f18) false)))
(assert (forall ((?v0 S6)) (= (= f18 (f15 f17 ?v0)) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f15 f17 ?v0) (f15 f16 ?v1)) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f15 f16 ?v0) (f15 f17 ?v1)) false)))
(assert (forall ((?v0 S6)) (= (= (f15 f16 ?v0) f18) (= ?v0 f18))))
(assert (forall ((?v0 S6)) (= (= f18 (f15 f16 ?v0)) (= f18 ?v0))))
(assert (= (f15 f16 f18) f18))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f6 f10 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v0)) (f5 (f6 f7 ?v1) ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 ?v1) f1) (= (f3 (f5 f9 ?v0) (f5 f9 ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f5 f9 ?v0) (f5 f9 ?v1)) f1) (= (f3 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2)) (= (= (f5 f9 ?v0) f4) (= ?v0 f4))))
(assert (= (f5 f9 f4) f4))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f5 f9 (f5 (f6 f10 ?v0) ?v1)) (f5 (f6 f10 (f5 f9 ?v0)) (f5 f9 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f5 f9 (f5 (f6 f7 ?v0) ?v1)) (f5 (f6 f7 (f5 f9 ?v0)) (f5 f9 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f26 ?v2))) (= (f15 (f24 f25 (f15 (f24 f27 ?v0) ?v1)) ?v_0) (f15 (f24 f27 (f15 (f24 f25 ?v0) ?v_0)) (f15 (f24 f25 ?v1) ?v_0))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (let ((?v_0 (f13 f14 ?v2))) (= (f5 (f6 f10 (f5 (f6 f8 ?v0) ?v1)) ?v_0) (f5 (f6 f8 (f5 (f6 f10 ?v0) ?v_0)) (f5 (f6 f10 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f24 f25 (f15 f26 ?v0)))) (= (f15 ?v_0 (f15 (f24 f27 ?v1) ?v2)) (f15 (f24 f27 (f15 ?v_0 ?v1)) (f15 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f10 (f13 f14 ?v0)))) (= (f5 ?v_0 (f5 (f6 f8 ?v1) ?v2)) (f5 (f6 f8 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (= (f15 f26 f18) f31))
(assert (= (f13 f14 f18) f4))
(check-sat)
(exit)