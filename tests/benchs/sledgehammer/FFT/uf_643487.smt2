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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 () S2)
(declare-fun f5 (S3 S2) S2)
(declare-fun f6 (S4 S2) S3)
(declare-fun f7 () S4)
(declare-fun f8 () S4)
(declare-fun f9 (S5 S6) S2)
(declare-fun f10 () S5)
(declare-fun f11 () S6)
(declare-fun f12 (S7 S8) S2)
(declare-fun f13 () S7)
(declare-fun f14 (S9 S8) S8)
(declare-fun f15 () S9)
(declare-fun f16 () S9)
(declare-fun f17 () S8)
(declare-fun f18 () S2)
(declare-fun f19 () S6)
(declare-fun f20 (S10 S6) S1)
(declare-fun f21 (S6) S10)
(declare-fun f22 () S6)
(declare-fun f23 () S8)
(declare-fun f24 () S9)
(declare-fun f25 (S8 S8) S1)
(declare-fun f26 (S11 S8) S9)
(declare-fun f27 () S11)
(declare-fun f28 (S12 S6) S6)
(declare-fun f29 (S13 S6) S12)
(declare-fun f30 () S13)
(declare-fun f31 (S14 S8) S6)
(declare-fun f32 () S14)
(declare-fun f33 (S15 S6) S10)
(assert (not (= f1 f2)))
(assert (not (= (f3 f4 (f5 (f6 f7 (f5 (f6 f8 (f9 f10 f11)) (f5 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) f18))) (f9 f10 f19))) f1)))
(assert (= (f20 (f21 f22) f11) f1))
(assert (= (f20 (f21 f11) f19) f1))
(assert (= (f20 (f21 f22) f11) f1))
(assert (= (f20 (f21 f11) f19) f1))
(assert (= (f3 f4 (f5 (f6 f7 f18) (f12 f13 (f14 f15 (f14 f16 f17))))) f1))
(assert (let ((?v_0 (f12 f13 (f14 f15 (f14 f16 f17))))) (= (f3 (f5 (f6 f7 f18) ?v_0) ?v_0) f1)))
(assert (not (= (f5 (f6 f7 f18) (f12 f13 (f14 f15 (f14 f16 f17)))) f4)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 (f5 (f6 f7 ?v0) (f12 f13 (f14 f15 (f14 f16 f17))))) f1) (= (f3 f4 ?v0) f1))))
(assert (forall ((?v0 S2)) (=> (= (f3 f4 ?v0) f1) (= (f3 f4 (f5 (f6 f7 ?v0) (f12 f13 (f14 f15 (f14 f16 f17))))) f1))))
(assert (let ((?v_0 (f12 f13 (f14 f15 (f14 f16 f17))))) (not (= (f5 (f6 f7 f18) ?v_0) ?v_0))))
(assert (= (f3 f18 (f12 f13 (f14 f15 (f14 f15 (f14 f16 f17))))) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17))))) (?v_1 (f6 f7 ?v1))) (= (= ?v0 (f5 ?v_1 (f5 ?v_0 ?v2))) (= (f5 ?v_0 ?v0) (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S8)) (let ((?v_0 (f12 f13 ?v2))) (let ((?v_1 (f5 (f6 f8 ?v0) ?v_0))) (= (= (f3 ?v0 (f5 (f6 f7 ?v1) ?v_0)) f1) (ite (= (f3 f4 ?v_0) f1) (= (f3 ?v_1 ?v1) f1) (ite (= (f3 ?v_0 f4) f1) (= (f3 ?v1 ?v_1) f1) (= (f3 ?v0 f4) f1))))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f13 ?v0))) (let ((?v_1 (f5 (f6 f8 ?v_0) ?v2))) (= (= (f3 ?v_0 (f5 (f6 f7 ?v1) ?v2)) f1) (ite (= (f3 f4 ?v2) f1) (= (f3 ?v_1 ?v1) f1) (ite (= (f3 ?v2 f4) f1) (= (f3 ?v1 ?v_1) f1) (= (f3 ?v_0 f4) f1))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S8)) (let ((?v_0 (f12 f13 ?v2))) (let ((?v_1 (f5 (f6 f8 ?v_0) ?v1))) (= (= (f3 (f5 (f6 f7 ?v0) ?v1) ?v_0) f1) (ite (= (f3 f4 ?v1) f1) (= (f3 ?v0 ?v_1) f1) (ite (= (f3 ?v1 f4) f1) (= (f3 ?v_1 ?v0) f1) (= (f3 f4 ?v_0) f1))))))))
(assert (forall ((?v0 S2) (?v1 S8) (?v2 S2)) (let ((?v_0 (f12 f13 ?v1))) (let ((?v_1 (f5 (f6 f8 ?v2) ?v_0))) (= (= (f3 (f5 (f6 f7 ?v0) ?v_0) ?v2) f1) (ite (= (f3 f4 ?v_0) f1) (= (f3 ?v0 ?v_1) f1) (ite (= (f3 ?v_0 f4) f1) (= (f3 ?v_1 ?v0) f1) (= (f3 f4 ?v2) f1))))))))
(assert (= f23 (f14 f24 f17)))
(assert (= (= (f25 f17 f23) f1) false))
(assert (forall ((?v0 S8)) (= (= (f25 (f14 f15 ?v0) f23) f1) (= (f25 ?v0 f23) f1))))
(assert (forall ((?v0 S8)) (= (= (f25 (f14 f16 ?v0) f23) f1) (= (f25 ?v0 f23) f1))))
(assert (forall ((?v0 S8)) (= (f14 (f26 f27 f17) ?v0) f17)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f25 (f14 f16 ?v0) (f14 f16 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f25 (f14 f16 ?v0) (f14 f16 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (= (= (f25 f17 f17) f1) false))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f14 (f26 f27 (f14 f15 ?v0)) ?v1) (f14 f15 (f14 (f26 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f25 (f14 f15 ?v0) (f14 f15 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f25 (f14 f15 ?v0) (f14 f15 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (= f17 f23))
(assert (forall ((?v0 S8)) (= (= (f25 (f14 f16 ?v0) f17) f1) (= (f25 ?v0 f17) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f25 (f14 f16 ?v0) (f14 f15 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f25 (f14 f16 ?v0) (f14 f15 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8)) (= (= (f25 (f14 f15 ?v0) f17) f1) (= (f25 ?v0 f17) f1))))
(assert (forall ((?v0 S8)) (= (= (f25 f17 (f14 f15 ?v0)) f1) (= (f25 f17 ?v0) f1))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f14 f15 (f14 f15 (f14 f16 f17))))) (= (f5 (f6 f8 (f9 f10 ?v0)) (f12 f13 ?v_0)) (f9 f10 (f28 (f29 f30 (f31 f32 ?v_0)) ?v0))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f14 f24 ?v0) (f14 f24 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f12 f13 ?v0) (f12 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S6)) (let ((?v_0 (f31 f32 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f14 f24 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f14 f16 ?v0) (f14 f16 ?v1)) (= ?v0 ?v1))))
(assert (= (= f17 f17) true))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f14 f15 ?v0) (f14 f15 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f25 (f14 f24 ?v0) (f14 f24 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f3 (f12 f13 ?v0) (f12 f13 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (f14 (f26 f27 (f14 f24 ?v0)) (f14 (f26 f27 (f14 f24 ?v1)) ?v2)) (f14 (f26 f27 (f14 f24 (f14 (f26 f27 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S2)) (= (f5 (f6 f8 (f12 f13 ?v0)) (f5 (f6 f8 (f12 f13 ?v1)) ?v2)) (f5 (f6 f8 (f12 f13 (f14 (f26 f27 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f14 (f26 f27 (f14 f24 ?v0)) (f14 f24 ?v1)) (f14 f24 (f14 (f26 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f5 (f6 f8 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f14 (f26 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f14 f24 (f14 (f26 f27 ?v0) ?v1)) (f14 (f26 f27 (f14 f24 ?v0)) (f14 f24 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 f13 (f14 (f26 f27 ?v0) ?v1)) (f5 (f6 f8 (f12 f13 ?v0)) (f12 f13 ?v1)))))
(assert (forall ((?v0 S8)) (= (= (f14 f16 ?v0) f17) false)))
(assert (forall ((?v0 S8)) (= (= f17 (f14 f16 ?v0)) false)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f14 f16 ?v0) (f14 f15 ?v1)) false)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f14 f15 ?v0) (f14 f16 ?v1)) false)))
(assert (forall ((?v0 S8)) (= (= (f14 f15 ?v0) f17) (= ?v0 f17))))
(assert (forall ((?v0 S8)) (= (= f17 (f14 f15 ?v0)) (= f17 ?v0))))
(assert (= (f14 f15 f17) f17))
(assert (not (= f18 f4)))
(assert (= (f14 f24 f17) f23))
(assert (= (f31 f32 f17) f22))
(assert (= (f12 f13 f17) f4))
(assert (= (f14 f24 f17) f23))
(assert (= (f12 f13 f17) f4))
(assert (= (f3 f4 f18) f1))
(assert (not (= (f3 f18 f4) f1)))
(assert (forall ((?v0 S8)) (= (= (f25 (f14 f24 ?v0) f23) f1) (= (f25 ?v0 f17) f1))))
(assert (forall ((?v0 S8)) (= (= (f3 (f12 f13 ?v0) f4) f1) (= (f25 ?v0 f17) f1))))
(assert (forall ((?v0 S8)) (= (= (f25 f23 (f14 f24 ?v0)) f1) (= (f25 f17 ?v0) f1))))
(assert (forall ((?v0 S8)) (= (= (f3 f4 (f12 f13 ?v0)) f1) (= (f25 f17 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S8) (?v2 S2)) (let ((?v_0 (f12 f13 ?v1))) (= (= (f5 (f6 f7 ?v0) ?v_0) ?v2) (ite (not (= ?v_0 f4)) (= ?v0 (f5 (f6 f8 ?v2) ?v_0)) (= ?v2 f4))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S8)) (let ((?v_0 (f12 f13 ?v2))) (= (= (f5 (f6 f7 ?v0) ?v1) ?v_0) (ite (not (= ?v1 f4)) (= ?v0 (f5 (f6 f8 ?v_0) ?v1)) (= ?v_0 f4))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (= ?v_0 (f5 (f6 f7 ?v1) ?v2)) (ite (not (= ?v2 f4)) (= (f5 (f6 f8 ?v_0) ?v2) ?v1) (= ?v_0 f4))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S8)) (let ((?v_0 (f12 f13 ?v2))) (= (= ?v0 (f5 (f6 f7 ?v1) ?v_0)) (ite (not (= ?v_0 f4)) (= (f5 (f6 f8 ?v0) ?v_0) ?v1) (= ?v0 f4))))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 ?v0) (f12 f13 f17)) f4)))
(assert (forall ((?v0 S8)) (= (f14 (f26 f27 (f14 f24 (f14 f16 f17))) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f8 (f12 f13 (f14 f16 f17))) ?v0) ?v0)))
(assert (forall ((?v0 S8)) (= (f14 (f26 f27 ?v0) (f14 f24 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f8 ?v0) (f12 f13 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 ?v0) (f12 f13 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 ?v0) (f12 f13 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S6)) (= (= (f3 f4 (f9 f10 ?v0)) f1) (= (f20 (f21 f22) ?v0) f1))))
(assert (forall ((?v0 S6)) (=> (= (f20 (f21 ?v0) f22) f1) false)))
(assert (= (f20 (f21 f22) (f31 f32 (f14 f15 (f14 f16 f17)))) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v2))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v2 f4) f1) (=> (= (f3 f4 (f5 (f6 f8 ?v0) ?v1)) f1) (= (f3 (f5 ?v_0 ?v0) (f5 ?v_0 ?v1)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v2))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 f4 ?v2) f1) (=> (= (f3 f4 (f5 (f6 f8 ?v1) ?v0)) f1) (= (f3 (f5 ?v_0 ?v1) (f5 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 f4) f1) (= (= (f3 (f5 (f6 f7 ?v1) ?v0) ?v2) f1) (= (f3 (f5 (f6 f8 ?v2) ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 f4) f1) (= (= (f3 ?v1 (f5 (f6 f7 ?v2) ?v0)) f1) (= (f3 ?v2 (f5 (f6 f8 ?v1) ?v0)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 f4 ?v0) f1) (=> (= (f3 (f5 (f6 f8 ?v1) ?v0) ?v2) f1) (= (f3 ?v1 (f5 (f6 f7 ?v2) ?v0)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 f4 ?v0) f1) (=> (= (f3 ?v1 (f5 (f6 f8 ?v2) ?v0)) f1) (= (f3 (f5 (f6 f7 ?v1) ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 f4 ?v0) f1) (= (= (f3 (f5 (f6 f7 ?v1) ?v0) ?v2) f1) (= (f3 ?v1 (f5 (f6 f8 ?v2) ?v0)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 f4 ?v0) f1) (= (= (f3 ?v1 (f5 (f6 f7 ?v2) ?v0)) f1) (= (f3 (f5 (f6 f8 ?v1) ?v0) ?v2) f1)))))
(assert (forall ((?v0 S8)) (= (f14 f24 ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f28 (f29 f30 ?v0) ?v1) (f28 (f29 f30 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f14 (f26 f27 ?v0) ?v1) (f14 (f26 f27 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (or (= (f25 ?v0 ?v1) f1) (or (= ?v0 ?v1) (= (f25 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f14 (f26 f27 (f14 f24 ?v0)) (f14 f24 ?v1)) (f14 f24 (f14 (f26 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f25 (f14 f24 ?v0) (f14 f24 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f29 f30 ?v0))) (= (f28 (f29 f30 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f29 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f26 f27 ?v0))) (= (f14 (f26 f27 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f26 f27 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f26 f27 ?v2))) (=> (= (f25 ?v0 ?v1) f1) (=> (= (f25 f23 ?v2) f1) (= (f25 (f14 ?v_0 ?v0) (f14 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f28 (f29 f30 ?v0) ?v1) (f28 (f29 f30 ?v2) ?v1)) (or (= ?v0 ?v2) (= ?v1 f22)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f29 f30 ?v0))) (= (= (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) (or (= ?v1 ?v2) (= ?v0 f22))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f28 (f29 f30 ?v0) ?v1) f22) (or (= ?v0 f22) (= ?v1 f22)))))
(assert (forall ((?v0 S6)) (= (f28 (f29 f30 ?v0) f22) f22)))
(assert (forall ((?v0 S6)) (= (f28 (f29 f30 f22) ?v0) f22)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S15)) (let ((?v_0 (= (f20 (f33 ?v2 ?v1) ?v0) f1))) (=> (=> (= (f20 (f21 ?v0) ?v1) f1) ?v_0) (=> (=> (= ?v0 ?v1) ?v_0) (=> (=> (= (f20 (f21 ?v1) ?v0) f1) ?v_0) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f20 (f21 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f20 (f21 ?v0) ?v1) f1) (not (= ?v1 ?v0)))))
(assert (forall ((?v0 S6)) (=> (= (f20 (f21 ?v0) ?v0) f1) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f20 (f21 ?v0) ?v1) f1) false) (=> (=> (= (f20 (f21 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (not (= ?v0 ?v1)) (or (= (f20 (f21 ?v0) ?v1) f1) (= (f20 (f21 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S6)) (not (= (f20 (f21 ?v0) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f5 (f6 f8 ?v0) ?v1) (f5 (f6 f8 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f8 ?v0))) (= (f5 (f6 f8 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f8 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f9 f10 ?v0) (f9 f10 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (f5 (f6 f8 (f5 (f6 f7 ?v0) ?v1)) (f5 (f6 f7 ?v2) ?v3)) (f5 (f6 f7 (f5 (f6 f8 ?v0) ?v2)) (f5 (f6 f8 ?v1) ?v3)))))
(assert (forall ((?v0 S6)) (=> (=> (= ?v0 f22) false) (= (f20 (f21 f22) ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f29 f30 ?v2))) (=> (= (f20 (f21 ?v0) ?v1) f1) (=> (= (f20 (f21 f22) ?v2) f1) (= (f20 (f21 (f28 ?v_0 ?v0)) (f28 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f20 (f21 ?v0) ?v1) f1) (=> (= (f20 (f21 f22) ?v2) f1) (= (f20 (f21 (f28 (f29 f30 ?v0) ?v2)) (f28 (f29 f30 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f20 (f21 ?v0) ?v1) f1) (not (= ?v1 f22)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f20 (f21 (f28 (f29 f30 ?v0) ?v1)) (f28 (f29 f30 ?v2) ?v1)) f1) (and (= (f20 (f21 f22) ?v1) f1) (= (f20 (f21 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f29 f30 ?v0))) (= (= (f20 (f21 (f28 ?v_0 ?v1)) (f28 ?v_0 ?v2)) f1) (and (= (f20 (f21 f22) ?v0) f1) (= (f20 (f21 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S6)) (= (= (f20 (f21 ?v0) f22) f1) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f21 f22))) (= (= (f20 ?v_0 (f28 (f29 f30 ?v0) ?v1)) f1) (and (= (f20 ?v_0 ?v0) f1) (= (f20 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S6)) (= (not (= ?v0 f22)) (= (f20 (f21 f22) ?v0) f1))))
(assert (forall ((?v0 S6)) (not (= (f20 (f21 ?v0) f22) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (not (= ?v0 f4)) (= (= (f5 (f6 f8 ?v1) ?v0) (f5 (f6 f8 ?v2) ?v0)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f8 ?v0))) (=> (not (= ?v0 f4)) (= (= (f5 ?v_0 ?v1) (f5 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f6 f8 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v0)) (f5 (f6 f7 ?v1) ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 f10 (f28 (f29 f30 ?v0) ?v1)) (f5 (f6 f8 (f9 f10 ?v0)) (f9 f10 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 f4 (f5 (f6 f7 ?v0) ?v1)) f1) (or (and (= (f3 f4 ?v0) f1) (= (f3 f4 ?v1) f1)) (and (= (f3 ?v0 f4) f1) (= (f3 ?v1 f4) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f5 (f6 f7 ?v0) ?v1) f4) f1) (or (and (= (f3 f4 ?v0) f1) (= (f3 ?v1 f4) f1)) (and (= (f3 ?v0 f4) f1) (= (f3 f4 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f3 (f5 (f6 f7 ?v0) ?v1) (f5 (f6 f7 ?v2) ?v1)) f1) (and (=> (= (f3 f4 ?v1) f1) (= (f3 ?v0 ?v2) f1)) (and (=> (= (f3 ?v1 f4) f1) (= (f3 ?v2 ?v0) f1)) (not (= ?v1 f4)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f4 ?v0) f1) (=> (= (f3 f4 ?v1) f1) (= (f3 f4 (f5 (f6 f7 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f4 ?v0) f1) (=> (= (f3 ?v1 f4) f1) (= (f3 (f5 (f6 f7 ?v0) ?v1) f4) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 f4) f1) (=> (= (f3 f4 ?v1) f1) (= (f3 (f5 (f6 f7 ?v0) ?v1) f4) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 f4) f1) (=> (= (f3 ?v1 f4) f1) (= (f3 f4 (f5 (f6 f7 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 f4 ?v2) f1) (= (f3 (f5 (f6 f7 ?v0) ?v2) (f5 (f6 f7 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v2 f4) f1) (= (f3 (f5 (f6 f7 ?v1) ?v2) (f5 (f6 f7 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= ?v0 (f5 (f6 f7 ?v1) ?v2)) (ite (not (= ?v2 f4)) (= (f5 (f6 f8 ?v0) ?v2) ?v1) (= ?v0 f4)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f5 (f6 f7 ?v0) ?v1) ?v2) (ite (not (= ?v1 f4)) (= ?v0 (f5 (f6 f8 ?v2) ?v1)) (= ?v2 f4)))))
(check-sat)
(exit)