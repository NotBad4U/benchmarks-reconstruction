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
(declare-fun f4 (S3 S2) S2)
(declare-fun f5 (S4 S2) S3)
(declare-fun f6 () S4)
(declare-fun f7 () S4)
(declare-fun f8 (S5 S6) S2)
(declare-fun f9 () S5)
(declare-fun f10 () S6)
(declare-fun f11 (S7 S8) S2)
(declare-fun f12 () S7)
(declare-fun f13 (S9 S8) S8)
(declare-fun f14 () S9)
(declare-fun f15 () S9)
(declare-fun f16 () S8)
(declare-fun f17 () S2)
(declare-fun f18 () S6)
(declare-fun f19 (S10 S6) S1)
(declare-fun f20 (S6) S10)
(declare-fun f21 () S6)
(declare-fun f22 () S2)
(declare-fun f23 (S11 S8) S9)
(declare-fun f24 () S11)
(declare-fun f25 () S9)
(declare-fun f26 () S8)
(declare-fun f27 (S8 S8) S1)
(declare-fun f28 (S12 S6) S6)
(declare-fun f29 (S13 S6) S12)
(declare-fun f30 () S13)
(declare-fun f31 (S14 S8) S6)
(declare-fun f32 () S14)
(declare-fun f33 (S15 S6) S10)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f4 (f5 f7 (f11 f12 (f13 f14 (f13 f15 f16)))) f17))) (not (= (f3 (f4 (f5 f6 (f4 (f5 f7 (f8 f9 f10)) ?v_0)) (f8 f9 f18)) ?v_0) f1))))
(assert (= (f19 (f20 f21) f10) f1))
(assert (= (f19 (f20 f10) f18) f1))
(assert (let ((?v_0 (f4 (f5 f7 (f11 f12 (f13 f14 (f13 f15 f16)))) f17)) (?v_1 (f8 f9 f18))) (=> (= (f19 (f20 f10) f18) f1) (=> (= (f3 f22 (f4 (f5 f6 ?v_0) ?v_1)) f1) (= (f3 (f4 (f5 f6 (f4 (f5 f7 (f8 f9 f10)) ?v_0)) ?v_1) ?v_0) f1)))))
(assert (= (f19 (f20 f21) f10) f1))
(assert (= (f19 (f20 f10) f18) f1))
(assert (let ((?v_0 (f4 (f5 f7 (f11 f12 (f13 f14 (f13 f15 f16)))) f17)) (?v_1 (f8 f9 f18))) (=> (= (f19 (f20 f10) f18) f1) (=> (= (f3 f22 (f4 (f5 f6 ?v_0) ?v_1)) f1) (= (f3 (f4 (f5 f6 (f4 (f5 f7 (f8 f9 f10)) ?v_0)) ?v_1) ?v_0) f1)))))
(assert (= (f3 f22 (f4 (f5 f6 (f4 (f5 f7 (f8 f9 f10)) (f4 (f5 f7 (f11 f12 (f13 f14 (f13 f15 f16)))) f17))) (f8 f9 f18))) f1))
(assert (let ((?v_0 (f11 f12 (f13 f14 (f13 f15 f16))))) (= (f3 (f4 (f5 f6 f17) ?v_0) ?v_0) f1)))
(assert (let ((?v_0 (f11 f12 (f13 f14 (f13 f15 f16))))) (not (= (f4 (f5 f6 f17) ?v_0) ?v_0))))
(assert (= (f3 f17 (f11 f12 (f13 f14 (f13 f14 (f13 f15 f16))))) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 (f11 f12 (f13 f14 (f13 f15 f16))))) (?v_1 (f5 f6 ?v1))) (= (= ?v0 (f4 ?v_1 (f4 ?v_0 ?v2))) (= (f4 ?v_0 ?v0) (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f11 f12 (f13 f15 f16))) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f11 f12 (f13 f15 f16))) ?v0)))
(assert (forall ((?v0 S8)) (= (f13 (f23 f24 ?v0) (f13 f25 (f13 f15 f16))) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) (f11 f12 (f13 f15 f16))) ?v0)))
(assert (forall ((?v0 S8)) (= (f13 (f23 f24 (f13 f25 (f13 f15 f16))) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 (f11 f12 (f13 f15 f16))) ?v0) ?v0)))
(assert (= (f3 f22 (f4 (f5 f6 f17) (f11 f12 (f13 f14 (f13 f15 f16))))) f1))
(assert (not (= (f4 (f5 f6 f17) (f11 f12 (f13 f14 (f13 f15 f16)))) f22)))
(assert (forall ((?v0 S2)) (= (= (f3 f22 (f4 (f5 f6 ?v0) (f11 f12 (f13 f14 (f13 f15 f16))))) f1) (= (f3 f22 ?v0) f1))))
(assert (forall ((?v0 S2)) (=> (= (f3 f22 ?v0) f1) (= (f3 f22 (f4 (f5 f6 ?v0) (f11 f12 (f13 f14 (f13 f15 f16))))) f1))))
(assert (= f26 (f13 f25 f16)))
(assert (= (= (f27 f16 f26) f1) false))
(assert (forall ((?v0 S8)) (= (= (f27 (f13 f14 ?v0) f26) f1) (= (f27 ?v0 f26) f1))))
(assert (forall ((?v0 S8)) (= (= (f27 (f13 f15 ?v0) f26) f1) (= (f27 ?v0 f26) f1))))
(assert (forall ((?v0 S8)) (= (f13 (f23 f24 f16) ?v0) f16)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f27 (f13 f15 ?v0) (f13 f15 ?v1)) f1) (= (f27 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f27 (f13 f15 ?v0) (f13 f15 ?v1)) f1) (= (f27 ?v0 ?v1) f1))))
(assert (= (= (f27 f16 f16) f1) false))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f13 (f23 f24 (f13 f14 ?v0)) ?v1) (f13 f14 (f13 (f23 f24 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f27 (f13 f14 ?v0) (f13 f14 ?v1)) f1) (= (f27 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f27 (f13 f14 ?v0) (f13 f14 ?v1)) f1) (= (f27 ?v0 ?v1) f1))))
(assert (= f16 f26))
(assert (forall ((?v0 S8)) (= (= (f27 (f13 f15 ?v0) f16) f1) (= (f27 ?v0 f16) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f27 (f13 f15 ?v0) (f13 f14 ?v1)) f1) (= (f27 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f27 (f13 f15 ?v0) (f13 f14 ?v1)) f1) (= (f27 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8)) (= (= (f27 (f13 f14 ?v0) f16) f1) (= (f27 ?v0 f16) f1))))
(assert (forall ((?v0 S8)) (= (= (f27 f16 (f13 f14 ?v0)) f1) (= (f27 f16 ?v0) f1))))
(assert (not (= f17 f22)))
(assert (forall ((?v0 S6)) (let ((?v_0 (f13 f14 (f13 f14 (f13 f15 f16))))) (= (f4 (f5 f7 (f8 f9 ?v0)) (f11 f12 ?v_0)) (f8 f9 (f28 (f29 f30 (f31 f32 ?v_0)) ?v0))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f13 f25 ?v0) (f13 f25 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f11 f12 ?v0) (f11 f12 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S6)) (let ((?v_0 (f31 f32 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f13 f25 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S2)) (let ((?v_0 (f11 f12 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f13 f15 ?v0) (f13 f15 ?v1)) (= ?v0 ?v1))))
(assert (= (= f16 f16) true))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f13 f14 ?v0) (f13 f14 ?v1)) (= ?v0 ?v1))))
(assert (= (f13 f25 f16) f26))
(assert (= (f11 f12 f16) f22))
(assert (= (f31 f32 f16) f21))
(assert (= (f13 f25 f16) f26))
(assert (= (f11 f12 f16) f22))
(assert (= (f3 f22 f17) f1))
(assert (not (= (f3 f17 f22) f1)))
(assert (forall ((?v0 S8)) (= (= (f27 (f13 f25 ?v0) f26) f1) (= (f27 ?v0 f16) f1))))
(assert (forall ((?v0 S8)) (= (= (f3 (f11 f12 ?v0) f22) f1) (= (f27 ?v0 f16) f1))))
(assert (forall ((?v0 S8)) (= (= (f27 f26 (f13 f25 ?v0)) f1) (= (f27 f16 ?v0) f1))))
(assert (forall ((?v0 S8)) (= (= (f3 f22 (f11 f12 ?v0)) f1) (= (f27 f16 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S8) (?v2 S2)) (let ((?v_0 (f11 f12 ?v1))) (= (= (f4 (f5 f6 ?v0) ?v_0) ?v2) (ite (not (= ?v_0 f22)) (= ?v0 (f4 (f5 f7 ?v2) ?v_0)) (= ?v2 f22))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S8)) (let ((?v_0 (f11 f12 ?v2))) (= (= (f4 (f5 f6 ?v0) ?v1) ?v_0) (ite (not (= ?v1 f22)) (= ?v0 (f4 (f5 f7 ?v_0) ?v1)) (= ?v_0 f22))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f12 ?v0))) (= (= ?v_0 (f4 (f5 f6 ?v1) ?v2)) (ite (not (= ?v2 f22)) (= (f4 (f5 f7 ?v_0) ?v2) ?v1) (= ?v_0 f22))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S8)) (let ((?v_0 (f11 f12 ?v2))) (= (= ?v0 (f4 (f5 f6 ?v1) ?v_0)) (ite (not (= ?v_0 f22)) (= (f4 (f5 f7 ?v0) ?v_0) ?v1) (= ?v0 f22))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f11 f12 f16)) f22)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f27 (f13 f25 ?v0) (f13 f25 ?v1)) f1) (= (f27 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f3 (f11 f12 ?v0) (f11 f12 ?v1)) f1) (= (f27 ?v0 ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (f13 (f23 f24 (f13 f25 ?v0)) (f13 (f23 f24 (f13 f25 ?v1)) ?v2)) (f13 (f23 f24 (f13 f25 (f13 (f23 f24 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S2)) (= (f4 (f5 f7 (f11 f12 ?v0)) (f4 (f5 f7 (f11 f12 ?v1)) ?v2)) (f4 (f5 f7 (f11 f12 (f13 (f23 f24 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f13 (f23 f24 (f13 f25 ?v0)) (f13 f25 ?v1)) (f13 f25 (f13 (f23 f24 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f4 (f5 f7 (f11 f12 ?v0)) (f11 f12 ?v1)) (f11 f12 (f13 (f23 f24 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f13 f25 (f13 (f23 f24 ?v0) ?v1)) (f13 (f23 f24 (f13 f25 ?v0)) (f13 f25 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f11 f12 (f13 (f23 f24 ?v0) ?v1)) (f4 (f5 f7 (f11 f12 ?v0)) (f11 f12 ?v1)))))
(assert (forall ((?v0 S8)) (= (= (f13 f15 ?v0) f16) false)))
(assert (forall ((?v0 S8)) (= (= f16 (f13 f15 ?v0)) false)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f13 f15 ?v0) (f13 f14 ?v1)) false)))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f13 f14 ?v0) (f13 f15 ?v1)) false)))
(assert (forall ((?v0 S8)) (= (= (f13 f14 ?v0) f16) (= ?v0 f16))))
(assert (forall ((?v0 S8)) (= (= f16 (f13 f14 ?v0)) (= f16 ?v0))))
(assert (= (f13 f14 f16) f16))
(assert (forall ((?v0 S2) (?v1 S8) (?v2 S2)) (let ((?v_0 (f11 f12 ?v1))) (let ((?v_1 (f4 (f5 f7 ?v2) ?v_0))) (= (= (f3 (f4 (f5 f6 ?v0) ?v_0) ?v2) f1) (ite (= (f3 f22 ?v_0) f1) (= (f3 ?v0 ?v_1) f1) (ite (= (f3 ?v_0 f22) f1) (= (f3 ?v_1 ?v0) f1) (= (f3 f22 ?v2) f1))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S8)) (let ((?v_0 (f11 f12 ?v2))) (let ((?v_1 (f4 (f5 f7 ?v_0) ?v1))) (= (= (f3 (f4 (f5 f6 ?v0) ?v1) ?v_0) f1) (ite (= (f3 f22 ?v1) f1) (= (f3 ?v0 ?v_1) f1) (ite (= (f3 ?v1 f22) f1) (= (f3 ?v_1 ?v0) f1) (= (f3 f22 ?v_0) f1))))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f12 ?v0))) (let ((?v_1 (f4 (f5 f7 ?v_0) ?v2))) (= (= (f3 ?v_0 (f4 (f5 f6 ?v1) ?v2)) f1) (ite (= (f3 f22 ?v2) f1) (= (f3 ?v_1 ?v1) f1) (ite (= (f3 ?v2 f22) f1) (= (f3 ?v1 ?v_1) f1) (= (f3 ?v_0 f22) f1))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S8)) (let ((?v_0 (f11 f12 ?v2))) (let ((?v_1 (f4 (f5 f7 ?v0) ?v_0))) (= (= (f3 ?v0 (f4 (f5 f6 ?v1) ?v_0)) f1) (ite (= (f3 f22 ?v_0) f1) (= (f3 ?v_1 ?v1) f1) (ite (= (f3 ?v_0 f22) f1) (= (f3 ?v1 ?v_1) f1) (= (f3 ?v0 f22) f1))))))))
(assert (forall ((?v0 S6)) (= (= (f3 f22 (f8 f9 ?v0)) f1) (= (f19 (f20 f21) ?v0) f1))))
(assert (forall ((?v0 S6)) (=> (= (f19 (f20 ?v0) f21) f1) false)))
(assert (= (f19 (f20 f21) (f31 f32 (f13 f14 (f13 f15 f16)))) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v2))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v2 f22) f1) (=> (= (f3 f22 (f4 (f5 f7 ?v0) ?v1)) f1) (= (f3 (f4 ?v_0 ?v0) (f4 ?v_0 ?v1)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v2))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 f22 ?v2) f1) (=> (= (f3 f22 (f4 (f5 f7 ?v1) ?v0)) f1) (= (f3 (f4 ?v_0 ?v1) (f4 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 f22) f1) (= (= (f3 (f4 (f5 f6 ?v1) ?v0) ?v2) f1) (= (f3 (f4 (f5 f7 ?v2) ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 f22) f1) (= (= (f3 ?v1 (f4 (f5 f6 ?v2) ?v0)) f1) (= (f3 ?v2 (f4 (f5 f7 ?v1) ?v0)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 f22 ?v0) f1) (=> (= (f3 (f4 (f5 f7 ?v1) ?v0) ?v2) f1) (= (f3 ?v1 (f4 (f5 f6 ?v2) ?v0)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 f22 ?v0) f1) (=> (= (f3 ?v1 (f4 (f5 f7 ?v2) ?v0)) f1) (= (f3 (f4 (f5 f6 ?v1) ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 f22 ?v0) f1) (= (= (f3 (f4 (f5 f6 ?v1) ?v0) ?v2) f1) (= (f3 ?v1 (f4 (f5 f7 ?v2) ?v0)) f1)))))
(assert (forall ((?v0 S8)) (= (f13 f25 ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f28 (f29 f30 ?v0) ?v1) (f28 (f29 f30 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f13 (f23 f24 ?v0) ?v1) (f13 (f23 f24 ?v1) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (or (= (f27 ?v0 ?v1) f1) (or (= ?v0 ?v1) (= (f27 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f13 (f23 f24 (f13 f25 ?v0)) (f13 f25 ?v1)) (f13 f25 (f13 (f23 f24 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f27 (f13 f25 ?v0) (f13 f25 ?v1)) f1) (= (f27 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f29 f30 ?v0))) (= (f28 (f29 f30 (f28 ?v_0 ?v1)) ?v2) (f28 ?v_0 (f28 (f29 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f23 f24 ?v0))) (= (f13 (f23 f24 (f13 ?v_0 ?v1)) ?v2) (f13 ?v_0 (f13 (f23 f24 ?v1) ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (let ((?v_0 (f23 f24 ?v2))) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f27 f26 ?v2) f1) (= (f27 (f13 ?v_0 ?v0) (f13 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f28 (f29 f30 ?v0) ?v1) (f28 (f29 f30 ?v2) ?v1)) (or (= ?v0 ?v2) (= ?v1 f21)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f29 f30 ?v0))) (= (= (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) (or (= ?v1 ?v2) (= ?v0 f21))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f28 (f29 f30 ?v0) ?v1) f21) (or (= ?v0 f21) (= ?v1 f21)))))
(assert (forall ((?v0 S6)) (= (f28 (f29 f30 ?v0) f21) f21)))
(assert (forall ((?v0 S6)) (= (f28 (f29 f30 f21) ?v0) f21)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S15)) (let ((?v_0 (= (f19 (f33 ?v2 ?v1) ?v0) f1))) (=> (=> (= (f19 (f20 ?v0) ?v1) f1) ?v_0) (=> (=> (= ?v0 ?v1) ?v_0) (=> (=> (= (f19 (f20 ?v1) ?v0) f1) ?v_0) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f19 (f20 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f19 (f20 ?v0) ?v1) f1) (not (= ?v1 ?v0)))))
(assert (forall ((?v0 S6)) (=> (= (f19 (f20 ?v0) ?v0) f1) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f19 (f20 ?v0) ?v1) f1) false) (=> (=> (= (f19 (f20 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (not (= ?v0 ?v1)) (or (= (f19 (f20 ?v0) ?v1) f1) (= (f19 (f20 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S6)) (not (= (f19 (f20 ?v0) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 ?v0) ?v1) (f4 (f5 f7 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (f4 (f5 f7 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f8 f9 ?v0) (f8 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (f4 (f5 f7 (f4 (f5 f6 ?v0) ?v1)) (f4 (f5 f6 ?v2) ?v3)) (f4 (f5 f6 (f4 (f5 f7 ?v0) ?v2)) (f4 (f5 f7 ?v1) ?v3)))))
(assert (forall ((?v0 S6)) (=> (=> (= ?v0 f21) false) (= (f19 (f20 f21) ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f29 f30 ?v2))) (=> (= (f19 (f20 ?v0) ?v1) f1) (=> (= (f19 (f20 f21) ?v2) f1) (= (f19 (f20 (f28 ?v_0 ?v0)) (f28 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f19 (f20 ?v0) ?v1) f1) (=> (= (f19 (f20 f21) ?v2) f1) (= (f19 (f20 (f28 (f29 f30 ?v0) ?v2)) (f28 (f29 f30 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f19 (f20 ?v0) ?v1) f1) (not (= ?v1 f21)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f19 (f20 (f28 (f29 f30 ?v0) ?v1)) (f28 (f29 f30 ?v2) ?v1)) f1) (and (= (f19 (f20 f21) ?v1) f1) (= (f19 (f20 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f29 f30 ?v0))) (= (= (f19 (f20 (f28 ?v_0 ?v1)) (f28 ?v_0 ?v2)) f1) (and (= (f19 (f20 f21) ?v0) f1) (= (f19 (f20 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S6)) (= (= (f19 (f20 ?v0) f21) f1) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f20 f21))) (= (= (f19 ?v_0 (f28 (f29 f30 ?v0) ?v1)) f1) (and (= (f19 ?v_0 ?v0) f1) (= (f19 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S6)) (= (not (= ?v0 f21)) (= (f19 (f20 f21) ?v0) f1))))
(assert (forall ((?v0 S6)) (not (= (f19 (f20 ?v0) f21) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (not (= ?v0 f22)) (= (= (f4 (f5 f7 ?v1) ?v0) (f4 (f5 f7 ?v2) ?v0)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (=> (not (= ?v0 f22)) (= (= (f4 ?v_0 ?v1) (f4 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (f4 (f5 f6 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v0)) (f4 (f5 f6 ?v1) ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f8 f9 (f28 (f29 f30 ?v0) ?v1)) (f4 (f5 f7 (f8 f9 ?v0)) (f8 f9 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 f22 (f4 (f5 f6 ?v0) ?v1)) f1) (or (and (= (f3 f22 ?v0) f1) (= (f3 f22 ?v1) f1)) (and (= (f3 ?v0 f22) f1) (= (f3 ?v1 f22) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 (f5 f6 ?v0) ?v1) f22) f1) (or (and (= (f3 f22 ?v0) f1) (= (f3 ?v1 f22) f1)) (and (= (f3 ?v0 f22) f1) (= (f3 f22 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 (f5 f6 ?v0) ?v1) (f4 (f5 f6 ?v2) ?v1)) f1) (and (=> (= (f3 f22 ?v1) f1) (= (f3 ?v0 ?v2) f1)) (and (=> (= (f3 ?v1 f22) f1) (= (f3 ?v2 ?v0) f1)) (not (= ?v1 f22)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f22 ?v0) f1) (=> (= (f3 f22 ?v1) f1) (= (f3 f22 (f4 (f5 f6 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f22 ?v0) f1) (=> (= (f3 ?v1 f22) f1) (= (f3 (f4 (f5 f6 ?v0) ?v1) f22) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 f22) f1) (=> (= (f3 f22 ?v1) f1) (= (f3 (f4 (f5 f6 ?v0) ?v1) f22) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 f22) f1) (=> (= (f3 ?v1 f22) f1) (= (f3 f22 (f4 (f5 f6 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 f22 ?v2) f1) (= (f3 (f4 (f5 f6 ?v0) ?v2) (f4 (f5 f6 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v2 f22) f1) (= (f3 (f4 (f5 f6 ?v1) ?v2) (f4 (f5 f6 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= ?v0 (f4 (f5 f6 ?v1) ?v2)) (ite (not (= ?v2 f22)) (= (f4 (f5 f7 ?v0) ?v2) ?v1) (= ?v0 f22)))))
(check-sat)
(exit)
