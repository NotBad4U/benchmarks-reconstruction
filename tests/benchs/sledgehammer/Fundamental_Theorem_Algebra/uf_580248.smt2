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
(declare-sort S16 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 () S2)
(declare-fun f7 () S4)
(declare-fun f8 () S4)
(declare-fun f9 () S4)
(declare-fun f10 () S3)
(declare-fun f11 () S3)
(declare-fun f12 (S5 S6) S3)
(declare-fun f13 () S5)
(declare-fun f14 (S7 S6) S6)
(declare-fun f15 () S7)
(declare-fun f16 () S7)
(declare-fun f17 () S6)
(declare-fun f18 () S3)
(declare-fun f19 (S8 S6) S7)
(declare-fun f20 () S8)
(declare-fun f21 () S7)
(declare-fun f22 () S8)
(declare-fun f23 (S10 S9) S9)
(declare-fun f24 (S11 S9) S10)
(declare-fun f25 () S11)
(declare-fun f26 (S12 S6) S9)
(declare-fun f27 () S12)
(declare-fun f28 () S11)
(declare-fun f29 () S6)
(declare-fun f30 () S9)
(declare-fun f31 () S8)
(declare-fun f32 (S3 S3) S1)
(declare-fun f33 (S13 S9) S3)
(declare-fun f34 (S14 S3) S13)
(declare-fun f35 () S14)
(declare-fun f36 (S6 S6) S1)
(declare-fun f37 (S15 S9) S6)
(declare-fun f38 (S16 S6) S15)
(declare-fun f39 () S16)
(declare-fun f40 (S9 S9) S1)
(assert (not (= f1 f2)))
(assert (let ((?v_1 (f3 f6 (f3 (f4 f9 (f3 (f4 f8 f10) f10)) (f3 (f4 f8 f11) f11))))) (let ((?v_0 (f3 (f4 f9 ?v_1) f10)) (?v_3 (f12 f13 (f14 f15 (f14 f15 (f14 f16 f17))))) (?v_2 (f3 (f4 f5 ?v_1) f10))) (not (= (f3 (f4 f5 (f3 f6 (f3 (f4 f7 (f3 (f4 f8 ?v_0) ?v_0)) ?v_3))) (f3 f6 (f3 (f4 f7 (f3 (f4 f8 ?v_2) ?v_2)) ?v_3))) f10)))))
(assert (let ((?v_0 (f3 (f4 f9 (f3 f6 (f3 (f4 f9 (f3 (f4 f8 f10) f10)) (f3 (f4 f8 f11) f11)))) f10)) (?v_1 (f14 f15 (f14 f16 f17)))) (= (f3 f6 (f3 (f4 f7 (f3 (f4 f8 ?v_0) ?v_0)) (f12 f13 (f14 f15 ?v_1)))) (f3 (f4 f7 ?v_0) (f12 f13 ?v_1)))))
(assert (let ((?v_1 (f14 f15 (f14 f16 f17))) (?v_0 (f3 (f4 f5 (f3 f6 (f3 (f4 f9 (f3 (f4 f8 f10) f10)) (f3 (f4 f8 f11) f11)))) f10))) (= (f3 f6 (f3 (f4 f7 (f3 (f4 f8 ?v_0) ?v_0)) (f12 f13 (f14 f15 ?v_1)))) (f3 (f4 f7 ?v_0) (f12 f13 ?v_1)))))
(assert (let ((?v_0 (f3 (f4 f9 (f3 f6 (f3 (f4 f9 (f3 (f4 f8 f10) f10)) (f3 (f4 f8 f11) f11)))) f10)) (?v_1 (f14 f15 (f14 f16 f17)))) (= (f3 f6 (f3 (f4 f7 (f3 (f4 f8 ?v_0) ?v_0)) (f12 f13 (f14 f15 ?v_1)))) (f3 (f4 f7 ?v_0) (f12 f13 ?v_1)))))
(assert (let ((?v_1 (f14 f15 (f14 f16 f17))) (?v_0 (f3 (f4 f5 (f3 f6 (f3 (f4 f9 (f3 (f4 f8 f10) f10)) (f3 (f4 f8 f11) f11)))) f10))) (= (f3 f6 (f3 (f4 f7 (f3 (f4 f8 ?v_0) ?v_0)) (f12 f13 (f14 f15 ?v_1)))) (f3 (f4 f7 ?v_0) (f12 f13 ?v_1)))))
(assert (not (= f11 f18)))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f12 f13 (f14 f15 (f14 f16 f17))))) (= (f3 (f4 f5 (f3 (f4 f7 (f3 (f4 f9 ?v0) ?v1)) ?v_0)) ?v0) (f3 (f4 f7 (f3 (f4 f5 ?v1) ?v0)) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f12 f13 (f14 f15 (f14 f16 f17))))) (= (f3 (f4 f5 (f3 (f4 f7 (f3 (f4 f9 ?v0) ?v1)) ?v_0)) ?v1) (f3 (f4 f7 (f3 (f4 f5 ?v0) ?v1)) ?v_0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f3 (f4 f7 ?v0) (f12 f13 (f14 f15 (f14 f16 f17)))))) (= (f3 (f4 f9 ?v_0) ?v_0) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f4 f7 ?v1)) (?v_0 (f4 f8 (f12 f13 (f14 f15 (f14 f16 f17)))))) (= (= ?v0 (f3 ?v_1 (f3 ?v_0 ?v2))) (= (f3 ?v_0 ?v0) (f3 ?v_1 ?v2))))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 ?v0) (f12 f13 (f14 f15 (f14 f16 f17)))) (f3 (f4 f9 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 ?v0) (f14 f21 (f14 f15 (f14 f16 f17)))) (f14 (f19 f22 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 ?v0) (f12 f13 (f14 f15 (f14 f16 f17)))) (f3 (f4 f9 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 ?v0) (f14 f21 (f14 f15 (f14 f16 f17)))) (f14 (f19 f22 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f23 (f24 f25 ?v0) (f26 f27 (f14 f15 (f14 f16 f17)))) (f23 (f24 f28 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) ?v0) (f3 (f4 f9 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 (f14 f21 (f14 f15 (f14 f16 f17)))) ?v0) (f14 (f19 f22 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) ?v0) (f3 (f4 f9 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 (f14 f21 (f14 f15 (f14 f16 f17)))) ?v0) (f14 (f19 f22 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f23 (f24 f25 (f26 f27 (f14 f15 (f14 f16 f17)))) ?v0) (f23 (f24 f28 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f7 ?v0) (f12 f13 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f7 ?v0) (f12 f13 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 ?v0) (f12 f13 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 ?v0) (f14 f21 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 (f12 f13 (f14 f16 f17))) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 (f14 f21 (f14 f16 f17))) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f19 f22 ?v0) f17) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f19 f22 f17) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f22 (f14 f15 ?v0)) (f14 f15 ?v1)) (f14 f15 (f14 (f19 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (f14 f15 ?v0) (f14 (f19 f22 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 f17) ?v0) f17)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f20 (f14 f15 ?v0)) ?v1) (f14 f15 (f14 (f19 f20 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f9 ?v0) ?v0) f18) (= ?v0 f18))))
(assert (forall ((?v0 S6)) (= (= (f14 (f19 f22 ?v0) ?v0) f29) (= ?v0 f29))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f20 (f14 f16 ?v0)) ?v1) (f14 (f19 f22 (f14 f15 (f14 (f19 f20 ?v0) ?v1))) ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f22 (f14 f16 ?v0)) (f14 f15 ?v1)) (f14 f16 (f14 (f19 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f22 (f14 f15 ?v0)) (f14 f16 ?v1)) (f14 f16 (f14 (f19 f22 ?v0) ?v1)))))
(assert (= (f26 f27 f17) f30))
(assert (= (f12 f13 f17) f18))
(assert (= (f14 f21 f17) f29))
(assert (= (f12 f13 f17) f18))
(assert (= (f14 f21 f17) f29))
(assert (forall ((?v0 S6)) (let ((?v_0 (f12 f13 ?v0))) (= (f12 f13 (f14 f15 ?v0)) (f3 (f4 f9 (f3 (f4 f9 f18) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f14 f21 ?v0))) (= (f14 f21 (f14 f15 ?v0)) (f14 (f19 f22 (f14 (f19 f22 f29) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S3)) (let ((?v_0 (f12 f13 ?v1))) (= (= (f3 (f4 f7 ?v0) ?v_0) ?v2) (ite (not (= ?v_0 f18)) (= ?v0 (f3 (f4 f8 ?v2) ?v_0)) (= ?v2 f18))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6)) (let ((?v_0 (f12 f13 ?v2))) (= (= (f3 (f4 f7 ?v0) ?v1) ?v_0) (ite (not (= ?v1 f18)) (= ?v0 (f3 (f4 f8 ?v_0) ?v1)) (= ?v_0 f18))))))
(assert (forall ((?v0 S6) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f13 ?v0))) (= (= ?v_0 (f3 (f4 f7 ?v1) ?v2)) (ite (not (= ?v2 f18)) (= (f3 (f4 f8 ?v_0) ?v2) ?v1) (= ?v_0 f18))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6)) (let ((?v_0 (f12 f13 ?v2))) (= (= ?v0 (f3 (f4 f7 ?v1) ?v_0)) (ite (not (= ?v_0 f18)) (= (f3 (f4 f8 ?v0) ?v_0) ?v1) (= ?v0 f18))))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f7 ?v0) (f12 f13 f17)) f18)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f12 f13 ?v0) (f12 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 f21 ?v0) (f14 f21 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S3)) (let ((?v_0 (f12 f13 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f14 f21 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S9)) (let ((?v_0 (f26 f27 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 f16 ?v0) (f14 f16 ?v1)) (= ?v0 ?v1))))
(assert (= (= f17 f17) true))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 f15 ?v0) (f14 f15 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (= (f3 (f4 f8 (f12 f13 ?v0)) (f3 (f4 f8 (f12 f13 ?v1)) ?v2)) (f3 (f4 f8 (f12 f13 (f14 (f19 f20 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f14 (f19 f20 (f14 f21 ?v0)) (f14 (f19 f20 (f14 f21 ?v1)) ?v2)) (f14 (f19 f20 (f14 f21 (f14 (f19 f20 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f3 (f4 f8 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f14 (f19 f20 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f20 (f14 f21 ?v0)) (f14 f21 ?v1)) (f14 f21 (f14 (f19 f20 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f12 f13 (f14 (f19 f20 ?v0) ?v1)) (f3 (f4 f8 (f12 f13 ?v0)) (f12 f13 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 f21 (f14 (f19 f20 ?v0) ?v1)) (f14 (f19 f20 (f14 f21 ?v0)) (f14 f21 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (= (f3 (f4 f9 (f12 f13 ?v0)) (f3 (f4 f9 (f12 f13 ?v1)) ?v2)) (f3 (f4 f9 (f12 f13 (f14 (f19 f22 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f14 (f19 f22 (f14 f21 ?v0)) (f14 (f19 f22 (f14 f21 ?v1)) ?v2)) (f14 (f19 f22 (f14 f21 (f14 (f19 f22 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f3 (f4 f9 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f14 (f19 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f22 (f14 f21 ?v0)) (f14 f21 ?v1)) (f14 f21 (f14 (f19 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f12 f13 (f14 (f19 f22 ?v0) ?v1)) (f3 (f4 f9 (f12 f13 ?v0)) (f12 f13 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 f21 (f14 (f19 f22 ?v0) ?v1)) (f14 (f19 f22 (f14 f21 ?v0)) (f14 f21 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (f3 (f4 f5 (f3 (f4 f9 ?v0) ?v1)) (f3 (f4 f9 ?v2) ?v3)) (f3 (f4 f9 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v3)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (f14 (f19 f31 (f14 (f19 f22 ?v0) ?v1)) (f14 (f19 f22 ?v2) ?v3)) (f14 (f19 f22 (f14 (f19 f31 ?v0) ?v2)) (f14 (f19 f31 ?v1) ?v3)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f12 f13 (f14 (f19 f31 ?v0) ?v1)) (f3 (f4 f5 (f12 f13 ?v0)) (f12 f13 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 f21 (f14 (f19 f31 ?v0) ?v1)) (f14 (f19 f31 (f14 f21 ?v0)) (f14 f21 ?v1)))))
(assert (forall ((?v0 S6)) (= (= (f14 f16 ?v0) f17) false)))
(assert (forall ((?v0 S6)) (= (= f17 (f14 f16 ?v0)) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 f16 ?v0) (f14 f15 ?v1)) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 f15 ?v0) (f14 f16 ?v1)) false)))
(assert (forall ((?v0 S6)) (= (= (f14 f15 ?v0) f17) (= ?v0 f17))))
(assert (forall ((?v0 S6)) (= (= f17 (f14 f15 ?v0)) (= f17 ?v0))))
(assert (= (f14 f15 f17) f17))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6)) (let ((?v_0 (f12 f13 ?v2))) (= (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v1)) ?v_0) (f3 (f4 f9 (f3 (f4 f8 ?v0) ?v_0)) (f3 (f4 f8 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f14 f21 ?v2))) (= (f14 (f19 f20 (f14 (f19 f22 ?v0) ?v1)) ?v_0) (f14 (f19 f22 (f14 (f19 f20 ?v0) ?v_0)) (f14 (f19 f20 ?v1) ?v_0))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S6)) (let ((?v_0 (f26 f27 ?v2))) (= (f23 (f24 f25 (f23 (f24 f28 ?v0) ?v1)) ?v_0) (f23 (f24 f28 (f23 (f24 f25 ?v0) ?v_0)) (f23 (f24 f25 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f8 (f12 f13 ?v0)))) (= (f3 ?v_0 (f3 (f4 f9 ?v1) ?v2)) (f3 (f4 f9 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f19 f20 (f14 f21 ?v0)))) (= (f14 ?v_0 (f14 (f19 f22 ?v1) ?v2)) (f14 (f19 f22 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S9)) (let ((?v_0 (f24 f25 (f26 f27 ?v0)))) (= (f23 ?v_0 (f23 (f24 f28 ?v1) ?v2)) (f23 (f24 f28 (f23 ?v_0 ?v1)) (f23 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6)) (let ((?v_0 (f12 f13 ?v2))) (= (f3 (f4 f8 (f3 (f4 f5 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f8 ?v0) ?v_0)) (f3 (f4 f8 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f14 f21 ?v2))) (= (f14 (f19 f20 (f14 (f19 f31 ?v0) ?v1)) ?v_0) (f14 (f19 f31 (f14 (f19 f20 ?v0) ?v_0)) (f14 (f19 f20 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f8 (f12 f13 ?v0)))) (= (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2)) (f3 (f4 f5 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f19 f20 (f14 f21 ?v0)))) (= (f14 ?v_0 (f14 (f19 f31 ?v1) ?v2)) (f14 (f19 f31 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (= (f3 (f4 f9 (f12 f13 ?v0)) (f3 (f4 f5 (f12 f13 ?v1)) ?v2)) (f3 (f4 f5 (f12 f13 (f14 (f19 f22 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f14 (f19 f22 (f14 f21 ?v0)) (f14 (f19 f31 (f14 f21 ?v1)) ?v2)) (f14 (f19 f31 (f14 f21 (f14 (f19 f22 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 (f12 f13 f17)) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f19 f22 (f14 f21 f17)) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 ?v0) (f12 f13 f17)) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f19 f22 ?v0) (f14 f21 f17)) ?v0)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f3 ?v0 ?v1)) (?v_1 (f4 f5 (f3 ?v0 ?v2)))) (let ((?v_2 (f4 f8 (f3 (f4 f7 (f3 ?v_1 ?v_0)) (f3 (f4 f5 ?v2) ?v1))))) (= (f3 (f4 f5 ?v_0) (f3 ?v_2 ?v1)) (f3 ?v_1 (f3 ?v_2 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f4 f8 ?v0))) (= (f3 (f4 f7 (f3 (f4 f5 (f3 ?v_0 ?v1)) (f3 (f4 f8 ?v2) ?v3))) ?v4) (f3 (f4 f9 (f3 ?v_0 (f3 (f4 f7 (f3 (f4 f5 ?v1) ?v3)) ?v4))) (f3 (f4 f8 (f3 (f4 f7 (f3 (f4 f5 ?v0) ?v2)) ?v4)) ?v3))))))
(assert (= (f32 f18 (f3 (f4 f7 (f3 (f4 f5 (f3 f6 (f3 (f4 f9 (f3 (f4 f8 f10) f10)) (f3 (f4 f8 f11) f11)))) f10)) (f12 f13 (f14 f15 (f14 f16 f17))))) f1))
(assert (= (f32 f18 (f3 (f4 f7 (f3 (f4 f9 (f3 f6 (f3 (f4 f9 (f3 (f4 f8 f10) f10)) (f3 (f4 f8 f11) f11)))) f10)) (f12 f13 (f14 f15 (f14 f16 f17))))) f1))
(assert (let ((?v_0 (f14 f15 (f14 f16 f17))) (?v_1 (f3 (f4 f5 (f3 f6 (f3 (f4 f9 (f3 (f4 f8 f10) f10)) (f3 (f4 f8 f11) f11)))) f10))) (= (f3 f6 (f3 (f4 f7 (f33 (f34 f35 ?v_1) (f26 f27 ?v_0))) (f12 f13 (f14 f15 ?v_0)))) (f3 (f4 f7 ?v_1) (f12 f13 ?v_0)))))
(assert (let ((?v_1 (f3 (f4 f9 (f3 f6 (f3 (f4 f9 (f3 (f4 f8 f10) f10)) (f3 (f4 f8 f11) f11)))) f10)) (?v_0 (f14 f15 (f14 f16 f17)))) (= (f3 f6 (f3 (f4 f7 (f33 (f34 f35 ?v_1) (f26 f27 ?v_0))) (f12 f13 (f14 f15 ?v_0)))) (f3 (f4 f7 ?v_1) (f12 f13 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f32 f18 (f3 (f4 f7 (f3 (f4 f5 (f3 f6 (f3 (f4 f9 (f3 (f4 f8 ?v0) ?v0)) (f3 (f4 f8 ?v1) ?v1)))) ?v0)) (f12 f13 (f14 f15 (f14 f16 f17))))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f32 f18 (f3 (f4 f7 (f3 (f4 f9 (f3 f6 (f3 (f4 f9 (f3 (f4 f8 ?v0) ?v0)) (f3 (f4 f8 ?v1) ?v1)))) ?v0)) (f12 f13 (f14 f15 (f14 f16 f17))))) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (not (= ?v0 f18)) (=> (not (= ?v1 f18)) (= (f3 (f4 f5 (f3 (f4 f7 ?v2) ?v0)) (f3 (f4 f7 ?v3) ?v1)) (f3 (f4 f7 (f3 (f4 f5 (f3 (f4 f8 ?v2) ?v1)) (f3 (f4 f8 ?v3) ?v0))) (f3 (f4 f8 ?v0) ?v1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (not (= ?v0 f18)) (= (f3 (f4 f5 (f3 (f4 f7 ?v1) ?v0)) ?v2) (f3 (f4 f7 (f3 (f4 f5 ?v1) (f3 (f4 f8 ?v0) ?v2))) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (not (= ?v0 f18)) (= (f3 (f4 f5 ?v1) (f3 (f4 f7 ?v2) ?v0)) (f3 (f4 f7 (f3 (f4 f5 (f3 (f4 f8 ?v0) ?v1)) ?v2)) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (not (= ?v0 f18)) (=> (not (= ?v1 f18)) (= (f3 (f4 f9 (f3 (f4 f7 ?v2) ?v0)) (f3 (f4 f7 ?v3) ?v1)) (f3 (f4 f7 (f3 (f4 f9 (f3 (f4 f8 ?v2) ?v1)) (f3 (f4 f8 ?v3) ?v0))) (f3 (f4 f8 ?v0) ?v1)))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f14 f15 (f14 f16 f17)))) (let ((?v_1 (f26 f27 ?v_0))) (= (f3 (f4 f7 (f33 (f34 f35 ?v0) ?v_1)) (f12 f13 (f14 f15 ?v_0))) (f33 (f34 f35 (f3 (f4 f7 ?v0) (f12 f13 ?v_0))) ?v_1))))))
(assert (forall ((?v0 S6)) (= (f14 (f19 f22 f29) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f19 f22 ?v0) f29) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f22 ?v0) ?v1) (f14 (f19 f22 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f20 ?v0) ?v1) (f14 (f19 f20 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f19 f22 ?v0)) (?v_0 (f19 f22 ?v1))) (= (f14 ?v_1 (f14 ?v_0 ?v2)) (f14 ?v_0 (f14 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f19 f20 ?v0))) (= (f14 ?v_0 (f14 (f19 f22 ?v1) ?v2)) (f14 (f19 f22 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f19 f20 ?v0))) (= (f14 ?v_0 (f14 (f19 f31 ?v1) ?v2)) (f14 (f19 f31 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f22 (f14 f21 ?v0)) (f14 f21 ?v1)) (f14 f21 (f14 (f19 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f20 (f14 f21 ?v0)) (f14 f21 ?v1)) (f14 f21 (f14 (f19 f20 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f19 f22 ?v0))) (= (f14 (f19 f22 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f19 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f19 f20 ?v0))) (= (f14 (f19 f20 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f19 f20 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f14 (f19 f20 (f14 (f19 f22 ?v0) ?v1)) ?v2) (f14 (f19 f22 (f14 (f19 f20 ?v0) ?v2)) (f14 (f19 f20 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f14 (f19 f20 (f14 (f19 f31 ?v0) ?v1)) ?v2) (f14 (f19 f31 (f14 (f19 f20 ?v0) ?v2)) (f14 (f19 f20 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f32 (f12 f13 ?v0) (f12 f13 ?v1)) f1) (= (f36 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f36 (f14 f21 ?v0) (f14 f21 ?v1)) f1) (= (f36 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6)) (= (f14 (f19 f31 ?v0) f17) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f31 (f14 f15 ?v0)) (f14 f15 ?v1)) (f14 f15 (f14 (f19 f31 ?v0) ?v1)))))
(assert (= f17 f29))
(assert (= f29 (f14 f21 f17)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f32 ?v0 ?v1) f1) (=> (= (f32 ?v2 f18) f1) (= (f32 (f3 (f4 f7 ?v1) ?v2) (f3 (f4 f7 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f32 ?v0 ?v1) f1) (=> (= (f32 f18 ?v2) f1) (= (f32 (f3 (f4 f7 ?v0) ?v2) (f3 (f4 f7 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f32 (f3 (f4 f7 ?v0) ?v1) f18) f1) (or (and (= (f32 f18 ?v0) f1) (= (f32 ?v1 f18) f1)) (and (= (f32 ?v0 f18) f1) (= (f32 f18 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f32 f18 (f3 (f4 f7 ?v0) ?v1)) f1) (or (and (= (f32 f18 ?v0) f1) (= (f32 f18 ?v1) f1)) (and (= (f32 ?v0 f18) f1) (= (f32 ?v1 f18) f1))))))
(assert (forall ((?v0 S6)) (= (= (f32 f18 (f12 f13 ?v0)) f1) (= (f36 f17 ?v0) f1))))
(assert (forall ((?v0 S6)) (= (= (f36 f29 (f14 f21 ?v0)) f1) (= (f36 f17 ?v0) f1))))
(assert (forall ((?v0 S6)) (= (= (f32 (f12 f13 ?v0) f18) f1) (= (f36 ?v0 f17) f1))))
(assert (forall ((?v0 S6)) (= (= (f36 (f14 f21 ?v0) f29) f1) (= (f36 ?v0 f17) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f31 (f14 f16 ?v0)) (f14 f15 ?v1)) (f14 f16 (f14 (f19 f31 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f31 (f14 f16 ?v0)) (f14 f16 ?v1)) (f14 f15 (f14 (f19 f31 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f19 f31 f17))) (= (f14 ?v_0 (f14 f15 ?v0)) (f14 f15 (f14 ?v_0 ?v0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (f3 (f4 f8 (f3 (f4 f7 ?v0) ?v1)) (f3 (f4 f7 ?v2) ?v3)) (f3 (f4 f7 (f3 (f4 f8 ?v0) ?v2)) (f3 (f4 f8 ?v1) ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= ?v0 (f3 (f4 f7 ?v1) ?v2)) (ite (not (= ?v2 f18)) (= (f3 (f4 f8 ?v0) ?v2) ?v1) (= ?v0 f18)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f3 (f4 f7 ?v0) ?v1) ?v2) (ite (not (= ?v1 f18)) (= ?v0 (f3 (f4 f8 ?v2) ?v1)) (= ?v2 f18)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (not (= ?v0 f18)) (= (f3 (f4 f7 (f3 (f4 f8 ?v1) ?v0)) (f3 (f4 f8 ?v2) ?v0)) (f3 (f4 f7 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f8 ?v0))) (=> (not (= ?v0 f18)) (= (f3 (f4 f7 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2)) (f3 (f4 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (not (= ?v0 f18)) (=> (not (= ?v1 f18)) (= (= (f3 (f4 f7 ?v2) ?v0) (f3 (f4 f7 ?v3) ?v1)) (= (f3 (f4 f8 ?v2) ?v1) (f3 (f4 f8 ?v3) ?v0)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (not (= ?v0 f18)) (= (f3 (f4 f9 ?v1) (f3 (f4 f7 ?v2) ?v0)) (f3 (f4 f7 (f3 (f4 f9 ?v2) (f3 (f4 f8 ?v1) ?v0))) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (not (= ?v0 f18)) (= (f3 (f4 f9 ?v1) (f3 (f4 f7 ?v2) ?v0)) (f3 (f4 f7 (f3 (f4 f9 (f3 (f4 f8 ?v0) ?v1)) ?v2)) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (not (= ?v0 f18)) (= (f3 (f4 f9 (f3 (f4 f7 ?v1) ?v0)) ?v2) (f3 (f4 f7 (f3 (f4 f9 ?v1) (f3 (f4 f8 ?v2) ?v0))) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (not (= ?v0 f18)) (= (f3 (f4 f9 (f3 (f4 f7 ?v1) ?v0)) ?v2) (f3 (f4 f7 (f3 (f4 f9 ?v1) (f3 (f4 f8 ?v0) ?v2))) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f26 f27 (f14 f15 (f14 f16 f17))))) (= (f32 f18 (f3 f6 (f3 (f4 f8 (f3 (f4 f9 (f33 (f34 f35 ?v0) ?v_0)) (f33 (f34 f35 ?v1) ?v_0))) (f3 (f4 f9 (f33 (f34 f35 ?v2) ?v_0)) (f33 (f34 f35 ?v3) ?v_0))))) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f26 f27 (f14 f15 (f14 f16 f17))))) (= (f32 f18 (f3 f6 (f3 (f4 f9 (f33 (f34 f35 ?v0) ?v_0)) (f33 (f34 f35 ?v1) ?v_0)))) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f14 f15 (f14 f16 f17)))) (let ((?v_0 (f26 f27 ?v_1))) (= (f33 (f34 f35 (f3 (f4 f5 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f9 (f33 (f34 f35 ?v0) ?v_0)) (f33 (f34 f35 ?v1) ?v_0))) (f3 (f4 f8 (f3 (f4 f8 (f12 f13 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_1 (f14 f15 (f14 f16 f17)))) (let ((?v_0 (f26 f27 ?v_1))) (= (f37 (f38 f39 (f14 (f19 f31 ?v0) ?v1)) ?v_0) (f14 (f19 f31 (f14 (f19 f22 (f37 (f38 f39 ?v0) ?v_0)) (f37 (f38 f39 ?v1) ?v_0))) (f14 (f19 f20 (f14 (f19 f20 (f14 f21 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f26 f27 (f14 f15 (f14 f16 f17))))) (let ((?v_1 (f3 (f4 f8 (f3 (f4 f9 (f33 (f34 f35 ?v0) ?v_0)) (f33 (f34 f35 ?v1) ?v_0))) (f3 (f4 f9 (f33 (f34 f35 ?v2) ?v_0)) (f33 (f34 f35 ?v3) ?v_0))))) (= (f33 (f34 f35 (f3 f6 ?v_1)) ?v_0) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f26 f27 (f14 f15 (f14 f16 f17))))) (=> (= (f3 f6 (f3 (f4 f9 (f33 (f34 f35 ?v0) ?v_0)) (f33 (f34 f35 ?v1) ?v_0))) ?v0) (= ?v1 f18)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f26 f27 (f14 f15 (f14 f16 f17))))) (=> (= (f3 f6 (f3 (f4 f9 (f33 (f34 f35 ?v0) ?v_0)) (f33 (f34 f35 ?v1) ?v_0))) ?v1) (= ?v0 f18)))))
(assert (forall ((?v0 S6)) (= (f36 ?v0 ?v0) f1)))
(assert (forall ((?v0 S6)) (= (f14 f21 ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (or (= (f36 ?v0 ?v1) f1) (= (f36 ?v1 ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f36 (f14 f21 ?v0) (f14 f21 ?v1)) f1) (= (f36 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f40 (f26 f27 ?v0) (f26 f27 ?v1)) f1) (ite (= (f36 ?v0 ?v1) f1) true (= (f36 ?v0 f17) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f36 ?v0 ?v1) f1) (=> (= (f36 ?v1 ?v2) f1) (= (f36 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f36 ?v0 ?v1) f1) (=> (= (f36 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S9)) (let ((?v_0 (f38 f39 ?v0))) (= (f37 ?v_0 (f23 (f24 f28 ?v1) ?v2)) (f14 (f19 f20 (f37 ?v_0 ?v1)) (f37 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f36 (f14 f16 ?v0) (f14 f16 ?v1)) f1) (= (f36 ?v0 ?v1) f1))))
(check-sat)
(exit)