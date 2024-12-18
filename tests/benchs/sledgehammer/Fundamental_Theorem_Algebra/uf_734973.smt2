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
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 (S3 S2) S2)
(declare-fun f5 (S4 S2) S3)
(declare-fun f6 () S4)
(declare-fun f7 () S4)
(declare-fun f8 (S5 S6) S2)
(declare-fun f9 () S5)
(declare-fun f10 (S7 S6) S6)
(declare-fun f11 () S7)
(declare-fun f12 () S7)
(declare-fun f13 () S6)
(declare-fun f14 (S8 S9) S2)
(declare-fun f15 (S10 S2) S8)
(declare-fun f16 () S10)
(declare-fun f17 () S2)
(declare-fun f18 (S11 S6) S9)
(declare-fun f19 () S11)
(declare-fun f20 () S2)
(declare-fun f21 () S2)
(declare-fun f22 (S12 S9) S6)
(declare-fun f23 (S13 S6) S12)
(declare-fun f24 () S13)
(declare-fun f25 () S6)
(declare-fun f26 (S14 S9) S9)
(declare-fun f27 (S15 S9) S14)
(declare-fun f28 () S15)
(declare-fun f29 () S9)
(declare-fun f30 (S16 S6) S7)
(declare-fun f31 () S16)
(declare-fun f32 () S7)
(declare-fun f33 () S15)
(declare-fun f34 () S16)
(declare-fun f35 (S6 S6) S1)
(declare-fun f36 () S15)
(declare-fun f37 () S3)
(declare-fun f38 () S6)
(declare-fun f39 () S7)
(declare-fun f40 (S9 S9) S1)
(assert (not (= f1 f2)))
(assert (not false))
(assert (let ((?v_0 (f10 f11 (f10 f12 f13)))) (let ((?v_1 (f5 f7 (f8 f9 (f10 f11 ?v_0)))) (?v_2 (f18 f19 ?v_0))) (= (f3 (f4 (f5 f6 (f4 ?v_1 (f14 (f15 f16 f17) ?v_2))) (f4 ?v_1 (f14 (f15 f16 f20) ?v_2))) (f4 (f5 f6 f21) f21)) f1))))
(assert (let ((?v_0 (f18 f19 (f10 f11 (f10 f12 f13))))) (= (f4 (f5 f6 (f14 (f15 f16 f17) ?v_0)) (f14 (f15 f16 f20) ?v_0)) f21)))
(assert (let ((?v_0 (f18 f19 (f10 f11 (f10 f12 f13))))) (= (f4 (f5 f6 (f14 (f15 f16 f17) ?v_0)) (f14 (f15 f16 f20) ?v_0)) f21)))
(assert (let ((?v_0 (f10 f11 (f10 f12 f13)))) (let ((?v_1 (f5 f7 (f8 f9 (f10 f11 ?v_0)))) (?v_2 (f18 f19 ?v_0))) (= (f3 (f4 (f5 f6 (f4 ?v_1 (f14 (f15 f16 f17) ?v_2))) (f4 ?v_1 (f14 (f15 f16 f20) ?v_2))) (f4 (f5 f6 f21) f21)) f1))))
(assert (let ((?v_0 (f10 f11 (f10 f12 f13)))) (= (f3 (f4 (f5 f7 (f8 f9 (f10 f11 ?v_0))) (f14 (f15 f16 f17) (f18 f19 ?v_0))) f21) f1)))
(assert (let ((?v_0 (f10 f11 (f10 f12 f13)))) (= (f3 (f4 (f5 f7 (f8 f9 (f10 f11 ?v_0))) (f14 (f15 f16 f20) (f18 f19 ?v_0))) f21) f1)))
(assert (= (f3 (f4 (f5 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f17) f21) f1))
(assert (= (f3 (f4 (f5 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f20) f21) f1))
(assert (= (f14 (f15 f16 f21) (f18 f19 (f10 f11 (f10 f12 f13)))) f21))
(assert (= (f22 (f23 f24 f25) (f18 f19 (f10 f11 (f10 f12 f13)))) f25))
(assert (= (f26 (f27 f28 f29) (f18 f19 (f10 f11 (f10 f12 f13)))) f29))
(assert (= (f4 (f5 f6 f21) f21) (f8 f9 (f10 f11 (f10 f12 f13)))))
(assert (= (f10 (f30 f31 f25) f25) (f10 f32 (f10 f11 (f10 f12 f13)))))
(assert (= (f4 (f5 f6 f21) f21) (f8 f9 (f10 f11 (f10 f12 f13)))))
(assert (= (f10 (f30 f31 f25) f25) (f10 f32 (f10 f11 (f10 f12 f13)))))
(assert (= (f26 (f27 f33 f29) f29) (f18 f19 (f10 f11 (f10 f12 f13)))))
(assert (forall ((?v0 S6)) (= (f4 (f5 f6 f21) (f8 f9 ?v0)) (f8 f9 (f10 (f30 f31 (f10 f12 f13)) ?v0)))))
(assert (forall ((?v0 S6)) (= (f10 (f30 f31 f25) (f10 f32 ?v0)) (f10 f32 (f10 (f30 f31 (f10 f12 f13)) ?v0)))))
(assert (forall ((?v0 S6)) (= (f4 (f5 f6 (f8 f9 ?v0)) f21) (f8 f9 (f10 (f30 f31 ?v0) (f10 f12 f13))))))
(assert (forall ((?v0 S6)) (= (f10 (f30 f31 (f10 f32 ?v0)) f25) (f10 f32 (f10 (f30 f31 ?v0) (f10 f12 f13))))))
(assert (= f21 (f8 f9 (f10 f12 f13))))
(assert (= f25 (f10 f32 (f10 f12 f13))))
(assert (= (f8 f9 (f10 f12 f13)) f21))
(assert (= (f10 f32 (f10 f12 f13)) f25))
(assert (= (f8 f9 (f10 f12 f13)) f21))
(assert (= (f10 f32 (f10 f12 f13)) f25))
(assert (= (f18 f19 (f10 f12 f13)) f29))
(assert (forall ((?v0 S6)) (= (f10 f12 ?v0) (f10 (f30 f31 (f10 (f30 f31 f25) ?v0)) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f30 f31 ?v0) ?v1) (f10 (f30 f31 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f30 f31 ?v0)) (?v_0 (f30 f31 ?v1))) (= (f10 ?v_1 (f10 ?v_0 ?v2)) (f10 ?v_0 (f10 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f30 f31 (f10 f32 ?v0)) (f10 f32 ?v1)) (f10 f32 (f10 (f30 f31 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f30 f31 ?v0))) (= (f10 (f30 f31 (f10 ?v_0 ?v1)) ?v2) (f10 ?v_0 (f10 (f30 f31 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S2)) (= (f4 (f5 f7 (f8 f9 ?v0)) (f4 (f5 f7 (f8 f9 ?v1)) ?v2)) (f4 (f5 f7 (f8 f9 (f10 (f30 f34 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f10 (f30 f34 (f10 f32 ?v0)) (f10 (f30 f34 (f10 f32 ?v1)) ?v2)) (f10 (f30 f34 (f10 f32 (f10 (f30 f34 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f4 (f5 f7 (f8 f9 ?v0)) (f8 f9 ?v1)) (f8 f9 (f10 (f30 f34 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f30 f34 (f10 f32 ?v0)) (f10 f32 ?v1)) (f10 f32 (f10 (f30 f34 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f8 f9 (f10 (f30 f34 ?v0) ?v1)) (f4 (f5 f7 (f8 f9 ?v0)) (f8 f9 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 f32 (f10 (f30 f34 ?v0) ?v1)) (f10 (f30 f34 (f10 f32 ?v0)) (f10 f32 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f3 (f8 f9 ?v0) (f8 f9 ?v1)) f1) (= (f35 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f35 (f10 f32 ?v0) (f10 f32 ?v1)) f1) (= (f35 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6)) (= (f10 (f30 f31 ?v0) f13) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f30 f31 f13) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f30 f31 (f10 f11 ?v0)) (f10 f11 ?v1)) (f10 f11 (f10 (f30 f31 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (f10 f11 ?v0) (f10 (f30 f31 ?v0) ?v0))))
(assert (= f25 (f10 f32 (f10 f12 f13))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f30 f31 (f10 f12 ?v0)) (f10 f11 ?v1)) (f10 f12 (f10 (f30 f31 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f30 f31 (f10 f11 ?v0)) (f10 f12 ?v1)) (f10 f12 (f10 (f30 f31 ?v0) ?v1)))))
(assert (= (f26 (f27 f33 f29) f29) (f18 f19 (f10 f11 (f10 f12 f13)))))
(assert (= (f18 f19 (f10 f12 f13)) f29))
(assert (= f29 (f18 f19 (f10 f12 f13))))
(assert (forall ((?v0 S6)) (= (= (f3 (f8 f9 ?v0) f21) f1) (= (f35 ?v0 (f10 f12 f13)) f1))))
(assert (forall ((?v0 S6)) (= (= (f35 (f10 f32 ?v0) f25) f1) (= (f35 ?v0 (f10 f12 f13)) f1))))
(assert (forall ((?v0 S6)) (= (= (f3 f21 (f8 f9 ?v0)) f1) (= (f35 (f10 f12 f13) ?v0) f1))))
(assert (forall ((?v0 S6)) (= (= (f35 f25 (f10 f32 ?v0)) f1) (= (f35 (f10 f12 f13) ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f8 f9 ?v0) (f8 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f10 f32 ?v0) (f10 f32 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S9)) (let ((?v_0 (f18 f19 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f10 f32 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f10 f12 ?v0) (f10 f12 ?v1)) (= ?v0 ?v1))))
(assert (= (= f13 f13) true))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f10 f11 ?v0) (f10 f11 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (let ((?v_0 (f8 f9 ?v2))) (= (f4 (f5 f7 (f4 (f5 f6 ?v0) ?v1)) ?v_0) (f4 (f5 f6 (f4 (f5 f7 ?v0) ?v_0)) (f4 (f5 f7 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f10 f32 ?v2))) (= (f10 (f30 f34 (f10 (f30 f31 ?v0) ?v1)) ?v_0) (f10 (f30 f31 (f10 (f30 f34 ?v0) ?v_0)) (f10 (f30 f34 ?v1) ?v_0))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S6)) (let ((?v_0 (f18 f19 ?v2))) (= (f26 (f27 f36 (f26 (f27 f33 ?v0) ?v1)) ?v_0) (f26 (f27 f33 (f26 (f27 f36 ?v0) ?v_0)) (f26 (f27 f36 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 (f8 f9 ?v0)))) (= (f4 ?v_0 (f4 (f5 f6 ?v1) ?v2)) (f4 (f5 f6 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f30 f34 (f10 f32 ?v0)))) (= (f10 ?v_0 (f10 (f30 f31 ?v1) ?v2)) (f10 (f30 f31 (f10 ?v_0 ?v1)) (f10 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S9)) (let ((?v_0 (f27 f36 (f18 f19 ?v0)))) (= (f26 ?v_0 (f26 (f27 f33 ?v1) ?v2)) (f26 (f27 f33 (f26 ?v_0 ?v1)) (f26 ?v_0 ?v2))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 (f8 f9 (f10 f12 f13))) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f30 f34 (f10 f32 (f10 f12 f13))) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) (f8 f9 (f10 f12 f13))) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f30 f34 ?v0) (f10 f32 (f10 f12 f13))) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S2)) (= (f4 (f5 f6 (f8 f9 ?v0)) (f4 (f5 f6 (f8 f9 ?v1)) ?v2)) (f4 (f5 f6 (f8 f9 (f10 (f30 f31 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f10 (f30 f31 (f10 f32 ?v0)) (f10 (f30 f31 (f10 f32 ?v1)) ?v2)) (f10 (f30 f31 (f10 f32 (f10 (f30 f31 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f4 (f5 f6 (f8 f9 ?v0)) (f8 f9 ?v1)) (f8 f9 (f10 (f30 f31 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f30 f31 (f10 f32 ?v0)) (f10 f32 ?v1)) (f10 f32 (f10 (f30 f31 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f8 f9 (f10 (f30 f31 ?v0) ?v1)) (f4 (f5 f6 (f8 f9 ?v0)) (f8 f9 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 f32 (f10 (f30 f31 ?v0) ?v1)) (f10 (f30 f31 (f10 f32 ?v0)) (f10 f32 ?v1)))))
(assert (forall ((?v0 S6)) (= (= (f10 f12 ?v0) f13) false)))
(assert (forall ((?v0 S6)) (= (= f13 (f10 f12 ?v0)) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f10 f12 ?v0) (f10 f11 ?v1)) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f10 f11 ?v0) (f10 f12 ?v1)) false)))
(assert (forall ((?v0 S6)) (= (= (f10 f11 ?v0) f13) (= ?v0 f13))))
(assert (forall ((?v0 S6)) (= (= f13 (f10 f11 ?v0)) (= f13 ?v0))))
(assert (= (f10 f11 f13) f13))
(assert (forall ((?v0 S6)) (= (f4 (f5 f7 (f4 (f5 f6 f21) f21)) (f8 f9 ?v0)) (f8 f9 (f10 f11 ?v0)))))
(assert (forall ((?v0 S6)) (= (f10 (f30 f34 (f10 (f30 f31 f25) f25)) (f10 f32 ?v0)) (f10 f32 (f10 f11 ?v0)))))
(assert (forall ((?v0 S9)) (= (f26 (f27 f28 ?v0) (f18 f19 (f10 f12 (f10 f12 f13)))) (f26 (f27 f36 (f26 (f27 f36 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S2)) (= (f14 (f15 f16 ?v0) (f18 f19 (f10 f12 (f10 f12 f13)))) (f4 (f5 f7 (f4 (f5 f7 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S6)) (= (f22 (f23 f24 ?v0) (f18 f19 (f10 f12 (f10 f12 f13)))) (f10 (f30 f34 (f10 (f30 f34 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) ?v0) (f4 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f10 (f30 f34 (f10 f32 (f10 f11 (f10 f12 f13)))) ?v0) (f10 (f30 f31 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f26 (f27 f36 (f18 f19 (f10 f11 (f10 f12 f13)))) ?v0) (f26 (f27 f33 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) ?v0) (f4 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f10 (f30 f34 (f10 f32 (f10 f11 (f10 f12 f13)))) ?v0) (f10 (f30 f31 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f4 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f10 (f30 f34 ?v0) (f10 f32 (f10 f11 (f10 f12 f13)))) (f10 (f30 f31 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f26 (f27 f36 ?v0) (f18 f19 (f10 f11 (f10 f12 f13)))) (f26 (f27 f33 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) (f8 f9 (f10 f11 (f10 f12 f13)))) (f4 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f10 (f30 f34 ?v0) (f10 f32 (f10 f11 (f10 f12 f13)))) (f10 (f30 f31 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f26 (f27 f28 ?v0) (f18 f19 (f10 f11 (f10 f12 f13)))) (f26 (f27 f36 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f14 (f15 f16 ?v0) (f18 f19 (f10 f11 (f10 f12 f13)))) (f4 (f5 f7 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f22 (f23 f24 ?v0) (f18 f19 (f10 f11 (f10 f12 f13)))) (f10 (f30 f34 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 (f8 f9 f13)) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f30 f31 (f10 f32 f13)) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f8 f9 f13)) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f30 f31 ?v0) (f10 f32 f13)) ?v0)))
(assert (forall ((?v0 S6)) (let ((?v_0 (f18 f19 ?v0))) (= (f26 (f27 f28 ?v_0) (f18 f19 (f10 f11 (f10 f12 f13)))) (f26 (f27 f36 ?v_0) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f8 f9 ?v0))) (= (f14 (f15 f16 ?v_0) (f18 f19 (f10 f11 (f10 f12 f13)))) (f4 (f5 f7 ?v_0) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f10 f32 ?v0))) (= (f22 (f23 f24 ?v_0) (f18 f19 (f10 f11 (f10 f12 f13)))) (f10 (f30 f34 ?v_0) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f10 f11 (f10 f12 f13)))) (let ((?v_0 (f18 f19 ?v_1))) (= (f14 (f15 f16 (f4 (f5 f6 ?v0) ?v1)) ?v_0) (f4 (f5 f6 (f4 (f5 f6 (f14 (f15 f16 ?v0) ?v_0)) (f14 (f15 f16 ?v1) ?v_0))) (f4 (f5 f7 (f4 (f5 f7 (f8 f9 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_1 (f10 f11 (f10 f12 f13)))) (let ((?v_0 (f18 f19 ?v_1))) (= (f22 (f23 f24 (f10 (f30 f31 ?v0) ?v1)) ?v_0) (f10 (f30 f31 (f10 (f30 f31 (f22 (f23 f24 ?v0) ?v_0)) (f22 (f23 f24 ?v1) ?v_0))) (f10 (f30 f34 (f10 (f30 f34 (f10 f32 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_0 (f18 f19 (f10 f11 (f10 f12 f13))))) (= (f26 (f27 f28 (f26 (f27 f33 ?v0) ?v1)) ?v_0) (f26 (f27 f33 (f26 (f27 f33 (f26 (f27 f28 ?v0) ?v_0)) (f26 (f27 f28 ?v1) ?v_0))) (f26 (f27 f36 (f26 (f27 f36 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f8 f9 ?v0))) (= (f8 f9 (f10 f12 ?v0)) (f4 (f5 f6 (f4 (f5 f6 f21) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f10 f32 ?v0))) (= (f10 f32 (f10 f12 ?v0)) (f10 (f30 f31 (f10 (f30 f31 f25) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f10 f11 (f10 f12 f13)))) (let ((?v_0 (f18 f19 ?v_1))) (= (f14 (f15 f16 (f4 (f5 f6 ?v0) ?v1)) ?v_0) (f4 (f5 f6 (f4 (f5 f6 (f14 (f15 f16 ?v0) ?v_0)) (f14 (f15 f16 ?v1) ?v_0))) (f4 (f5 f7 (f4 (f5 f7 (f8 f9 ?v_1)) ?v0)) ?v1)))))))
(assert (let ((?v_0 (f10 f11 (f10 f12 f13)))) (let ((?v_1 (f18 f19 ?v_0))) (= (f3 (f14 (f15 f16 (f4 f37 (f4 (f5 f7 (f8 f9 ?v_0)) f20))) ?v_1) (f14 (f15 f16 f21) ?v_1)) f1))))
(assert (let ((?v_0 (f10 f11 (f10 f12 f13)))) (let ((?v_1 (f18 f19 ?v_0))) (= (f3 (f14 (f15 f16 (f4 f37 (f4 (f5 f7 (f8 f9 ?v_0)) f17))) ?v_1) (f14 (f15 f16 f21) ?v_1)) f1))))
(assert (forall ((?v0 S9)) (= (f3 f21 (f14 (f15 f16 (f8 f9 (f10 f11 (f10 f12 f13)))) ?v0)) f1)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f10 f11 (f10 f12 f13)))) (let ((?v_1 (f18 f19 ?v_0))) (= (f4 (f5 f7 (f8 f9 (f10 f11 ?v_0))) (f14 (f15 f16 ?v0) ?v_1)) (f14 (f15 f16 (f4 (f5 f7 (f8 f9 ?v_0)) ?v0)) ?v_1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_0 (f27 f28 ?v0))) (let ((?v_1 (f26 ?v_0 ?v1))) (= (f26 ?v_0 (f26 (f27 f36 (f18 f19 (f10 f11 (f10 f12 f13)))) ?v1)) (f26 (f27 f36 ?v_1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S9)) (let ((?v_0 (f15 f16 ?v0))) (let ((?v_1 (f14 ?v_0 ?v1))) (= (f14 ?v_0 (f26 (f27 f36 (f18 f19 (f10 f11 (f10 f12 f13)))) ?v1)) (f4 (f5 f7 ?v_1) ?v_1))))))
(assert (forall ((?v0 S6) (?v1 S9)) (let ((?v_0 (f23 f24 ?v0))) (let ((?v_1 (f22 ?v_0 ?v1))) (= (f22 ?v_0 (f26 (f27 f36 (f18 f19 (f10 f11 (f10 f12 f13)))) ?v1)) (f10 (f30 f34 ?v_1) ?v_1))))))
(assert (forall ((?v0 S9)) (= (f26 (f27 f36 ?v0) ?v0) (f26 (f27 f28 ?v0) (f18 f19 (f10 f11 (f10 f12 f13)))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) ?v0) (f14 (f15 f16 ?v0) (f18 f19 (f10 f11 (f10 f12 f13)))))))
(assert (forall ((?v0 S6)) (= (f10 (f30 f34 ?v0) ?v0) (f22 (f23 f24 ?v0) (f18 f19 (f10 f11 (f10 f12 f13)))))))
(assert (= (f3 (f4 f37 (f4 (f5 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f20)) f21) f1))
(assert (= (f3 (f4 f37 (f4 (f5 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f17)) f21) f1))
(assert (= (f3 (f8 f9 f38) (f4 (f5 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f20)) f1))
(assert (= (f3 (f8 f9 f38) (f4 (f5 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f17)) f1))
(assert (forall ((?v0 S6)) (= (f10 f32 ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f30 f34 f25) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f30 f34 ?v0) f25) ?v0)))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S9)) (let ((?v_0 (f23 f24 ?v0))) (= (f22 ?v_0 (f26 (f27 f33 ?v1) ?v2)) (f10 (f30 f34 (f22 ?v_0 ?v1)) (f22 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f30 f34 (f10 f32 ?v0)) (f10 f32 ?v1)) (f10 f32 (f10 (f30 f34 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f35 (f10 f32 ?v0) (f10 f32 ?v1)) f1) (= (f35 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f10 f32 f38))) (= (= (f10 (f30 f34 ?v0) ?v1) f25) (or (and (= ?v0 f25) (= ?v1 f25)) (and (= ?v0 ?v_0) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S9)) (let ((?v_0 (f23 f24 ?v0))) (= (f22 (f23 f24 (f22 ?v_0 ?v1)) ?v2) (f22 ?v_0 (f26 (f27 f36 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f10 (f30 f34 ?v0) ?v1) f25) (or (= ?v0 f25) (= ?v0 (f10 f32 f38))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f35 ?v0 ?v1) f1) (=> (= (f35 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f35 ?v0 ?v1) f1) (=> (= (f35 ?v1 ?v2) f1) (= (f35 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f30 f34 ?v0))) (= (f10 (f30 f34 (f10 ?v_0 ?v1)) ?v2) (f10 ?v_0 (f10 (f30 f34 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6)) (or (= (f35 ?v0 ?v1) f1) (= (f35 ?v1 ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f30 f34 ?v0) ?v1) (f10 (f30 f34 ?v1) ?v0))))
(assert (= (= (f35 f38 f38) f1) true))
(assert (= (= f38 f38) true))
(assert (forall ((?v0 S6)) (= (f35 ?v0 ?v0) f1)))
(assert (forall ((?v0 S6)) (= (= (f35 (f10 f12 ?v0) f38) f1) (= (f35 ?v0 f38) f1))))
(assert (forall ((?v0 S6)) (= (= (f35 f38 (f10 f12 ?v0)) f1) (= (f35 f38 ?v0) f1))))
(assert (= (= (f35 f13 f38) f1) false))
(assert (= (= (f35 f38 f13) f1) true))
(assert (forall ((?v0 S6)) (= (= (f35 (f10 f11 ?v0) f38) f1) (= (f35 ?v0 f38) f1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f27 f28 ?v0))) (= (f26 (f27 f28 (f26 ?v_0 ?v1)) ?v2) (f26 ?v_0 (f26 (f27 f36 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S9) (?v2 S9)) (let ((?v_0 (f15 f16 ?v0))) (= (f14 (f15 f16 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f26 (f27 f36 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S9)) (let ((?v_0 (f23 f24 ?v0))) (= (f22 (f23 f24 (f22 ?v_0 ?v1)) ?v2) (f22 ?v_0 (f26 (f27 f36 ?v1) ?v2))))))
(assert (= (f10 f39 (f10 f32 f38)) f25))
(assert (= (f4 f37 (f8 f9 f38)) f21))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f40 (f18 f19 ?v0) (f18 f19 ?v1)) f1) (ite (= (f35 ?v0 ?v1) f1) true (= (f35 ?v0 f13) f1)))))
(assert (= (f10 f12 f38) f38))
(assert (forall ((?v0 S6)) (= (= f38 (f10 f12 ?v0)) (= f38 ?v0))))
(assert (forall ((?v0 S6)) (= (= (f10 f12 ?v0) f38) (= ?v0 f38))))
(assert (= (= f38 f13) false))
(assert (= (= f13 f38) false))
(assert (not (= (f10 f32 f13) (f10 f32 f38))))
(assert (forall ((?v0 S6)) (= (= f38 (f10 f11 ?v0)) false)))
(assert (forall ((?v0 S6)) (= (= (f10 f11 ?v0) f38) false)))
(assert (forall ((?v0 S6)) (= (f10 (f30 f34 f13) ?v0) f13)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f10 (f30 f34 (f10 f11 ?v0)) ?v1) (f10 f11 (f10 (f30 f34 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f35 (f10 f12 ?v0) (f10 f12 ?v1)) f1) (= (f35 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f35 (f10 f12 ?v0) (f10 f12 ?v1)) f1) (= (f35 ?v0 ?v1) f1))))
(assert (= (= (f35 f13 f13) f1) true))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f35 (f10 f11 ?v0) (f10 f11 ?v1)) f1) (= (f35 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f35 (f10 f11 ?v0) (f10 f11 ?v1)) f1) (= (f35 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f10 (f30 f34 (f10 (f30 f31 ?v0) ?v1)) ?v2) (f10 (f30 f31 (f10 (f30 f34 ?v0) ?v2)) (f10 (f30 f34 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f30 f34 ?v0))) (= (f10 ?v_0 (f10 (f30 f31 ?v1) ?v2)) (f10 (f30 f31 (f10 ?v_0 ?v1)) (f10 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f30 f31 ?v2))) (=> (= (f35 ?v0 ?v1) f1) (= (f35 (f10 ?v_0 ?v0) (f10 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S9)) (= (f10 f39 (f22 (f23 f24 (f10 f32 f38)) ?v0)) f25)))
(assert (forall ((?v0 S9)) (= (f4 f37 (f14 (f15 f16 (f8 f9 f38)) ?v0)) f21)))
(assert (forall ((?v0 S6)) (= (= (f35 f13 (f10 f12 ?v0)) f1) (= (f35 f13 ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f35 (f10 f11 ?v0) (f10 f12 ?v1)) f1) (= (f35 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f35 (f10 f11 ?v0) (f10 f12 ?v1)) f1) (= (f35 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6)) (= (= (f35 f13 (f10 f11 ?v0)) f1) (= (f35 f13 ?v0) f1))))
(check-sat)
(exit)
