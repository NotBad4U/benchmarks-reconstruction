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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2) S1)
(declare-fun f4 (S3 S2) S2)
(declare-fun f5 (S4 S2) S3)
(declare-fun f6 () S4)
(declare-fun f7 () S4)
(declare-fun f8 () S3)
(declare-fun f9 () S3)
(declare-fun f10 () S3)
(declare-fun f11 () S2)
(declare-fun f12 () S2)
(declare-fun f13 () S2)
(declare-fun f14 () S2)
(declare-fun f15 (S5 S2) S1)
(declare-fun f16 (S2) S5)
(declare-fun f17 (S6 S6) S1)
(declare-fun f18 () S6)
(declare-fun f19 (S7 S6) S6)
(declare-fun f20 (S8 S6) S7)
(declare-fun f21 () S8)
(declare-fun f22 (S2) S5)
(declare-fun f23 (S2) S1)
(declare-fun f24 (S6 S6) S1)
(declare-fun f25 () S8)
(declare-fun f26 (S9 S2) S6)
(declare-fun f27 () S9)
(declare-fun f28 () S2)
(declare-fun f29 (S10 S6) S2)
(declare-fun f30 () S10)
(declare-fun f31 () S6)
(declare-fun f32 () S4)
(declare-fun f33 () S2)
(declare-fun f34 () S6)
(declare-fun f35 (S2) S5)
(declare-fun f36 () S7)
(assert (not (= f1 f2)))
(assert (not false))
(assert (= (f3 (f4 (f5 f6 (f4 (f5 f7 (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f14)) f1))
(assert (not (= (f3 (f4 (f5 f6 (f4 (f5 f7 (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f14)) f1)))
(assert (= (f15 (f16 f13) f14) f1))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0) f1) (=> (= (f3 ?v1) f1) (= (f3 (f4 (f5 f6 ?v0) ?v1)) f1)))))
(assert (not (= (f3 (f4 (f5 f6 (f4 (f5 f7 (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f14)) f1)))
(assert (= (f3 (f4 (f5 f6 (f4 (f5 f7 (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f14)) f1))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f16 f13))) (=> (= (f15 ?v_0 ?v0) f1) (=> (= (f15 ?v_0 ?v1) f1) (= (f15 ?v_0 (f4 (f5 f6 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f17 f18 ?v0) f1) (=> (= (f17 f18 ?v1) f1) (= (f17 f18 (f19 (f20 f21 ?v0) ?v1)) f1)))))
(assert (= (f15 (f22 f13) f14) f1))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f13) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f13) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f13) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 f18) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f13) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 f18) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f13) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 f18) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f13) ?v0)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 ?v0) f18) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f13) ?v0)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 ?v0) f18) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f13) ?v0)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 ?v0) f18) ?v0)))
(assert (= (f15 (f16 f14) (f4 (f5 f7 (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f1))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f16 ?v0))) (= (= (f15 ?v_0 (f4 (f5 f7 ?v1) f13)) f1) (or (= (f15 ?v_0 ?v1) f1) (= ?v0 ?v1))))))
(assert (= (f23 (f4 (f5 f7 (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f1))
(assert (forall ((?v0 S2)) (= (= (f15 (f16 f11) (f4 f10 ?v0)) f1) (= (f15 (f22 f11) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f15 (f22 f13) (f4 f8 ?v0)) f1) (= (f15 (f22 (f4 f10 f11)) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f15 (f22 (f4 f10 ?v0)) f11) f1) (= (f15 (f16 ?v0) f11) f1))))
(assert (forall ((?v0 S2)) (= (= (f15 (f22 (f4 f8 ?v0)) f13) f1) (= (f15 (f22 ?v0) (f4 f10 f11)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f16 (f4 f9 ?v0)) (f4 f10 ?v1)) f1) (= (f15 (f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f16 (f4 f9 ?v0)) (f4 f10 ?v1)) f1) (= (f15 (f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f22 (f4 f10 ?v0)) (f4 f9 ?v1)) f1) (= (f15 (f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f22 (f4 f10 ?v0)) (f4 f9 ?v1)) f1) (= (f15 (f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (=> (= (f15 (f22 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v2)) f1) (= (f15 (f22 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v0))) (=> (= (f24 (f19 ?v_0 ?v1) (f19 ?v_0 ?v2)) f1) (= (f24 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f15 (f22 (f4 (f5 f7 ?v0) ?v1)) (f4 (f5 f7 ?v2) ?v1)) f1) (= (f15 (f22 ?v0) ?v2) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f24 (f19 (f20 f25 ?v0) ?v1) (f19 (f20 f25 ?v2) ?v1)) f1) (= (f24 ?v0 ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f5 f7 ?v0) ?v1) (f4 (f5 f7 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f19 (f20 f25 ?v0) ?v1) (f19 (f20 f25 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (=> (= (f4 ?v_0 ?v1) (f4 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v0))) (=> (= (f19 ?v_0 ?v1) (f19 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (=> (= (f4 ?v_0 ?v1) (f4 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v0))) (=> (= (f19 ?v_0 ?v1) (f19 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f15 (f22 ?v0) ?v1) f1) (=> (= (f15 (f22 ?v2) ?v3) f1) (= (f15 (f22 (f4 (f5 f7 ?v0) ?v2)) (f4 (f5 f7 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (=> (= (f24 ?v0 ?v1) f1) (=> (= (f24 ?v2 ?v3) f1) (= (f24 (f19 (f20 f25 ?v0) ?v2) (f19 (f20 f25 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f15 (f22 ?v0) ?v1) f1) (=> (= (f15 (f22 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f22 ?v0))) (=> (= (f15 ?v_0 ?v1) f1) (=> (= (f15 (f22 ?v1) ?v2) f1) (= (f15 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v2))) (=> (= (f15 (f22 ?v0) ?v1) f1) (= (f15 (f22 (f4 ?v_0 ?v0)) (f4 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v2))) (=> (= (f15 (f22 ?v0) ?v1) f1) (= (f15 (f22 (f4 ?v_0 ?v0)) (f4 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v2))) (=> (= (f24 ?v0 ?v1) f1) (= (f24 (f19 ?v_0 ?v0) (f19 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f15 (f22 ?v0) ?v1) f1) (= (f15 (f22 (f4 (f5 f7 ?v0) ?v2)) (f4 (f5 f7 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f24 ?v0 ?v1) f1) (= (f24 (f19 (f20 f25 ?v0) ?v2) (f19 (f20 f25 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (f4 (f5 f7 (f4 ?v_0 ?v1)) (f4 (f5 f7 ?v2) ?v3)) (f4 (f5 f7 (f4 ?v_0 ?v2)) (f4 (f5 f7 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f20 f25 ?v0))) (= (f19 (f20 f25 (f19 ?v_0 ?v1)) (f19 (f20 f25 ?v2) ?v3)) (f19 (f20 f25 (f19 ?v_0 ?v2)) (f19 (f20 f25 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (= (f15 (f22 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v2)) f1) (= (f15 (f22 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v0))) (= (= (f24 (f19 ?v_0 ?v1) (f19 ?v_0 ?v2)) f1) (= (f24 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f15 (f22 (f4 (f5 f7 ?v0) ?v1)) (f4 (f5 f7 ?v2) ?v1)) f1) (= (f15 (f22 ?v0) ?v2) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f24 (f19 (f20 f25 ?v0) ?v1) (f19 (f20 f25 ?v2) ?v1)) f1) (= (f24 ?v0 ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f4 (f5 f7 ?v0) ?v1) (f4 (f5 f7 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f19 (f20 f25 ?v0) ?v1) (f19 (f20 f25 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (= (f4 ?v_0 ?v1) (f4 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v0))) (= (= (f19 ?v_0 ?v1) (f19 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (f4 (f5 f7 (f4 ?v_0 ?v1)) ?v2) (f4 (f5 f7 (f4 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v0))) (= (f19 (f20 f25 (f19 ?v_0 ?v1)) ?v2) (f19 (f20 f25 (f19 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (f4 (f5 f7 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (f4 (f5 f7 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v0))) (= (f19 (f20 f25 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f20 f25 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (f4 (f5 f7 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v0))) (= (f19 (f20 f25 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f20 f25 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f7 (f4 f8 ?v0)) (f4 (f5 f7 (f4 f8 ?v1)) ?v2)) (f4 (f5 f7 (f4 f8 (f4 (f5 f7 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f22 (f4 f8 ?v0)) (f4 f8 ?v1)) f1) (= (f15 (f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f22 (f4 f8 ?v0)) (f4 f8 ?v1)) f1) (= (f15 (f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f22 (f4 f10 ?v0)) (f4 f10 ?v1)) f1) (= (f15 (f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f22 (f4 f10 ?v0)) (f4 f10 ?v1)) f1) (= (f15 (f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f22 (f4 f9 ?v0)) (f4 f10 ?v1)) f1) (= (f15 (f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f22 (f4 f9 ?v0)) (f4 f9 ?v1)) f1) (= (f15 (f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f22 (f4 f9 ?v0)) (f4 f10 ?v1)) f1) (= (f15 (f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f22 (f4 f9 ?v0)) (f4 f9 ?v1)) f1) (= (f15 (f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f8 ?v0) (f4 f8 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f10 ?v0) (f4 f10 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f9 ?v0) (f4 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 (f4 f8 ?v0)) (f4 f8 ?v1)) (f4 f8 (f4 (f5 f7 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 (f4 f8 ?v0)) (f4 f8 ?v1)) (f4 f8 (f4 (f5 f7 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 (f4 f10 ?v0)) (f4 f9 ?v1)) (f4 f10 (f4 (f5 f7 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 (f4 f9 ?v0)) (f4 f10 ?v1)) (f4 f10 (f4 (f5 f7 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 (f4 f9 ?v0)) (f4 f9 ?v1)) (f4 f9 (f4 (f5 f7 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f10 ?v0) (f4 f9 ?v1)) false)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f9 ?v0) (f4 f10 ?v1)) false)))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f8 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S6)) (let ((?v_0 (f26 f27 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S2)) (= (= (f15 (f22 (f4 f9 ?v0)) f11) f1) (= (f15 (f22 ?v0) f11) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 f9 ?v0) f11) (= ?v0 f11))))
(assert (forall ((?v0 S2)) (= (= (f4 f10 ?v0) f11) false)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 (f4 f8 f11)) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (f4 ?v_0 (f4 (f5 f7 ?v1) ?v2)) (f4 (f5 f7 (f4 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v0))) (= (f19 ?v_0 (f19 (f20 f25 ?v1) ?v2)) (f19 (f20 f25 (f19 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f5 f7 ?v0)) (?v_0 (f5 f7 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f5 f7 ?v0)) (?v_0 (f5 f7 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f20 f25 ?v0)) (?v_0 (f20 f25 ?v1))) (= (f19 ?v_1 (f19 ?v_0 ?v2)) (f19 ?v_0 (f19 ?v_1 ?v2))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) (f4 f8 f11)) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f15 (f22 ?v0) ?v1) f1) (= (f15 (f22 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 ?v0) ?v1) (f4 (f5 f7 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 ?v0) ?v1) (f4 (f5 f7 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f19 (f20 f25 ?v0) ?v1) (f19 (f20 f25 ?v1) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) f11) ?v0)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f22 f11))) (= (= (f15 ?v_0 (f4 f10 ?v0)) f1) (= (f15 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f22 f11))) (= (= (f15 ?v_0 (f4 f9 ?v0)) f1) (= (f15 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (= f11 (f4 f9 ?v0)) (= f11 ?v0))))
(assert (forall ((?v0 S2)) (= (= f11 (f4 f10 ?v0)) false)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 f11) ?v0) ?v0)))
(assert (= (= (f15 (f22 f11) f11) f1) true))
(assert (= (= f11 f11) true))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 f8 (f4 (f5 f7 ?v0) ?v1)) (f4 (f5 f7 (f4 f8 ?v0)) (f4 f8 ?v1)))))
(assert (forall ((?v0 S2)) (= (f4 f9 ?v0) (f4 (f5 f7 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 f8 ?v0) ?v0)))
(assert (= (f4 f9 f11) f11))
(assert (forall ((?v0 S2)) (= (f15 (f22 ?v0) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f4 f8 ?v0)) (?v_0 (f4 f8 ?v1))) (= (= (f15 (f22 ?v_1) ?v_0) f1) (not (= (f15 (f16 ?v_0) ?v_1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f26 f27 ?v0)) (?v_0 (f26 f27 ?v1))) (= (= (f24 ?v_1 ?v_0) f1) (not (= (f17 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f15 (f22 ?v0) ?v1) f1) (=> (= (f15 (f16 ?v2) ?v3) f1) (= (f15 (f16 (f4 (f5 f7 ?v0) ?v2)) (f4 (f5 f7 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (=> (= (f24 ?v0 ?v1) f1) (=> (= (f17 ?v2 ?v3) f1) (= (f17 (f19 (f20 f25 ?v0) ?v2) (f19 (f20 f25 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f15 (f16 ?v0) ?v1) f1) (=> (= (f15 (f22 ?v2) ?v3) f1) (= (f15 (f16 (f4 (f5 f7 ?v0) ?v2)) (f4 (f5 f7 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (=> (= (f17 ?v0 ?v1) f1) (=> (= (f24 ?v2 ?v3) f1) (= (f17 (f19 (f20 f25 ?v0) ?v2) (f19 (f20 f25 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f10 f11)))) ?v0) (f4 (f5 f7 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 (f26 f27 (f4 f9 (f4 f10 f11)))) ?v0) (f19 (f20 f25 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f10 f11)))) ?v0) (f4 (f5 f7 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f4 f8 (f4 f9 (f4 f10 f11)))) (f4 (f5 f7 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 ?v0) (f26 f27 (f4 f9 (f4 f10 f11)))) (f19 (f20 f25 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f4 f8 (f4 f9 (f4 f10 f11)))) (f4 (f5 f7 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 (f4 f8 ?v0)) f13) (f4 f8 (f4 (f5 f7 ?v0) (f4 f10 f11))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 f13) (f4 f8 ?v0)) (f4 f8 (f4 (f5 f7 (f4 f10 f11)) ?v0)))))
(assert (= (f4 (f5 f7 f13) f13) (f4 f8 (f4 f9 (f4 f10 f11)))))
(assert (= (f19 (f20 f25 f18) f18) (f26 f27 (f4 f9 (f4 f10 f11)))))
(assert (= (f4 (f5 f7 f13) f13) (f4 f8 (f4 f9 (f4 f10 f11)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f15 (f16 ?v0) ?v1) f1) (=> (= (f15 (f22 ?v2) ?v3) f1) (= (f15 (f16 (f4 (f5 f7 ?v0) ?v2)) (f4 (f5 f7 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f16 ?v0) ?v1) f1) (and (= (f15 (f22 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f4 f8 ?v0))) (= (f4 f8 (f4 f10 ?v0)) (f4 (f5 f7 (f4 (f5 f7 f13) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 (f4 f8 (f4 f10 f11))) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f4 f8 (f4 f10 f11))) ?v0)))
(assert (= (f4 f8 (f4 f10 f11)) f13))
(assert (= (f26 f27 (f4 f10 f11)) f18))
(assert (= (f4 f8 (f4 f10 f11)) f13))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f6 (f4 f10 ?v0)) ?v1) (f4 (f5 f7 (f4 f9 (f4 (f5 f6 ?v0) ?v1))) ?v1))))
(assert (= f13 (f4 f8 (f4 f10 f11))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f8 ?v2))) (= (f4 (f5 f6 (f4 (f5 f7 ?v0) ?v1)) ?v_0) (f4 (f5 f7 (f4 (f5 f6 ?v0) ?v_0)) (f4 (f5 f6 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S2)) (let ((?v_0 (f26 f27 ?v2))) (= (f19 (f20 f21 (f19 (f20 f25 ?v0) ?v1)) ?v_0) (f19 (f20 f25 (f19 (f20 f21 ?v0) ?v_0)) (f19 (f20 f21 ?v1) ?v_0))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 (f4 f8 ?v0)))) (= (f4 ?v_0 (f4 (f5 f7 ?v1) ?v2)) (f4 (f5 f7 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f21 (f26 f27 ?v0)))) (= (f19 ?v_0 (f19 (f20 f25 ?v1) ?v2)) (f19 (f20 f25 (f19 ?v_0 ?v1)) (f19 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f16 (f4 f10 ?v0)) (f4 f9 ?v1)) f1) (= (f15 (f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f16 (f4 f10 ?v0)) (f4 f9 ?v1)) f1) (= (f15 (f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2)) (= (f4 f10 ?v0) (f4 (f5 f7 (f4 (f5 f7 f13) ?v0)) ?v0))))
(assert (forall ((?v0 S2)) (= (= (f15 (f16 (f4 f9 ?v0)) f11) f1) (= (f15 (f16 ?v0) f11) f1))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f16 f11))) (= (= (f15 ?v_0 (f4 f9 ?v0)) f1) (= (f15 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (= (f15 (f16 (f4 f10 ?v0)) f11) f1) (= (f15 (f16 ?v0) f11) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f15 (f16 ?v0) ?v1) f1) (= (f15 (f22 (f4 (f5 f7 ?v0) f13)) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f22 (f4 (f5 f7 ?v0) f13)) ?v1) f1) (= (f15 (f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f16 ?v0) (f4 (f5 f7 ?v1) f13)) f1) (= (f15 (f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (=> (= (f15 (f16 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v2)) f1) (= (f15 (f16 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v0))) (=> (= (f17 (f19 ?v_0 ?v1) (f19 ?v_0 ?v2)) f1) (= (f17 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f15 (f16 (f4 (f5 f7 ?v0) ?v1)) (f4 (f5 f7 ?v2) ?v1)) f1) (= (f15 (f16 ?v0) ?v2) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f17 (f19 (f20 f25 ?v0) ?v1) (f19 (f20 f25 ?v2) ?v1)) f1) (= (f17 ?v0 ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f15 (f16 ?v0) ?v1) f1) (=> (= (f15 (f16 ?v2) ?v3) f1) (= (f15 (f16 (f4 (f5 f7 ?v0) ?v2)) (f4 (f5 f7 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (=> (= (f17 ?v0 ?v1) f1) (=> (= (f17 ?v2 ?v3) f1) (= (f17 (f19 (f20 f25 ?v0) ?v2) (f19 (f20 f25 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v2))) (=> (= (f15 (f16 ?v0) ?v1) f1) (= (f15 (f16 (f4 ?v_0 ?v0)) (f4 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v2))) (=> (= (f17 ?v0 ?v1) f1) (= (f17 (f19 ?v_0 ?v0) (f19 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f15 (f16 ?v0) ?v1) f1) (= (f15 (f16 (f4 (f5 f7 ?v0) ?v2)) (f4 (f5 f7 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f17 ?v0 ?v1) f1) (= (f17 (f19 (f20 f25 ?v0) ?v2) (f19 (f20 f25 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (= (f15 (f16 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v2)) f1) (= (f15 (f16 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f25 ?v0))) (= (= (f17 (f19 ?v_0 ?v1) (f19 ?v_0 ?v2)) f1) (= (f17 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f15 (f16 (f4 (f5 f7 ?v0) ?v1)) (f4 (f5 f7 ?v2) ?v1)) f1) (= (f15 (f16 ?v0) ?v2) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f17 (f19 (f20 f25 ?v0) ?v1) (f19 (f20 f25 ?v2) ?v1)) f1) (= (f17 ?v0 ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f5 f6 ?v0)) (?v_1 (f5 f6 ?v2))) (= (= (f4 (f5 f7 (f4 ?v_0 ?v1)) (f4 ?v_1 ?v3)) (f4 (f5 f7 (f4 ?v_0 ?v3)) (f4 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f20 f21 ?v0)) (?v_1 (f20 f21 ?v2))) (= (= (f19 (f20 f25 (f19 ?v_0 ?v1)) (f19 ?v_1 ?v3)) (f19 (f20 f25 (f19 ?v_0 ?v3)) (f19 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (f4 (f5 f7 (f4 (f5 f6 ?v0) ?v1)) (f4 (f5 f7 (f4 (f5 f6 ?v2) ?v1)) ?v3)) (f4 (f5 f7 (f4 (f5 f6 (f4 (f5 f7 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (f19 (f20 f25 (f19 (f20 f21 ?v0) ?v1)) (f19 (f20 f25 (f19 (f20 f21 ?v2) ?v1)) ?v3)) (f19 (f20 f25 (f19 (f20 f21 (f19 (f20 f25 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f7 (f4 (f5 f6 ?v0) ?v1)) (f4 (f5 f6 ?v2) ?v1)) (f4 (f5 f6 (f4 (f5 f7 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f19 (f20 f25 (f19 (f20 f21 ?v0) ?v1)) (f19 (f20 f21 ?v2) ?v1)) (f19 (f20 f21 (f19 (f20 f25 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f6 (f4 (f5 f7 ?v0) ?v1)) ?v2) (f4 (f5 f7 (f4 (f5 f6 ?v0) ?v2)) (f4 (f5 f6 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f19 (f20 f21 (f19 (f20 f25 ?v0) ?v1)) ?v2) (f19 (f20 f25 (f19 (f20 f21 ?v0) ?v2)) (f19 (f20 f21 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f6 (f4 (f5 f7 ?v0) ?v1)) ?v2) (f4 (f5 f7 (f4 (f5 f6 ?v0) ?v2)) (f4 (f5 f6 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f19 (f20 f21 (f19 (f20 f25 ?v0) ?v1)) ?v2) (f19 (f20 f25 (f19 (f20 f21 ?v0) ?v2)) (f19 (f20 f21 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f5 f6 ?v0)) (?v_1 (f5 f6 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f4 (f5 f7 (f4 ?v_0 ?v2)) (f4 ?v_1 ?v3)) (f4 (f5 f7 (f4 ?v_0 ?v3)) (f4 ?v_1 ?v2))))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f20 f21 ?v0)) (?v_1 (f20 f21 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f19 (f20 f25 (f19 ?v_0 ?v2)) (f19 ?v_1 ?v3)) (f19 (f20 f25 (f19 ?v_0 ?v3)) (f19 ?v_1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v0))) (= (f4 ?v_0 (f4 (f5 f7 ?v1) ?v2)) (f4 (f5 f7 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 ?v_0 (f19 (f20 f25 ?v1) ?v2)) (f19 (f20 f25 (f19 ?v_0 ?v1)) (f19 ?v_0 ?v2))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 (f4 (f5 f7 f13) f13)) (f4 f8 ?v0)) (f4 f8 (f4 f9 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f16 (f4 f8 ?v0)) (f4 f8 ?v1)) f1) (= (f15 (f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f15 (f16 ?v0) ?v1) f1) (= (f15 (f16 (f4 (f5 f7 ?v0) ?v2)) (f4 (f5 f7 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f16 (f4 f9 ?v0)) (f4 f9 ?v1)) f1) (= (f15 (f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f16 (f4 f9 ?v0)) (f4 f9 ?v1)) f1) (= (f15 (f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f16 (f4 f10 ?v0)) (f4 f10 ?v1)) f1) (= (f15 (f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f16 (f4 f10 ?v0)) (f4 f10 ?v1)) f1) (= (f15 (f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f6 (f4 f8 ?v0)) (f4 f8 ?v1)) (f4 f8 (f4 (f5 f6 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f6 (f4 (f5 f7 ?v0) ?v1)) ?v2) (f4 (f5 f7 (f4 (f5 f6 ?v0) ?v2)) (f4 (f5 f6 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v0))) (= (f4 ?v_0 (f4 (f5 f7 ?v1) ?v2)) (f4 (f5 f7 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f6 (f4 f9 ?v0)) ?v1) (f4 f9 (f4 (f5 f6 ?v0) ?v1)))))
(assert (= (= (f15 (f16 f11) f11) f1) false))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f11) ?v0) f11)))
(assert (forall ((?v0 S2)) (= (= (f15 (f16 (f4 f8 ?v0)) f13) f1) (= (f15 (f16 ?v0) (f4 f10 f11)) f1))))
(assert (forall ((?v0 S2)) (= (= (f15 (f16 f13) (f4 f8 ?v0)) f1) (= (f15 (f16 (f4 f10 f11)) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f15 (f16 ?v0) ?v1) f1) false) (=> (=> (= (f15 (f16 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f5 f6 ?v0))) (= (f4 (f5 f6 (f4 ?v_0 ?v1)) (f4 (f5 f6 ?v2) ?v3)) (f4 (f5 f6 (f4 ?v_0 ?v2)) (f4 (f5 f6 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) (f19 (f20 f21 ?v2) ?v3)) (f19 (f20 f21 (f19 ?v_0 ?v2)) (f19 (f20 f21 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_1 (f5 f6 (f4 (f5 f6 ?v0) ?v1))) (?v_0 (f5 f6 ?v2))) (= (f4 ?v_1 (f4 ?v_0 ?v3)) (f4 ?v_0 (f4 ?v_1 ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_1 (f20 f21 (f19 (f20 f21 ?v0) ?v1))) (?v_0 (f20 f21 ?v2))) (= (f19 ?v_1 (f19 ?v_0 ?v3)) (f19 ?v_0 (f19 ?v_1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f5 f6 ?v0)) (?v_1 (f4 (f5 f6 ?v2) ?v3))) (= (f4 (f5 f6 (f4 ?v_0 ?v1)) ?v_1) (f4 ?v_0 (f4 (f5 f6 ?v1) ?v_1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f20 f21 ?v0)) (?v_1 (f19 (f20 f21 ?v2) ?v3))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v_1) (f19 ?v_0 (f19 (f20 f21 ?v1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v0))) (= (f4 (f5 f6 (f4 ?v_0 ?v1)) ?v2) (f4 (f5 f6 (f4 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v2) (f19 (f20 f21 (f19 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v0))) (= (f4 (f5 f6 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f6 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f20 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v0))) (= (f4 (f5 f6 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f6 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f20 f21 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v0))) (= (f4 ?v_0 (f4 (f5 f6 ?v1) ?v2)) (f4 (f5 f6 (f4 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 ?v_0 (f19 (f20 f21 ?v1) ?v2)) (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f5 f6 ?v0)) (?v_0 (f5 f6 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f20 f21 ?v0)) (?v_0 (f20 f21 ?v1))) (= (f19 ?v_1 (f19 ?v_0 ?v2)) (f19 ?v_0 (f19 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f6 ?v0) ?v1) (f4 (f5 f6 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f19 (f20 f21 ?v0) ?v1) (f19 (f20 f21 ?v1) ?v0))))
(assert (forall ((?v0 S2)) (= (= f13 ?v0) (= ?v0 f13))))
(assert (forall ((?v0 S6)) (= (= f18 ?v0) (= ?v0 f18))))
(assert (forall ((?v0 S2)) (= (f15 (f16 ?v0) (f4 (f5 f7 ?v0) f13)) f1)))
(assert (forall ((?v0 S6)) (= (f17 ?v0 (f19 (f20 f25 ?v0) f18)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f15 (f16 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f15 (f16 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f15 (f16 (f4 f8 ?v0)) (f4 f8 ?v1)) f1) (= (f15 (f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 (f4 (f5 f6 ?v0) ?v1)) ?v1) (f4 (f5 f6 (f4 (f5 f7 ?v0) f13)) ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f19 (f20 f25 (f19 (f20 f21 ?v0) ?v1)) ?v1) (f19 (f20 f21 (f19 (f20 f25 ?v0) f18)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 ?v0) (f4 (f5 f6 ?v1) ?v0)) (f4 (f5 f6 (f4 (f5 f7 ?v1) f13)) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f19 (f20 f25 ?v0) (f19 (f20 f21 ?v1) ?v0)) (f19 (f20 f21 (f19 (f20 f25 ?v1) f18)) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) ?v0) (f4 (f5 f6 (f4 (f5 f7 f13) f13)) ?v0))))
(assert (forall ((?v0 S6)) (= (f19 (f20 f25 ?v0) ?v0) (f19 (f20 f21 (f19 (f20 f25 f18) f18)) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v0))) (= (f4 (f5 f6 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f6 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f6 ?v0) ?v1) (f4 (f5 f6 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f6 (f4 f8 ?v0)) (f4 (f5 f6 (f4 f8 ?v1)) ?v2)) (f4 (f5 f6 (f4 f8 (f4 (f5 f6 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f6 (f4 f8 ?v0)) (f4 f8 ?v1)) (f4 f8 (f4 (f5 f6 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 f8 (f4 (f5 f6 ?v0) ?v1)) (f4 (f5 f6 (f4 f8 ?v0)) (f4 f8 ?v1)))))
(assert (= (f15 (f16 f28) (f4 (f5 f7 (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f1))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f22 f11))) (=> (= (f15 ?v_0 ?v0) f1) (=> (= (f15 ?v_0 ?v1) f1) (= (f4 (f5 f7 (f4 f8 ?v0)) (f4 f8 ?v1)) (f4 f8 (f4 (f5 f7 ?v0) ?v1))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f22 f11))) (=> (= (f15 ?v_0 ?v0) f1) (=> (= (f15 ?v_0 ?v1) f1) (= (f19 (f20 f25 (f26 f27 ?v0)) (f26 f27 ?v1)) (f26 f27 (f4 (f5 f7 ?v0) ?v1))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f22 f11))) (=> (= (f15 ?v_0 ?v0) f1) (=> (= (f15 ?v_0 ?v1) f1) (= (f4 (f5 f6 (f4 f8 ?v0)) (f4 f8 ?v1)) (f4 f8 (f4 (f5 f6 ?v0) ?v1))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f22 f11))) (=> (= (f15 ?v_0 ?v0) f1) (=> (= (f15 ?v_0 ?v1) f1) (= (f19 (f20 f21 (f26 f27 ?v0)) (f26 f27 ?v1)) (f26 f27 (f4 (f5 f6 ?v0) ?v1))))))))
(assert (= f13 (f4 f8 (f4 f10 f11))))
(assert (not (= (f3 (f4 (f5 f6 (f4 (f5 f7 (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) (f4 (f5 f7 f13) (f29 f30 f31)))) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S5)) (=> (= (f15 (f22 ?v0) ?v1) f1) (=> (= (f15 ?v2 ?v0) f1) (=> (forall ((?v3 S2)) (=> (= (f15 (f22 ?v0) ?v3) f1) (=> (= (f15 ?v2 ?v3) f1) (= (f15 ?v2 (f4 (f5 f7 ?v3) f13)) f1)))) (= (f15 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S5)) (=> (= (f15 (f16 ?v0) ?v1) f1) (=> (= (f15 ?v2 (f4 (f5 f7 ?v0) f13)) f1) (=> (forall ((?v3 S2)) (=> (= (f15 (f16 ?v0) ?v3) f1) (=> (= (f15 ?v2 ?v3) f1) (= (f15 ?v2 (f4 (f5 f7 ?v3) f13)) f1)))) (= (f15 ?v2 ?v1) f1))))))
(assert (= (f4 (f5 f32 (f4 f8 f33)) (f4 (f5 f7 (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f13))
(assert (let ((?v_0 (f4 (f5 f7 (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) (?v_1 (f4 (f5 f7 f13) (f29 f30 f34)))) (=> (= (f15 (f16 ?v_1) ?v_0) f1) (not (= (f3 (f4 (f5 f6 ?v_0) ?v_1)) f1)))))
(assert (= (f15 (f35 (f4 (f5 f7 (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) (f4 f8 f33)) f1))
(assert (= (f17 f31 f34) f1))
(assert (let ((?v_1 (f4 (f5 f7 (f4 (f5 f6 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) (?v_0 (f4 f8 f33))) (=> (not (= (f15 (f35 ?v_1) ?v_0) f1)) (not (= (f4 (f5 f32 ?v_0) ?v_1) f13)))))
(assert (forall ((?v0 S6)) (= (= (f15 (f16 f28) (f29 f30 ?v0)) f1) (= (f17 f31 ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f29 f30 ?v0) (f29 f30 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6)) (= (= (f15 (f22 (f29 f30 ?v0)) f28) f1) (= ?v0 f31))))
(assert (forall ((?v0 S6)) (= (= (f29 f30 ?v0) f28) (= ?v0 f31))))
(assert (forall ((?v0 S2)) (= (= f28 ?v0) (= ?v0 f28))))
(assert (forall ((?v0 S6)) (= (= f31 ?v0) (= ?v0 f31))))
(assert (= (= f33 f33) true))
(assert (forall ((?v0 S6)) (let ((?v_0 (f29 f30 ?v0))) (= (f4 f8 ?v_0) ?v_0))))
(assert (forall ((?v0 S6)) (= (f26 f27 (f29 f30 ?v0)) (f19 f36 ?v0))))
(assert (= (f29 f30 f31) f28))
(assert (= (f26 f27 f11) f31))
(assert (= f31 (f26 f27 f11)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f15 (f22 (f29 f30 ?v0)) (f29 f30 ?v1)) f1) (= (f24 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f4 (f5 f7 (f29 f30 ?v0)) (f29 f30 ?v1)) (f29 f30 (f19 (f20 f25 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S2)) (= (f4 (f5 f7 (f29 f30 ?v0)) (f4 (f5 f7 (f29 f30 ?v1)) ?v2)) (f4 (f5 f7 (f29 f30 (f19 (f20 f25 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6)) (not (= (f15 (f16 (f29 f30 ?v0)) f28) f1))))
(assert (forall ((?v0 S6)) (= (f15 (f22 f28) (f29 f30 ?v0)) f1)))
(assert (= (= (f15 (f16 f33) f28) f1) true))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f22 ?v0))) (= (= (f24 (f26 f27 ?v0) (f26 f27 ?v1)) f1) (ite (= (f15 ?v_0 ?v1) f1) true (= (f15 ?v_0 f11) f1))))))
(assert (forall ((?v0 S2)) (= (= (f17 f31 (f26 f27 ?v0)) f1) (= (f15 (f16 f11) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= f31 (f26 f27 ?v0)) (= (f15 (f22 ?v0) f11) f1))))
(assert (forall ((?v0 S2)) (= (= (f26 f27 ?v0) f31) (= (f15 (f22 ?v0) f11) f1))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f4 f8 ?v0))) (= (f29 f30 (f26 f27 ?v0)) (ite (= (f15 (f22 f28) ?v_0) f1) ?v_0 f28)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (let ((?v_0 (f5 f6 (f29 f30 ?v2)))) (=> (= (f15 (f16 ?v0) ?v1) f1) (=> (= (f17 f31 ?v2) f1) (= (f15 (f16 (f4 ?v_0 ?v0)) (f4 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 (f26 f27 (f4 f9 (f4 f10 f11)))) ?v0) (f19 (f20 f25 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 ?v0) (f26 f27 (f4 f9 (f4 f10 f11)))) (f19 (f20 f25 ?v0) ?v0))))
(assert (= (f19 (f20 f25 f18) f18) (f26 f27 (f4 f9 (f4 f10 f11)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f26 f27 ?v0)) (?v_0 (f26 f27 ?v1))) (= (f19 (f20 f25 ?v_1) ?v_0) (ite (= (f15 (f16 ?v0) f11) f1) ?v_0 (ite (= (f15 (f16 ?v1) f11) f1) ?v_1 (f26 f27 (f4 (f5 f7 ?v0) ?v1))))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f15 (f16 (f29 f30 ?v0)) (f29 f30 ?v1)) f1) (= (f17 ?v0 ?v1) f1))))
(assert (= (f29 f30 f18) f13))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f4 (f5 f6 (f29 f30 ?v0)) (f29 f30 ?v1)) (f29 f30 (f19 (f20 f21 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f29 f30 (f19 (f20 f21 ?v0) ?v1)) (f4 (f5 f6 (f29 f30 ?v0)) (f29 f30 ?v1)))))
(assert (= (f4 f10 f33) f33))
(assert (forall ((?v0 S2)) (= (= f33 (f4 f10 ?v0)) (= f33 ?v0))))
(assert (forall ((?v0 S2)) (= (= (f4 f10 ?v0) f33) (= ?v0 f33))))
(assert (= (= f33 f11) false))
(assert (= (= f11 f33) false))
(assert (forall ((?v0 S2)) (= (= f33 (f4 f9 ?v0)) false)))
(assert (forall ((?v0 S2)) (= (= (f4 f9 ?v0) f33) false)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f19 (f20 f21 (f26 f27 ?v0)) (f26 f27 ?v1)) (ite (= (f15 (f16 ?v0) f11) f1) f31 (f26 f27 (f4 (f5 f6 ?v0) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (= (f19 (f20 f21 (f26 f27 ?v0)) (f19 (f20 f21 (f26 f27 ?v1)) ?v2)) (ite (= (f15 (f16 ?v0) f11) f1) f31 (f19 (f20 f21 (f26 f27 (f4 (f5 f6 ?v0) ?v1))) ?v2)))))
(assert (= (= (f15 (f16 f33) f33) f1) false))
(assert (= (= (f15 (f22 f33) f33) f1) true))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f28) ?v0) f28)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 f31) ?v0) f31)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f28) ?v0) f28)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 f31) ?v0) f31)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f28) f28)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 ?v0) f31) f31)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f28) f28)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 ?v0) f31) f31)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f6 ?v0) ?v1) f28) (or (= ?v0 f28) (= ?v1 f28)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 f28)) (=> (not (= ?v1 f28)) (not (= (f4 (f5 f6 ?v0) ?v1) f28))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (not (= ?v0 f31)) (=> (not (= ?v1 f31)) (not (= (f19 (f20 f21 ?v0) ?v1) f31))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f5 f6 ?v0) ?v1) f28) (or (= ?v0 f28) (= ?v1 f28)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f19 (f20 f21 ?v0) ?v1) f31) (or (= ?v0 f31) (= ?v1 f31)))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 f28) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f25 f31) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 f28) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f25 f31) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 f28) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f25 f31) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (= f28 (f4 (f5 f7 ?v0) ?v0)) (= ?v0 f28))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) f28) ?v0)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f25 ?v0) f31) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) f28) ?v0)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f25 ?v0) f31) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) f28) ?v0)))
(assert (forall ((?v0 S6)) (= (f19 (f20 f25 ?v0) f31) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 (f4 (f5 f7 ?v0) ?v1)) (= ?v1 f28))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= ?v0 (f19 (f20 f25 ?v0) ?v1)) (= ?v1 f31))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f7 ?v0) ?v0) f28) (= ?v0 f28))))
(assert (not (= f13 f28)))
(assert (not (= f18 f31)))
(assert (not (= f28 f13)))
(assert (not (= f31 f18)))
(assert (= f11 f28))
(assert (not (= f28 f13)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 f28) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) f28) ?v0)))
(assert (= (f26 f27 (f4 f10 f11)) f18))
(assert (= f18 (f26 f27 (f4 f10 f11))))
(assert (not (= (f4 f8 f11) (f4 f8 f33))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f17 (f26 f27 ?v0) (f26 f27 ?v1)) f1) (ite (= (f15 (f16 ?v0) ?v1) f1) (= (f15 (f16 f11) ?v1) f1) false))))
(check-sat)
(exit)