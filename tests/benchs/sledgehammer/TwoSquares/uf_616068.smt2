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
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S3) S2)
(declare-fun f5 (S4 S3) S3)
(declare-fun f6 () S4)
(declare-fun f7 () S4)
(declare-fun f8 () S4)
(declare-fun f9 () S3)
(declare-fun f10 (S5 S3) S4)
(declare-fun f11 () S5)
(declare-fun f12 () S5)
(declare-fun f13 () S3)
(declare-fun f14 () S3)
(declare-fun f15 (S3) S2)
(declare-fun f16 (S3) S1)
(declare-fun f17 (S3) S1)
(declare-fun f18 (S6 S7) S7)
(declare-fun f19 (S8 S7) S6)
(declare-fun f20 () S8)
(declare-fun f21 () S7)
(declare-fun f22 (S9 S3) S7)
(declare-fun f23 () S9)
(declare-fun f24 () S8)
(declare-fun f25 () S5)
(declare-fun f26 () S3)
(declare-fun f27 (S7 S7) S1)
(declare-fun f28 () S3)
(declare-fun f29 () S5)
(declare-fun f30 (S10 S3) S2)
(declare-fun f31 (S3) S10)
(declare-fun f32 (S7 S7) S1)
(declare-fun f33 () S7)
(assert (not (= f1 f2)))
(assert (not false))
(assert (let ((?v_0 (f5 f7 (f5 f8 f9)))) (= (f3 (f4 (f5 f6 ?v_0)) (f5 (f10 f11 (f5 (f10 f12 (f5 f6 (f5 f7 ?v_0))) f13)) f14)) f1)))
(assert (let ((?v_1 (f5 f7 (f5 f8 f9)))) (let ((?v_0 (f15 (f5 (f10 f11 (f5 (f10 f12 (f5 f6 (f5 f7 ?v_1))) f13)) f14)))) (or (= (f3 ?v_0 f14) f1) (= (f3 ?v_0 (f5 f6 ?v_1)) f1)))))
(assert (let ((?v_0 (f5 f7 (f5 f8 f9)))) (= (f3 (f4 (f5 f6 ?v_0)) (f5 (f10 f11 (f5 (f10 f12 (f5 f6 (f5 f7 ?v_0))) f13)) f14)) f1)))
(assert (let ((?v_1 (f5 f7 (f5 f8 f9)))) (let ((?v_0 (f15 (f5 (f10 f11 (f5 (f10 f12 (f5 f6 (f5 f7 ?v_1))) f13)) f14)))) (or (= (f3 ?v_0 f14) f1) (= (f3 ?v_0 (f5 f6 ?v_1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f16 ?v0) f1) (=> (= (f16 ?v1) f1) (= (f16 (f5 (f10 f12 ?v0) ?v1)) f1)))))
(assert (= (f17 (f5 (f10 f11 (f5 (f10 f12 (f5 f6 (f5 f7 (f5 f7 (f5 f8 f9))))) f13)) f14)) f1))
(assert (forall ((?v0 S3)) (= (f5 (f10 f11 f14) (f5 f6 ?v0)) (f5 f6 (f5 (f10 f11 (f5 f8 f9)) ?v0)))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f11 (f5 f6 ?v0)) f14) (f5 f6 (f5 (f10 f11 ?v0) (f5 f8 f9))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f14) (f5 f6 ?v0)) f1) (= (f3 (f4 (f5 f8 f9)) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 (f5 f6 ?v0)) f14) f1) (= (f3 (f4 ?v0) (f5 f8 f9)) f1))))
(assert (= (f5 (f10 f11 f14) f14) (f5 f6 (f5 f7 (f5 f8 f9)))))
(assert (= (f5 (f10 f11 f14) f14) (f5 f6 (f5 f7 (f5 f8 f9)))))
(assert (= (f18 (f19 f20 f21) f21) (f22 f23 (f5 f7 (f5 f8 f9)))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 ?v0) (f5 f6 (f5 f7 (f5 f8 f9)))) (f5 (f10 f11 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 ?v0) (f5 f6 (f5 f7 (f5 f8 f9)))) (f5 (f10 f11 ?v0) ?v0))))
(assert (forall ((?v0 S7)) (= (f18 (f19 f24 ?v0) (f22 f23 (f5 f7 (f5 f8 f9)))) (f18 (f19 f20 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 (f5 f6 (f5 f7 (f5 f8 f9)))) ?v0) (f5 (f10 f11 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 (f5 f6 (f5 f7 (f5 f8 f9)))) ?v0) (f5 (f10 f11 ?v0) ?v0))))
(assert (forall ((?v0 S7)) (= (f18 (f19 f24 (f22 f23 (f5 f7 (f5 f8 f9)))) ?v0) (f18 (f19 f20 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 (f5 (f10 f11 f14) f14)) (f5 f6 ?v0)) (f5 f6 (f5 f7 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f12 (f5 f8 ?v0)) ?v1) (f5 (f10 f11 (f5 f7 (f5 (f10 f12 ?v0) ?v1))) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f6 ?v0) (f5 f6 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f5 f6 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S7)) (let ((?v_0 (f22 f23 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f8 ?v0) (f5 f8 ?v1)) (= ?v0 ?v1))))
(assert (= (= f9 f9) true))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f7 ?v0) (f5 f7 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f3 (f4 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f4 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v0))) (= (f5 (f10 f12 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f10 f12 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f12 ?v0) ?v1) (f5 (f10 f12 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 f6 ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f11 ?v0))) (= (f5 (f10 f11 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f10 f11 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f10 f11 ?v0)) (?v_0 (f10 f11 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f11 ?v0) ?v1) (f5 (f10 f11 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (= (= (f5 f8 ?v0) f9) false)))
(assert (forall ((?v0 S3)) (= (= f9 (f5 f8 ?v0)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f8 ?v0) (f5 f7 ?v1)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f7 ?v0) (f5 f8 ?v1)) false)))
(assert (forall ((?v0 S3)) (= (= (f5 f7 ?v0) f9) (= ?v0 f9))))
(assert (forall ((?v0 S3)) (= (= f9 (f5 f7 ?v0)) (= f9 ?v0))))
(assert (= (f5 f7 f9) f9))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 (f5 f8 ?v0)) (f5 f8 ?v1)) f1) (= (f3 (f4 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 (f5 f8 ?v0)) (f5 f8 ?v1)) f1) (= (f3 (f4 ?v0) ?v1) f1))))
(assert (= (= (f3 (f4 f9) f9) f1) false))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 (f5 f7 ?v0)) (f5 f7 ?v1)) f1) (= (f3 (f4 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 (f5 f7 ?v0)) (f5 f7 ?v1)) f1) (= (f3 (f4 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 f9) ?v0) f9)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f12 (f5 f7 ?v0)) ?v1) (f5 f7 (f5 (f10 f12 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f11 ?v0) f9) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f10 f11 f9) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f11 (f5 f7 ?v0)) (f5 f7 ?v1)) (f5 f7 (f5 (f10 f11 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f5 f7 ?v0) (f5 (f10 f11 ?v0) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 (f5 f6 ?v0)) (f5 f6 ?v1)) f1) (= (f3 (f4 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 ?v0) f14) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 f14) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 ?v0) ?v1) f1) (= (f3 (f4 (f5 (f10 f11 ?v0) ?v2)) (f5 (f10 f11 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f12 (f5 f6 ?v0)) (f5 f6 ?v1)) (f5 f6 (f5 (f10 f12 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f10 f12 (f5 (f10 f11 ?v0) ?v1)) ?v2) (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v2)) (f5 (f10 f12 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v0))) (= (f5 ?v_0 (f5 (f10 f11 ?v1) ?v2)) (f5 (f10 f11 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f11 (f5 f6 ?v0)) (f5 f6 ?v1)) (f5 f6 (f5 (f10 f11 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f5 f6 ?v2))) (= (f5 (f10 f12 (f5 (f10 f11 ?v0) ?v1)) ?v_0) (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v_0)) (f5 (f10 f12 ?v1) ?v_0))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S3)) (let ((?v_0 (f22 f23 ?v2))) (= (f18 (f19 f24 (f18 (f19 f20 ?v0) ?v1)) ?v_0) (f18 (f19 f20 (f18 (f19 f24 ?v0) ?v_0)) (f18 (f19 f24 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 (f5 f6 ?v0)))) (= (f5 ?v_0 (f5 (f10 f11 ?v1) ?v2)) (f5 (f10 f11 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S7)) (let ((?v_0 (f19 f24 (f22 f23 ?v0)))) (= (f18 ?v_0 (f18 (f19 f20 ?v1) ?v2)) (f18 (f19 f20 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v2))))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f11 (f5 f6 f9)) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f10 f11 ?v0) (f5 f6 f9)) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 (f5 f6 ?v0)) (f5 f6 ?v1)) f1) (= (f3 (f4 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f10 f12 (f5 f6 ?v0)) (f5 (f10 f12 (f5 f6 ?v1)) ?v2)) (f5 (f10 f12 (f5 f6 (f5 (f10 f12 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f12 (f5 f6 ?v0)) (f5 f6 ?v1)) (f5 f6 (f5 (f10 f12 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 f6 (f5 (f10 f12 ?v0) ?v1)) (f5 (f10 f12 (f5 f6 ?v0)) (f5 f6 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f10 f11 (f5 f6 ?v0)) (f5 (f10 f11 (f5 f6 ?v1)) ?v2)) (f5 (f10 f11 (f5 f6 (f5 (f10 f11 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f11 (f5 f6 ?v0)) (f5 f6 ?v1)) (f5 f6 (f5 (f10 f11 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 f6 (f5 (f10 f11 ?v0) ?v1)) (f5 (f10 f11 (f5 f6 ?v0)) (f5 f6 ?v1)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 (f5 f8 ?v0)) f9) f1) (= (f3 (f4 ?v0) f9) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 (f5 f8 ?v0)) (f5 f7 ?v1)) f1) (= (f3 (f4 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 (f5 f8 ?v0)) (f5 f7 ?v1)) f1) (= (f3 (f4 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 (f5 f7 ?v0)) f9) f1) (= (f3 (f4 ?v0) f9) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f9))) (= (= (f3 ?v_0 (f5 f7 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f11 (f5 f8 ?v0)) (f5 f7 ?v1)) (f5 f8 (f5 (f10 f11 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f11 (f5 f7 ?v0)) (f5 f8 ?v1)) (f5 f8 (f5 (f10 f11 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f5 f8 ?v0) (f5 (f10 f11 (f5 (f10 f11 f14) ?v0)) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 ?v0))) (= (= (f3 ?v_0 (f5 (f10 f11 ?v1) f14)) f1) (or (= (f3 ?v_0 ?v1) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f15 ?v0)) (?v_1 (f10 f11 ?v2))) (=> (= (f3 ?v_0 ?v1) f1) (= (= (f3 ?v_0 (f5 ?v_1 ?v3)) f1) (= (f3 ?v_0 (f5 (f10 f11 (f5 ?v_1 (f5 (f10 f12 ?v4) ?v1))) ?v3)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f15 ?v0))) (= (= (f3 ?v_0 (f5 (f10 f11 ?v1) (f5 (f10 f12 ?v0) ?v2))) f1) (= (f3 ?v_0 ?v1) f1)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f5 f6 ?v0))) (= (f5 f6 (f5 f8 ?v0)) (f5 (f10 f11 (f5 (f10 f11 f14) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 (f5 f6 (f5 f8 f9))) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 ?v0) (f5 f6 (f5 f8 f9))) ?v0)))
(assert (= (f5 f6 (f5 f8 f9)) f14))
(assert (= (f22 f23 (f5 f8 f9)) f21))
(assert (= (f5 f6 (f5 f8 f9)) f14))
(assert (= f14 (f5 f6 (f5 f8 f9))))
(assert (= (f17 (f5 f6 (f5 f7 (f5 f8 f9)))) f1))
(assert (= f14 (f5 f6 (f5 f8 f9))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f3 (f4 ?v0) ?v1) f1) (=> (= (f3 ?v2 (f5 (f10 f11 ?v0) f14)) f1) (=> (forall ((?v3 S3)) (=> (= (f3 (f4 ?v0) ?v3) f1) (=> (= (f3 ?v2 ?v3) f1) (= (f3 ?v2 (f5 (f10 f11 ?v3) f14)) f1)))) (= (f3 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f15 ?v0))) (=> (= (f17 ?v0) f1) (=> (= (f3 ?v_0 (f5 (f10 f12 ?v1) ?v2)) f1) (or (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v2) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f22 f23 ?v0)) (?v_0 (f22 f23 ?v1))) (= (f18 (f19 f20 ?v_1) ?v_0) (ite (= (f3 (f4 ?v0) f9) f1) ?v_0 (ite (= (f3 (f4 ?v1) f9) f1) ?v_1 (f22 f23 (f5 (f10 f11 ?v0) ?v1))))))))
(assert (forall ((?v0 S7)) (= (f18 (f19 f24 (f22 f23 (f5 f7 (f5 f8 f9)))) ?v0) (f18 (f19 f20 ?v0) ?v0))))
(assert (forall ((?v0 S7)) (= (f18 (f19 f24 ?v0) (f22 f23 (f5 f7 (f5 f8 f9)))) (f18 (f19 f20 ?v0) ?v0))))
(assert (= (f18 (f19 f20 f21) f21) (f22 f23 (f5 f7 (f5 f8 f9)))))
(assert (let ((?v_2 (f5 f7 (f5 f8 f9)))) (let ((?v_0 (f5 (f10 f11 (f5 (f10 f12 (f5 f6 (f5 f7 ?v_2))) f13)) f14))) (let ((?v_1 (f15 ?v_0))) (or (= (f5 (f10 f25 (f5 f6 f26)) ?v_0) f14) (or (= (f3 ?v_1 f14) f1) (= (f3 ?v_1 (f5 f6 ?v_2)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v1)) ?v1) (f5 (f10 f12 (f5 (f10 f11 ?v0) f14)) ?v1))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f18 (f19 f20 (f18 (f19 f24 ?v0) ?v1)) ?v1) (f18 (f19 f24 (f18 (f19 f20 ?v0) f21)) ?v1))))
(assert (= (= f26 f26) true))
(assert (= (f5 f8 f26) f26))
(assert (forall ((?v0 S3)) (= (= f26 (f5 f8 ?v0)) (= f26 ?v0))))
(assert (forall ((?v0 S3)) (= (= (f5 f8 ?v0) f26) (= ?v0 f26))))
(assert (= (= f26 f9) false))
(assert (= (= f9 f26) false))
(assert (forall ((?v0 S3)) (= (= f26 (f5 f7 ?v0)) false)))
(assert (forall ((?v0 S3)) (= (= (f5 f7 ?v0) f26) false)))
(assert (= (= (f3 (f4 f26) f26) f1) false))
(assert (not (= (f5 f6 f9) (f5 f6 f26))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f26))) (= (= (f3 ?v_0 (f5 f8 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 (f5 f8 ?v0)) f26) f1) (= (f3 (f4 ?v0) f26) f1))))
(assert (= (= (f3 (f4 f26) f9) f1) true))
(assert (= (= (f3 (f4 f9) f26) f1) false))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f26))) (= (= (f3 ?v_0 (f5 f7 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f5 f6 f26))) (= (= (f5 (f10 f12 ?v0) ?v1) f14) (or (and (= ?v0 f14) (= ?v1 f14)) (and (= ?v0 ?v_0) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f5 (f10 f12 ?v0) ?v1) f14) (or (= ?v0 f14) (= ?v0 (f5 f6 f26))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f12 ?v0) ?v1) (f5 (f10 f12 ?v1) ?v0))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f18 (f19 f24 ?v0) ?v1) (f18 (f19 f24 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f10 f12 ?v0)) (?v_0 (f10 f12 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_1 (f19 f24 ?v0)) (?v_0 (f19 f24 ?v1))) (= (f18 ?v_1 (f18 ?v_0 ?v2)) (f18 ?v_0 (f18 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v0))) (= (f5 ?v_0 (f5 (f10 f12 ?v1) ?v2)) (f5 (f10 f12 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f19 f24 ?v0))) (= (f18 ?v_0 (f18 (f19 f24 ?v1) ?v2)) (f18 (f19 f24 (f18 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v0))) (= (f5 (f10 f12 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f10 f12 ?v1) ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f19 f24 ?v0))) (= (f18 (f19 f24 (f18 ?v_0 ?v1)) ?v2) (f18 ?v_0 (f18 (f19 f24 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v0))) (= (f5 (f10 f12 (f5 ?v_0 ?v1)) ?v2) (f5 (f10 f12 (f5 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f19 f24 ?v0))) (= (f18 (f19 f24 (f18 ?v_0 ?v1)) ?v2) (f18 (f19 f24 (f18 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f10 f12 ?v0)) (?v_1 (f5 (f10 f12 ?v2) ?v3))) (= (f5 (f10 f12 (f5 ?v_0 ?v1)) ?v_1) (f5 ?v_0 (f5 (f10 f12 ?v1) ?v_1))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (let ((?v_0 (f19 f24 ?v0)) (?v_1 (f18 (f19 f24 ?v2) ?v3))) (= (f18 (f19 f24 (f18 ?v_0 ?v1)) ?v_1) (f18 ?v_0 (f18 (f19 f24 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f10 f12 (f5 (f10 f12 ?v0) ?v1))) (?v_0 (f10 f12 ?v2))) (= (f5 ?v_1 (f5 ?v_0 ?v3)) (f5 ?v_0 (f5 ?v_1 ?v3))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (let ((?v_1 (f19 f24 (f18 (f19 f24 ?v0) ?v1))) (?v_0 (f19 f24 ?v2))) (= (f18 ?v_1 (f18 ?v_0 ?v3)) (f18 ?v_0 (f18 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f10 f12 ?v0))) (= (f5 (f10 f12 (f5 ?v_0 ?v1)) (f5 (f10 f12 ?v2) ?v3)) (f5 (f10 f12 (f5 ?v_0 ?v2)) (f5 (f10 f12 ?v1) ?v3))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (let ((?v_0 (f19 f24 ?v0))) (= (f18 (f19 f24 (f18 ?v_0 ?v1)) (f18 (f19 f24 ?v2) ?v3)) (f18 (f19 f24 (f18 ?v_0 ?v2)) (f18 (f19 f24 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f11 ?v0) ?v1) (f5 (f10 f11 ?v1) ?v0))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f18 (f19 f20 ?v0) ?v1) (f18 (f19 f20 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f10 f11 ?v0)) (?v_0 (f10 f11 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_1 (f19 f20 ?v0)) (?v_0 (f19 f20 ?v1))) (= (f18 ?v_1 (f18 ?v_0 ?v2)) (f18 ?v_0 (f18 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f11 ?v0))) (= (f5 ?v_0 (f5 (f10 f11 ?v1) ?v2)) (f5 (f10 f11 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f19 f20 ?v0))) (= (f18 ?v_0 (f18 (f19 f20 ?v1) ?v2)) (f18 (f19 f20 (f18 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f11 ?v0))) (= (f5 (f10 f11 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f10 f11 ?v1) ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f19 f20 ?v0))) (= (f18 (f19 f20 (f18 ?v_0 ?v1)) ?v2) (f18 ?v_0 (f18 (f19 f20 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f11 ?v0))) (= (f5 (f10 f11 (f5 ?v_0 ?v1)) ?v2) (f5 (f10 f11 (f5 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f19 f20 ?v0))) (= (f18 (f19 f20 (f18 ?v_0 ?v1)) ?v2) (f18 (f19 f20 (f18 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f10 f11 ?v0))) (= (f5 (f10 f11 (f5 ?v_0 ?v1)) (f5 (f10 f11 ?v2) ?v3)) (f5 (f10 f11 (f5 ?v_0 ?v2)) (f5 (f10 f11 ?v1) ?v3))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (let ((?v_0 (f19 f20 ?v0))) (= (f18 (f19 f20 (f18 ?v_0 ?v1)) (f18 (f19 f20 ?v2) ?v3)) (f18 (f19 f20 (f18 ?v_0 ?v2)) (f18 (f19 f20 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v0))) (= (f5 ?v_0 (f5 (f10 f11 ?v1) ?v2)) (f5 (f10 f11 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f19 f24 ?v0))) (= (f18 ?v_0 (f18 (f19 f20 ?v1) ?v2)) (f18 (f19 f20 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f10 f12 ?v0)) (?v_1 (f10 f12 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f5 (f10 f11 (f5 ?v_0 ?v2)) (f5 ?v_1 ?v3)) (f5 (f10 f11 (f5 ?v_0 ?v3)) (f5 ?v_1 ?v2))))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (let ((?v_0 (f19 f24 ?v0)) (?v_1 (f19 f24 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f18 (f19 f20 (f18 ?v_0 ?v2)) (f18 ?v_1 ?v3)) (f18 (f19 f20 (f18 ?v_0 ?v3)) (f18 ?v_1 ?v2))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f10 f12 (f5 (f10 f11 ?v0) ?v1)) ?v2) (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v2)) (f5 (f10 f12 ?v1) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f18 (f19 f24 (f18 (f19 f20 ?v0) ?v1)) ?v2) (f18 (f19 f20 (f18 (f19 f24 ?v0) ?v2)) (f18 (f19 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v1)) (f5 (f10 f12 ?v2) ?v1)) (f5 (f10 f12 (f5 (f10 f11 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f18 (f19 f20 (f18 (f19 f24 ?v0) ?v1)) (f18 (f19 f24 ?v2) ?v1)) (f18 (f19 f24 (f18 (f19 f20 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f10 f12 ?v0)) (?v_1 (f10 f12 ?v2))) (= (= (f5 (f10 f11 (f5 ?v_0 ?v1)) (f5 ?v_1 ?v3)) (f5 (f10 f11 (f5 ?v_0 ?v3)) (f5 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (let ((?v_0 (f19 f24 ?v0)) (?v_1 (f19 f24 ?v2))) (= (= (f18 (f19 f20 (f18 ?v_0 ?v1)) (f18 ?v_1 ?v3)) (f18 (f19 f20 (f18 ?v_0 ?v3)) (f18 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 f14) ?v0) ?v0)))
(assert (forall ((?v0 S7)) (= (f18 (f19 f24 f21) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 ?v0) f14) ?v0)))
(assert (forall ((?v0 S7)) (= (f18 (f19 f24 ?v0) f21) ?v0)))
(assert (= f21 (f22 f23 (f5 f8 f9))))
(assert (= (f22 f23 (f5 f8 f9)) f21))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f27 (f22 f23 ?v0) (f22 f23 ?v1)) f1) (ite (= (f3 (f4 ?v0) ?v1) f1) (= (f3 (f4 f9) ?v1) f1) false))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f11 ?v0) ?v0) (f5 (f10 f12 (f5 (f10 f11 f14) f14)) ?v0))))
(assert (forall ((?v0 S7)) (= (f18 (f19 f20 ?v0) ?v0) (f18 (f19 f24 (f18 (f19 f20 f21) f21)) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f11 ?v0) (f5 (f10 f12 ?v1) ?v0)) (f5 (f10 f12 (f5 (f10 f11 ?v1) f14)) ?v0))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f18 (f19 f20 ?v0) (f18 (f19 f24 ?v1) ?v0)) (f18 (f19 f24 (f18 (f19 f20 ?v1) f21)) ?v0))))
(assert (let ((?v_1 (f5 f6 f26))) (let ((?v_0 (f5 (f10 f25 ?v_1) (f5 (f10 f11 (f5 (f10 f12 (f5 f6 (f5 f7 (f5 f7 (f5 f8 f9))))) f13)) f14)))) (or (= ?v_0 f14) (or (= ?v_0 f28) (= ?v_0 ?v_1))))))
(assert (let ((?v_0 (f5 (f10 f11 (f5 (f10 f12 (f5 f6 (f5 f7 (f5 f7 (f5 f8 f9))))) f13)) f14))) (= (f3 (f15 ?v_0) (f5 (f10 f29 f14) (f5 (f10 f25 (f5 f6 f26)) ?v_0))) f1)))
(assert (let ((?v_0 (f5 (f10 f11 (f5 (f10 f12 (f5 f6 (f5 f7 (f5 f7 (f5 f8 f9))))) f13)) f14))) (= (f3 (f30 (f31 f14) (f5 (f10 f25 (f5 f6 f26)) ?v_0)) ?v_0) f1)))
(assert (forall ((?v0 S3)) (=> (= (f3 (f4 f14) ?v0) f1) (exists ((?v1 S3)) (and (= (f17 ?v1) f1) (= (f3 (f15 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S3)) (= (f3 (f4 ?v0) (f5 (f10 f11 ?v0) f14)) f1)))
(assert (forall ((?v0 S7)) (= (f27 ?v0 (f18 (f19 f20 ?v0) f21)) f1)))
(assert (forall ((?v0 S7)) (= (f32 ?v0 f33) f1)))
(assert (forall ((?v0 S3)) (= (f3 (f15 ?v0) f28) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 f6 (f5 (f10 f29 ?v0) ?v1)) (f5 (f10 f29 (f5 f6 ?v0)) (f5 f6 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f28))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 ?v_0 ?v2) f1) (=> (= (f3 (f30 (f31 ?v0) ?v1) ?v2) f1) (=> (= (f3 (f4 ?v0) ?v2) f1) (=> (= (f3 (f4 ?v1) ?v2) f1) (= ?v0 ?v1))))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f28) ?v0) f1) (=> (= (f3 (f4 ?v0) ?v1) f1) (not (= (f3 (f30 (f31 ?v0) f28) ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (f3 (f30 (f31 ?v0) f28) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f31 ?v0))) (=> (= (f3 (f30 ?v_0 ?v1) ?v2) f1) (=> (= ?v1 ?v3) (=> (= (f3 (f30 (f31 ?v3) ?v4) ?v2) f1) (= (f3 (f30 ?v_0 ?v4) ?v2) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f30 (f31 ?v0) f28) ?v1) f1) (= (f3 (f15 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f30 (f31 ?v0) f28) ?v1) f1) (= (f3 (f15 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 ?v0) ?v1) f1) (= (f3 (f4 (f5 (f10 f29 ?v0) ?v1)) f28) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f15 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 ?v_0 ?v2) f1) (= (f3 ?v_0 (f5 (f10 f29 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f31 ?v3))) (=> (= (f3 (f30 (f31 ?v0) ?v1) ?v2) f1) (= (= (f3 (f30 ?v_0 (f5 (f10 f12 ?v0) ?v4)) ?v2) f1) (= (f3 (f30 ?v_0 (f5 (f10 f12 ?v1) ?v4)) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f31 ?v3)) (?v_1 (f10 f12 ?v4))) (=> (= (f3 (f30 (f31 ?v0) ?v1) ?v2) f1) (= (= (f3 (f30 ?v_0 (f5 ?v_1 ?v0)) ?v2) f1) (= (f3 (f30 ?v_0 (f5 ?v_1 ?v1)) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f30 (f31 ?v0) ?v1) ?v2) f1) (= (f3 (f30 (f31 (f5 (f10 f11 ?v0) ?v3)) (f5 (f10 f11 ?v1) ?v3)) ?v2) f1))))
(assert (forall ((?v0 S7)) (= (f18 (f19 f24 f33) ?v0) f33)))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 f28) ?v0) f28)))
(assert (forall ((?v0 S7)) (= (f18 (f19 f24 ?v0) f33) f33)))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 ?v0) f28) f28)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 (f10 f12 ?v0) ?v1) f28) (or (= ?v0 f28) (= ?v1 f28)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (not (= ?v0 f33)) (=> (not (= ?v1 f33)) (not (= (f18 (f19 f24 ?v0) ?v1) f33))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 f28)) (=> (not (= ?v1 f28)) (not (= (f5 (f10 f12 ?v0) ?v1) f28))))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f18 (f19 f24 ?v0) ?v1) f33) (or (= ?v0 f33) (= ?v1 f33)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f5 (f10 f12 ?v0) ?v1) f28) (or (= ?v0 f28) (= ?v1 f28)))))
(assert (not (= f14 f28)))
(assert (not (= f21 f33)))
(assert (not (= f28 f14)))
(assert (not (= f33 f21)))
(assert (forall ((?v0 S7)) (=> (= (f32 f33 ?v0) f1) (= ?v0 f33))))
(assert (forall ((?v0 S3)) (=> (= (f3 (f15 f28) ?v0) f1) (= ?v0 f28))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f17 ?v0) f1) (=> (not (= (f3 (f30 (f31 ?v1) f28) ?v0) f1)) (=> (not (= (f3 (f30 (f31 ?v2) f28) ?v0) f1)) (not (= (f3 (f30 (f31 (f5 (f10 f12 ?v1) ?v2)) f28) ?v0) f1)))))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f29 ?v0) f9) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f29 (f5 f7 ?v0)) (f5 f7 ?v1)) (f5 f7 (f5 (f10 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f10 f12 (f5 (f10 f29 ?v0) ?v1)) ?v2) (f5 (f10 f29 (f5 (f10 f12 ?v0) ?v2)) (f5 (f10 f12 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v0))) (= (f5 ?v_0 (f5 (f10 f29 ?v1) ?v2)) (f5 (f10 f29 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f5 (f10 f29 ?v0) ?v1) ?v2) (= ?v0 (f5 (f10 f11 ?v2) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f15 ?v0))) (=> (= (f3 ?v_0 (f5 (f10 f29 ?v1) ?v2)) f1) (=> (= (f3 ?v_0 ?v2) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S7)) (= (f18 (f19 f24 ?v0) f33) f33)))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 ?v0) f28) f28)))
(assert (forall ((?v0 S7)) (= (f18 (f19 f24 f33) ?v0) f33)))
(assert (forall ((?v0 S3)) (= (f5 (f10 f12 f28) ?v0) f28)))
(assert (forall ((?v0 S3)) (= (= (f5 (f10 f11 ?v0) ?v0) f28) (= ?v0 f28))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 (f5 (f10 f11 ?v0) ?v1)) (= ?v1 f28))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= ?v0 (f18 (f19 f20 ?v0) ?v1)) (= ?v1 f33))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f11 ?v0) f28) ?v0)))
(assert (forall ((?v0 S7)) (= (f18 (f19 f20 ?v0) f33) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f10 f11 f28) ?v0) ?v0)))
(assert (forall ((?v0 S7)) (= (f18 (f19 f20 f33) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (= (= (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v1)) ?v2) (f5 (f10 f11 (f5 (f10 f12 ?v3) ?v1)) ?v4)) (= (f5 (f10 f11 (f5 (f10 f12 (f5 (f10 f29 ?v0) ?v3)) ?v1)) ?v2) ?v4))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (= (= (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v1)) ?v2) (f5 (f10 f11 (f5 (f10 f12 ?v3) ?v1)) ?v4)) (= ?v2 (f5 (f10 f11 (f5 (f10 f12 (f5 (f10 f29 ?v3) ?v0)) ?v1)) ?v4)))))
(assert (= f9 f28))
(assert (not (= f28 f14)))
(assert (forall ((?v0 S3)) (= (f5 (f10 f11 ?v0) f28) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f10 f11 f28) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v2))) (=> (= (f3 (f4 ?v0) ?v1) f1) (=> (= (f3 (f4 ?v2) f28) f1) (= (f3 (f4 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v0)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 ?v0) ?v1) f1) (=> (= (f3 (f4 ?v2) f28) f1) (= (f3 (f4 (f5 (f10 f12 ?v1) ?v2)) (f5 (f10 f12 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f19 f24 ?v2))) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f27 f33 ?v2) f1) (= (f27 (f18 ?v_0 ?v0) (f18 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v2))) (=> (= (f3 (f4 ?v0) ?v1) f1) (=> (= (f3 (f4 f28) ?v2) f1) (= (f3 (f4 (f5 ?v_0 ?v0)) (f5 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f19 f24 ?v2))) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f27 f33 ?v2) f1) (= (f27 (f18 ?v_0 ?v0) (f18 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v2))) (=> (= (f3 (f4 ?v0) ?v1) f1) (=> (= (f3 (f4 f28) ?v2) f1) (= (f3 (f4 (f5 ?v_0 ?v0)) (f5 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= (f27 ?v0 ?v1) f1) (=> (= (f27 f33 ?v2) f1) (= (f27 (f18 (f19 f24 ?v0) ?v2) (f18 (f19 f24 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 ?v0) ?v1) f1) (=> (= (f3 (f4 f28) ?v2) f1) (= (f3 (f4 (f5 (f10 f12 ?v0) ?v2)) (f5 (f10 f12 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 ?v0) f28) f1) (=> (= (f3 (f4 ?v1) f28) f1) (= (f3 (f4 f28) (f5 (f10 f12 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f27 ?v0 f33) f1) (=> (= (f27 f33 ?v1) f1) (= (f27 (f18 (f19 f24 ?v0) ?v1) f33) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 ?v0) f28) f1) (=> (= (f3 (f4 f28) ?v1) f1) (= (f3 (f4 (f5 (f10 f12 ?v0) ?v1)) f28) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v0))) (=> (= (f3 (f4 ?v0) f28) f1) (= (= (f3 (f4 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2)) f1) (= (f3 (f4 ?v2) ?v1) f1))))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f27 f33 (f18 (f19 f24 ?v0) ?v1)) f1) (=> (= (f27 f33 ?v1) f1) (= (f27 f33 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f28))) (=> (= (f3 ?v_0 (f5 (f10 f12 ?v0) ?v1)) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f27 f33 (f18 (f19 f24 ?v0) ?v1)) f1) (=> (= (f27 f33 ?v0) f1) (= (f27 f33 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f28))) (=> (= (f3 ?v_0 (f5 (f10 f12 ?v0) ?v1)) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f27 f33 ?v0) f1) (=> (= (f27 ?v1 f33) f1) (= (f27 (f18 (f19 f24 ?v1) ?v0) f33) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f28) ?v0) f1) (=> (= (f3 (f4 ?v1) f28) f1) (= (f3 (f4 (f5 (f10 f12 ?v1) ?v0)) f28) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f27 f33 ?v0) f1) (=> (= (f27 ?v1 f33) f1) (= (f27 (f18 (f19 f24 ?v0) ?v1) f33) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f28) ?v0) f1) (=> (= (f3 (f4 ?v1) f28) f1) (= (f3 (f4 (f5 (f10 f12 ?v0) ?v1)) f28) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f27 f33 ?v0) f1) (=> (= (f27 f33 ?v1) f1) (= (f27 f33 (f18 (f19 f24 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f28))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f5 (f10 f12 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v0))) (=> (= (f3 (f4 f28) ?v0) f1) (= (= (f3 (f4 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2)) f1) (= (f3 (f4 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v0))) (= (= (f3 (f4 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2)) f1) (or (and (= (f3 (f4 f28) ?v0) f1) (= (f3 (f4 ?v1) ?v2) f1)) (and (= (f3 (f4 ?v0) f28) f1) (= (f3 (f4 ?v2) ?v1) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f3 (f4 (f5 (f10 f12 ?v0) ?v1)) (f5 (f10 f12 ?v2) ?v1)) f1) (or (and (= (f3 (f4 f28) ?v1) f1) (= (f3 (f4 ?v0) ?v2) f1)) (and (= (f3 (f4 ?v1) f28) f1) (= (f3 (f4 ?v2) ?v0) f1))))))
(assert (forall ((?v0 S3)) (not (= (f3 (f4 (f5 (f10 f12 ?v0) ?v0)) f28) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 ?v1))) (=> (= (f3 (f4 f28) ?v0) f1) (=> (= (f3 ?v_0 ?v2) f1) (= (f3 ?v_0 (f5 (f10 f11 ?v0) ?v2)) f1))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= (f27 f33 ?v0) f1) (=> (= (f27 ?v1 ?v2) f1) (= (f27 ?v1 (f18 (f19 f20 ?v0) ?v2)) f1)))))
(assert (= (f3 (f4 f28) f14) f1))
(assert (= (f27 f33 f21) f1))
(assert (not (= (f3 (f4 f14) f28) f1)))
(assert (not (= (f27 f21 f33) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v0))) (= (= (f3 (f15 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2)) f1) (or (= ?v0 f28) (= (f3 (f15 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f3 (f15 (f5 (f10 f12 ?v0) ?v1)) (f5 (f10 f12 ?v2) ?v1)) f1) (or (= ?v1 f28) (= (f3 (f15 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f17 ?v0) f1) (=> (= (f3 (f4 f28) ?v1) f1) (=> (= (f3 (f30 (f31 (f5 (f10 f12 ?v1) ?v2)) f28) ?v0) f1) (or (= (f3 (f30 (f31 ?v1) f28) ?v0) f1) (= (f3 (f30 (f31 ?v2) f28) ?v0) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f17 ?v0) f1) (=> (= (f3 (f4 f28) ?v1) f1) (=> (and (not (= (f3 (f30 (f31 ?v1) f28) ?v0) f1)) (not (= (f3 (f30 (f31 ?v2) f28) ?v0) f1))) (not (= (f3 (f30 (f31 (f5 (f10 f12 ?v1) ?v2)) f28) ?v0) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (= (= (f3 (f4 (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v1)) ?v2)) (f5 (f10 f11 (f5 (f10 f12 ?v3) ?v1)) ?v4)) f1) (= (f3 (f4 (f5 (f10 f11 (f5 (f10 f12 (f5 (f10 f29 ?v0) ?v3)) ?v1)) ?v2)) ?v4) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (= (= (f3 (f4 (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v1)) ?v2)) (f5 (f10 f11 (f5 (f10 f12 ?v3) ?v1)) ?v4)) f1) (= (f3 (f4 ?v2) (f5 (f10 f11 (f5 (f10 f12 (f5 (f10 f29 ?v3) ?v0)) ?v1)) ?v4)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f5 f6 ?v2))) (= (f5 (f10 f12 (f5 (f10 f29 ?v0) ?v1)) ?v_0) (f5 (f10 f29 (f5 (f10 f12 ?v0) ?v_0)) (f5 (f10 f12 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 (f5 f6 ?v0)))) (= (f5 ?v_0 (f5 (f10 f29 ?v1) ?v2)) (f5 (f10 f29 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f29 (f5 f8 ?v0)) (f5 f8 ?v1)) (f5 f7 (f5 (f10 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f10 f29 (f5 f8 ?v0)) (f5 f7 ?v1)) (f5 f8 (f5 (f10 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f10 f29 f9))) (= (f5 ?v_0 (f5 f7 ?v0)) (f5 f7 (f5 ?v_0 ?v0))))))
(assert (= (f3 (f4 f28) (f5 (f10 f11 f14) f14)) f1))
(assert (= (f27 f33 (f18 (f19 f20 f21) f21)) f1))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 (f5 (f10 f11 ?v0) ?v0)) f28) f1) (= (f3 (f4 ?v0) f28) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f10 f12 ?v0))) (=> (not (= ?v0 f28)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f5 (f10 f11 ?v1) (f5 ?v_0 ?v3)) (f5 (f10 f11 ?v2) (f5 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7) (?v4 S7)) (let ((?v_0 (f19 f24 ?v0))) (=> (not (= ?v0 f33)) (=> (and (= ?v1 ?v2) (not (= ?v3 ?v4))) (not (= (f18 (f19 f20 ?v1) (f18 ?v_0 ?v3)) (f18 (f19 f20 ?v2) (f18 ?v_0 ?v4)))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v0)) (f5 (f10 f12 ?v1) ?v1)) f28) (and (= ?v0 f28) (= ?v1 f28)))))
(assert (= (f22 f23 f9) f33))
(assert (= (f5 f6 f9) f28))
(assert (= (f5 f6 f9) f28))
(assert (= f28 (f5 f6 f9)))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 (f5 f8 ?v0)) f28) f1) (= (f3 (f4 ?v0) f28) f1))))
(assert (= (= (f3 (f4 f9) f28) f1) false))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 (f5 f7 ?v0)) f28) f1) (= (f3 (f4 ?v0) f28) f1))))
(assert (= f28 (f5 f6 f9)))
(assert (= (f3 (f4 f28) f14) f1))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v2))) (=> (= (f3 (f4 ?v0) ?v1) f1) (=> (= (f3 (f4 f28) ?v2) f1) (= (f3 (f4 (f5 ?v_0 ?v0)) (f5 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f28))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 (f5 (f10 f12 ?v0) ?v1)) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (not (= (f5 (f10 f11 (f5 (f10 f11 f14) ?v0)) ?v0) f28))))
(assert (= (= (f3 (f4 f26) f28) f1) true))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f28) ?v0) f1) (=> (= (f3 (f4 ?v0) ?v1) f1) (not (= (f3 (f15 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f12 ?v0))) (=> (= (f3 (f15 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2)) f1) (=> (not (= ?v0 f28)) (= (f3 (f15 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f10 f11 (f5 f6 ?v0)) (f5 (f10 f29 (f5 f6 ?v1)) ?v2)) (f5 (f10 f29 (f5 f6 (f5 (f10 f11 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3)) (= (f5 (f10 f29 f9) (f5 f8 ?v0)) (f5 f8 (f5 (f10 f29 f26) ?v0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f10 f29 f26))) (= (f5 ?v_0 (f5 f8 ?v0)) (f5 f7 (f5 ?v_0 ?v0))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f10 f29 f26))) (= (f5 ?v_0 (f5 f7 ?v0)) (f5 f8 (f5 ?v_0 ?v0))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f28) (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v0)) (f5 (f10 f12 ?v1) ?v1))) f1) (or (not (= ?v0 f28)) (not (= ?v1 f28))))))
(assert (forall ((?v0 S3) (?v1 S3)) (not (= (f3 (f4 (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v0)) (f5 (f10 f12 ?v1) ?v1))) f28) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 (f4 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f5 f6 ?v0))) (= (f5 f6 (f5 f7 ?v0)) (f5 (f10 f11 (f5 (f10 f11 f28) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= (f32 ?v0 ?v1) f1) (=> (= (f32 ?v1 ?v2) f1) (= (f32 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f15 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f15 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S7)) (= (f32 ?v0 ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f3 (f15 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f28) ?v0) f1) (= (= (f5 (f10 f12 ?v0) ?v1) f14) (and (= ?v0 f14) (= ?v1 f14))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 (f5 (f10 f11 (f5 (f10 f11 f14) ?v0)) ?v0)) f28) f1) (= (f3 (f4 ?v0) f28) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 (f5 f6 ?v0)) f28) f1) (= (f3 (f4 ?v0) f9) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f28) (f5 f6 ?v0)) f1) (= (f3 (f4 f9) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f31 ?v1))) (=> (= (f3 (f4 (f5 f6 (f5 f7 (f5 f8 f9)))) ?v0) f1) (=> (= (f3 (f30 ?v_0 (f5 f6 f26)) ?v0) f1) (not (= (f3 (f30 ?v_0 f14) ?v0) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v1)) (f5 (f10 f11 (f5 (f10 f12 ?v2) ?v1)) ?v3)) (f5 (f10 f11 (f5 (f10 f12 (f5 (f10 f11 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (= (f18 (f19 f20 (f18 (f19 f24 ?v0) ?v1)) (f18 (f19 f20 (f18 (f19 f24 ?v2) ?v1)) ?v3)) (f18 (f19 f20 (f18 (f19 f24 (f18 (f19 f20 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f10 f12 (f5 (f10 f11 ?v0) ?v1)) ?v2) (f5 (f10 f11 (f5 (f10 f12 ?v0) ?v2)) (f5 (f10 f12 ?v1) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f18 (f19 f24 (f18 (f19 f20 ?v0) ?v1)) ?v2) (f18 (f19 f20 (f18 (f19 f24 ?v0) ?v2)) (f18 (f19 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= (f32 (f18 (f19 f24 ?v0) ?v1) ?v2) f1) (= (f32 ?v1 ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f15 (f5 (f10 f12 ?v0) ?v1)) ?v2) f1) (= (f3 (f15 ?v1) ?v2) f1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= (f32 (f18 (f19 f24 ?v0) ?v1) ?v2) f1) (= (f32 ?v0 ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f15 (f5 (f10 f12 ?v0) ?v1)) ?v2) f1) (= (f3 (f15 ?v0) ?v2) f1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= ?v0 (f18 (f19 f24 ?v1) ?v2)) (= (f32 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= ?v0 (f5 (f10 f12 ?v1) ?v2)) (= (f3 (f15 ?v1) ?v0) f1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (=> (= (f32 ?v0 ?v1) f1) (=> (= (f32 ?v2 ?v3) f1) (= (f32 (f18 (f19 f24 ?v0) ?v2) (f18 (f19 f24 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f15 ?v0) ?v1) f1) (=> (= (f3 (f15 ?v2) ?v3) f1) (= (f3 (f15 (f5 (f10 f12 ?v0) ?v2)) (f5 (f10 f12 ?v1) ?v3)) f1)))))
(check-sat)
(exit)