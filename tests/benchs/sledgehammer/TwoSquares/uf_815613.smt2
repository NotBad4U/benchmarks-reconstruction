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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 (S3 S2) S2)
(declare-fun f5 (S4 S2) S3)
(declare-fun f6 () S4)
(declare-fun f7 () S2)
(declare-fun f8 (S5 S6) S2)
(declare-fun f9 () S5)
(declare-fun f10 () S6)
(declare-fun f11 () S4)
(declare-fun f12 () S3)
(declare-fun f13 () S3)
(declare-fun f14 () S3)
(declare-fun f15 () S2)
(declare-fun f16 () S2)
(declare-fun f17 () S6)
(declare-fun f18 (S2) S1)
(declare-fun f19 (S6 S6) S1)
(declare-fun f20 () S2)
(declare-fun f21 (S2) S1)
(declare-fun f22 () S6)
(declare-fun f23 () S2)
(declare-fun f24 () S2)
(declare-fun f25 (S7 S6) S6)
(declare-fun f26 (S8 S6) S7)
(declare-fun f27 () S8)
(declare-fun f28 () S6)
(declare-fun f29 (S9 S2) S6)
(declare-fun f30 () S9)
(declare-fun f31 () S8)
(declare-fun f32 () S6)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 (f5 f6 f7) (f8 f9 f10)) (f4 (f5 f6 (f4 (f5 f11 (f4 f12 (f4 f13 (f4 f13 (f4 f14 f15))))) f16)) f7)) f1)))
(assert (let ((?v_0 (f4 (f5 f6 (f4 (f5 f11 (f4 f12 (f4 f13 (f4 f13 (f4 f14 f15))))) f16)) f7)) (?v_1 (f4 (f5 f6 f7) (f8 f9 f17)))) (and (= (f3 ?v_1 ?v_0) f1) (= (f18 (f4 (f5 f11 ?v_0) ?v_1)) f1))))
(assert (= (f19 f10 f17) f1))
(assert (= (f19 f10 f17) f1))
(assert (= (f3 f7 f20) f1))
(assert (let ((?v_0 (f4 (f5 f6 (f4 (f5 f11 (f4 f12 (f4 f13 (f4 f13 (f4 f14 f15))))) f16)) f7)) (?v_1 (f4 (f5 f6 f7) (f8 f9 f17)))) (and (= (f3 ?v_1 ?v_0) f1) (= (f18 (f4 (f5 f11 ?v_0) ?v_1)) f1))))
(assert (let ((?v_0 (f4 (f5 f6 (f4 (f5 f11 (f4 f12 (f4 f13 (f4 f13 (f4 f14 f15))))) f16)) f7)) (?v_1 (f4 (f5 f6 f7) (f8 f9 f17)))) (not (=> (= (f3 ?v_1 ?v_0) f1) (not (= (f18 (f4 (f5 f11 ?v_0) ?v_1)) f1))))))
(assert (= (f21 (f4 (f5 f6 (f4 (f5 f11 (f4 f12 (f4 f13 (f4 f13 (f4 f14 f15))))) f16)) f7)) f1))
(assert (not (= (f18 (f4 (f5 f11 (f4 (f5 f6 (f4 (f5 f11 (f4 f12 (f4 f13 (f4 f13 (f4 f14 f15))))) f16)) f7)) (f4 (f5 f6 f7) (f8 f9 f22)))) f1)))
(assert (= (f3 f20 (f4 (f5 f6 (f4 (f5 f11 (f4 f12 (f4 f13 (f4 f13 (f4 f14 f15))))) f16)) f7)) f1))
(assert (= (f3 f23 (f4 (f5 f6 (f4 (f5 f11 (f4 f12 (f4 f13 (f4 f13 (f4 f14 f15))))) f16)) f7)) f1))
(assert (= (f18 (f4 (f5 f11 (f4 (f5 f6 (f4 (f5 f11 (f4 f12 (f4 f13 (f4 f13 (f4 f14 f15))))) f16)) f7)) f20)) f1))
(assert (= (f18 (f4 (f5 f11 (f4 (f5 f6 (f4 (f5 f11 (f4 f12 (f4 f13 (f4 f13 (f4 f14 f15))))) f16)) f7)) f24)) f1))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f7) (f4 f12 ?v0)) (f4 f12 (f4 (f5 f6 (f4 f14 f15)) ?v0)))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 (f4 f12 ?v0)) f7) (f4 f12 (f4 (f5 f6 ?v0) (f4 f14 f15))))))
(assert (forall ((?v0 S2)) (= (= (f3 f7 (f4 f12 ?v0)) f1) (= (f3 (f4 f14 f15) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f12 ?v0) f7) f1) (= (f3 ?v0 (f4 f14 f15)) f1))))
(assert (= (f4 (f5 f6 f7) f7) (f4 f12 (f4 f13 (f4 f14 f15)))))
(assert (= (f4 (f5 f6 f7) f7) (f4 f12 (f4 f13 (f4 f14 f15)))))
(assert (= (f25 (f26 f27 f28) f28) (f29 f30 (f4 f13 (f4 f14 f15)))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f11 ?v0) (f4 f12 (f4 f13 (f4 f14 f15)))) (f4 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f11 ?v0) (f4 f12 (f4 f13 (f4 f14 f15)))) (f4 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f25 (f26 f31 ?v0) (f29 f30 (f4 f13 (f4 f14 f15)))) (f25 (f26 f27 ?v0) ?v0))))
(assert (= (f19 f22 f32) f1))
(assert (= (f19 f22 f17) f1))
(assert (= (f3 f23 f24) f1))
(assert (= (f3 f23 (f4 (f5 f6 f7) (f8 f9 f17))) f1))
(assert (= (f3 f24 (f4 (f5 f6 f7) (f8 f9 f17))) f1))
(assert (= (f8 f9 f22) f23))
(assert (forall ((?v0 S6)) (= (= (f8 f9 ?v0) f23) (= ?v0 f22))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f6 ?v0) ?v0) f23) (= ?v0 f23))))
(assert (= f15 f23))
(assert (not (= f23 f7)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f23) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f23) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (= (f3 f23 (f8 f9 ?v0)) f1) (= (f19 f22 ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 (f5 f6 ?v0) ?v0) f23) f1) (= (f3 ?v0 f23) f1))))
(assert (= (f29 f30 f15) f22))
(assert (= (f4 f12 f15) f23))
(assert (= (f4 f12 f15) f23))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S2)) (= (f4 (f5 f6 (f8 f9 ?v0)) (f4 (f5 f6 (f8 f9 ?v1)) ?v2)) (f4 (f5 f6 (f8 f9 (f25 (f26 f27 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f4 (f5 f6 (f8 f9 ?v0)) (f8 f9 ?v1)) (f8 f9 (f25 (f26 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f4 (f5 f11 (f8 f9 ?v0)) (f8 f9 ?v1)) (f8 f9 (f25 (f26 f31 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f8 f9 (f25 (f26 f31 ?v0) ?v1)) (f4 (f5 f11 (f8 f9 ?v0)) (f8 f9 ?v1)))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f14 ?v0) f23) f1) (= (f3 ?v0 f23) f1))))
(assert (= (= (f3 f15 f23) f1) false))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f13 ?v0) f23) f1) (= (f3 ?v0 f23) f1))))
(assert (= (f8 f9 f28) f7))
(assert (= f23 (f4 f12 f15)))
(assert (= (f3 f23 f7) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f11 ?v2))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 f23 ?v2) f1) (= (f3 (f4 ?v_0 ?v0) (f4 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2)) (not (= (f4 (f5 f6 (f4 (f5 f6 f7) ?v0)) ?v0) f23))))
(assert (forall ((?v0 S6)) (not (= (f3 (f8 f9 ?v0) f23) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (let ((?v_0 (f5 f11 (f8 f9 ?v2)))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f19 f22 ?v2) f1) (= (f3 (f4 ?v_0 ?v0) (f4 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f4 f12 ?v0))) (= (f4 f12 (f4 f13 ?v0)) (f4 (f5 f6 (f4 (f5 f6 f23) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f23 ?v0) f1) (= (= (f4 (f5 f11 ?v0) ?v1) f7) (and (= ?v0 f7) (= ?v1 f7))))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 (f5 f6 (f4 (f5 f6 f7) ?v0)) ?v0) f23) f1) (= (f3 ?v0 f23) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f12 ?v0) f23) f1) (= (f3 ?v0 f15) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f23 (f4 f12 ?v0)) f1) (= (f3 f15 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f12 ?v0) (f4 f12 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S6)) (let ((?v_0 (f29 f30 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f12 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f14 ?v0) (f4 f14 ?v1)) (= ?v0 ?v1))))
(assert (= (= f15 f15) true))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f13 ?v0) (f4 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 ?v0 ?v1) f1) (or (= ?v0 ?v1) (= (f3 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f11 ?v0))) (= (f4 (f5 f11 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f11 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f11 ?v0) ?v1) (f4 (f5 f11 ?v1) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 f12 ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v0))) (= (f4 (f5 f6 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f6 ?v1) ?v2))))))
(check-sat)
(exit)
