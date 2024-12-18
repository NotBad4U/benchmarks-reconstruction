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
(declare-fun f23 () S6)
(declare-fun f24 () S8)
(declare-fun f25 (S3 S3) S1)
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
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 ?v0) (f14 f21 (f14 f15 (f14 f16 f17)))) (f14 (f19 f22 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 ?v0) (f12 f13 (f14 f15 (f14 f16 f17)))) (f3 (f4 f9 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 ?v0) (f14 f21 (f14 f15 (f14 f16 f17)))) (f14 (f19 f22 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 ?v0) (f12 f13 (f14 f15 (f14 f16 f17)))) (f3 (f4 f9 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 (f14 f21 (f14 f15 (f14 f16 f17)))) ?v0) (f14 (f19 f22 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) ?v0) (f3 (f4 f9 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 (f14 f21 (f14 f15 (f14 f16 f17)))) ?v0) (f14 (f19 f22 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) ?v0) (f3 (f4 f9 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f7 ?v0) (f12 f13 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f7 ?v0) (f12 f13 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 ?v0) (f14 f21 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 ?v0) (f12 f13 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 (f14 f21 (f14 f16 f17))) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f8 (f12 f13 (f14 f16 f17))) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f19 f22 ?v0) f17) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f19 f22 f17) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f22 (f14 f15 ?v0)) (f14 f15 ?v1)) (f14 f15 (f14 (f19 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (f14 f15 ?v0) (f14 (f19 f22 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f14 (f19 f20 f17) ?v0) f17)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f20 (f14 f15 ?v0)) ?v1) (f14 f15 (f14 (f19 f20 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (= (f14 (f19 f22 ?v0) ?v0) f23) (= ?v0 f23))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f9 ?v0) ?v0) f18) (= ?v0 f18))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f20 (f14 f16 ?v0)) ?v1) (f14 (f19 f22 (f14 f15 (f14 (f19 f20 ?v0) ?v1))) ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f22 (f14 f16 ?v0)) (f14 f15 ?v1)) (f14 f16 (f14 (f19 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f22 (f14 f15 ?v0)) (f14 f16 ?v1)) (f14 f16 (f14 (f19 f22 ?v0) ?v1)))))
(assert (= (f14 f21 f17) f23))
(assert (= (f12 f13 f17) f18))
(assert (= (f14 f21 f17) f23))
(assert (= (f12 f13 f17) f18))
(assert (forall ((?v0 S6)) (let ((?v_0 (f14 f21 ?v0))) (= (f14 f21 (f14 f15 ?v0)) (f14 (f19 f22 (f14 (f19 f22 f23) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f12 f13 ?v0))) (= (f12 f13 (f14 f15 ?v0)) (f3 (f4 f9 (f3 (f4 f9 f18) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S3)) (let ((?v_0 (f12 f13 ?v1))) (= (= (f3 (f4 f7 ?v0) ?v_0) ?v2) (ite (not (= ?v_0 f18)) (= ?v0 (f3 (f4 f8 ?v2) ?v_0)) (= ?v2 f18))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6)) (let ((?v_0 (f12 f13 ?v2))) (= (= (f3 (f4 f7 ?v0) ?v1) ?v_0) (ite (not (= ?v1 f18)) (= ?v0 (f3 (f4 f8 ?v_0) ?v1)) (= ?v_0 f18))))))
(assert (forall ((?v0 S6) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f13 ?v0))) (= (= ?v_0 (f3 (f4 f7 ?v1) ?v2)) (ite (not (= ?v2 f18)) (= (f3 (f4 f8 ?v_0) ?v2) ?v1) (= ?v_0 f18))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6)) (let ((?v_0 (f12 f13 ?v2))) (= (= ?v0 (f3 (f4 f7 ?v1) ?v_0)) (ite (not (= ?v_0 f18)) (= (f3 (f4 f8 ?v0) ?v_0) ?v1) (= ?v0 f18))))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f7 ?v0) (f12 f13 f17)) f18)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 f21 ?v0) (f14 f21 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f12 f13 ?v0) (f12 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f14 f21 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S3)) (let ((?v_0 (f12 f13 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 f16 ?v0) (f14 f16 ?v1)) (= ?v0 ?v1))))
(assert (= (= f17 f17) true))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 f15 ?v0) (f14 f15 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f14 (f19 f20 (f14 f21 ?v0)) (f14 (f19 f20 (f14 f21 ?v1)) ?v2)) (f14 (f19 f20 (f14 f21 (f14 (f19 f20 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (= (f3 (f4 f8 (f12 f13 ?v0)) (f3 (f4 f8 (f12 f13 ?v1)) ?v2)) (f3 (f4 f8 (f12 f13 (f14 (f19 f20 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f20 (f14 f21 ?v0)) (f14 f21 ?v1)) (f14 f21 (f14 (f19 f20 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f3 (f4 f8 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f14 (f19 f20 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 f21 (f14 (f19 f20 ?v0) ?v1)) (f14 (f19 f20 (f14 f21 ?v0)) (f14 f21 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f12 f13 (f14 (f19 f20 ?v0) ?v1)) (f3 (f4 f8 (f12 f13 ?v0)) (f12 f13 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f14 (f19 f22 (f14 f21 ?v0)) (f14 (f19 f22 (f14 f21 ?v1)) ?v2)) (f14 (f19 f22 (f14 f21 (f14 (f19 f22 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (= (f3 (f4 f9 (f12 f13 ?v0)) (f3 (f4 f9 (f12 f13 ?v1)) ?v2)) (f3 (f4 f9 (f12 f13 (f14 (f19 f22 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 (f19 f22 (f14 f21 ?v0)) (f14 f21 ?v1)) (f14 f21 (f14 (f19 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f3 (f4 f9 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f14 (f19 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 f21 (f14 (f19 f22 ?v0) ?v1)) (f14 (f19 f22 (f14 f21 ?v0)) (f14 f21 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f12 f13 (f14 (f19 f22 ?v0) ?v1)) (f3 (f4 f9 (f12 f13 ?v0)) (f12 f13 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (f14 (f19 f24 (f14 (f19 f22 ?v0) ?v1)) (f14 (f19 f22 ?v2) ?v3)) (f14 (f19 f22 (f14 (f19 f24 ?v0) ?v2)) (f14 (f19 f24 ?v1) ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (f3 (f4 f5 (f3 (f4 f9 ?v0) ?v1)) (f3 (f4 f9 ?v2) ?v3)) (f3 (f4 f9 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v3)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f14 f21 (f14 (f19 f24 ?v0) ?v1)) (f14 (f19 f24 (f14 f21 ?v0)) (f14 f21 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f12 f13 (f14 (f19 f24 ?v0) ?v1)) (f3 (f4 f5 (f12 f13 ?v0)) (f12 f13 ?v1)))))
(assert (forall ((?v0 S6)) (= (= (f14 f16 ?v0) f17) false)))
(assert (forall ((?v0 S6)) (= (= f17 (f14 f16 ?v0)) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 f16 ?v0) (f14 f15 ?v1)) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 f15 ?v0) (f14 f16 ?v1)) false)))
(assert (forall ((?v0 S6)) (= (= (f14 f15 ?v0) f17) (= ?v0 f17))))
(assert (forall ((?v0 S6)) (= (= f17 (f14 f15 ?v0)) (= f17 ?v0))))
(assert (= (f14 f15 f17) f17))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f14 f21 ?v2))) (= (f14 (f19 f20 (f14 (f19 f22 ?v0) ?v1)) ?v_0) (f14 (f19 f22 (f14 (f19 f20 ?v0) ?v_0)) (f14 (f19 f20 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6)) (let ((?v_0 (f12 f13 ?v2))) (= (f3 (f4 f8 (f3 (f4 f9 ?v0) ?v1)) ?v_0) (f3 (f4 f9 (f3 (f4 f8 ?v0) ?v_0)) (f3 (f4 f8 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f19 f20 (f14 f21 ?v0)))) (= (f14 ?v_0 (f14 (f19 f22 ?v1) ?v2)) (f14 (f19 f22 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f8 (f12 f13 ?v0)))) (= (f3 ?v_0 (f3 (f4 f9 ?v1) ?v2)) (f3 (f4 f9 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f14 f21 ?v2))) (= (f14 (f19 f20 (f14 (f19 f24 ?v0) ?v1)) ?v_0) (f14 (f19 f24 (f14 (f19 f20 ?v0) ?v_0)) (f14 (f19 f20 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6)) (let ((?v_0 (f12 f13 ?v2))) (= (f3 (f4 f8 (f3 (f4 f5 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f8 ?v0) ?v_0)) (f3 (f4 f8 ?v1) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f19 f20 (f14 f21 ?v0)))) (= (f14 ?v_0 (f14 (f19 f24 ?v1) ?v2)) (f14 (f19 f24 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f8 (f12 f13 ?v0)))) (= (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2)) (f3 (f4 f5 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f14 (f19 f22 (f14 f21 ?v0)) (f14 (f19 f24 (f14 f21 ?v1)) ?v2)) (f14 (f19 f24 (f14 f21 (f14 (f19 f22 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S3)) (= (f3 (f4 f9 (f12 f13 ?v0)) (f3 (f4 f5 (f12 f13 ?v1)) ?v2)) (f3 (f4 f5 (f12 f13 (f14 (f19 f22 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6)) (= (f14 (f19 f22 (f14 f21 f17)) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 (f12 f13 f17)) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f19 f22 ?v0) (f14 f21 f17)) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f9 ?v0) (f12 f13 f17)) ?v0)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f3 ?v0 ?v1)) (?v_1 (f4 f5 (f3 ?v0 ?v2)))) (let ((?v_2 (f4 f8 (f3 (f4 f7 (f3 ?v_1 ?v_0)) (f3 (f4 f5 ?v2) ?v1))))) (= (f3 (f4 f5 ?v_0) (f3 ?v_2 ?v1)) (f3 ?v_1 (f3 ?v_2 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f4 f8 ?v0))) (= (f3 (f4 f7 (f3 (f4 f5 (f3 ?v_0 ?v1)) (f3 (f4 f8 ?v2) ?v3))) ?v4) (f3 (f4 f9 (f3 ?v_0 (f3 (f4 f7 (f3 (f4 f5 ?v1) ?v3)) ?v4))) (f3 (f4 f8 (f3 (f4 f7 (f3 (f4 f5 ?v0) ?v2)) ?v4)) ?v3))))))
(assert (= (f25 f18 (f3 (f4 f7 (f3 (f4 f5 (f3 f6 (f3 (f4 f9 (f3 (f4 f8 f10) f10)) (f3 (f4 f8 f11) f11)))) f10)) (f12 f13 (f14 f15 (f14 f16 f17))))) f1))
(check-sat)
(exit)
