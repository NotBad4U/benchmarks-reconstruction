(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unknown)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-sort S3 0)
(declare-sort S4 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
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
(declare-fun f14 () S4)
(declare-fun f15 () S2)
(declare-fun f16 (S2) S1)
(declare-fun f17 () S2)
(declare-fun f18 (S2) S1)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f4 f9 (f4 f10 f11)))) (not (= (f3 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 ?v_0))) f12)) f13) (f4 f8 ?v_0)) f1))))
(assert (let ((?v_2 (f4 f9 (f4 f10 f11)))) (let ((?v_0 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 ?v_2))) f12)) f13))) (let ((?v_1 (f4 (f5 f7 ?v_0) (f4 (f5 f14 ?v_0) f13)))) (= (f3 ?v_1 (f4 (f5 f6 (f4 (f5 f14 ?v_1) ?v_0)) (f4 f8 ?v_2))) f1)))))
(assert (let ((?v_2 (f4 f9 (f4 f10 f11)))) (let ((?v_0 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 ?v_2))) f12)) f13))) (let ((?v_1 (f4 (f5 f7 ?v_0) (f4 (f5 f14 ?v_0) f13)))) (= (f3 ?v_1 (f4 (f5 f6 (f4 (f5 f14 ?v_1) ?v_0)) (f4 f8 ?v_2))) f1)))))
(assert (not (= (f3 f15 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f1)))
(assert (= (f16 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f1))
(assert (= (f3 f17 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f1))
(assert (= (f3 (f4 (f5 f14 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f13) f15) f1))
(assert (let ((?v_0 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13))) (let ((?v_1 (f5 f7 ?v_0))) (= (f3 (f4 ?v_1 (f4 (f5 f14 ?v_0) f13)) (f4 ?v_1 f15)) f1))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f13) (f4 f8 ?v0)) (f4 f8 (f4 (f5 f6 (f4 f10 f11)) ?v0)))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 (f4 f8 ?v0)) f13) (f4 f8 (f4 (f5 f6 ?v0) (f4 f10 f11))))))
(assert (forall ((?v0 S2)) (= (= (f3 f13 (f4 f8 ?v0)) f1) (= (f3 (f4 f10 f11) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f8 ?v0) f13) f1) (= (f3 ?v0 (f4 f10 f11)) f1))))
(assert (= (f4 (f5 f6 f13) f13) (f4 f8 (f4 f9 (f4 f10 f11)))))
(assert (= (f4 (f5 f6 f13) f13) (f4 f8 (f4 f9 (f4 f10 f11)))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) (f4 f8 (f4 f9 (f4 f10 f11)))) (f4 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) (f4 f8 (f4 f9 (f4 f10 f11)))) (f4 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f10 f11)))) ?v0) (f4 (f5 f6 ?v0) ?v0))))
(assert (= (f18 (f4 (f5 f7 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f15)) f1))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 ?v0 ?v1) f1) (= (f3 (f4 (f5 f14 ?v0) ?v1) f17) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f6 ?v0) ?v0) f17) (= ?v0 f17))))
(assert (= f11 f17))
(assert (not (= f17 f13)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f17) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f17) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 f8 (f4 (f5 f14 ?v0) ?v1)) (f4 (f5 f14 (f4 f8 ?v0)) (f4 f8 ?v1)))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 (f5 f6 ?v0) ?v0) f17) f1) (= (f3 ?v0 f17) f1))))
(assert (= (f4 f8 f11) f17))
(assert (= (f4 f8 f11) f17))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f10 ?v0) f17) f1) (= (f3 ?v0 f17) f1))))
(assert (= (= (f3 f11 f17) f1) false))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f9 ?v0) f17) f1) (= (f3 ?v0 f17) f1))))
(assert (= f17 (f4 f8 f11)))
(assert (= (f3 f17 f13) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v2))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 f17 ?v2) f1) (= (f3 (f4 ?v_0 ?v0) (f4 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2)) (not (= (f4 (f5 f6 (f4 (f5 f6 f13) ?v0)) ?v0) f17))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f14 ?v0) f11) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f14 (f4 f9 ?v0)) (f4 f9 ?v1)) (f4 f9 (f4 (f5 f14 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f7 (f4 (f5 f14 ?v0) ?v1)) ?v2) (f4 (f5 f14 (f4 (f5 f7 ?v0) ?v2)) (f4 (f5 f7 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (f4 ?v_0 (f4 (f5 f14 ?v1) ?v2)) (f4 (f5 f14 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v2))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f4 f8 ?v0))) (= (f4 f8 (f4 f9 ?v0)) (f4 (f5 f6 (f4 (f5 f6 f17) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f17 ?v0) f1) (= (= (f4 (f5 f7 ?v0) ?v1) f13) (and (= ?v0 f13) (= ?v1 f13))))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 (f5 f6 (f4 (f5 f6 f13) ?v0)) ?v0) f17) f1) (= (f3 ?v0 f17) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f8 ?v0) f17) f1) (= (f3 ?v0 f11) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f17 (f4 f8 ?v0)) f1) (= (f3 f11 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f8 ?v0) (f4 f8 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f8 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f10 ?v0) (f4 f10 ?v1)) (= ?v0 ?v1))))
(assert (= (= f11 f11) true))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f9 ?v0) (f4 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f8 ?v2))) (= (f4 (f5 f7 (f4 (f5 f14 ?v0) ?v1)) ?v_0) (f4 (f5 f14 (f4 (f5 f7 ?v0) ?v_0)) (f4 (f5 f7 ?v1) ?v_0))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 (f4 f8 ?v0)))) (= (f4 ?v_0 (f4 (f5 f14 ?v1) ?v2)) (f4 (f5 f14 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 ?v0 ?v1) f1) (or (= ?v0 ?v1) (= (f3 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (f4 (f5 f7 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 ?v0) ?v1) (f4 (f5 f7 ?v1) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 f8 ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v0))) (= (f4 (f5 f6 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f6 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f5 f6 ?v0)) (?v_0 (f5 f6 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f6 ?v0) ?v1) (f4 (f5 f6 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f14 (f4 f10 ?v0)) (f4 f10 ?v1)) (f4 f9 (f4 (f5 f14 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f14 (f4 f10 ?v0)) (f4 f9 ?v1)) (f4 f10 (f4 (f5 f14 ?v0) ?v1)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f14 f11))) (= (f4 ?v_0 (f4 f9 ?v0)) (f4 f9 (f4 ?v_0 ?v0))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f6 (f4 f8 ?v0)) (f4 (f5 f14 (f4 f8 ?v1)) ?v2)) (f4 (f5 f14 (f4 f8 (f4 (f5 f6 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S2)) (= (= (f4 f10 ?v0) f11) false)))
(assert (forall ((?v0 S2)) (= (= f11 (f4 f10 ?v0)) false)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f10 ?v0) (f4 f9 ?v1)) false)))
(check-sat)
(exit)