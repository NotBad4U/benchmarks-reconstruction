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
(declare-fun f14 (S2 S2) S1)
(declare-fun f15 (S2) S1)
(assert (not (= f1 f2)))
(assert (not false))
(assert (= (f3 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f1))
(assert (= (f14 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13) f13) f1))
(assert (not (= (f14 f13 f12) f1)))
(assert (= (f3 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13)) f1))
(assert (= (f14 (f4 (f5 f6 (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f9 (f4 f10 f11))))) f12)) f13) f13) f1))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f15 ?v0) f1) (=> (= (f15 ?v1) f1) (= (f15 (f4 (f5 f7 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f4 f10 f11))) (let ((?v_1 (f4 f9 ?v_0))) (=> (= (f3 ?v0) f1) (=> (not (= ?v0 (f4 f8 ?v_1))) (=> (not (= ?v0 (f4 f8 (f4 f10 ?v_0)))) (= (f14 (f4 f8 (f4 f10 ?v_1)) ?v0) f1))))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f13) (f4 f8 ?v0)) (f4 f8 (f4 (f5 f6 (f4 f10 f11)) ?v0)))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 (f4 f8 ?v0)) f13) (f4 f8 (f4 (f5 f6 ?v0) (f4 f10 f11))))))
(assert (forall ((?v0 S2)) (= (= (f14 f13 (f4 f8 ?v0)) f1) (= (f14 (f4 f10 f11) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f14 (f4 f8 ?v0) f13) f1) (= (f14 ?v0 (f4 f10 f11)) f1))))
(assert (= (f4 (f5 f6 f13) f13) (f4 f8 (f4 f9 (f4 f10 f11)))))
(assert (= (f4 (f5 f6 f13) f13) (f4 f8 (f4 f9 (f4 f10 f11)))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) (f4 f8 (f4 f9 (f4 f10 f11)))) (f4 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) (f4 f8 (f4 f9 (f4 f10 f11)))) (f4 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f10 f11)))) ?v0) (f4 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 (f4 f8 (f4 f9 (f4 f10 f11)))) ?v0) (f4 (f5 f6 ?v0) ?v0))))
(assert (= (f3 (f4 f8 (f4 f9 (f4 f10 f11)))) f1))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f8 ?v0) (f4 f8 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f8 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f10 ?v0) (f4 f10 ?v1)) (= ?v0 ?v1))))
(assert (= (= f11 f11) true))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f9 ?v0) (f4 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f14 ?v0 ?v1) f1) (=> (= (f14 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f14 ?v0 ?v1) f1) (=> (= (f14 ?v1 ?v2) f1) (= (f14 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f14 ?v0 ?v1) f1) (= (f14 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2)) (= (f14 ?v0 ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (f4 (f5 f7 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 ?v0) ?v1) (f4 (f5 f7 ?v1) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 f8 ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v0))) (= (f4 (f5 f6 (f4 ?v_0 ?v1)) ?v2) (f4 ?v_0 (f4 (f5 f6 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f5 f6 ?v0)) (?v_0 (f5 f6 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f6 ?v0) ?v1) (f4 (f5 f6 ?v1) ?v0))))
(assert (forall ((?v0 S2)) (= (= (f4 f10 ?v0) f11) false)))
(assert (forall ((?v0 S2)) (= (= f11 (f4 f10 ?v0)) false)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f10 ?v0) (f4 f9 ?v1)) false)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 f9 ?v0) (f4 f10 ?v1)) false)))
(assert (forall ((?v0 S2)) (= (= (f4 f9 ?v0) f11) (= ?v0 f11))))
(assert (forall ((?v0 S2)) (= (= f11 (f4 f9 ?v0)) (= f11 ?v0))))
(assert (= (f4 f9 f11) f11))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f14 (f4 f10 ?v0) (f4 f10 ?v1)) f1) (= (f14 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f14 (f4 f10 ?v0) (f4 f10 ?v1)) f1) (= (f14 ?v0 ?v1) f1))))
(assert (= (= (f14 f11 f11) f1) true))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f14 (f4 f9 ?v0) (f4 f9 ?v1)) f1) (= (f14 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f14 (f4 f9 ?v0) (f4 f9 ?v1)) f1) (= (f14 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 f11) ?v0) f11)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 (f4 f9 ?v0)) ?v1) (f4 f9 (f4 (f5 f7 ?v0) ?v1)))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f11) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f11) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f6 (f4 f9 ?v0)) (f4 f9 ?v1)) (f4 f9 (f4 (f5 f6 ?v0) ?v1)))))
(assert (forall ((?v0 S2)) (= (f4 f9 ?v0) (f4 (f5 f6 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 ?v0) f13) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f7 f13) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f14 (f4 f8 ?v0) (f4 f8 ?v1)) f1) (= (f14 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v2))) (=> (= (f14 ?v0 ?v1) f1) (= (f14 (f4 ?v_0 ?v0) (f4 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f7 (f4 f8 ?v0)) (f4 f8 ?v1)) (f4 f8 (f4 (f5 f7 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f7 (f4 (f5 f6 ?v0) ?v1)) ?v2) (f4 (f5 f6 (f4 (f5 f7 ?v0) ?v2)) (f4 (f5 f7 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 ?v0))) (= (f4 ?v_0 (f4 (f5 f6 ?v1) ?v2)) (f4 (f5 f6 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f6 (f4 f8 ?v0)) (f4 f8 ?v1)) (f4 f8 (f4 (f5 f6 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f8 ?v2))) (= (f4 (f5 f7 (f4 (f5 f6 ?v0) ?v1)) ?v_0) (f4 (f5 f6 (f4 (f5 f7 ?v0) ?v_0)) (f4 (f5 f7 ?v1) ?v_0))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f7 (f4 f8 ?v0)))) (= (f4 ?v_0 (f4 (f5 f6 ?v1) ?v2)) (f4 (f5 f6 (f4 ?v_0 ?v1)) (f4 ?v_0 ?v2))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 (f4 f8 f11)) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f4 f8 f11)) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f14 (f4 f8 ?v0) (f4 f8 ?v1)) f1) (= (f14 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f7 (f4 f8 ?v0)) (f4 (f5 f7 (f4 f8 ?v1)) ?v2)) (f4 (f5 f7 (f4 f8 (f4 (f5 f7 ?v0) ?v1))) ?v2))))
(check-sat)
(exit)