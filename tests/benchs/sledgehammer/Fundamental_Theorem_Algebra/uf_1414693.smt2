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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () S2)
(declare-fun f4 () S2)
(declare-fun f5 () S2)
(declare-fun f6 () S2)
(declare-fun f7 (S3 S2) S2)
(declare-fun f8 (S4 S2) S3)
(declare-fun f9 () S4)
(declare-fun f10 () S4)
(declare-fun f11 () S2)
(declare-fun f12 (S6 S5) S5)
(declare-fun f13 (S7 S5) S6)
(declare-fun f14 () S7)
(declare-fun f15 () S5)
(declare-fun f16 () S7)
(assert (not (= f1 f2)))
(assert (not (=> (= f3 f4) (=> (not (= f5 f4)) (= (= f6 f4) (= (f7 (f8 f9 (f7 (f8 f10 f5) f6)) (f7 (f8 f10 f11) f3)) f4))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f10 ?v0))) (= (f7 ?v_0 (f7 (f8 f9 ?v1) ?v2)) (f7 (f8 f9 (f7 ?v_0 ?v1)) (f7 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f10 ?v0))) (= (f7 ?v_0 (f7 (f8 f9 ?v1) ?v2)) (f7 (f8 f9 (f7 ?v_0 ?v1)) (f7 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f7 (f8 f10 (f7 (f8 f9 ?v0) ?v1)) ?v2) (f7 (f8 f9 (f7 (f8 f10 ?v0) ?v2)) (f7 (f8 f10 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f7 (f8 f10 (f7 (f8 f9 ?v0) ?v1)) ?v2) (f7 (f8 f9 (f7 (f8 f10 ?v0) ?v2)) (f7 (f8 f10 ?v1) ?v2)))))
(assert (forall ((?v0 S2)) (= (f7 (f8 f9 ?v0) f4) ?v0)))
(assert (forall ((?v0 S5)) (= (f12 (f13 f14 ?v0) f15) ?v0)))
(assert (forall ((?v0 S2)) (= (f7 (f8 f9 ?v0) ?v0) f4)))
(assert (forall ((?v0 S5)) (= (f12 (f13 f14 ?v0) ?v0) f15)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 ?v1) (= (f7 (f8 f9 ?v0) ?v1) f4))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= ?v0 ?v1) (= (f12 (f13 f14 ?v0) ?v1) f15))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f7 (f8 f9 ?v0) ?v1) f4) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f12 (f13 f14 ?v0) ?v1) f15) (= ?v0 ?v1))))
(assert (forall ((?v0 S2)) (= (f7 (f8 f10 f4) ?v0) f4)))
(assert (forall ((?v0 S5)) (= (f12 (f13 f16 f15) ?v0) f15)))
(assert (forall ((?v0 S2)) (= (f7 (f8 f10 f4) ?v0) f4)))
(assert (forall ((?v0 S5)) (= (f12 (f13 f16 f15) ?v0) f15)))
(assert (forall ((?v0 S2)) (= (f7 (f8 f10 f4) ?v0) f4)))
(assert (forall ((?v0 S2)) (= (f7 (f8 f10 f4) ?v0) f4)))
(assert (forall ((?v0 S2)) (= (= f4 ?v0) (= ?v0 f4))))
(assert (forall ((?v0 S5)) (= (= f15 ?v0) (= ?v0 f15))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (let ((?v_0 (f13 f16 ?v0))) (= (f12 (f13 f16 (f12 ?v_0 ?v1)) (f12 (f13 f16 ?v2) ?v3)) (f12 (f13 f16 (f12 ?v_0 ?v2)) (f12 (f13 f16 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f8 f10 ?v0))) (= (f7 (f8 f10 (f7 ?v_0 ?v1)) (f7 (f8 f10 ?v2) ?v3)) (f7 (f8 f10 (f7 ?v_0 ?v2)) (f7 (f8 f10 ?v1) ?v3))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (let ((?v_1 (f13 f16 (f12 (f13 f16 ?v0) ?v1))) (?v_0 (f13 f16 ?v2))) (= (f12 ?v_1 (f12 ?v_0 ?v3)) (f12 ?v_0 (f12 ?v_1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_1 (f8 f10 (f7 (f8 f10 ?v0) ?v1))) (?v_0 (f8 f10 ?v2))) (= (f7 ?v_1 (f7 ?v_0 ?v3)) (f7 ?v_0 (f7 ?v_1 ?v3))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (let ((?v_0 (f13 f16 ?v0)) (?v_1 (f12 (f13 f16 ?v2) ?v3))) (= (f12 (f13 f16 (f12 ?v_0 ?v1)) ?v_1) (f12 ?v_0 (f12 (f13 f16 ?v1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f8 f10 ?v0)) (?v_1 (f7 (f8 f10 ?v2) ?v3))) (= (f7 (f8 f10 (f7 ?v_0 ?v1)) ?v_1) (f7 ?v_0 (f7 (f8 f10 ?v1) ?v_1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f13 f16 ?v0))) (= (f12 (f13 f16 (f12 ?v_0 ?v1)) ?v2) (f12 (f13 f16 (f12 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f10 ?v0))) (= (f7 (f8 f10 (f7 ?v_0 ?v1)) ?v2) (f7 (f8 f10 (f7 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f13 f16 ?v0))) (= (f12 (f13 f16 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f13 f16 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f10 ?v0))) (= (f7 (f8 f10 (f7 ?v_0 ?v1)) ?v2) (f7 ?v_0 (f7 (f8 f10 ?v1) ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f13 f16 ?v0))) (= (f12 (f13 f16 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f13 f16 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f10 ?v0))) (= (f7 (f8 f10 (f7 ?v_0 ?v1)) ?v2) (f7 ?v_0 (f7 (f8 f10 ?v1) ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f13 f16 ?v0))) (= (f12 ?v_0 (f12 (f13 f16 ?v1) ?v2)) (f12 (f13 f16 (f12 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f10 ?v0))) (= (f7 ?v_0 (f7 (f8 f10 ?v1) ?v2)) (f7 (f8 f10 (f7 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_1 (f13 f16 ?v0)) (?v_0 (f13 f16 ?v1))) (= (f12 ?v_1 (f12 ?v_0 ?v2)) (f12 ?v_0 (f12 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f8 f10 ?v0)) (?v_0 (f8 f10 ?v1))) (= (f7 ?v_1 (f7 ?v_0 ?v2)) (f7 ?v_0 (f7 ?v_1 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f12 (f13 f16 ?v0) ?v1) (f12 (f13 f16 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f7 (f8 f10 ?v0) ?v1) (f7 (f8 f10 ?v1) ?v0))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (=> (= (f12 (f13 f14 ?v0) ?v1) (f12 (f13 f14 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f7 (f8 f10 ?v0) ?v1) f4) (or (= ?v0 f4) (= ?v1 f4)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f12 (f13 f16 ?v0) ?v1) f15) (or (= ?v0 f15) (= ?v1 f15)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 f4)) (=> (not (= ?v1 f4)) (not (= (f7 (f8 f10 ?v0) ?v1) f4))))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= ?v0 f15)) (=> (not (= ?v1 f15)) (not (= (f12 (f13 f16 ?v0) ?v1) f15))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f7 (f8 f10 ?v0) ?v1) f4) (or (= ?v0 f4) (= ?v1 f4)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f12 (f13 f16 ?v0) ?v1) f15) (or (= ?v0 f15) (= ?v1 f15)))))
(assert (forall ((?v0 S2)) (= (f7 (f8 f10 ?v0) f4) f4)))
(assert (forall ((?v0 S2)) (= (f7 (f8 f10 ?v0) f4) f4)))
(assert (forall ((?v0 S2)) (= (f7 (f8 f10 ?v0) f4) f4)))
(assert (forall ((?v0 S5)) (= (f12 (f13 f16 ?v0) f15) f15)))
(assert (forall ((?v0 S2)) (= (f7 (f8 f10 ?v0) f4) f4)))
(assert (forall ((?v0 S5)) (= (f12 (f13 f16 ?v0) f15) f15)))
(check-sat)
(exit)
