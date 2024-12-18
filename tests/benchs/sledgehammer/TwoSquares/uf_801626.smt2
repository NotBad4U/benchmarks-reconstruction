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
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 () S4)
(declare-fun f7 () S2)
(declare-fun f8 () S4)
(declare-fun f9 () S2)
(declare-fun f10 (S5 S3) S3)
(declare-fun f11 () S5)
(declare-fun f12 () S4)
(declare-fun f13 (S6 S2) S2)
(declare-fun f14 (S7 S2) S6)
(declare-fun f15 () S7)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (and (= (f3 (f4 f6 f7) ?v1) f1) (= (f3 (f4 f8 ?v1) ?v0) f1)))))
(assert (not (= (f3 (f4 f8 f7) f9) f1)))
(assert (not (= f9 f7)))
(assert (= (f3 (f4 f6 f7) f9) f1))
(assert (not (= f9 f7)))
(assert (= (f3 (f4 f6 f7) f9) f1))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f8 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f4 f8 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2)) (not (= (f3 (f4 f8 ?v0) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= ?v0 ?v1)) (or (= (f3 (f4 f8 ?v0) ?v1) f1) (= (f3 (f4 f8 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f4 f8 ?v0) ?v1) f1)) (or (= (f3 (f4 f8 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f8 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f4 f8 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f4 f8 ?v0) ?v1) f1)) (= (not (= (f3 (f4 f8 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 (f4 f8 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f8 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 (f4 f8 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f8 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (not (= (f3 (f4 f8 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (= (not (= (f3 (f4 f8 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S2)) (= (f3 (f4 f6 ?v0) ?v0) f1)))
(assert (forall ((?v0 S2)) (= (f3 (f4 f6 ?v0) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f6 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f6 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 ?v1) (and (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f6 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= ?v0 ?v1) (= (f3 (f4 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (= (= (f3 (f4 f6 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f3 (f4 f6 ?v1) ?v2) f1) (= (f3 (f4 f6 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f6 ?v2))) (=> (= ?v0 ?v1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f6 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f3 (f4 f6 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f6 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f6 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 (f4 f6 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f6 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f6 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 (f4 f6 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f6 ?v2))) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 (f4 f6 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f3 (f4 f6 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f6 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f8 ?v2))) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f3 (f4 f8 ?v1) ?v2) f1) (= (f3 (f4 f8 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (=> (= (f3 (f4 f6 ?v2) ?v0) f1) (= (f3 (f4 f8 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f8 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f6 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (not (= ?v1 ?v0)) (= (f3 (f4 f8 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f3 (f4 f8 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (or (= (f3 (f4 f8 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (= (not (= (f3 (f4 f8 ?v0) ?v1) f1)) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (= (f3 (f4 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (not (= (f3 (f4 f8 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (= (f3 (f4 f6 ?v1) ?v0) f1) (= (f3 (f4 f8 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f8 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f4 f8 ?v0) ?v1) f1)) (= (= (f3 (f4 f6 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f4 f6 ?v0) ?v1) f1)) (= (f3 (f4 f8 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f4 f8 ?v0) ?v1) f1)) (= (f3 (f4 f6 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f6 ?v0) ?v1) f1) (or (= (f3 (f4 f8 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f8 ?v0) ?v1) f1) (and (= (f3 (f4 f6 ?v0) ?v1) f1) (not (= (f3 (f4 f6 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f8 ?v0) ?v1) f1) (and (= (f3 (f4 f6 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f6 ?v0) ?v1) f1) (= (f3 (f4 f8 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f4 f6 ?v0) ?v1) f1)) (= (f3 (f4 f8 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f4 f8 ?v0) ?v1) f1)) (= (f3 (f4 f6 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f8 ?v0) ?v1) f1) (and (= (f3 (f4 f6 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f3 (f4 f8 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f3 (f4 f8 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (=> (=> (not false) (= (f3 (f4 f8 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f8 ?v2))) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f8 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f8 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f3 (f4 f8 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f8 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f8 ?v2))) (=> (= ?v0 ?v1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f3 (f4 f8 ?v1) ?v2) f1) (= (f3 (f4 f8 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (=> (= (f3 (f4 f8 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (=> (= (f3 (f4 f8 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S1)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (= (=> (= (f3 (f4 f8 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S3)) (= (f10 f11 ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (=> (= (f3 (f4 f8 ?v2) ?v1) f1) (or (= (f3 (f4 f6 ?v0) ?v2) f1) (= (f3 (f4 f6 ?v2) ?v0) f1))))))
(assert (= (f3 (f4 f6 f7) f7) f1))
(assert (forall ((?v0 S2) (?v1 S1) (?v2 S1)) (let ((?v_0 (= (f3 (f4 f6 f7) ?v0) f1)) (?v_1 (= ?v1 f1)) (?v_2 (= ?v2 f1))) (=> (=> ?v_0 (= ?v_1 ?v_2)) (= (and ?v_0 ?v_1) (and ?v_0 ?v_2))))))
(assert (forall ((?v0 S2) (?v1 S1) (?v2 S1)) (let ((?v_0 (= (f3 (f4 f6 f7) ?v0) f1)) (?v_1 (= ?v1 f1)) (?v_2 (= ?v2 f1))) (=> (=> ?v_0 (= ?v_1 ?v_2)) (= (=> ?v_0 ?v_1) (=> ?v_0 ?v_2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f3 (f4 f8 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2)) (= (f4 f12 ?v0) (f10 f11 (f4 f5 ?v0)))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (forall ((?v2 S2)) (=> (= (f3 (f4 f8 ?v1) ?v2) f1) (= (= (f3 (f4 f6 ?v2) ?v0) f1) false))))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (forall ((?v2 S2)) (=> (= (f3 (f4 f8 ?v2) ?v1) f1) (= (= (f3 (f4 f6 ?v2) ?v0) f1) true))))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (forall ((?v2 S2)) (=> (= (f3 (f4 f8 ?v1) ?v2) f1) (= (= (f3 (f4 f6 ?v0) ?v2) f1) true))))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (forall ((?v2 S2)) (=> (= (f3 (f4 f8 ?v2) ?v1) f1) (= (= (f3 (f4 f6 ?v0) ?v2) f1) false))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f4 f6 f7))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f13 (f14 f15 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6) (?v3 S2)) (=> (= (f3 (f4 f8 ?v0) ?v1) f1) (=> (= (f13 ?v2 ?v0) ?v3) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f4 f8 ?v5) ?v4) f1) (= (f3 (f4 f8 (f13 ?v2 ?v5)) (f13 ?v2 ?v4)) f1))) (= (f3 (f4 f8 ?v3) (f13 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f3 (f4 f8 ?v4) ?v5) f1) (= (= (f3 ?v0 ?v5) f1) (= (f3 ?v1 ?v5) f1))))) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f3 (f4 f8 ?v4) ?v5) f1) (= (= (f3 ?v2 ?v5) f1) (= (f3 ?v3 ?v5) f1))))) (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f3 (f4 f8 ?v4) ?v5) f1) (= (or (= (f3 ?v0 ?v5) f1) (= (f3 ?v2 ?v5) f1)) (or (= (f3 ?v1 ?v5) f1) (= (f3 ?v3 ?v5) f1))))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f3 (f4 f8 ?v4) ?v5) f1) (= (= (f3 ?v0 ?v5) f1) (= (f3 ?v1 ?v5) f1))))) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f3 (f4 f8 ?v4) ?v5) f1) (= (= (f3 ?v2 ?v5) f1) (= (f3 ?v3 ?v5) f1))))) (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f3 (f4 f8 ?v4) ?v5) f1) (= (and (= (f3 ?v0 ?v5) f1) (= (f3 ?v2 ?v5) f1)) (and (= (f3 ?v1 ?v5) f1) (= (f3 ?v3 ?v5) f1))))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f3 (f4 f8 ?v5) ?v4) f1) (= (= (f3 ?v0 ?v5) f1) (= (f3 ?v1 ?v5) f1))))) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f3 (f4 f8 ?v5) ?v4) f1) (= (= (f3 ?v2 ?v5) f1) (= (f3 ?v3 ?v5) f1))))) (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f3 (f4 f8 ?v5) ?v4) f1) (= (or (= (f3 ?v0 ?v5) f1) (= (f3 ?v2 ?v5) f1)) (or (= (f3 ?v1 ?v5) f1) (= (f3 ?v3 ?v5) f1))))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f3 (f4 f8 ?v5) ?v4) f1) (= (= (f3 ?v0 ?v5) f1) (= (f3 ?v1 ?v5) f1))))) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f3 (f4 f8 ?v5) ?v4) f1) (= (= (f3 ?v2 ?v5) f1) (= (f3 ?v3 ?v5) f1))))) (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f3 (f4 f8 ?v5) ?v4) f1) (= (and (= (f3 ?v0 ?v5) f1) (= (f3 ?v2 ?v5) f1)) (and (= (f3 ?v1 ?v5) f1) (= (f3 ?v3 ?v5) f1))))))))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (forall ((?v2 S2)) (=> (= (f3 (f4 f8 ?v1) ?v2) f1) (= (= (f3 (f4 f8 ?v2) ?v0) f1) false))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S2) (?v3 S2)) (=> (= ?v0 (f13 ?v1 ?v2)) (=> (= (f3 (f4 f8 ?v3) ?v2) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f4 f8 ?v5) ?v4) f1) (= (f3 (f4 f8 (f13 ?v1 ?v5)) (f13 ?v1 ?v4)) f1))) (= (f3 (f4 f8 (f13 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (forall ((?v2 S2)) (=> (= (f3 (f4 f8 ?v1) ?v2) f1) (= (= ?v2 ?v0) false))))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (forall ((?v2 S2)) (let ((?v_0 (f4 f8 ?v2))) (=> (= (f3 ?v_0 ?v1) f1) (= (= (f3 ?v_0 ?v0) f1) true)))))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (forall ((?v2 S2)) (=> (= (f3 (f4 f8 ?v2) ?v1) f1) (= (= ?v2 ?v0) false))))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (forall ((?v2 S2)) (=> (= (f3 (f4 f8 ?v1) ?v2) f1) (= (= (f3 (f4 f8 ?v0) ?v2) f1) true))))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (forall ((?v2 S2)) (=> (= (f3 (f4 f8 ?v2) ?v1) f1) (= (= (f3 (f4 f8 ?v0) ?v2) f1) false))))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (forall ((?v2 S2)) (=> (= (f3 (f4 f8 ?v2) ?v1) f1) (= (not (= ?v2 ?v0)) true))))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (forall ((?v2 S2)) (=> (= (f3 (f4 f8 ?v1) ?v2) f1) (= (not (= ?v2 ?v0)) true))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6) (?v3 S2)) (=> (= (f3 (f4 f6 ?v0) ?v1) f1) (=> (= (f13 ?v2 ?v0) ?v3) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f4 f6 ?v5) ?v4) f1) (= (f3 (f4 f6 (f13 ?v2 ?v5)) (f13 ?v2 ?v4)) f1))) (= (f3 (f4 f6 ?v3) (f13 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S2) (?v3 S2)) (=> (= ?v0 (f13 ?v1 ?v2)) (=> (= (f3 (f4 f6 ?v3) ?v2) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f4 f6 ?v5) ?v4) f1) (= (f3 (f4 f6 (f13 ?v1 ?v5)) (f13 ?v1 ?v4)) f1))) (= (f3 (f4 f6 (f13 ?v1 ?v3)) ?v0) f1))))))
(check-sat)
(exit)
