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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () S1)
(declare-fun f4 (S3 S2) S1)
(declare-fun f5 () S3)
(declare-fun f6 (S4 S2) S3)
(declare-fun f7 () S4)
(declare-fun f8 (S5 S2) S2)
(declare-fun f9 (S6 S2) S5)
(declare-fun f10 () S6)
(declare-fun f11 () S6)
(declare-fun f12 () S4)
(assert (not (= f1 f2)))
(assert (not (= f3 f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 f5 ?v0) f1) (=> (forall ((?v2 S2)) (=> (= (f4 f5 ?v2) f1) (= (f4 (f6 f7 ?v2) ?v1) f1))) (= f3 f1)))))
(assert (exists ((?v0 S2)) (= (f4 f5 ?v0) f1)))
(assert (exists ((?v0 S2)) (forall ((?v1 S2)) (=> (= (f4 f5 ?v1) f1) (= (f4 (f6 f7 ?v1) ?v0) f1)))))
(assert (exists ((?v0 S2)) (= (f4 f5 ?v0) f1)))
(assert (exists ((?v0 S2)) (forall ((?v1 S2)) (=> (= (f4 f5 ?v1) f1) (= (f4 (f6 f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2)) (not (= (f4 (f6 f7 ?v0) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= ?v0 ?v1)) (or (= (f4 (f6 f7 ?v0) ?v1) f1) (= (f4 (f6 f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f4 (f6 f7 ?v0) ?v1) f1)) (or (= (f4 (f6 f7 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f4 (f6 f7 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f4 (f6 f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v0))) (= (= (f4 ?v_0 (f8 (f9 f10 ?v1) ?v2)) f1) (or (= (f4 ?v_0 ?v1) f1) (= (f4 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v0))) (= (= (f4 ?v_0 (f8 (f9 f11 ?v1) ?v2)) f1) (and (= (f4 ?v_0 ?v1) f1) (= (f4 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f4 (f6 f7 (f8 (f9 f10 ?v0) ?v1)) ?v2) f1) (and (= (f4 (f6 f7 ?v0) ?v2) f1) (= (f4 (f6 f7 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f4 (f6 f7 (f8 (f9 f11 ?v0) ?v1)) ?v2) f1) (or (= (f4 (f6 f7 ?v0) ?v2) f1) (= (f4 (f6 f7 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f4 (f6 f7 ?v0) ?v1) f1)) (= (not (= (f4 (f6 f7 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f4 (f6 f7 ?v0) ?v1) f1) false) (=> (=> (= (f4 (f6 f7 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f4 (f6 f7 ?v0) ?v1) f1) false) (=> (=> (= (f4 (f6 f7 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f4 (f6 f7 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f4 (f6 f7 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (=> (=> (not false) (= (f4 (f6 f7 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v2))) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (=> (= (f4 ?v_0 ?v0) f1) (= (f4 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f4 ?v_0 ?v1) f1) (=> (= (f4 (f6 f7 ?v1) ?v2) f1) (= (f4 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f4 (f6 f7 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f4 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f4 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v2))) (=> (= ?v0 ?v1) (=> (= (f4 ?v_0 ?v1) f1) (= (f4 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f4 (f6 f7 ?v1) ?v2) f1) (= (f4 (f6 f7 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (=> (= (f4 (f6 f7 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (=> (= (f4 (f6 f7 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S1)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (= (=> (= (f4 (f6 f7 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (= (not (= (f4 (f6 f7 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (not (= (f4 (f6 f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2) (?v3 S2)) (=> (= ?v0 (f8 ?v1 ?v2)) (=> (= (f4 (f6 f7 ?v3) ?v2) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f4 (f6 f7 ?v5) ?v4) f1) (= (f4 (f6 f7 (f8 ?v1 ?v5)) (f8 ?v1 ?v4)) f1))) (= (f4 (f6 f7 (f8 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S5) (?v3 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (=> (= (f8 ?v2 ?v0) ?v3) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f4 (f6 f7 ?v5) ?v4) f1) (= (f4 (f6 f7 (f8 ?v2 ?v5)) (f8 ?v2 ?v4)) f1))) (= (f4 (f6 f7 ?v3) (f8 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (exists ((?v2 S2)) (and (= (f4 (f6 f7 ?v0) ?v2) f1) (= (f4 (f6 f7 ?v2) ?v1) f1))))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (= (f4 (f6 f7 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (= (f4 (f6 f7 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f4 ?v_0 ?v1) f1) (= (f4 ?v_0 (f8 (f9 f10 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f4 ?v_0 ?v1) f1) (= (f4 ?v_0 (f8 (f9 f10 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (= (f4 (f6 f7 (f8 (f9 f11 ?v0) ?v2)) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f6 f7 ?v0) ?v1) f1) (= (f4 (f6 f7 (f8 (f9 f11 ?v2) ?v0)) ?v1) f1))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (= (f4 (f6 f7 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2)) (exists ((?v1 S2)) (= (f4 (f6 f7 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f4 (f6 f7 ?v4) ?v5) f1) (= (= (f4 ?v0 ?v5) f1) (= (f4 ?v1 ?v5) f1))))) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f4 (f6 f7 ?v4) ?v5) f1) (= (= (f4 ?v2 ?v5) f1) (= (f4 ?v3 ?v5) f1))))) (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f4 (f6 f7 ?v4) ?v5) f1) (= (or (= (f4 ?v0 ?v5) f1) (= (f4 ?v2 ?v5) f1)) (or (= (f4 ?v1 ?v5) f1) (= (f4 ?v3 ?v5) f1))))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f4 (f6 f7 ?v4) ?v5) f1) (= (= (f4 ?v0 ?v5) f1) (= (f4 ?v1 ?v5) f1))))) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f4 (f6 f7 ?v4) ?v5) f1) (= (= (f4 ?v2 ?v5) f1) (= (f4 ?v3 ?v5) f1))))) (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f4 (f6 f7 ?v4) ?v5) f1) (= (and (= (f4 ?v0 ?v5) f1) (= (f4 ?v2 ?v5) f1)) (and (= (f4 ?v1 ?v5) f1) (= (f4 ?v3 ?v5) f1))))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f4 (f6 f7 ?v5) ?v4) f1) (= (= (f4 ?v0 ?v5) f1) (= (f4 ?v1 ?v5) f1))))) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f4 (f6 f7 ?v5) ?v4) f1) (= (= (f4 ?v2 ?v5) f1) (= (f4 ?v3 ?v5) f1))))) (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f4 (f6 f7 ?v5) ?v4) f1) (= (or (= (f4 ?v0 ?v5) f1) (= (f4 ?v2 ?v5) f1)) (or (= (f4 ?v1 ?v5) f1) (= (f4 ?v3 ?v5) f1))))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f4 (f6 f7 ?v5) ?v4) f1) (= (= (f4 ?v0 ?v5) f1) (= (f4 ?v1 ?v5) f1))))) (=> (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f4 (f6 f7 ?v5) ?v4) f1) (= (= (f4 ?v2 ?v5) f1) (= (f4 ?v3 ?v5) f1))))) (exists ((?v4 S2)) (forall ((?v5 S2)) (=> (= (f4 (f6 f7 ?v5) ?v4) f1) (= (and (= (f4 ?v0 ?v5) f1) (= (f4 ?v2 ?v5) f1)) (and (= (f4 ?v1 ?v5) f1) (= (f4 ?v3 ?v5) f1))))))))))
(assert (forall ((?v0 S2)) (= (f4 (f6 f12 ?v0) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f6 f12 ?v0) (f8 (f9 f10 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f6 f12 ?v0) (f8 (f9 f10 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f6 f12 (f8 (f9 f11 ?v0) ?v1)) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f6 f12 (f8 (f9 f11 ?v0) ?v1)) ?v1) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f6 f12 ?v0) ?v1) f1) (= (f8 (f9 f10 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f6 f12 ?v0) ?v1) f1) (= (f8 (f9 f11 ?v0) ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f12 ?v0))) (= (= (f4 ?v_0 (f8 (f9 f11 ?v1) ?v2)) f1) (and (= (f4 ?v_0 ?v1) f1) (= (f4 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f9 f10 ?v0))) (= (f4 (f6 f12 (f8 ?v_0 (f8 (f9 f11 ?v1) ?v2))) (f8 (f9 f11 (f8 ?v_0 ?v1)) (f8 ?v_0 ?v2))) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f4 (f6 f12 (f8 (f9 f10 ?v0) ?v1)) ?v2) f1) (and (= (f4 (f6 f12 ?v0) ?v2) f1) (= (f4 (f6 f12 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f9 f11 ?v0))) (= (f4 (f6 f12 (f8 (f9 f10 (f8 ?v_0 ?v1)) (f8 ?v_0 ?v2))) (f8 ?v_0 (f8 (f9 f10 ?v1) ?v2))) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f12 ?v0))) (=> (= (f4 ?v_0 ?v1) f1) (= (f4 ?v_0 (f8 (f9 f10 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f12 ?v0))) (=> (= (f4 ?v_0 ?v1) f1) (= (f4 ?v_0 (f8 (f9 f10 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f6 f12 ?v0) ?v1) f1) (= (f4 (f6 f12 (f8 (f9 f11 ?v0) ?v2)) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f6 f12 ?v0) ?v1) f1) (= (f4 (f6 f12 (f8 (f9 f11 ?v2) ?v0)) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f12 ?v0) ?v1) f1) (= (f8 (f9 f10 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f12 ?v0) ?v1) f1) (= (f8 (f9 f11 ?v0) ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f12 ?v0) ?v1) f1) (= (f8 (f9 f10 ?v1) ?v0) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f6 f12 ?v0) ?v1) f1) (= (f8 (f9 f11 ?v1) ?v0) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f12 ?v0))) (=> (= (f4 ?v_0 ?v1) f1) (=> (= (f4 ?v_0 ?v2) f1) (= (f4 ?v_0 (f8 (f9 f11 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f12 ?v0))) (=> (= (f4 ?v_0 ?v1) f1) (=> (= (f4 ?v_0 ?v2) f1) (= (f4 ?v_0 (f8 (f9 f11 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f6 f12 ?v0) ?v1) f1) (=> (= (f4 (f6 f12 ?v2) ?v1) f1) (= (f4 (f6 f12 (f8 (f9 f10 ?v0) ?v2)) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f6 f12 ?v0) ?v1) f1) (=> (= (f4 (f6 f12 ?v2) ?v1) f1) (= (f4 (f6 f12 (f8 (f9 f10 ?v0) ?v2)) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f4 (f6 f12 ?v0) ?v1) f1) (=> (= (f4 (f6 f12 ?v2) ?v3) f1) (= (f4 (f6 f12 (f8 (f9 f10 ?v0) ?v2)) (f8 (f9 f10 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f4 (f6 f12 ?v0) ?v1) f1) (=> (= (f4 (f6 f12 ?v2) ?v3) f1) (= (f4 (f6 f12 (f8 (f9 f11 ?v0) ?v2)) (f8 (f9 f11 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f12 ?v0))) (=> (= (f4 ?v_0 (f8 (f9 f11 ?v1) ?v2)) f1) (=> (=> (= (f4 ?v_0 ?v1) f1) (=> (= (f4 ?v_0 ?v2) f1) false)) false)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f6 f12 (f8 (f9 f10 ?v0) ?v1)) ?v2) f1) (=> (=> (= (f4 (f6 f12 ?v0) ?v2) f1) (=> (= (f4 (f6 f12 ?v1) ?v2) f1) false)) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f4 (f6 f12 ?v0) ?v1) f1) (= (f4 (f6 f12 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 ?v1) (and (= (f4 (f6 f12 ?v0) ?v1) f1) (= (f4 (f6 f12 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f12 ?v0))) (= (= (f4 ?v_0 (f8 (f9 f10 ?v1) ?v2)) f1) (or (= (f4 ?v_0 ?v1) f1) (= (f4 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f4 (f6 f12 (f8 (f9 f11 ?v0) ?v1)) ?v2) f1) (or (= (f4 (f6 f12 ?v0) ?v2) f1) (= (f4 (f6 f12 ?v1) ?v2) f1)))))
(check-sat)
(exit)