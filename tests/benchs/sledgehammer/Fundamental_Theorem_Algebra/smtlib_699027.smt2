(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-sort S1 0)
(declare-sort S2 0)
(declare-sort S3 0)
(declare-sort S4 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () S1)
(declare-fun f4 (S2) S1)
(declare-fun f5 (S2 S2) S1)
(declare-fun f6 (S3 S2) S2)
(declare-fun f7 (S4 S2) S3)
(declare-fun f8 () S4)
(declare-fun f9 () S4)
(assert (not (= f1 f2)))
(assert (not (= f3 f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 ?v0) f1) (=> (forall ((?v2 S2)) (=> (= (f4 ?v2) f1) (= (f5 ?v2 ?v1) f1))) (= f3 f1)))))
(assert (exists ((?v0 S2)) (= (f4 ?v0) f1)))
(assert (exists ((?v0 S2)) (forall ((?v1 S2)) (=> (= (f4 ?v1) f1) (= (f5 ?v1 ?v0) f1)))))
(assert (exists ((?v0 S2)) (= (f4 ?v0) f1)))
(assert (exists ((?v0 S2)) (forall ((?v1 S2)) (=> (= (f4 ?v1) f1) (= (f5 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S2)) (not (= (f5 ?v0 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= ?v0 ?v1)) (or (= (f5 ?v0 ?v1) f1) (= (f5 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f5 ?v0 ?v1) f1)) (or (= (f5 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f5 ?v0 ?v1) f1) (or (= ?v0 ?v1) (= (f5 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f5 ?v0 (f6 (f7 f8 ?v1) ?v2)) f1) (or (= (f5 ?v0 ?v1) f1) (= (f5 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f5 ?v0 (f6 (f7 f9 ?v1) ?v2)) f1) (and (= (f5 ?v0 ?v1) f1) (= (f5 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) f1) (and (= (f5 ?v0 ?v2) f1) (= (f5 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f5 (f6 (f7 f9 ?v0) ?v1) ?v2) f1) (or (= (f5 ?v0 ?v2) f1) (= (f5 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f5 ?v0 ?v1) f1)) (= (not (= (f5 ?v1 ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f5 ?v0 ?v1) f1) false) (=> (=> (= (f5 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f5 ?v0 ?v1) f1) false) (=> (=> (= (f5 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f5 ?v0 ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f5 ?v0 ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f5 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f5 ?v0 ?v1) f1) (=> (=> (not false) (= (f5 ?v1 ?v0) f1)) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f5 ?v0 ?v1) f1) (=> (= (f5 ?v2 ?v0) f1) (= (f5 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f5 ?v0 ?v1) f1) (=> (= (f5 ?v1 ?v2) f1) (= (f5 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f5 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f5 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f5 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f5 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f5 ?v2 ?v1) f1) (= (f5 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f5 ?v1 ?v2) f1) (= (f5 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f5 ?v0 ?v1) f1) (=> (= (f5 ?v1 ?v0) f1) false))))
(check-sat)
(exit)