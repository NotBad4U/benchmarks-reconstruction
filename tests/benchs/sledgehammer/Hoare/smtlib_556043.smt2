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
(declare-sort S11 0)
(declare-sort S12 0)
(declare-sort S13 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () S1)
(declare-fun f4 () S1)
(declare-fun f5 () S1)
(declare-fun f6 (S3) S4)
(declare-fun f7 (S3 S3) S4)
(declare-fun f8 (S3) S5)
(declare-fun f9 (S3 S3) S5)
(declare-fun f10 (S3) S6)
(declare-fun f11 (S3 S3) S6)
(declare-fun f12 (S3) S7)
(declare-fun f13 (S3 S3) S7)
(declare-fun f14 (S3) S8)
(declare-fun f15 (S3 S3) S8)
(declare-fun f16 (S3) S9)
(declare-fun f17 (S3 S3) S9)
(declare-fun f18 (S3) S10)
(declare-fun f19 (S3 S3) S10)
(declare-fun f20 (S3) S11)
(declare-fun f21 (S3 S3) S11)
(declare-fun f22 (S3) S12)
(declare-fun f23 (S3 S3) S12)
(declare-fun f24 (S3) S13)
(declare-fun f25 (S3 S3) S13)
(assert (not (= f1 f2)))
(assert (not (forall ((?v0 S2)) (=> (forall ((?v1 S2)) (= ?v1 ?v0)) false))))
(assert (= f3 f1))
(assert (= (= f3 f1) (exists ((?v0 S2) (?v1 S2)) (not (= ?v0 ?v1)))))
(assert (= (= f4 f1) false))
(assert (= f5 f1))
(assert (= (= f5 f1) true))
(assert (forall ((?v0 S3)) (= (f6 ?v0) (f7 ?v0 ?v0))))
(assert (forall ((?v0 S3)) (= (f8 ?v0) (f9 ?v0 ?v0))))
(assert (forall ((?v0 S3)) (= (f10 ?v0) (f11 ?v0 ?v0))))
(assert (forall ((?v0 S3)) (= (f12 ?v0) (f13 ?v0 ?v0))))
(assert (forall ((?v0 S3)) (= (f14 ?v0) (f15 ?v0 ?v0))))
(assert (forall ((?v0 S3)) (= (f16 ?v0) (f17 ?v0 ?v0))))
(assert (forall ((?v0 S3)) (= (f18 ?v0) (f19 ?v0 ?v0))))
(assert (forall ((?v0 S3)) (= (f20 ?v0) (f21 ?v0 ?v0))))
(assert (forall ((?v0 S3)) (= (f22 ?v0) (f23 ?v0 ?v0))))
(assert (forall ((?v0 S3)) (= (f24 ?v0) (f25 ?v0 ?v0))))
(check-sat)
(exit)