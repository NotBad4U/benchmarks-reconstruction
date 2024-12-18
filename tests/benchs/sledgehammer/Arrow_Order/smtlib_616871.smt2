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
(declare-fun f3 (S3 S4) S1)
(declare-fun f4 (S5 S2) S3)
(declare-fun f5 (S6 S2) S5)
(declare-fun f6 () S6)
(declare-fun f7 () S4)
(declare-fun f8 () S2)
(declare-fun f9 () S2)
(declare-fun f10 (S4 S3) S1)
(assert (not (= f1 f2)))
(assert (not (and (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f5 f6 ?v0)) (?v_3 (= ?v0 f8))) (let ((?v_2 (not ?v_3)) (?v_0 (= ?v1 f8))) (let ((?v_4 (not ?v_0))) (and (=> (and (= (f3 (f4 ?v_1 ?v1) f7) f1) (and ?v_2 ?v_4)) (forall ((?v2 S2)) (let ((?v_5 (= ?v2 f8)) (?v_7 (or (= ?v0 f9) (= (f3 (f4 ?v_1 f9) f7) f1))) (?v_6 (f5 f6 ?v1))) (and (=> (and (= ?v1 f9) ?v_5) ?v_7) (and (=> (and (= (f3 (f4 ?v_6 ?v2) f7) f1) (not ?v_5)) (= (f3 (f4 ?v_1 ?v2) f7) f1)) (=> (and ?v_5 (= (f3 (f4 ?v_6 f9) f7) f1)) ?v_7)))))) (and (=> (and ?v_0 (and (= (f3 (f4 ?v_1 f9) f7) f1) ?v_2)) (forall ((?v2 S2)) (=> (and (= (f3 (f4 (f5 f6 f9) ?v2) f7) f1) (not (= ?v2 f8))) (= (f3 (f4 ?v_1 ?v2) f7) f1)))) (=> (and ?v_3 (and (= (f3 (f4 (f5 f6 f9) ?v1) f7) f1) ?v_4)) (forall ((?v2 S2)) (let ((?v_10 (f5 f6 ?v1)) (?v_9 (= ?v2 f8))) (let ((?v_8 (not ?v_9))) (and (=> (= ?v1 f9) ?v_8) (and (=> (and (= (f3 (f4 ?v_10 ?v2) f7) f1) ?v_8) (= (f3 (f4 (f5 f6 f9) ?v2) f7) f1)) (=> ?v_9 (not (= (f3 (f4 ?v_10 f9) f7) f1))))))))))))))) (forall ((?v0 S2) (?v1 S2)) (let ((?v_17 (f5 f6 f9)) (?v_11 (= ?v1 f8)) (?v_12 (f5 f6 ?v0)) (?v_14 (= ?v0 f8))) (let ((?v_13 (not ?v_14)) (?v_15 (not ?v_11)) (?v_16 (f5 f6 ?v1))) (=> (not (= ?v0 ?v1)) (or (and (= ?v0 f9) ?v_11) (or (and (= (f3 (f4 ?v_12 ?v1) f7) f1) (and ?v_13 ?v_15)) (or (and ?v_11 (and (= (f3 (f4 ?v_12 f9) f7) f1) ?v_13)) (or (and ?v_14 (and (= (f3 (f4 ?v_17 ?v1) f7) f1) ?v_15)) (or (and (= ?v1 f9) ?v_14) (or (and (= (f3 (f4 ?v_16 ?v0) f7) f1) (and ?v_15 ?v_13)) (or (and ?v_14 (and (= (f3 (f4 ?v_16 f9) f7) f1) ?v_15)) (and ?v_11 (and (= (f3 (f4 ?v_17 ?v0) f7) f1) ?v_13))))))))))))))))
(assert (not (= f9 f8)))
(assert (and (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 (f5 f6 ?v0) ?v1) f7) f1) (forall ((?v2 S2)) (=> (= (f3 (f4 (f5 f6 ?v1) ?v2) f7) f1) (= (f3 (f4 (f5 f6 ?v0) ?v2) f7) f1))))) (and (forall ((?v0 S2)) (not (= (f3 (f4 (f5 f6 ?v0) ?v0) f7) f1))) (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (or (= (f3 (f4 (f5 f6 ?v0) ?v1) f7) f1) (= (f3 (f4 (f5 f6 ?v1) ?v0) f7) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f4 (f5 f6 ?v0) ?v1) (f4 (f5 f6 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S4)) (= (= (f3 ?v0 ?v1) f1) (= (f10 ?v1 ?v0) f1))))
(check-sat)
(exit)
