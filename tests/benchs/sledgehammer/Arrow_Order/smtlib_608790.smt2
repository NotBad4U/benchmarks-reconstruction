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
(declare-fun f3 () S2)
(declare-fun f4 () S2)
(declare-fun f5 (S3 S4) S1)
(declare-fun f6 (S2 S2) S3)
(declare-fun f7 () S4)
(assert (not (= f1 f2)))
(assert (not (=> (not (= f3 f4)) (=> (and (forall ((?v0 S2) (?v1 S2)) (=> (= (f5 (f6 ?v0 ?v1) f7) f1) (forall ((?v2 S2)) (=> (= (f5 (f6 ?v1 ?v2) f7) f1) (= (f5 (f6 ?v0 ?v2) f7) f1))))) (and (forall ((?v0 S2)) (not (= (f5 (f6 ?v0 ?v0) f7) f1))) (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (or (= (f5 (f6 ?v0 ?v1) f7) f1) (= (f5 (f6 ?v1 ?v0) f7) f1)))))) (and (forall ((?v0 S2) (?v1 S2)) (let ((?v_2 (= ?v0 f3))) (let ((?v_1 (not ?v_2)) (?v_0 (= ?v1 f3))) (let ((?v_3 (not ?v_0))) (and (=> (and (= (f5 (f6 ?v0 ?v1) f7) f1) (and ?v_1 ?v_3)) (forall ((?v2 S2)) (let ((?v_4 (= ?v2 f3))) (and (=> (and (= (f5 (f6 ?v1 ?v2) f7) f1) (not ?v_4)) (= (f5 (f6 ?v0 ?v2) f7) f1)) (=> (and ?v_4 (= (f5 (f6 ?v1 f4) f7) f1)) (= (f5 (f6 ?v0 f4) f7) f1)))))) (and (=> (and ?v_0 (and (= (f5 (f6 ?v0 f4) f7) f1) ?v_1)) (forall ((?v2 S2)) (=> (and (= (f5 (f6 f4 ?v2) f7) f1) (not (= ?v2 f3))) (= (f5 (f6 ?v0 ?v2) f7) f1)))) (=> (and ?v_2 (and (= (f5 (f6 f4 ?v1) f7) f1) ?v_3)) (forall ((?v2 S2)) (let ((?v_5 (= ?v2 f3))) (and (=> (and (= (f5 (f6 ?v1 ?v2) f7) f1) (not ?v_5)) (or (= ?v2 f4) (= (f5 (f6 f4 ?v2) f7) f1))) (=> ?v_5 (not (= (f5 (f6 ?v1 f4) f7) f1))))))))))))) (forall ((?v0 S2) (?v1 S2)) (let ((?v_6 (= ?v0 f3))) (let ((?v_8 (not ?v_6)) (?v_7 (= ?v1 f3))) (let ((?v_9 (not ?v_7))) (=> (not (= ?v0 ?v1)) (or (and ?v_6 (= ?v1 f4)) (or (and (= (f5 (f6 ?v0 ?v1) f7) f1) (and ?v_8 ?v_9)) (or (and ?v_7 (and (= (f5 (f6 ?v0 f4) f7) f1) ?v_8)) (or (and ?v_6 (and (= (f5 (f6 f4 ?v1) f7) f1) ?v_9)) (or (and ?v_7 (= ?v0 f4)) (or (and (= (f5 (f6 ?v1 ?v0) f7) f1) (and ?v_9 ?v_8)) (or (and ?v_6 (and (= (f5 (f6 ?v1 f4) f7) f1) ?v_9)) (and ?v_7 (and (= (f5 (f6 f4 ?v0) f7) f1) ?v_8)))))))))))))))))))
(check-sat)
(exit)