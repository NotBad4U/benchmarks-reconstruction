(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unknown)
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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 () S4)
(declare-fun f7 () S2)
(declare-fun f8 () S2)
(declare-fun f9 () S2)
(declare-fun f10 () S3)
(declare-fun f11 (S5 S6) S3)
(declare-fun f12 (S7 S3) S5)
(declare-fun f13 () S7)
(declare-fun f14 () S3)
(declare-fun f15 (S8 S3) S6)
(declare-fun f16 () S8)
(declare-fun f17 () S3)
(declare-fun f18 () S2)
(declare-fun f19 (S9 S6) S6)
(declare-fun f20 (S10 S6) S9)
(declare-fun f21 () S10)
(declare-fun f22 () S10)
(declare-fun f23 () S10)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f3 f8 (f3 f9 f10)))) (let ((?v_1 (f4 f6 (f3 f7 (f3 f8 ?v_0)))) (?v_2 (f15 f16 ?v_0)) (?v_3 (f4 f6 (f3 f7 ?v_0)))) (not (= (f3 (f4 f5 (f3 ?v_1 (f11 (f12 f13 f14) ?v_2))) (f3 ?v_1 (f11 (f12 f13 f17) ?v_2))) (f3 (f4 f5 (f11 (f12 f13 (f3 ?v_3 (f3 f18 f14))) ?v_2)) (f11 (f12 f13 (f3 ?v_3 (f3 f18 f17))) ?v_2)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f8 (f3 f9 f10)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f11 (f12 f13 (f3 (f4 f5 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f5 (f11 (f12 f13 ?v0) ?v_0)) (f3 (f4 f6 (f3 (f4 f6 (f3 f7 ?v_1)) ?v0)) ?v1))) (f11 (f12 f13 ?v1) ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_3 (f3 f9 f10))) (let ((?v_5 (f15 f16 (f3 f8 ?v_3))) (?v_1 (f3 f9 ?v_3))) (let ((?v_0 (f15 f16 ?v_1)) (?v_2 (f12 f13 ?v0)) (?v_4 (f4 f6 (f3 f7 ?v_1))) (?v_6 (f12 f13 ?v1))) (= (f11 (f12 f13 (f3 (f4 f5 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f5 (f3 (f4 f5 (f11 ?v_2 ?v_0)) (f3 (f4 f6 (f3 ?v_4 (f11 ?v_2 ?v_5))) ?v1))) (f3 (f4 f6 (f3 ?v_4 ?v0)) (f11 ?v_6 ?v_5)))) (f11 ?v_6 ?v_0))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f3 f8 (f3 f9 f10)))) (let ((?v_0 (f15 f16 ?v_1))) (= (f11 (f12 f13 (f3 (f4 f5 ?v0) ?v1)) ?v_0) (f3 (f4 f5 (f3 (f4 f5 (f11 (f12 f13 ?v0) ?v_0)) (f11 (f12 f13 ?v1) ?v_0))) (f3 (f4 f6 (f3 (f4 f6 (f3 f7 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f15 f16 (f3 f8 (f3 f9 f10))))) (= (f19 (f20 f21 (f19 (f20 f22 ?v0) ?v1)) ?v_0) (f19 (f20 f22 (f19 (f20 f22 (f19 (f20 f21 ?v0) ?v_0)) (f19 (f20 f21 ?v1) ?v_0))) (f19 (f20 f23 (f19 (f20 f23 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f15 f16 ?v0))) (= (f19 (f20 f21 ?v_0) (f15 f16 (f3 f8 (f3 f9 f10)))) (f19 (f20 f23 ?v_0) ?v_0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f3 f7 ?v0))) (= (f11 (f12 f13 ?v_0) (f15 f16 (f3 f8 (f3 f9 f10)))) (f3 (f4 f6 ?v_0) ?v_0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f15 f16 (f3 f8 (f3 f9 f10))))) (= (f3 f18 (f11 (f12 f13 ?v0) ?v_0)) (f11 (f12 f13 (f3 f18 ?v0)) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f15 f16 (f3 f8 (f3 f9 f10))))) (= (= (f11 (f12 f13 ?v0) ?v_0) (f11 (f12 f13 ?v1) ?v_0)) (= (f3 f18 ?v0) (f3 f18 ?v1))))))
(assert (forall ((?v0 S3)) (let ((?v_1 (f3 f9 f10)) (?v_0 (f12 f13 ?v0))) (= (f3 (f4 f6 ?v0) (f11 ?v_0 (f15 f16 (f3 f8 ?v_1)))) (f11 ?v_0 (f15 f16 (f3 f9 ?v_1)))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f11 (f12 f13 ?v0) (f15 f16 (f3 f8 (f3 f9 f10)))))) (= (f3 f18 ?v_0) ?v_0))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f15 f16 (f3 f8 (f3 f9 f10))))) (= (f11 (f12 f13 (f3 f18 ?v0)) ?v_0) (f11 (f12 f13 ?v0) ?v_0)))))
(assert (forall ((?v0 S6)) (= (f19 (f20 f23 ?v0) ?v0) (f19 (f20 f21 ?v0) (f15 f16 (f3 f8 (f3 f9 f10)))))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f6 ?v0) ?v0) (f11 (f12 f13 ?v0) (f15 f16 (f3 f8 (f3 f9 f10)))))))
(assert (forall ((?v0 S6)) (= (f19 (f20 f21 ?v0) (f15 f16 (f3 f8 (f3 f9 f10)))) (f19 (f20 f23 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f11 (f12 f13 ?v0) (f15 f16 (f3 f8 (f3 f9 f10)))) (f3 (f4 f6 ?v0) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f20 f21 ?v0))) (let ((?v_1 (f19 ?v_0 ?v1))) (= (f19 ?v_0 (f19 (f20 f23 (f15 f16 (f3 f8 (f3 f9 f10)))) ?v1)) (f19 (f20 f23 ?v_1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S6)) (let ((?v_0 (f12 f13 ?v0))) (let ((?v_1 (f11 ?v_0 ?v1))) (= (f11 ?v_0 (f19 (f20 f23 (f15 f16 (f3 f8 (f3 f9 f10)))) ?v1)) (f3 (f4 f6 ?v_1) ?v_1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f20 f23 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (let ((?v_0 (f12 f13 ?v0))) (= (f11 (f12 f13 (f11 ?v_0 ?v1)) ?v2) (f11 ?v_0 (f19 (f20 f23 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f21 ?v0))) (= (f19 (f20 f23 (f19 ?v_0 ?v1)) (f19 ?v_0 ?v2)) (f19 ?v_0 (f19 (f20 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (let ((?v_0 (f12 f13 ?v0))) (= (f3 (f4 f6 (f11 ?v_0 ?v1)) (f11 ?v_0 ?v2)) (f11 ?v_0 (f19 (f20 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S6)) (= (f19 (f20 f23 (f15 f16 (f3 f8 (f3 f9 f10)))) ?v0) (f19 (f20 f22 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f19 (f20 f23 ?v0) (f15 f16 (f3 f8 (f3 f9 f10)))) (f19 (f20 f22 ?v0) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f6 ?v0))) (= (f3 (f4 f6 (f3 ?v_0 ?v1)) (f3 (f4 f6 ?v2) ?v3)) (f3 (f4 f6 (f3 ?v_0 ?v2)) (f3 (f4 f6 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f20 f23 ?v0))) (= (f19 (f20 f23 (f19 ?v_0 ?v1)) (f19 (f20 f23 ?v2) ?v3)) (f19 (f20 f23 (f19 ?v_0 ?v2)) (f19 (f20 f23 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f4 f6 (f3 (f4 f6 ?v0) ?v1))) (?v_0 (f4 f6 ?v2))) (= (f3 ?v_1 (f3 ?v_0 ?v3)) (f3 ?v_0 (f3 ?v_1 ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_1 (f20 f23 (f19 (f20 f23 ?v0) ?v1))) (?v_0 (f20 f23 ?v2))) (= (f19 ?v_1 (f19 ?v_0 ?v3)) (f19 ?v_0 (f19 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f6 ?v0)) (?v_1 (f3 (f4 f6 ?v2) ?v3))) (= (f3 (f4 f6 (f3 ?v_0 ?v1)) ?v_1) (f3 ?v_0 (f3 (f4 f6 ?v1) ?v_1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f20 f23 ?v0)) (?v_1 (f19 (f20 f23 ?v2) ?v3))) (= (f19 (f20 f23 (f19 ?v_0 ?v1)) ?v_1) (f19 ?v_0 (f19 (f20 f23 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f6 ?v0))) (= (f3 (f4 f6 (f3 ?v_0 ?v1)) ?v2) (f3 (f4 f6 (f3 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f23 ?v0))) (= (f19 (f20 f23 (f19 ?v_0 ?v1)) ?v2) (f19 (f20 f23 (f19 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f6 ?v0))) (= (f3 (f4 f6 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f6 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f23 ?v0))) (= (f19 (f20 f23 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f20 f23 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f6 ?v0))) (= (f3 ?v_0 (f3 (f4 f6 ?v1) ?v2)) (f3 (f4 f6 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f23 ?v0))) (= (f19 ?v_0 (f19 (f20 f23 ?v1) ?v2)) (f19 (f20 f23 (f19 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f4 f6 ?v0)) (?v_0 (f4 f6 ?v1))) (= (f3 ?v_1 (f3 ?v_0 ?v2)) (f3 ?v_0 (f3 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f20 f23 ?v0)) (?v_0 (f20 f23 ?v1))) (= (f19 ?v_1 (f19 ?v_0 ?v2)) (f19 ?v_0 (f19 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f6 ?v0) ?v1) (f3 (f4 f6 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f19 (f20 f23 ?v0) ?v1) (f19 (f20 f23 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) (f3 (f4 f5 ?v2) ?v3)) (f3 (f4 f5 (f3 ?v_0 ?v2)) (f3 (f4 f5 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f20 f22 ?v0))) (= (f19 (f20 f22 (f19 ?v_0 ?v1)) (f19 (f20 f22 ?v2) ?v3)) (f19 (f20 f22 (f19 ?v_0 ?v2)) (f19 (f20 f22 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 (f4 f5 (f3 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f22 ?v0))) (= (f19 (f20 f22 (f19 ?v_0 ?v1)) ?v2) (f19 (f20 f22 (f19 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f22 ?v0))) (= (f19 (f20 f22 (f19 ?v_0 ?v1)) ?v2) (f19 ?v_0 (f19 (f20 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2)) (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f20 f22 ?v0))) (= (f19 ?v_0 (f19 (f20 f22 ?v1) ?v2)) (f19 (f20 f22 (f19 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f4 f5 ?v0)) (?v_0 (f4 f5 ?v1))) (= (f3 ?v_1 (f3 ?v_0 ?v2)) (f3 ?v_0 (f3 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f20 f22 ?v0)) (?v_0 (f20 f22 ?v1))) (= (f19 ?v_1 (f19 ?v_0 ?v2)) (f19 ?v_0 (f19 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f5 ?v0) ?v1) (f3 (f4 f5 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f19 (f20 f22 ?v0) ?v1) (f19 (f20 f22 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_1 (f15 f16 (f3 f8 (f3 f9 f10)))) (?v_0 (f20 f21 ?v0))) (= (f19 ?v_0 (f19 (f20 f23 ?v_1) ?v1)) (f19 (f20 f21 (f19 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S6)) (let ((?v_1 (f15 f16 (f3 f8 (f3 f9 f10)))) (?v_0 (f12 f13 ?v0))) (= (f11 ?v_0 (f19 (f20 f23 ?v_1) ?v1)) (f11 (f12 f13 (f11 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f4 f6 ?v0)) (?v_1 (f4 f6 ?v2))) (= (= (f3 (f4 f5 (f3 ?v_0 ?v1)) (f3 ?v_1 ?v3)) (f3 (f4 f5 (f3 ?v_0 ?v3)) (f3 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f20 f23 ?v0)) (?v_1 (f20 f23 ?v2))) (= (= (f19 (f20 f22 (f19 ?v_0 ?v1)) (f19 ?v_1 ?v3)) (f19 (f20 f22 (f19 ?v_0 ?v3)) (f19 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(check-sat)
(exit)