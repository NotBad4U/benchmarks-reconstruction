(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status sat)
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
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 (S3 S4) S2)
(declare-fun f5 (S5 S2) S3)
(declare-fun f6 () S5)
(declare-fun f7 (S6 S2) S2)
(declare-fun f8 (S7 S2) S6)
(declare-fun f9 () S7)
(declare-fun f10 () S2)
(declare-fun f11 () S3)
(declare-fun f12 () S4)
(declare-fun f13 (S8 S2) S4)
(declare-fun f14 () S8)
(declare-fun f15 () S6)
(declare-fun f16 () S6)
(declare-fun f17 () S2)
(declare-fun f18 () S2)
(declare-fun f19 () S2)
(declare-fun f20 (S9 S4) S4)
(declare-fun f21 (S10 S4) S9)
(declare-fun f22 () S10)
(declare-fun f23 () S4)
(declare-fun f24 () S6)
(declare-fun f25 () S10)
(declare-fun f26 () S9)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f13 f14 (f7 f15 (f7 f16 f17))))) (not (= (f3 (f4 (f5 f6 (f7 (f8 f9 f10) (f4 f11 f12))) ?v_0) (f7 (f8 f9 (f4 (f5 f6 f18) ?v_0)) (f4 (f5 f6 f19) ?v_0))) f1))))
(assert (let ((?v_0 (f13 f14 (f7 f15 (f7 f16 f17))))) (let ((?v_1 (f4 (f5 f6 (f7 (f8 f9 f10) (f4 f11 f12))) ?v_0))) (and (= (f3 ?v_1 (f4 (f5 f6 f18) ?v_0)) f1) (= (f3 ?v_1 (f4 (f5 f6 f19) ?v_0)) f1)))))
(assert (let ((?v_0 (f13 f14 (f7 f15 (f7 f16 f17))))) (let ((?v_1 (f4 (f5 f6 (f7 (f8 f9 f10) (f4 f11 f12))) ?v_0))) (and (= (f3 ?v_1 (f4 (f5 f6 f18) ?v_0)) f1) (= (f3 ?v_1 (f4 (f5 f6 f19) ?v_0)) f1)))))
(assert (let ((?v_0 (f7 (f8 f9 f10) (f4 f11 f12)))) (and (= (f3 ?v_0 f18) f1) (= (f3 ?v_0 f19) f1))))
(assert (= (f4 (f5 f6 f10) (f13 f14 (f7 f15 (f7 f16 f17)))) f10))
(assert (= (f20 (f21 f22 f23) (f13 f14 (f7 f15 (f7 f16 f17)))) f23))
(assert (forall ((?v0 S2)) (= (f7 (f8 f9 f10) (f7 f24 ?v0)) (f7 f24 (f7 (f8 f9 (f7 f16 f17)) ?v0)))))
(assert (forall ((?v0 S2)) (= (f7 (f8 f9 (f7 f24 ?v0)) f10) (f7 f24 (f7 (f8 f9 ?v0) (f7 f16 f17))))))
(assert (= (f7 (f8 f9 f10) f10) (f7 f24 (f7 f15 (f7 f16 f17)))))
(assert (= (f7 (f8 f9 f10) f10) (f7 f24 (f7 f15 (f7 f16 f17)))))
(assert (= (f20 (f21 f25 f23) f23) (f13 f14 (f7 f15 (f7 f16 f17)))))
(assert (forall ((?v0 S2)) (let ((?v_2 (f7 f15 (f7 f16 f17)))) (let ((?v_0 (f13 f14 ?v_2)) (?v_1 (f5 f6 ?v0))) (= (f4 (f5 f6 (f4 ?v_1 ?v_0)) ?v_0) (f4 ?v_1 (f13 f14 (f7 f15 ?v_2))))))))
(assert (= f10 (f7 f24 (f7 f16 f17))))
(assert (= (f7 f24 (f7 f16 f17)) f10))
(assert (= (f7 f24 (f7 f16 f17)) f10))
(assert (= (f13 f14 (f7 f16 f17)) f23))
(assert (forall ((?v0 S2)) (let ((?v_0 (f7 f24 ?v0))) (= (f7 f24 (f7 f16 ?v0)) (f7 (f8 f9 (f7 (f8 f9 f10) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S4)) (= (f13 f14 (f4 f11 ?v0)) (f20 f26 ?v0))))
(assert (forall ((?v0 S4)) (let ((?v_0 (f4 f11 ?v0))) (= (f7 f24 ?v_0) ?v_0))))
(assert (forall ((?v0 S2)) (= (f7 f16 ?v0) (f7 (f8 f9 (f7 (f8 f9 f10) ?v0)) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f7 (f8 f9 (f7 f24 ?v0)) (f7 f24 ?v1)) (f7 f24 (f7 (f8 f9 ?v0) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f4 (f5 f6 (f4 f11 ?v0)) ?v1) (f4 f11 (f20 (f21 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f4 f11 (f20 (f21 f22 ?v0) ?v1)) (f4 (f5 f6 (f4 f11 ?v0)) ?v1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2)) (= (f7 (f8 f9 (f4 f11 ?v0)) (f7 (f8 f9 (f4 f11 ?v1)) ?v2)) (f7 (f8 f9 (f4 f11 (f20 (f21 f25 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f7 (f8 f9 (f4 f11 ?v0)) (f4 f11 ?v1)) (f4 f11 (f20 (f21 f25 ?v0) ?v1)))))
(assert (= (f4 f11 f23) f10))
(assert (= (f20 (f21 f25 f23) f23) (f13 f14 (f7 f15 (f7 f16 f17)))))
(assert (= f10 (f7 f24 (f7 f16 f17))))
(assert (= (f13 f14 (f7 f16 f17)) f23))
(assert (= f23 (f13 f14 (f7 f16 f17))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f7 f24 ?v0) (f7 f24 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S4)) (let ((?v_0 (f13 f14 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f7 f24 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f7 f16 ?v0) (f7 f16 ?v1)) (= ?v0 ?v1))))
(assert (= (= f17 f17) true))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f7 f15 ?v0) (f7 f15 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f8 f9 ?v0))) (= (f7 (f8 f9 (f7 ?v_0 ?v1)) ?v2) (f7 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f8 f9 ?v0)) (?v_0 (f8 f9 ?v1))) (= (f7 ?v_1 (f7 ?v_0 ?v2)) (f7 ?v_0 (f7 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v1) ?v0))))
(check-sat)
(exit)