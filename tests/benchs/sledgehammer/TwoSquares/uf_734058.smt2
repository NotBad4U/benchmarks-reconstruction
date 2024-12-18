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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 () S2)
(declare-fun f5 (S3 S2) S2)
(declare-fun f6 (S4 S2) S3)
(declare-fun f7 () S4)
(declare-fun f8 () S4)
(declare-fun f9 () S2)
(declare-fun f10 (S5 S6) S2)
(declare-fun f11 () S5)
(declare-fun f12 () S6)
(declare-fun f13 () S4)
(declare-fun f14 () S3)
(declare-fun f15 () S3)
(declare-fun f16 () S3)
(declare-fun f17 () S2)
(declare-fun f18 () S2)
(declare-fun f19 (S2 S2) S1)
(declare-fun f20 (S7 S2) S6)
(declare-fun f21 () S7)
(declare-fun f22 (S8 S6) S6)
(declare-fun f23 (S9 S6) S8)
(declare-fun f24 () S9)
(declare-fun f25 () S6)
(declare-fun f26 () S2)
(declare-fun f27 (S6 S6) S1)
(declare-fun f28 () S6)
(declare-fun f29 () S9)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f5 (f6 f8 f9) (f10 f11 f12))) (?v_1 (f5 f15 (f5 f16 f17)))) (not (= (f3 f4 (f5 (f6 f7 ?v_0) (f5 (f6 f13 (f5 (f6 f7 (f5 f14 ?v_1)) ?v_0)) (f5 (f6 f7 (f5 f14 (f5 f15 ?v_1))) f18)))) f1))))
(assert (let ((?v_1 (f5 (f6 f8 f9) (f10 f11 f12)))) (let ((?v_0 (f6 f7 ?v_1)) (?v_2 (f5 f15 (f5 f16 f17)))) (= (f3 (f5 (f6 f7 (f5 ?v_0 f18)) (f5 f14 (f5 f15 ?v_2))) (f5 (f6 f7 (f5 ?v_0 ?v_1)) (f5 f14 ?v_2))) f1))))
(assert (let ((?v_1 (f5 (f6 f8 f9) (f10 f11 f12)))) (let ((?v_0 (f6 f7 ?v_1)) (?v_2 (f5 f15 (f5 f16 f17)))) (= (f3 (f5 (f6 f7 (f5 ?v_0 f18)) (f5 f14 (f5 f15 ?v_2))) (f5 (f6 f7 (f5 ?v_0 ?v_1)) (f5 f14 ?v_2))) f1))))
(assert (= (f3 (f5 (f6 f13 (f5 (f6 f8 f9) (f10 f11 f12))) f18) f4) f1))
(assert (let ((?v_0 (f6 f7 (f5 f14 (f5 f15 (f5 f15 (f5 f16 f17))))))) (= (f3 (f5 (f6 f13 (f5 ?v_0 (f5 (f6 f8 f9) (f10 f11 f12)))) (f5 ?v_0 f18)) f4) f1)))
(assert (not (= (f19 f18 (f5 (f6 f8 f9) (f10 f11 f12))) f1)))
(assert (let ((?v_0 (f5 (f6 f8 f9) (f10 f11 f12))) (?v_1 (f5 f15 (f5 f16 f17)))) (= (f19 (f5 (f6 f7 ?v_0) (f5 (f6 f13 (f5 (f6 f7 (f5 f14 ?v_1)) ?v_0)) (f5 (f6 f7 (f5 f14 (f5 f15 ?v_1))) f18))) f4) f1)))
(assert (let ((?v_0 (f5 (f6 f8 f9) (f10 f11 f12)))) (let ((?v_2 (f6 f7 ?v_0)) (?v_1 (f5 f15 (f5 f16 f17)))) (= (f19 (f5 ?v_2 (f5 (f6 f13 (f5 (f6 f7 (f5 f14 ?v_1)) ?v_0)) (f5 (f6 f7 (f5 f14 (f5 f15 ?v_1))) f18))) (f5 ?v_2 f4)) f1))))
(assert (let ((?v_0 (f5 f15 (f5 f16 f17)))) (= (f19 (f5 (f6 f13 (f5 (f6 f7 (f5 f14 ?v_0)) (f5 (f6 f8 f9) (f10 f11 f12)))) (f5 (f6 f7 (f5 f14 (f5 f15 ?v_0))) f18)) f4) f1)))
(assert (= (f3 f4 (f5 f14 (f5 f15 (f5 f16 f17)))) f1))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f14 ?v0))) (= (f10 f11 (f20 f21 ?v0)) (ite (= (f3 f4 ?v_0) f1) ?v_0 f4)))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f8 f9) (f5 f14 ?v0)) (f5 f14 (f5 (f6 f8 (f5 f16 f17)) ?v0)))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f8 (f5 f14 ?v0)) f9) (f5 f14 (f5 (f6 f8 ?v0) (f5 f16 f17))))))
(assert (forall ((?v0 S2)) (= (= (f3 f9 (f5 f14 ?v0)) f1) (= (f3 (f5 f16 f17) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 (f5 f14 ?v0) f9) f1) (= (f3 ?v0 (f5 f16 f17)) f1))))
(assert (= (f5 (f6 f8 f9) f9) (f5 f14 (f5 f15 (f5 f16 f17)))))
(assert (= (f22 (f23 f24 f25) f25) (f20 f21 (f5 f15 (f5 f16 f17)))))
(assert (= (f5 (f6 f8 f9) f9) (f5 f14 (f5 f15 (f5 f16 f17)))))
(assert (forall ((?v0 S2)) (= (f5 (f6 f7 ?v0) (f5 f14 (f5 f15 (f5 f16 f17)))) (f5 (f6 f8 ?v0) ?v0))))
(assert (= (f19 f9 f26) f1))
(assert (= (f19 f4 (f5 (f6 f8 f9) (f10 f11 f12))) f1))
(assert (= (f27 f28 f12) f1))
(assert (= f28 (f20 f21 f17)))
(assert (= (f20 f21 f17) f28))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f19 ?v0 ?v1) f1) (or (= ?v0 ?v1) (= (f19 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f19 (f5 f14 ?v0) (f5 f14 ?v1)) f1) (= (f19 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f22 (f23 f29 (f20 f21 ?v0)) (f20 f21 ?v1)) (ite (= (f19 ?v0 f17) f1) f28 (f20 f21 (f5 (f6 f7 ?v0) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (= (f22 (f23 f29 (f20 f21 ?v0)) (f22 (f23 f29 (f20 f21 ?v1)) ?v2)) (ite (= (f19 ?v0 f17) f1) f28 (f22 (f23 f29 (f20 f21 (f5 (f6 f7 ?v0) ?v1))) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f20 f21 ?v0)) (?v_0 (f20 f21 ?v1))) (= (f22 (f23 f24 ?v_1) ?v_0) (ite (= (f19 ?v0 f17) f1) ?v_0 (ite (= (f19 ?v1 f17) f1) ?v_1 (f20 f21 (f5 (f6 f8 ?v0) ?v1))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f19 (f5 f16 ?v0) (f5 f16 ?v1)) f1) (= (f19 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f19 (f5 f16 ?v0) (f5 f16 ?v1)) f1) (= (f19 ?v0 ?v1) f1))))
(assert (= (= (f19 f17 f17) f1) false))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f19 (f5 f15 ?v0) (f5 f15 ?v1)) f1) (= (f19 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f19 (f5 f15 ?v0) (f5 f15 ?v1)) f1) (= (f19 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f19 ?v0 ?v1) f1) (and (= (f3 ?v0 ?v1) f1) (not (= ?v0 ?v1))))))
(check-sat)
(exit)
