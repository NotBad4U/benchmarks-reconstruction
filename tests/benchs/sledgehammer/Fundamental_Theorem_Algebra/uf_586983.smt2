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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 () S4)
(declare-fun f7 (S5 S6) S3)
(declare-fun f8 () S5)
(declare-fun f9 (S7 S6) S6)
(declare-fun f10 () S7)
(declare-fun f11 () S7)
(declare-fun f12 () S6)
(declare-fun f13 () S3)
(declare-fun f14 () S2)
(declare-fun f15 () S4)
(declare-fun f16 () S4)
(declare-fun f17 () S3)
(declare-fun f18 () S2)
(declare-fun f19 () S3)
(declare-fun f20 (S3 S3) S1)
(declare-fun f21 (S8 S6) S7)
(declare-fun f22 () S8)
(declare-fun f23 () S7)
(declare-fun f24 () S8)
(declare-fun f25 (S6 S6) S1)
(declare-fun f26 () S6)
(assert (not (= f1 f2)))
(assert (let ((?v_2 (f9 f10 (f9 f11 f12))) (?v_0 (f4 f6 f13))) (let ((?v_1 (f3 f14 (f3 (f4 f16 (f3 (f4 f6 f17) f17)) (f3 ?v_0 f13))))) (not (= (f3 (f4 f5 (f3 (f4 f6 (f7 f8 ?v_2)) (f3 ?v_0 (f3 f14 (f3 (f4 f5 (f3 (f4 f6 (f3 (f4 f15 ?v_1) f17)) (f3 (f4 f16 ?v_1) f17))) (f7 f8 (f9 f10 ?v_2))))))) (f3 f18 f13)) f13)))))
(assert (let ((?v_1 (f3 (f4 f16 (f3 (f4 f6 f17) f17)) (f3 (f4 f6 f13) f13)))) (let ((?v_0 (f3 f14 ?v_1))) (= (f3 (f4 f6 ?v_0) ?v_0) ?v_1))))
(assert (not (= f13 f19)))
(assert (not (= f13 f19)))
(assert (let ((?v_1 (f3 (f4 f16 (f3 (f4 f6 f17) f17)) (f3 (f4 f6 f13) f13)))) (let ((?v_0 (f3 f14 ?v_1))) (= (f3 (f4 f6 ?v_0) ?v_0) ?v_1))))
(assert (let ((?v_0 (f9 f10 (f9 f11 f12)))) (= (f3 f14 (f7 f8 (f9 f10 ?v_0))) (f7 f8 ?v_0))))
(assert (let ((?v_1 (f3 f14 (f3 (f4 f16 (f3 (f4 f6 f17) f17)) (f3 (f4 f6 f13) f13))))) (let ((?v_2 (f3 (f4 f15 ?v_1) f17)) (?v_0 (f3 (f4 f16 ?v_1) f17)) (?v_3 (f7 f8 (f9 f10 (f9 f10 (f9 f11 f12)))))) (= (f3 (f4 f15 (f3 f14 (f3 (f4 f5 (f3 (f4 f6 ?v_0) ?v_0)) ?v_3))) (f3 f14 (f3 (f4 f5 (f3 (f4 f6 ?v_2) ?v_2)) ?v_3))) f17))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f7 f8 (f9 f10 (f9 f11 f12))))) (= (f3 (f4 f15 (f3 (f4 f5 (f3 (f4 f16 ?v0) ?v1)) ?v_0)) ?v0) (f3 (f4 f5 (f3 (f4 f15 ?v1) ?v0)) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f7 f8 (f9 f10 (f9 f11 f12))))) (= (f3 (f4 f15 (f3 (f4 f5 (f3 (f4 f16 ?v0) ?v1)) ?v_0)) ?v1) (f3 (f4 f5 (f3 (f4 f15 ?v0) ?v1)) ?v_0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f3 (f4 f5 ?v0) (f7 f8 (f9 f10 (f9 f11 f12)))))) (= (f3 (f4 f16 ?v_0) ?v_0) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f6 (f7 f8 (f9 f10 (f9 f11 f12))))) (?v_1 (f4 f5 ?v1))) (= (= ?v0 (f3 ?v_1 (f3 ?v_0 ?v2))) (= (f3 ?v_0 ?v0) (f3 ?v_1 ?v2))))))
(assert (= (f20 f19 (f3 (f4 f5 (f3 (f4 f15 (f3 f14 (f3 (f4 f16 (f3 (f4 f6 f17) f17)) (f3 (f4 f6 f13) f13)))) f17)) (f7 f8 (f9 f10 (f9 f11 f12))))) f1))
(assert (forall ((?v0 S6)) (= (f9 (f21 f22 ?v0) (f9 f23 (f9 f10 (f9 f11 f12)))) (f9 (f21 f24 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f6 ?v0) (f7 f8 (f9 f10 (f9 f11 f12)))) (f3 (f4 f16 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f9 (f21 f22 ?v0) (f9 f23 (f9 f10 (f9 f11 f12)))) (f9 (f21 f24 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f6 ?v0) (f7 f8 (f9 f10 (f9 f11 f12)))) (f3 (f4 f16 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f9 (f21 f22 (f9 f23 (f9 f10 (f9 f11 f12)))) ?v0) (f9 (f21 f24 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f6 (f7 f8 (f9 f10 (f9 f11 f12)))) ?v0) (f3 (f4 f16 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f9 (f21 f22 (f9 f23 (f9 f10 (f9 f11 f12)))) ?v0) (f9 (f21 f24 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f6 (f7 f8 (f9 f10 (f9 f11 f12)))) ?v0) (f3 (f4 f16 ?v0) ?v0))))
(assert (= (f20 f19 (f3 (f4 f5 (f3 (f4 f16 (f3 f14 (f3 (f4 f16 (f3 (f4 f6 f17) f17)) (f3 (f4 f6 f13) f13)))) f17)) (f7 f8 (f9 f10 (f9 f11 f12))))) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f20 f19 (f3 (f4 f5 (f3 (f4 f15 (f3 f14 (f3 (f4 f16 (f3 (f4 f6 ?v0) ?v0)) (f3 (f4 f6 ?v1) ?v1)))) ?v0)) (f7 f8 (f9 f10 (f9 f11 f12))))) f1)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) (f7 f8 (f9 f11 f12))) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f20 f19 (f3 (f4 f5 (f3 (f4 f16 (f3 f14 (f3 (f4 f16 (f3 (f4 f6 ?v0) ?v0)) (f3 (f4 f6 ?v1) ?v1)))) ?v0)) (f7 f8 (f9 f10 (f9 f11 f12))))) f1)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f25 (f9 f23 ?v0) (f9 f23 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f20 (f7 f8 ?v0) (f7 f8 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6)) (= (f9 (f21 f24 ?v0) f12) ?v0)))
(assert (forall ((?v0 S6)) (= (f9 (f21 f24 f12) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f21 f24 (f9 f10 ?v0)) (f9 f10 ?v1)) (f9 f10 (f9 (f21 f24 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (f9 f10 ?v0) (f9 (f21 f24 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f9 (f21 f22 f12) ?v0) f12)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f21 f22 (f9 f10 ?v0)) ?v1) (f9 f10 (f9 (f21 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (= (f25 (f9 f23 ?v0) f26) f1) (= (f25 ?v0 f12) f1))))
(assert (forall ((?v0 S6)) (= (= (f20 (f7 f8 ?v0) f19) f1) (= (f25 ?v0 f12) f1))))
(assert (forall ((?v0 S6)) (= (= (f25 f26 (f9 f23 ?v0)) f1) (= (f25 f12 ?v0) f1))))
(assert (forall ((?v0 S6)) (= (= (f20 f19 (f7 f8 ?v0)) f1) (= (f25 f12 ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f21 f22 (f9 f11 ?v0)) ?v1) (f9 (f21 f24 (f9 f10 (f9 (f21 f22 ?v0) ?v1))) ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f21 f24 (f9 f11 ?v0)) (f9 f10 ?v1)) (f9 f11 (f9 (f21 f24 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f21 f24 (f9 f10 ?v0)) (f9 f11 ?v1)) (f9 f11 (f9 (f21 f24 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (= (f9 (f21 f24 ?v0) ?v0) f26) (= ?v0 f26))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f16 ?v0) ?v0) f19) (= ?v0 f19))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f9 f23 ?v0) (f9 f23 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f7 f8 ?v0) (f7 f8 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f9 f23 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S3)) (let ((?v_0 (f7 f8 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(check-sat)
(exit)
