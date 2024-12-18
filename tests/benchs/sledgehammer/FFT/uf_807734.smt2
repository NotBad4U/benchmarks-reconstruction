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
(declare-sort S11 0)
(declare-sort S12 0)
(declare-sort S13 0)
(declare-sort S14 0)
(declare-sort S15 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 (S5 S4) S2)
(declare-fun f5 () S5)
(declare-fun f6 (S6 S4) S4)
(declare-fun f7 () S6)
(declare-fun f8 () S4)
(declare-fun f9 (S7 S3) S3)
(declare-fun f10 (S8 S3) S7)
(declare-fun f11 () S8)
(declare-fun f12 () S3)
(declare-fun f13 () S3)
(declare-fun f14 (S9 S4) S6)
(declare-fun f15 () S9)
(declare-fun f16 (S10 S3) S1)
(declare-fun f17 (S3) S10)
(declare-fun f18 () S4)
(declare-fun f19 () S8)
(declare-fun f20 (S12 S3) S11)
(declare-fun f21 (S13 S11) S12)
(declare-fun f22 () S13)
(declare-fun f23 () S11)
(declare-fun f24 (S11 S11) S1)
(declare-fun f25 (S14 S11) S11)
(declare-fun f26 (S15 S11) S14)
(declare-fun f27 () S15)
(declare-fun f28 () S9)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f4 f5 f8))) (not (= (f3 (f4 f5 (f6 f7 f8)) (f9 (f10 f11 f12) f13)) (f6 (f14 f15 (f3 ?v_0 f13)) (f3 ?v_0 f12))))))
(assert (= (f16 (f17 f13) f12) f1))
(assert (not (= f8 f18)))
(assert (forall ((?v0 S3)) (= (f16 (f17 f13) ?v0) f1)))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (=> (not (= ?v0 f18)) (=> (= (f16 (f17 ?v1) ?v2) f1) (= (f3 ?v_0 (f9 (f10 f11 ?v2) ?v1)) (f6 (f14 f15 (f3 ?v_0 ?v2)) (f3 ?v_0 ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f9 (f10 f11 ?v0) ?v1) f13) (= (f16 (f17 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f16 (f17 ?v0) ?v1) f1) (= (f9 (f10 f11 ?v0) ?v1) f13))))
(assert (forall ((?v0 S4) (?v1 S3)) (=> (not (= ?v0 f18)) (= (f6 f7 (f3 (f4 f5 ?v0) ?v1)) (f3 (f4 f5 (f6 f7 ?v0)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (=> (not (= ?v0 f18)) (= (f3 (f4 f5 (f6 (f14 f15 ?v1) ?v0)) ?v2) (f6 (f14 f15 (f3 (f4 f5 ?v1) ?v2)) (f3 (f4 f5 ?v0) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f9 (f10 f19 ?v0) ?v1) f13) (and (= ?v0 f13) (not (= ?v1 f13))))))
(assert (forall ((?v0 S4) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f18) (and (= ?v0 f18) (not (= ?v1 f13))))))
(assert (forall ((?v0 S11) (?v1 S3)) (= (= (f20 (f21 f22 ?v0) ?v1) f23) (and (= ?v0 f23) (not (= ?v1 f13))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f16 (f17 ?v0) ?v1) f1) (=> (= (f16 (f17 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f17 ?v0))) (=> (= (f16 ?v_0 ?v1) f1) (=> (= (f16 (f17 ?v1) ?v2) f1) (= (f16 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f16 (f17 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f16 (f17 ?v0) ?v1) f1) (= (f16 (f17 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f16 (f17 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f11 ?v0))) (= (f9 (f10 f11 (f9 ?v_0 ?v1)) ?v2) (f9 (f10 f11 (f9 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S3)) (=> (not (= ?v0 f18)) (not (= (f3 (f4 f5 ?v0) ?v1) f18)))))
(assert (forall ((?v0 S11) (?v1 S3)) (=> (not (= ?v0 f23)) (not (= (f20 (f21 f22 ?v0) ?v1) f23)))))
(assert (forall ((?v0 S3)) (= (= (f16 (f17 ?v0) f13) f1) (= ?v0 f13))))
(assert (forall ((?v0 S3)) (= (= (f16 (f17 f13) ?v0) f1) true)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f9 (f10 f11 ?v0) ?v1) f13) (=> (= (f9 (f10 f11 ?v1) ?v0) f13) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3)) (= (f9 (f10 f11 ?v0) ?v0) f13)))
(assert (forall ((?v0 S3)) (= (f9 (f10 f11 ?v0) f13) ?v0)))
(assert (forall ((?v0 S3)) (= (f9 (f10 f11 f13) ?v0) f13)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f17 ?v0))) (=> (= (f16 ?v_0 ?v1) f1) (=> (= (f16 ?v_0 ?v2) f1) (= (= (f16 (f17 (f9 (f10 f11 ?v1) ?v0)) (f9 (f10 f11 ?v2) ?v0)) f1) (= (f16 (f17 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f17 ?v0)) (?v_1 (f10 f11 ?v1))) (=> (= (f16 ?v_0 ?v1) f1) (=> (= (f16 ?v_0 ?v2) f1) (= (f9 (f10 f11 (f9 ?v_1 ?v0)) (f9 (f10 f11 ?v2) ?v0)) (f9 ?v_1 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f17 ?v0))) (=> (= (f16 ?v_0 ?v1) f1) (=> (= (f16 ?v_0 ?v2) f1) (= (= (f9 (f10 f11 ?v1) ?v0) (f9 (f10 f11 ?v2) ?v0)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f10 f11 ?v1))) (=> (= (f16 (f17 ?v0) ?v1) f1) (= (f9 ?v_0 (f9 ?v_0 ?v0)) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f16 (f17 ?v0) ?v1) f1) (= (f16 (f17 (f9 (f10 f11 ?v0) ?v2)) (f9 (f10 f11 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f10 f11 ?v2))) (=> (= (f16 (f17 ?v0) ?v1) f1) (= (f16 (f17 (f9 ?v_0 ?v1)) (f9 ?v_0 ?v0)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f16 (f17 (f9 (f10 f11 ?v0) ?v1)) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f16 (f17 ?v0) ?v1) f1) (=> (= (f16 (f17 f13) ?v0) f1) (= (f16 (f17 (f9 (f10 f19 ?v0) ?v2)) (f9 (f10 f19 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S3)) (=> (= (f24 ?v0 ?v1) f1) (=> (= (f24 f23 ?v0) f1) (= (f24 (f20 (f21 f22 ?v0) ?v2) (f20 (f21 f22 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f17 f13))) (=> (= (f16 ?v_0 ?v0) f1) (= (f16 ?v_0 (f9 (f10 f19 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S3)) (=> (= (f24 f23 ?v0) f1) (= (f24 f23 (f20 (f21 f22 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f24 ?v0 ?v1) f1) (= (f24 (f25 (f26 f27 ?v0) ?v1) f23) f1))))
(assert (forall ((?v0 S11)) (= (f24 ?v0 ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f16 (f17 ?v0) ?v0) f1)))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (= (f6 f7 ?v0) (f6 f7 ?v1)) (=> (not (= ?v0 f18)) (=> (not (= ?v1 f18)) (= ?v0 ?v1))))))
(assert (forall ((?v0 S4)) (=> (= (f6 f7 ?v0) f18) (= ?v0 f18))))
(assert (forall ((?v0 S4)) (=> (not (= ?v0 f18)) (= (f6 f7 (f6 f7 ?v0)) ?v0))))
(assert (forall ((?v0 S4)) (=> (not (= ?v0 f18)) (not (= (f6 f7 ?v0) f18)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (f6 (f14 f15 (f6 (f14 f28 ?v0) ?v1)) ?v2) (f6 (f14 f28 (f6 (f14 f15 ?v0) ?v2)) (f6 (f14 f15 ?v1) ?v2)))))
(assert (forall ((?v0 S3)) (= (= f13 ?v0) (= ?v0 f13))))
(assert (forall ((?v0 S4)) (= (= f18 ?v0) (= ?v0 f18))))
(assert (forall ((?v0 S11)) (= (= f23 ?v0) (= ?v0 f23))))
(assert (forall ((?v0 S11) (?v1 S11)) (or (= (f24 ?v0 ?v1) f1) (= (f24 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f16 (f17 ?v0) ?v1) f1) (= (f16 (f17 ?v1) ?v0) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= ?v0 ?v1) (and (= (f24 ?v0 ?v1) f1) (= (f24 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (and (= (f16 (f17 ?v0) ?v1) f1) (= (f16 (f17 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= ?v0 ?v1) (= (f24 ?v0 ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f16 (f17 ?v0) ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f24 ?v0 ?v1) f1) (= (= (f24 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f16 (f17 ?v0) ?v1) f1) (= (= (f16 (f17 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= ?v0 ?v1) (=> (= (f24 ?v1 ?v2) f1) (= (f24 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= ?v0 ?v1) (=> (= (f16 (f17 ?v1) ?v2) f1) (= (f16 (f17 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= ?v0 ?v1) (=> (= (f24 ?v2 ?v1) f1) (= (f24 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f17 ?v2))) (=> (= ?v0 ?v1) (=> (= (f16 ?v_0 ?v1) f1) (= (f16 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f24 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f24 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f17 ?v0))) (=> (= (f16 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f16 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f24 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f24 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f16 (f17 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f16 (f17 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f24 ?v0 ?v1) f1) (=> (= (f24 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f16 (f17 ?v0) ?v1) f1) (=> (= (f16 (f17 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(check-sat)
(exit)
