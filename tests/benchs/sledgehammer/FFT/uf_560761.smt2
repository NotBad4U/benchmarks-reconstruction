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
(declare-sort S11 0)
(declare-sort S12 0)
(declare-sort S13 0)
(declare-sort S14 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S6) S3)
(declare-fun f7 () S5)
(declare-fun f8 () S6)
(declare-fun f9 (S7 S8) S3)
(declare-fun f10 (S9 S5) S7)
(declare-fun f11 () S9)
(declare-fun f12 (S6 S6) S8)
(declare-fun f13 () S6)
(declare-fun f14 (S6 S6) S8)
(declare-fun f15 (S6 S6) S1)
(declare-fun f16 (S10 S6) S6)
(declare-fun f17 (S11 S6) S10)
(declare-fun f18 () S11)
(declare-fun f19 (S8 S6) S1)
(declare-fun f20 (S12 S6) S8)
(declare-fun f21 () S10)
(declare-fun f22 (S13 S8) S6)
(declare-fun f23 (S14 S10) S13)
(declare-fun f24 () S14)
(declare-fun f25 (S6 S6) S1)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f10 f11 f7))) (not (= (f3 (f4 f5 (f6 f7 f8)) (f9 ?v_0 (f12 f8 f13))) (f9 ?v_0 (f14 f8 f13))))))
(assert (= (f15 f8 f13) f1))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f16 (f17 f18 ?v0) ?v1) (f16 (f17 f18 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f17 f18 ?v0)) (?v_0 (f17 f18 ?v1))) (= (f16 ?v_1 (f16 ?v_0 ?v2)) (f16 ?v_0 (f16 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (= (f16 ?v_0 (f16 (f17 f18 ?v1) ?v2)) (f16 (f17 f18 (f16 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (= (f16 (f17 f18 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f17 f18 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f3 (f4 f5 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (= (f16 (f17 f18 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f17 f18 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (= (f16 (f17 f18 (f16 ?v_0 ?v1)) ?v2) (f16 (f17 f18 (f16 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (= (= (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f16 (f17 f18 ?v0) ?v1) (f16 (f17 f18 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f17 f18 ?v0))) (= (f16 (f17 f18 (f16 ?v_0 ?v1)) (f16 (f17 f18 ?v2) ?v3)) (f16 (f17 f18 (f16 ?v_0 ?v2)) (f16 (f17 f18 ?v1) ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (=> (= (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (=> (= (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f16 (f17 f18 ?v0) ?v1) (f16 (f17 f18 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (=> (= (f15 (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) f1) (= (f15 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f15 (f16 (f17 f18 ?v0) ?v1) (f16 (f17 f18 ?v2) ?v1)) f1) (= (f15 ?v0 ?v2) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (=> (= (f15 ?v0 ?v1) f1) (=> (= (f15 ?v2 ?v3) f1) (= (f15 (f16 (f17 f18 ?v0) ?v2) (f16 (f17 f18 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v2))) (=> (= (f15 ?v0 ?v1) f1) (= (f15 (f16 ?v_0 ?v0) (f16 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f15 ?v0 ?v1) f1) (= (f15 (f16 (f17 f18 ?v0) ?v2) (f16 (f17 f18 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (= (= (f15 (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) f1) (= (f15 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f15 (f16 (f17 f18 ?v0) ?v1) (f16 (f17 f18 ?v2) ?v1)) f1) (= (f15 ?v0 ?v2) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (=> (= (f14 ?v0 ?v1) (f14 ?v2 ?v3)) (=> (= (f15 ?v0 ?v1) f1) (=> (= (f15 ?v2 ?v3) f1) (= ?v1 ?v3))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (=> (= (f14 ?v0 ?v1) (f14 ?v2 ?v3)) (=> (= (f15 ?v0 ?v1) f1) (=> (= (f15 ?v2 ?v3) f1) (= ?v0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (=> (= (f15 ?v0 ?v1) f1) (=> (= (f15 ?v2 ?v3) f1) (= (= (f14 ?v0 ?v1) (f14 ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))))
(assert (forall ((?v0 S6)) (not (= (f15 ?v0 ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (not (= (f15 (f16 (f17 f18 ?v0) ?v1) ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (not (= (f15 (f16 (f17 f18 ?v0) ?v1) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (not (= ?v0 ?v1)) (or (= (f15 ?v0 ?v1) f1) (= (f15 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (= (= (f15 (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) f1) (= (f15 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f15 ?v0 ?v1) f1) false) (=> (=> (= (f15 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S6)) (=> (= (f15 ?v0 ?v0) f1) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f15 ?v0 ?v1) f1) (not (= ?v1 ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f16 (f17 f18 ?v0) ?v1) (f16 (f17 f18 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f17 f18 ?v0)) (?v_0 (f17 f18 ?v1))) (= (f16 ?v_1 (f16 ?v_0 ?v2)) (f16 ?v_0 (f16 ?v_1 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (= (f16 (f17 f18 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f17 f18 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f17 f18 ?v0))) (= (= (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f16 (f17 f18 ?v0) ?v1) (f16 (f17 f18 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S12)) (let ((?v_0 (= (f19 (f20 ?v2 ?v1) ?v0) f1))) (=> (=> (= (f15 ?v0 ?v1) f1) ?v_0) (=> (=> (= ?v0 ?v1) ?v_0) (=> (=> (= (f15 ?v1 ?v0) f1) ?v_0) ?v_0))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f15 (f16 (f17 f18 ?v0) ?v1) ?v2) f1) (= (f15 ?v0 ?v2) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (=> (= (f15 ?v0 ?v1) f1) (=> (= (f16 (f17 f18 ?v2) ?v1) (f16 (f17 f18 ?v0) ?v3)) (= (f15 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (=> (= (f15 ?v0 ?v1) f1) (=> (= (f15 ?v2 ?v3) f1) (= (f15 (f16 (f17 f18 ?v0) ?v2) (f16 (f17 f18 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f15 ?v0 ?v1) f1) (= (f15 (f16 (f17 f18 ?v0) ?v2) (f16 (f17 f18 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f15 ?v0 ?v1) f1) (= (f15 ?v0 (f16 (f17 f18 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f15 ?v0 ?v1) f1) (= (f15 ?v0 (f16 (f17 f18 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f15 ?v0 ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f15 ?v0 ?v1) f1) (= (f15 ?v0 (f16 (f17 f18 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f15 ?v0 ?v1) f1) (= (f15 ?v0 (f16 (f17 f18 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S5)) (let ((?v_0 (f10 f11 ?v2))) (=> (= (f15 ?v0 ?v1) f1) (= (f9 ?v_0 (f14 ?v0 ?v1)) (f3 (f4 f5 (f6 ?v2 ?v0)) (f9 ?v_0 (f14 (f16 f21 ?v0) ?v1))))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S10)) (let ((?v_0 (f23 f24 ?v2))) (=> (= (f15 ?v0 ?v1) f1) (= (f22 ?v_0 (f14 ?v0 ?v1)) (f16 (f17 f18 (f16 ?v2 ?v0)) (f22 ?v_0 (f14 (f16 f21 ?v0) ?v1))))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S5)) (let ((?v_0 (f10 f11 ?v3))) (=> (= (f25 ?v0 ?v1) f1) (=> (= (f25 ?v1 ?v2) f1) (= (f3 (f4 f5 (f9 ?v_0 (f14 ?v0 ?v1))) (f9 ?v_0 (f14 ?v1 ?v2))) (f9 ?v_0 (f14 ?v0 ?v2))))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S10)) (let ((?v_0 (f23 f24 ?v3))) (=> (= (f25 ?v0 ?v1) f1) (=> (= (f25 ?v1 ?v2) f1) (= (f16 (f17 f18 (f22 ?v_0 (f14 ?v0 ?v1))) (f22 ?v_0 (f14 ?v1 ?v2))) (f22 ?v_0 (f14 ?v0 ?v2))))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (=> (= (f15 ?v0 ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f15 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f15 ?v0 ?v1) f1) (=> (=> (not false) (= (f15 ?v1 ?v0) f1)) false))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f15 ?v0 ?v1) f1) (=> (= (f15 ?v2 ?v0) f1) (= (f15 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f15 ?v0 ?v1) f1) (=> (= (f15 ?v1 ?v2) f1) (= (f15 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f15 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f15 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S6)) (= (f25 ?v0 ?v0) f1)))
(assert (forall ((?v0 S6)) (= (f15 ?v0 (f16 f21 ?v0)) f1)))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f15 ?v0 ?v1) f1) (= (f15 (f16 f21 ?v0) (f16 f21 ?v1)) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f15 ?v0 ?v1) f1) (= (f25 (f16 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f15 ?v0 (f16 f21 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f25 (f16 f21 ?v0) ?v1) f1) (= (f15 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f25 ?v0 ?v1) f1) (= (f15 ?v0 (f16 f21 ?v1)) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f15 ?v0 ?v1) f1) (= (f25 (f16 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f25 ?v0 ?v1) f1) (= (= (f15 ?v1 (f16 f21 ?v0)) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f25 (f16 f21 ?v0) ?v1) f1) (= (f15 ?v0 ?v1) f1))))
(check-sat)
(exit)