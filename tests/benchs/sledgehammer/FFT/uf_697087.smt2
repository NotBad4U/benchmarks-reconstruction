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
(declare-sort S16 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 (S5 S4) S2)
(declare-fun f5 () S5)
(declare-fun f6 () S2)
(declare-fun f7 (S6 S3) S3)
(declare-fun f8 (S7 S3) S6)
(declare-fun f9 () S7)
(declare-fun f10 (S8 S9) S3)
(declare-fun f11 () S8)
(declare-fun f12 (S10 S9) S9)
(declare-fun f13 () S10)
(declare-fun f14 () S10)
(declare-fun f15 () S9)
(declare-fun f16 () S3)
(declare-fun f17 () S3)
(declare-fun f18 () S3)
(declare-fun f19 () S7)
(declare-fun f20 (S11 S4) S4)
(declare-fun f21 (S12 S4) S11)
(declare-fun f22 () S12)
(declare-fun f23 (S13 S3) S9)
(declare-fun f24 (S14 S9) S13)
(declare-fun f25 () S14)
(declare-fun f26 (S15 S9) S10)
(declare-fun f27 () S15)
(declare-fun f28 (S16 S9) S4)
(declare-fun f29 () S16)
(declare-fun f30 () S10)
(declare-fun f31 () S4)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15))))) (?v_1 (f8 f9 f17))) (not (= (f3 (f4 f5 (f3 f6 (f7 ?v_0 f16))) (f7 ?v_1 (f7 ?v_0 f18))) (f3 (f4 f5 (f3 f6 f16)) (f7 ?v_1 f18))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f8 f19 ?v0))) (let ((?v_1 (f7 ?v_0 ?v1))) (= (f7 ?v_0 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1)) (f7 (f8 f9 ?v_1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f4 f5 ?v0))) (let ((?v_1 (f3 ?v_0 ?v1))) (= (f3 ?v_0 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1)) (f20 (f21 f22 ?v_1) ?v_1))))))
(assert (forall ((?v0 S9) (?v1 S3)) (let ((?v_0 (f24 f25 ?v0))) (let ((?v_1 (f23 ?v_0 ?v1))) (= (f23 ?v_0 (f7 (f8 f9 (f10 f11 (f12 f13 (f12 f14 f15)))) ?v1)) (f12 (f26 f27 ?v_1) ?v_1))))))
(assert (forall ((?v0 S9)) (let ((?v_0 (f10 f11 ?v0))) (= (f7 (f8 f19 ?v_0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f7 (f8 f9 ?v_0) ?v_0)))))
(assert (forall ((?v0 S9)) (let ((?v_0 (f28 f29 ?v0))) (= (f3 (f4 f5 ?v_0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f20 (f21 f22 ?v_0) ?v_0)))))
(assert (forall ((?v0 S9)) (let ((?v_0 (f12 f30 ?v0))) (= (f23 (f24 f25 ?v_0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f12 (f26 f27 ?v_0) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f8 f19 ?v0))) (= (f7 ?v_0 (f7 (f8 f9 ?v_1) ?v1)) (f7 (f8 f19 (f7 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f7 (f8 f9 ?v_1) ?v1)) (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S9) (?v1 S3)) (let ((?v_1 (f10 f11 (f12 f13 (f12 f14 f15)))) (?v_0 (f24 f25 ?v0))) (= (f23 ?v_0 (f7 (f8 f9 ?v_1) ?v1)) (f23 (f24 f25 (f23 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 ?v0) ?v0) (f7 (f8 f19 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))))))
(assert (forall ((?v0 S4)) (= (f20 (f21 f22 ?v0) ?v0) (f3 (f4 f5 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))))))
(assert (forall ((?v0 S9)) (= (f12 (f26 f27 ?v0) ?v0) (f23 (f24 f25 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f19 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f7 (f8 f9 ?v0) ?v0))))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f20 (f21 f22 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f23 (f24 f25 ?v0) (f10 f11 (f12 f13 (f12 f14 f15)))) (f12 (f26 f27 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f19 ?v0) (f10 f11 (f12 f14 (f12 f14 f15)))) (f7 (f8 f9 (f7 (f8 f9 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) (f10 f11 (f12 f14 (f12 f14 f15)))) (f20 (f21 f22 (f20 (f21 f22 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S9)) (= (f23 (f24 f25 ?v0) (f10 f11 (f12 f14 (f12 f14 f15)))) (f12 (f26 f27 (f12 (f26 f27 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S4)) (= (f20 (f21 f22 ?v0) (f28 f29 (f12 f14 f15))) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f26 f27 ?v0) (f12 f30 (f12 f14 f15))) ?v0)))
(assert (forall ((?v0 S4)) (= (f20 (f21 f22 (f28 f29 (f12 f14 f15))) ?v0) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f26 f27 (f12 f30 (f12 f14 f15))) ?v0) ?v0)))
(assert (= (f3 f6 (f10 f11 (f12 f13 (f12 f13 (f12 f14 f15))))) f31))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f19 ?v0))) (= (f7 ?v_0 (f7 (f8 f9 ?v1) ?v2)) (f7 (f8 f19 (f7 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 ?v_0 (f7 (f8 f9 ?v1) ?v2)) (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S3)) (let ((?v_0 (f24 f25 ?v0))) (= (f23 ?v_0 (f7 (f8 f9 ?v1) ?v2)) (f23 (f24 f25 (f23 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f19 ?v0))) (= (f7 (f8 f19 (f7 ?v_0 ?v1)) ?v2) (f7 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f4 f5 (f3 ?v_0 ?v1)) ?v2) (f3 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S3)) (let ((?v_0 (f24 f25 ?v0))) (= (f23 (f24 f25 (f23 ?v_0 ?v1)) ?v2) (f23 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (= (f12 f13 f15) f15))
(assert (forall ((?v0 S9)) (= (f12 (f26 f27 f15) ?v0) f15)))
(assert (forall ((?v0 S9) (?v1 S3) (?v2 S3)) (let ((?v_0 (f24 f25 ?v0))) (= (f23 (f24 f25 (f23 ?v_0 ?v1)) ?v2) (f23 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 (f26 f27 (f12 f13 ?v0)) ?v1) (f12 f13 (f12 (f26 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f21 f22 ?v0))) (= (f20 (f21 f22 (f20 ?v_0 ?v1)) (f20 (f21 f22 ?v2) ?v3)) (f20 (f21 f22 (f20 ?v_0 ?v2)) (f20 (f21 f22 ?v1) ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f7 (f8 f9 (f7 ?v_0 ?v1)) (f7 (f8 f9 ?v2) ?v3)) (f7 (f8 f9 (f7 ?v_0 ?v2)) (f7 (f8 f9 ?v1) ?v3))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (let ((?v_0 (f26 f27 ?v0))) (= (f12 (f26 f27 (f12 ?v_0 ?v1)) (f12 (f26 f27 ?v2) ?v3)) (f12 (f26 f27 (f12 ?v_0 ?v2)) (f12 (f26 f27 ?v1) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_1 (f21 f22 (f20 (f21 f22 ?v0) ?v1))) (?v_0 (f21 f22 ?v2))) (= (f20 ?v_1 (f20 ?v_0 ?v3)) (f20 ?v_0 (f20 ?v_1 ?v3))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_1 (f8 f9 (f7 (f8 f9 ?v0) ?v1))) (?v_0 (f8 f9 ?v2))) (= (f7 ?v_1 (f7 ?v_0 ?v3)) (f7 ?v_0 (f7 ?v_1 ?v3))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (let ((?v_1 (f26 f27 (f12 (f26 f27 ?v0) ?v1))) (?v_0 (f26 f27 ?v2))) (= (f12 ?v_1 (f12 ?v_0 ?v3)) (f12 ?v_0 (f12 ?v_1 ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f21 f22 ?v0)) (?v_1 (f20 (f21 f22 ?v2) ?v3))) (= (f20 (f21 f22 (f20 ?v_0 ?v1)) ?v_1) (f20 ?v_0 (f20 (f21 f22 ?v1) ?v_1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (let ((?v_0 (f8 f9 ?v0)) (?v_1 (f7 (f8 f9 ?v2) ?v3))) (= (f7 (f8 f9 (f7 ?v_0 ?v1)) ?v_1) (f7 ?v_0 (f7 (f8 f9 ?v1) ?v_1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (let ((?v_0 (f26 f27 ?v0)) (?v_1 (f12 (f26 f27 ?v2) ?v3))) (= (f12 (f26 f27 (f12 ?v_0 ?v1)) ?v_1) (f12 ?v_0 (f12 (f26 f27 ?v1) ?v_1))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f21 f22 ?v0))) (= (f20 (f21 f22 (f20 ?v_0 ?v1)) ?v2) (f20 (f21 f22 (f20 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f7 (f8 f9 (f7 ?v_0 ?v1)) ?v2) (f7 (f8 f9 (f7 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f26 f27 ?v0))) (= (f12 (f26 f27 (f12 ?v_0 ?v1)) ?v2) (f12 (f26 f27 (f12 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f21 f22 ?v0))) (= (f20 (f21 f22 (f20 ?v_0 ?v1)) ?v2) (f20 ?v_0 (f20 (f21 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f7 (f8 f9 (f7 ?v_0 ?v1)) ?v2) (f7 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f26 f27 ?v0))) (= (f12 (f26 f27 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f26 f27 ?v1) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f21 f22 ?v0))) (= (f20 ?v_0 (f20 (f21 f22 ?v1) ?v2)) (f20 (f21 f22 (f20 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f7 ?v_0 (f7 (f8 f9 ?v1) ?v2)) (f7 (f8 f9 (f7 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f26 f27 ?v0))) (= (f12 ?v_0 (f12 (f26 f27 ?v1) ?v2)) (f12 (f26 f27 (f12 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_1 (f21 f22 ?v0)) (?v_0 (f21 f22 ?v1))) (= (f20 ?v_1 (f20 ?v_0 ?v2)) (f20 ?v_0 (f20 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f8 f9 ?v0)) (?v_0 (f8 f9 ?v1))) (= (f7 ?v_1 (f7 ?v_0 ?v2)) (f7 ?v_0 (f7 ?v_1 ?v2))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_1 (f26 f27 ?v0)) (?v_0 (f26 f27 ?v1))) (= (f12 ?v_1 (f12 ?v_0 ?v2)) (f12 ?v_0 (f12 ?v_1 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f20 (f21 f22 ?v0) ?v1) (f20 (f21 f22 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v1) ?v0))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 (f26 f27 ?v0) ?v1) (f12 (f26 f27 ?v1) ?v0))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f28 f29 ?v0) (f28 f29 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f12 f30 ?v0) (f12 f30 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S4)) (let ((?v_0 (f28 f29 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S3)) (let ((?v_0 (f10 f11 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_0 (f12 f30 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f12 f14 ?v0) (f12 f14 ?v1)) (= ?v0 ?v1))))
(assert (= (= f15 f15) true))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f12 f13 ?v0) (f12 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S4)) (= (f20 (f21 f22 (f28 f29 ?v0)) (f20 (f21 f22 (f28 f29 ?v1)) ?v2)) (f20 (f21 f22 (f28 f29 (f12 (f26 f27 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (= (f12 (f26 f27 (f12 f30 ?v0)) (f12 (f26 f27 (f12 f30 ?v1)) ?v2)) (f12 (f26 f27 (f12 f30 (f12 (f26 f27 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f20 (f21 f22 (f28 f29 ?v0)) (f28 f29 ?v1)) (f28 f29 (f12 (f26 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 (f26 f27 (f12 f30 ?v0)) (f12 f30 ?v1)) (f12 f30 (f12 (f26 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f28 f29 (f12 (f26 f27 ?v0) ?v1)) (f20 (f21 f22 (f28 f29 ?v0)) (f28 f29 ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 f30 (f12 (f26 f27 ?v0) ?v1)) (f12 (f26 f27 (f12 f30 ?v0)) (f12 f30 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f7 (f8 f19 (f7 (f8 f9 ?v0) ?v1)) ?v2) (f7 (f8 f9 (f7 (f8 f19 ?v0) ?v2)) (f7 (f8 f19 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (= (f3 (f4 f5 (f20 (f21 f22 ?v0) ?v1)) ?v2) (f20 (f21 f22 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S3)) (= (f23 (f24 f25 (f12 (f26 f27 ?v0) ?v1)) ?v2) (f12 (f26 f27 (f23 (f24 f25 ?v0) ?v2)) (f23 (f24 f25 ?v1) ?v2)))))
(check-sat)
(exit)
