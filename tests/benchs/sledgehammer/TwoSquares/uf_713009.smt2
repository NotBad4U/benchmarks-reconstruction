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
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S3) S3)
(declare-fun f7 (S6 S3) S5)
(declare-fun f8 () S6)
(declare-fun f9 () S6)
(declare-fun f10 () S5)
(declare-fun f11 () S5)
(declare-fun f12 () S5)
(declare-fun f13 () S3)
(declare-fun f14 () S6)
(declare-fun f15 () S3)
(declare-fun f16 (S7 S8) S3)
(declare-fun f17 () S7)
(declare-fun f18 () S8)
(declare-fun f19 () S3)
(declare-fun f20 () S3)
(declare-fun f21 () S4)
(declare-fun f22 (S9 S3) S8)
(declare-fun f23 () S9)
(declare-fun f24 (S10 S8) S8)
(declare-fun f25 (S11 S8) S10)
(declare-fun f26 () S11)
(declare-fun f27 () S8)
(declare-fun f28 () S11)
(declare-fun f29 () S3)
(declare-fun f30 (S12 S8) S1)
(declare-fun f31 (S13 S8) S12)
(declare-fun f32 () S13)
(declare-fun f33 () S8)
(declare-fun f34 () S13)
(declare-fun f35 () S10)
(declare-fun f36 () S3)
(declare-fun f37 () S2)
(declare-fun f38 () S8)
(declare-fun f39 () S2)
(declare-fun f40 () S11)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f7 f9 (f6 f10 (f6 f11 (f6 f11 (f6 f12 f13))))))) (not (= (f3 (f4 f5 (f6 (f7 f8 (f6 ?v_0 (f6 (f7 f14 f15) (f16 f17 f18)))) (f6 ?v_0 f19))) f20) f1))))
(assert (= (f3 (f4 f5 (f6 (f7 f8 (f6 (f7 f14 f15) (f16 f17 f18))) f19)) f20) f1))
(assert (= (f3 (f4 f5 (f6 (f7 f8 (f6 (f7 f14 f15) (f16 f17 f18))) f19)) f20) f1))
(assert (not (= (f3 (f4 f21 f19) (f6 (f7 f14 f15) (f16 f17 f18))) f1)))
(assert (= (f3 (f4 f5 f20) (f6 f10 (f6 f11 (f6 f12 f13)))) f1))
(assert (forall ((?v0 S3)) (let ((?v_0 (f6 f10 ?v0))) (= (f16 f17 (f22 f23 ?v0)) (ite (= (f3 (f4 f5 f20) ?v_0) f1) ?v_0 f20)))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f14 f15) (f6 f10 ?v0)) (f6 f10 (f6 (f7 f14 (f6 f12 f13)) ?v0)))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f14 (f6 f10 ?v0)) f15) (f6 f10 (f6 (f7 f14 ?v0) (f6 f12 f13))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 f15) (f6 f10 ?v0)) f1) (= (f3 (f4 f5 (f6 f12 f13)) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 (f6 f10 ?v0)) f15) f1) (= (f3 (f4 f5 ?v0) (f6 f12 f13)) f1))))
(assert (= (f6 (f7 f14 f15) f15) (f6 f10 (f6 f11 (f6 f12 f13)))))
(assert (= (f6 (f7 f14 f15) f15) (f6 f10 (f6 f11 (f6 f12 f13)))))
(assert (= (f24 (f25 f26 f27) f27) (f22 f23 (f6 f11 (f6 f12 f13)))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f9 ?v0) (f6 f10 (f6 f11 (f6 f12 f13)))) (f6 (f7 f14 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f9 ?v0) (f6 f10 (f6 f11 (f6 f12 f13)))) (f6 (f7 f14 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f24 (f25 f28 ?v0) (f22 f23 (f6 f11 (f6 f12 f13)))) (f24 (f25 f26 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f9 (f6 f10 (f6 f11 (f6 f12 f13)))) ?v0) (f6 (f7 f14 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f9 (f6 f10 (f6 f11 (f6 f12 f13)))) ?v0) (f6 (f7 f14 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f24 (f25 f28 (f22 f23 (f6 f11 (f6 f12 f13)))) ?v0) (f24 (f25 f26 ?v0) ?v0))))
(assert (= (f3 (f4 f21 f15) f29) f1))
(assert (= (f3 (f4 f21 f20) (f6 (f7 f14 f15) (f16 f17 f18))) f1))
(assert (= (f30 (f31 f32 f33) f18) f1))
(assert (= f33 (f22 f23 f13)))
(assert (= (f22 f23 f13) f33))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f3 (f4 f21 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f4 f21 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f6 f10 ?v0)) (f6 f10 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f24 (f25 f28 (f22 f23 ?v0)) (f22 f23 ?v1)) (ite (= (f3 (f4 f21 ?v0) f13) f1) f33 (f22 f23 (f6 (f7 f9 ?v0) ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S8)) (= (f24 (f25 f28 (f22 f23 ?v0)) (f24 (f25 f28 (f22 f23 ?v1)) ?v2)) (ite (= (f3 (f4 f21 ?v0) f13) f1) f33 (f24 (f25 f28 (f22 f23 (f6 (f7 f9 ?v0) ?v1))) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f22 f23 ?v0)) (?v_0 (f22 f23 ?v1))) (= (f24 (f25 f26 ?v_1) ?v_0) (ite (= (f3 (f4 f21 ?v0) f13) f1) ?v_0 (ite (= (f3 (f4 f21 ?v1) f13) f1) ?v_1 (f22 f23 (f6 (f7 f14 ?v0) ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f6 f12 ?v0)) (f6 f12 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f6 f12 ?v0)) (f6 f12 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (= (= (f3 (f4 f21 f13) f13) f1) false))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f6 f11 ?v0)) (f6 f11 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f6 f11 ?v0)) (f6 f11 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 ?v0) ?v1) f1) (and (= (f3 (f4 f5 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f6 f10 ?v0)) (f6 f10 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f21 ?v0) ?v1) f1) (= (f3 (f4 f21 (f6 (f7 f14 ?v0) ?v2)) (f6 (f7 f14 ?v1) ?v2)) f1))))
(assert (= (f22 f23 (f6 f12 f13)) f27))
(assert (= f27 (f22 f23 (f6 f12 f13))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (= (f30 (f31 f34 (f22 f23 ?v0)) (f22 f23 ?v1)) f1) (ite (= (f3 ?v_0 ?v1) f1) true (= (f3 ?v_0 f13) f1))))))
(assert (forall ((?v0 S3)) (= (= (f22 f23 ?v0) f33) (= (f3 (f4 f5 ?v0) f13) f1))))
(assert (forall ((?v0 S3)) (= (= f33 (f22 f23 ?v0)) (= (f3 (f4 f5 ?v0) f13) f1))))
(assert (forall ((?v0 S8)) (= (f24 (f25 f28 (f22 f23 (f6 f11 (f6 f12 f13)))) ?v0) (f24 (f25 f26 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f24 (f25 f28 ?v0) (f22 f23 (f6 f11 (f6 f12 f13)))) (f24 (f25 f26 ?v0) ?v0))))
(assert (= (f24 (f25 f26 f27) f27) (f22 f23 (f6 f11 (f6 f12 f13)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f6 f10 ?v0)) f20) f1) (= (f3 (f4 f21 ?v0) f13) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 f20) (f6 f10 ?v0)) f1) (= (f3 (f4 f21 f13) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f6 (f7 f14 ?v0) ?v0)) f20) f1) (= (f3 (f4 f21 ?v0) f20) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f6 f10 ?v0)) (?v_0 (f6 f10 ?v1))) (= (= (f3 (f4 f5 ?v_1) ?v_0) f1) (not (= (f3 (f4 f21 ?v_0) ?v_1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f22 f23 ?v0)) (?v_0 (f22 f23 ?v1))) (= (= (f30 (f31 f34 ?v_1) ?v_0) f1) (not (= (f30 (f31 f32 ?v_0) ?v_1) f1))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f6 f12 ?v0)) f13) f1) (= (f3 (f4 f21 ?v0) f13) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f6 f12 ?v0)) (f6 f11 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f6 f12 ?v0)) (f6 f11 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f6 f11 ?v0)) f13) f1) (= (f3 (f4 f21 ?v0) f13) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f21 f13))) (= (= (f3 ?v_0 (f6 f11 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f6 f12 ?v0)) f20) f1) (= (f3 (f4 f21 ?v0) f20) f1))))
(assert (= (= (f3 (f4 f21 f13) f20) f1) false))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f6 f11 ?v0)) f20) f1) (= (f3 (f4 f21 ?v0) f20) f1))))
(assert (= (f3 (f4 f21 f20) f15) f1))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f9 ?v2))) (=> (= (f3 (f4 f21 ?v0) ?v1) f1) (=> (= (f3 (f4 f21 f20) ?v2) f1) (= (f3 (f4 f21 (f6 ?v_0 ?v0)) (f6 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f21 ?v0))) (= (= (f3 ?v_0 (f6 (f7 f14 ?v1) f15)) f1) (or (= (f3 ?v_0 ?v1) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f4 f21 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v2) ?v3) f1) (= (f3 (f4 f21 (f6 (f7 f14 ?v0) ?v2)) (f6 (f7 f14 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 ?v0) ?v1) f1) (= (f3 (f4 f21 (f6 (f7 f8 ?v0) ?v1)) f20) f1))))
(assert (forall ((?v0 S8)) (not (= (f3 (f4 f21 (f16 f17 ?v0)) f20) f1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S3)) (= (f6 (f7 f14 (f16 f17 ?v0)) (f6 (f7 f14 (f16 f17 ?v1)) ?v2)) (f6 (f7 f14 (f16 f17 (f24 (f25 f26 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f6 (f7 f14 (f16 f17 ?v0)) (f16 f17 ?v1)) (f16 f17 (f24 (f25 f26 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f6 (f7 f14 (f16 f17 ?v0)) (f16 f17 ?v1)) (f16 f17 (f24 (f25 f26 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f6 (f7 f9 (f16 f17 ?v0)) (f16 f17 ?v1)) (f16 f17 (f24 (f25 f28 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f6 (f7 f9 (f16 f17 ?v0)) (f16 f17 ?v1)) (f16 f17 (f24 (f25 f28 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f16 f17 (f24 (f25 f28 ?v0) ?v1)) (f6 (f7 f9 (f16 f17 ?v0)) (f16 f17 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f3 (f4 f5 (f16 f17 ?v0)) (f16 f17 ?v1)) f1) (= (f30 (f31 f34 ?v0) ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f3 (f4 f5 (f16 f17 ?v0)) (f16 f17 ?v1)) f1) (= (f30 (f31 f34 ?v0) ?v1) f1))))
(assert (= (f16 f17 f27) f15))
(assert (= f15 (f16 f17 f27)))
(assert (forall ((?v0 S8)) (= (= (f16 f17 ?v0) f20) (= ?v0 f33))))
(assert (= (f16 f17 f33) f20))
(assert (= f20 (f16 f17 f33)))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f6 f10 ?v0)) f15) f1) (= (f3 (f4 f21 ?v0) (f6 f12 f13)) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 f15) (f6 f10 ?v0)) f1) (= (f3 (f4 f21 (f6 f12 f13)) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 f20) (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v0)) (f6 (f7 f9 ?v1) ?v1))) f1) (or (not (= ?v0 f20)) (not (= ?v1 f20))))))
(assert (forall ((?v0 S3) (?v1 S3)) (not (= (f3 (f4 f21 (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v0)) (f6 (f7 f9 ?v1) ?v1))) f20) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 (f6 f12 ?v0)) f13) f1) (= (f3 (f4 f21 ?v0) f13) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 f13) (f6 f12 ?v0)) f1) (= (f3 (f4 f5 f13) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f6 f12 ?v0)) (f6 f11 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f6 f12 ?v0)) (f6 f11 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f6 f11 ?v0)) (f6 f12 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f6 f11 ?v0)) (f6 f12 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 f15) ?v0) f1) (= (f3 (f4 f21 f20) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f21 f20) ?v0) f1) (= (= (f6 (f7 f9 ?v0) ?v1) f15) (and (= ?v0 f15) (= ?v1 f15))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f6 (f7 f14 (f6 (f7 f14 f15) ?v0)) ?v0)) f20) f1) (= (f3 (f4 f21 ?v0) f20) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f21 ?v0) ?v1) f1) (= (f3 (f4 f5 (f6 (f7 f14 ?v0) f15)) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f6 (f7 f14 ?v0) f15)) ?v1) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 ?v0) (f6 (f7 f14 ?v1) f15)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) (f6 (f7 f8 ?v1) f15)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S8)) (= (= (f3 (f4 f5 (f16 f17 ?v0)) f20) f1) (= ?v0 f33))))
(assert (let ((?v_0 (f6 f12 (f6 f12 f13)))) (= (f6 f10 ?v_0) (f16 f17 (f22 f23 ?v_0)))))
(assert (forall ((?v0 S3)) (=> (= (f3 (f4 f5 f20) ?v0) f1) (= (f3 (f4 f21 f20) (f6 (f7 f14 f15) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 f10 ?v0) (f6 f10 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f6 f10 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S8)) (let ((?v_0 (f22 f23 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 f12 ?v0) (f6 f12 ?v1)) (= ?v0 ?v1))))
(assert (= (= f13 f13) true))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 f11 ?v0) (f6 f11 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f3 (f4 f5 ?v0) ?v1) f1) (= (f3 (f4 f5 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f9 ?v0))) (= (f6 (f7 f9 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f7 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f9 ?v0) ?v1) (f6 (f7 f9 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (= (f6 f10 ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f14 ?v0))) (= (f6 (f7 f14 (f6 ?v_0 ?v1)) ?v2) (f6 ?v_0 (f6 (f7 f14 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f7 f14 ?v0)) (?v_0 (f7 f14 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f14 ?v0) ?v1) (f6 (f7 f14 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S8) (?v2 S8)) (let ((?v_0 (= ?v0 f1))) (= (ite ?v_0 (f16 f17 ?v1) (f16 f17 ?v2)) (f16 f17 (ite ?v_0 ?v1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f16 f17 ?v0) (f16 f17 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f16 f17 ?v0) (f16 f17 ?v1)) (= ?v0 ?v1))))
(assert (let ((?v_0 (f6 f11 (f6 f12 f13)))) (= (f6 f10 ?v_0) (f16 f17 (f22 f23 ?v_0)))))
(assert (forall ((?v0 S3)) (= (= (f6 (f7 f14 ?v0) ?v0) f20) (= ?v0 f20))))
(assert (forall ((?v0 S3)) (= (= (f6 f12 ?v0) f13) false)))
(assert (forall ((?v0 S3)) (= (= f13 (f6 f12 ?v0)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 f12 ?v0) (f6 f11 ?v1)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 f11 ?v0) (f6 f12 ?v1)) false)))
(assert (forall ((?v0 S3)) (= (= (f6 f11 ?v0) f13) (= ?v0 f13))))
(assert (forall ((?v0 S3)) (= (= f13 (f6 f11 ?v0)) (= f13 ?v0))))
(assert (= (f6 f11 f13) f13))
(assert (= f13 f20))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f6 f12 ?v0)) (f6 f12 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f6 f12 ?v0)) (f6 f12 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (= (= (f3 (f4 f5 f13) f13) f1) true))
(assert (not (= f20 f15)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f6 f11 ?v0)) (f6 f11 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f6 f11 ?v0)) (f6 f11 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f9 f13) ?v0) f13)))
(assert (= (f3 (f4 f5 f20) f20) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f9 (f6 f11 ?v0)) ?v1) (f6 f11 (f6 (f7 f9 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f14 ?v0) f13) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f14 f13) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f14 (f6 f11 ?v0)) (f6 f11 ?v1)) (f6 f11 (f6 (f7 f14 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f6 f11 ?v0) (f6 (f7 f14 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f14 ?v0) f20) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f14 f20) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f9 ?v0) f15) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f9 f15) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f6 f10 ?v0)) (f6 f10 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f9 (f6 f10 ?v0)) (f6 f10 ?v1)) (f6 f10 (f6 (f7 f9 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f14 ?v2))) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (= (f3 (f4 f5 (f6 ?v_0 ?v0)) (f6 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 ?v0) f13) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f8 (f6 f11 ?v0)) (f6 f11 ?v1)) (f6 f11 (f6 (f7 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f6 (f7 f9 (f6 (f7 f14 ?v0) ?v1)) ?v2) (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v2)) (f6 (f7 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f9 ?v0))) (= (f6 ?v_0 (f6 (f7 f14 ?v1) ?v2)) (f6 (f7 f14 (f6 ?v_0 ?v1)) (f6 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f14 (f6 f10 ?v0)) (f6 f10 ?v1)) (f6 f10 (f6 (f7 f14 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f6 (f7 f9 (f6 (f7 f8 ?v0) ?v1)) ?v2) (f6 (f7 f8 (f6 (f7 f9 ?v0) ?v2)) (f6 (f7 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f9 ?v0))) (= (f6 ?v_0 (f6 (f7 f8 ?v1) ?v2)) (f6 (f7 f8 (f6 ?v_0 ?v1)) (f6 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v0)) (f6 (f7 f9 ?v1) ?v1)) f20) (and (= ?v0 f20) (= ?v1 f20)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f10 ?v2))) (= (f6 (f7 f9 (f6 (f7 f14 ?v0) ?v1)) ?v_0) (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v_0)) (f6 (f7 f9 ?v1) ?v_0))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S3)) (let ((?v_0 (f22 f23 ?v2))) (= (f24 (f25 f28 (f24 (f25 f26 ?v0) ?v1)) ?v_0) (f24 (f25 f26 (f24 (f25 f28 ?v0) ?v_0)) (f24 (f25 f28 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f9 (f6 f10 ?v0)))) (= (f6 ?v_0 (f6 (f7 f14 ?v1) ?v2)) (f6 (f7 f14 (f6 ?v_0 ?v1)) (f6 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8)) (let ((?v_0 (f25 f28 (f22 f23 ?v0)))) (= (f24 ?v_0 (f24 (f25 f26 ?v1) ?v2)) (f24 (f25 f26 (f24 ?v_0 ?v1)) (f24 ?v_0 ?v2))))))
(assert (= (f6 f10 f13) f20))
(assert (= (f22 f23 f13) f33))
(assert (= (f6 f10 f13) f20))
(assert (= f20 (f6 f10 f13)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f10 ?v2))) (= (f6 (f7 f9 (f6 (f7 f8 ?v0) ?v1)) ?v_0) (f6 (f7 f8 (f6 (f7 f9 ?v0) ?v_0)) (f6 (f7 f9 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f9 (f6 f10 ?v0)))) (= (f6 ?v_0 (f6 (f7 f8 ?v1) ?v2)) (f6 (f7 f8 (f6 ?v_0 ?v1)) (f6 ?v_0 ?v2))))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f14 (f6 f10 f13)) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f14 ?v0) (f6 f10 f13)) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f6 f10 ?v0)) (f6 f10 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f6 (f7 f9 (f6 f10 ?v0)) (f6 (f7 f9 (f6 f10 ?v1)) ?v2)) (f6 (f7 f9 (f6 f10 (f6 (f7 f9 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f9 (f6 f10 ?v0)) (f6 f10 ?v1)) (f6 f10 (f6 (f7 f9 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 f10 (f6 (f7 f9 ?v0) ?v1)) (f6 (f7 f9 (f6 f10 ?v0)) (f6 f10 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f6 (f7 f14 (f6 f10 ?v0)) (f6 (f7 f14 (f6 f10 ?v1)) ?v2)) (f6 (f7 f14 (f6 f10 (f6 (f7 f14 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f14 (f6 f10 ?v0)) (f6 f10 ?v1)) (f6 f10 (f6 (f7 f14 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 f10 (f6 (f7 f14 ?v0) ?v1)) (f6 (f7 f14 (f6 f10 ?v0)) (f6 f10 ?v1)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f5 f13))) (= (= (f3 ?v_0 (f6 f12 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f6 f11 ?v0)) (f6 f12 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f6 f11 ?v0)) (f6 f12 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 (f6 f11 ?v0)) f13) f1) (= (f3 (f4 f5 ?v0) f13) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f5 f13))) (= (= (f3 ?v_0 (f6 f11 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 f10 (f6 (f7 f8 ?v0) ?v1)) (f6 (f7 f8 (f6 f10 ?v0)) (f6 f10 ?v1)))))
(assert (= f20 (f6 f10 f13)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f14 (f6 f12 ?v0)) (f6 f11 ?v1)) (f6 f12 (f6 (f7 f14 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f14 (f6 f11 ?v0)) (f6 f12 ?v1)) (f6 f12 (f6 (f7 f14 ?v0) ?v1)))))
(assert (= (f3 (f4 f5 f20) f15) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f20))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f6 (f7 f9 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S3)) (= (f6 f12 ?v0) (f6 (f7 f14 (f6 (f7 f14 f15) ?v0)) ?v0))))
(assert (forall ((?v0 S3)) (not (= (f6 (f7 f14 (f6 (f7 f14 f15) ?v0)) ?v0) f20))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f8 (f6 f12 ?v0)) (f6 f12 ?v1)) (f6 f11 (f6 (f7 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f8 (f6 f12 ?v0)) (f6 f11 ?v1)) (f6 f12 (f6 (f7 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f7 f8 f13))) (= (f6 ?v_0 (f6 f11 ?v0)) (f6 f11 (f6 ?v_0 ?v0))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f20))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f6 (f7 f14 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f16 f17 ?v0))) (= (f6 f10 ?v_0) ?v_0))))
(assert (forall ((?v0 S8)) (= (f22 f23 (f16 f17 ?v0)) (f24 f35 ?v0))))
(assert (forall ((?v0 S2)) (= (forall ((?v1 S3)) (=> (= (f3 (f4 f5 f20) ?v1) f1) (= (f3 ?v0 ?v1) f1))) (forall ((?v1 S8)) (= (f3 ?v0 (f16 f17 ?v1)) f1)))))
(assert (forall ((?v0 S2)) (= (exists ((?v1 S3)) (and (= (f3 (f4 f5 f20) ?v1) f1) (= (f3 ?v0 ?v1) f1))) (exists ((?v1 S8)) (= (f3 ?v0 (f16 f17 ?v1)) f1)))))
(assert (forall ((?v0 S8)) (= (f3 (f4 f5 f20) (f16 f17 ?v0)) f1)))
(assert (forall ((?v0 S8)) (= (f3 (f4 f5 f20) (f16 f17 ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (exists ((?v2 S8)) (= ?v1 (f6 (f7 f14 ?v0) (f16 f17 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v0)) (f6 (f7 f9 ?v1) ?v1))) f20) f1) (and (= ?v0 f20) (= ?v1 f20)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f5 f20) (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v0)) (f6 (f7 f9 ?v1) ?v1))) f1)))
(assert (forall ((?v0 S3)) (let ((?v_0 (f6 f10 ?v0))) (= (f6 f10 (f6 f11 ?v0)) (f6 (f7 f14 (f6 (f7 f14 f20) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f6 f10 ?v0))) (= (f6 f10 (f6 f12 ?v0)) (f6 (f7 f14 (f6 (f7 f14 f15) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f9 (f6 f10 (f6 f12 f13))) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f9 ?v0) (f6 f10 (f6 f12 f13))) ?v0)))
(assert (= (f6 f10 (f6 f12 f13)) f15))
(assert (= (f22 f23 (f6 f12 f13)) f27))
(assert (= (f6 f10 (f6 f12 f13)) f15))
(assert (= f15 (f6 f10 (f6 f12 f13))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f6 (f7 f14 (f6 f10 ?v0)) (f6 (f7 f8 (f6 f10 ?v1)) ?v2)) (f6 (f7 f8 (f6 f10 (f6 (f7 f14 ?v0) ?v1))) ?v2))))
(assert (= f15 (f6 f10 (f6 f12 f13))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f6 (f7 f9 (f6 f12 ?v0)) ?v1) (f6 (f7 f14 (f6 f11 (f6 (f7 f9 ?v0) ?v1))) ?v1))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f9 (f6 (f7 f14 f15) f15)) (f6 f10 ?v0)) (f6 f10 (f6 f11 ?v0)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 (f6 f10 ?v0)) f20) f1) (= (f3 (f4 f5 ?v0) f13) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 f20) (f6 f10 ?v0)) f1) (= (f3 (f4 f5 f13) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f13))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f6 (f7 f9 (f6 f10 ?v0)) (f6 f10 ?v1)) (f6 f10 (f6 (f7 f9 ?v0) ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f13))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f24 (f25 f28 (f22 f23 ?v0)) (f22 f23 ?v1)) (f22 f23 (f6 (f7 f9 ?v0) ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f13))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f6 (f7 f14 (f6 f10 ?v0)) (f6 f10 ?v1)) (f6 f10 (f6 (f7 f14 ?v0) ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f13))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f24 (f25 f26 (f22 f23 ?v0)) (f22 f23 ?v1)) (f22 f23 (f6 (f7 f14 ?v0) ?v1))))))))
(assert (= (f3 (f4 f5 f20) (f6 f10 (f6 f12 (f6 f12 f13)))) f1))
(assert (forall ((?v0 S3)) (=> (= (f3 (f4 f5 f20) ?v0) f1) (=> (= (f3 (f4 f21 ?v0) (f6 f10 (f6 f11 (f6 f12 f13)))) f1) (or (= ?v0 f20) (= ?v0 f15))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f21 f20) ?v0) f1) (=> (= ?v0 (f6 (f7 f14 ?v1) (f6 (f7 f9 ?v0) ?v2))) (=> (= (f3 (f4 f21 ?v1) ?v0) f1) (= (f3 (f4 f5 f15) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f21 f20) ?v0) f1) (=> (= ?v0 (f6 (f7 f14 ?v1) (f6 (f7 f9 ?v0) ?v2))) (=> (= (f3 (f4 f5 f20) ?v1) f1) (= (f3 (f4 f5 ?v2) f15) f1))))))
(assert (let ((?v_1 (f6 (f7 f14 f15) (f16 f17 f18))) (?v_0 (f6 (f7 f14 (f6 (f7 f9 (f6 f10 (f6 f11 (f6 f11 (f6 f12 f13))))) f36)) f15))) (not (=> (= (f3 (f4 f21 ?v_1) ?v_0) f1) (not (= (f3 f37 (f6 (f7 f9 ?v_0) ?v_1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f4 f5 f20))) (=> (= (f3 (f4 f21 ?v0) ?v1) f1) (=> (= (f3 (f4 f21 ?v2) ?v1) f1) (=> (= (f3 ?v_0 ?v3) f1) (=> (= (f3 ?v_0 ?v4) f1) (=> (= (f6 (f7 f14 ?v3) ?v4) f15) (= (f3 (f4 f21 (f6 (f7 f14 (f6 (f7 f9 ?v3) ?v0)) (f6 (f7 f9 ?v4) ?v2))) ?v1) f1)))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3) (?v5 S3)) (let ((?v_0 (f6 (f7 f14 (f6 (f7 f9 ?v3) ?v4)) ?v5))) (=> (= (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v1)) ?v2) ?v_0) (=> (= (f3 (f4 f21 ?v_0) f20) f1) (=> (= (f3 (f4 f21 ?v2) ?v0) f1) (=> (= (f3 (f4 f5 f20) ?v5) f1) (=> (= (f3 (f4 f21 f20) ?v3) f1) (=> (= (f3 (f4 f5 ?v3) ?v0) f1) (= (f3 (f4 f5 ?v4) ?v1) f1))))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f7 f9 ?v0)) (?v_1 (f4 f21 ?v0))) (=> (= (f3 (f4 f5 (f6 (f7 f14 (f6 ?v_0 ?v1)) ?v2)) (f6 (f7 f14 (f6 ?v_0 ?v3)) ?v4)) f1) (=> (= (f3 (f4 f5 ?v4) f20) f1) (=> (= (f3 ?v_1 ?v4) f1) (=> (= (f3 ?v_1 ?v2) f1) (= (f3 (f4 f5 ?v3) ?v1) f1))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3) (?v5 S3)) (let ((?v_1 (f4 f5 f20)) (?v_0 (f6 (f7 f14 (f6 (f7 f9 ?v3) ?v4)) ?v5))) (=> (= (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v1)) ?v2) ?v_0) (=> (= (f3 ?v_1 ?v_0) f1) (=> (= (f3 (f4 f21 ?v5) ?v3) f1) (=> (= (f3 ?v_1 ?v2) f1) (=> (= (f3 (f4 f21 f20) ?v3) f1) (=> (= (f3 (f4 f5 ?v3) ?v0) f1) (= (f3 (f4 f5 ?v1) ?v4) f1))))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f7 f9 ?v0))) (=> (= (f3 (f4 f5 (f6 (f7 f14 (f6 ?v_0 ?v1)) ?v2)) (f6 (f7 f14 (f6 ?v_0 ?v3)) ?v4)) f1) (=> (= (f3 (f4 f5 f20) ?v2) f1) (=> (= (f3 (f4 f21 ?v2) ?v0) f1) (=> (= (f3 (f4 f21 ?v4) ?v0) f1) (= (f3 (f4 f5 ?v1) ?v3) f1))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f21 (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v1)) ?v2)) f20) f1) (=> (= (f3 (f4 f5 f20) ?v2) f1) (=> (= (f3 (f4 f21 f20) ?v0) f1) (= (f3 (f4 f5 ?v1) f20) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 f20))) (=> (= (f3 ?v_0 (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v1)) ?v2)) f1) (=> (= (f3 (f4 f21 ?v2) ?v0) f1) (=> (= (f3 (f4 f21 f20) ?v0) f1) (= (f3 ?v_0 ?v1) f1)))))))
(assert (= (f30 (f31 f32 f33) f38) f1))
(assert (= (f3 (f4 f5 f15) f29) f1))
(assert (not (= (f3 f37 (f6 (f7 f9 (f6 (f7 f14 (f6 (f7 f9 (f6 f10 (f6 f11 (f6 f11 (f6 f12 f13))))) f36)) f15)) (f6 (f7 f14 f15) (f16 f17 f33)))) f1)))
(assert (= (f3 (f4 f21 f20) (f6 (f7 f14 (f6 (f7 f9 (f6 f10 (f6 f11 (f6 f11 (f6 f12 f13))))) f36)) f15)) f1))
(assert (= (f3 (f4 f21 f29) (f6 (f7 f14 (f6 (f7 f9 (f6 f10 (f6 f11 (f6 f11 (f6 f12 f13))))) f36)) f15)) f1))
(assert (= (f3 f37 (f6 (f7 f9 (f6 (f7 f14 (f6 (f7 f9 (f6 f10 (f6 f11 (f6 f11 (f6 f12 f13))))) f36)) f15)) f29)) f1))
(assert (let ((?v_1 (f6 (f7 f14 f15) (f16 f17 f18))) (?v_0 (f6 (f7 f14 (f6 (f7 f9 (f6 f10 (f6 f11 (f6 f11 (f6 f12 f13))))) f36)) f15))) (and (= (f3 (f4 f21 ?v_1) ?v_0) f1) (= (f3 f37 (f6 (f7 f9 ?v_0) ?v_1)) f1))))
(assert (= (f3 f39 (f6 (f7 f14 (f6 (f7 f9 (f6 f10 (f6 f11 (f6 f11 (f6 f12 f13))))) f36)) f15)) f1))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f24 (f25 f28 ?v0) ?v1) (ite (= ?v0 f33) f33 (f24 (f25 f26 ?v1) (f24 (f25 f28 (f24 (f25 f40 ?v0) f27)) ?v1))))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f30 (f31 f34 ?v0) ?v1) f1) (= (f6 (f7 f8 (f16 f17 ?v1)) (f16 f17 ?v0)) (f16 f17 (f24 (f25 f40 ?v1) ?v0))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f3 (f4 f21 (f16 f17 ?v0)) (f16 f17 ?v1)) f1) (= (f30 (f31 f32 ?v0) ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f3 (f4 f21 (f16 f17 ?v0)) (f16 f17 ?v1)) f1) (= (f30 (f31 f32 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 f37 ?v0) f1) (=> (= (f3 f37 ?v1) f1) (= (f3 f37 (f6 (f7 f9 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f30 (f31 f32 (f22 f23 ?v0)) (f22 f23 ?v1)) f1) (ite (= (f3 (f4 f21 ?v0) ?v1) f1) (= (f3 (f4 f21 f13) ?v1) f1) false))))
(assert (forall ((?v0 S3)) (= (= (f30 (f31 f32 f33) (f22 f23 ?v0)) f1) (= (f3 (f4 f21 f13) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 (f4 f21 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f21 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S8)) (= (= (f3 (f4 f21 f20) (f16 f17 ?v0)) f1) (= (f30 (f31 f32 f33) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S8)) (let ((?v_0 (f7 f9 (f16 f17 ?v2)))) (=> (= (f3 (f4 f21 ?v0) ?v1) f1) (=> (= (f30 (f31 f32 f33) ?v2) f1) (= (f3 (f4 f21 (f6 ?v_0 ?v0)) (f6 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f9 f20) ?v0) f20)))
(assert (forall ((?v0 S8)) (= (f24 (f25 f28 f33) ?v0) f33)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f9 ?v0) f20) f20)))
(assert (forall ((?v0 S8)) (= (f24 (f25 f28 ?v0) f33) f33)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f6 (f7 f9 ?v0) ?v1) f20) (or (= ?v0 f20) (= ?v1 f20)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 f20)) (=> (not (= ?v1 f20)) (not (= (f6 (f7 f9 ?v0) ?v1) f20))))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (not (= ?v0 f33)) (=> (not (= ?v1 f33)) (not (= (f24 (f25 f28 ?v0) ?v1) f33))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f6 (f7 f9 ?v0) ?v1) f20) (or (= ?v0 f20) (= ?v1 f20)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f24 (f25 f28 ?v0) ?v1) f33) (or (= ?v0 f33) (= ?v1 f33)))))
(assert (not (= f15 f20)))
(assert (not (= f27 f33)))
(assert (not (= f20 f15)))
(assert (not (= f33 f27)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f6 (f7 f9 (f6 (f7 f14 ?v0) ?v1)) ?v2) (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v2)) (f6 (f7 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8)) (= (f24 (f25 f28 (f24 (f25 f26 ?v0) ?v1)) ?v2) (f24 (f25 f26 (f24 (f25 f28 ?v0) ?v2)) (f24 (f25 f28 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (f6 (f7 f14 (f6 (f7 f9 ?v0) ?v1)) (f6 (f7 f14 (f6 (f7 f9 ?v2) ?v1)) ?v3)) (f6 (f7 f14 (f6 (f7 f9 (f6 (f7 f14 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (= (f24 (f25 f26 (f24 (f25 f28 ?v0) ?v1)) (f24 (f25 f26 (f24 (f25 f28 ?v2) ?v1)) ?v3)) (f24 (f25 f26 (f24 (f25 f28 (f24 (f25 f26 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f20) (f6 (f7 f9 ?v0) ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f20))) (= (= (f3 ?v_0 (f6 (f7 f9 ?v0) ?v1)) f1) (or (and (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1)) (and (= (f3 (f4 f5 ?v0) f20) f1) (= (f3 (f4 f5 ?v1) f20) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f20))) (= (= (f3 (f4 f5 (f6 (f7 f9 ?v0) ?v1)) f20) f1) (or (and (= (f3 ?v_0 ?v0) f1) (= (f3 (f4 f5 ?v1) f20) f1)) (and (= (f3 (f4 f5 ?v0) f20) f1) (= (f3 ?v_0 ?v1) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f20))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f6 (f7 f9 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_0 (f31 f34 f33))) (=> (= (f30 ?v_0 ?v0) f1) (=> (= (f30 ?v_0 ?v1) f1) (= (f30 ?v_0 (f24 (f25 f28 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 f20) ?v0) f1) (=> (= (f3 (f4 f5 ?v1) f20) f1) (= (f3 (f4 f5 (f6 (f7 f9 ?v0) ?v1)) f20) f1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f30 (f31 f34 f33) ?v0) f1) (=> (= (f30 (f31 f34 ?v1) f33) f1) (= (f30 (f31 f34 (f24 (f25 f28 ?v0) ?v1)) f33) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 f20) ?v0) f1) (=> (= (f3 (f4 f5 ?v1) f20) f1) (= (f3 (f4 f5 (f6 (f7 f9 ?v1) ?v0)) f20) f1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f30 (f31 f34 f33) ?v0) f1) (=> (= (f30 (f31 f34 ?v1) f33) f1) (= (f30 (f31 f34 (f24 (f25 f28 ?v1) ?v0)) f33) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) f20) f1) (=> (= (f3 (f4 f5 f20) ?v1) f1) (= (f3 (f4 f5 (f6 (f7 f9 ?v0) ?v1)) f20) f1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f30 (f31 f34 ?v0) f33) f1) (=> (= (f30 (f31 f34 f33) ?v1) f1) (= (f30 (f31 f34 (f24 (f25 f28 ?v0) ?v1)) f33) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) f20) f1) (=> (= (f3 (f4 f5 ?v1) f20) f1) (= (f3 (f4 f5 f20) (f6 (f7 f9 ?v0) ?v1)) f1)))))
(check-sat)
(exit)