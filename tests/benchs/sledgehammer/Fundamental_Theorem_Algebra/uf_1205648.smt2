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
(declare-sort S15 0)
(declare-sort S16 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S6) S3)
(declare-fun f7 () S5)
(declare-fun f8 (S7 S6) S6)
(declare-fun f9 (S8 S6) S7)
(declare-fun f10 () S8)
(declare-fun f11 (S9 S3) S6)
(declare-fun f12 () S9)
(declare-fun f13 () S3)
(declare-fun f14 () S6)
(declare-fun f15 (S10 S3) S3)
(declare-fun f16 (S11 S3) S10)
(declare-fun f17 () S11)
(declare-fun f18 () S3)
(declare-fun f19 () S4)
(declare-fun f20 () S3)
(declare-fun f21 () S3)
(declare-fun f22 () S10)
(declare-fun f23 (S13 S12) S1)
(declare-fun f24 (S14 S12) S13)
(declare-fun f25 () S14)
(declare-fun f26 () S10)
(declare-fun f27 () S6)
(declare-fun f28 () S6)
(declare-fun f29 () S14)
(declare-fun f30 () S6)
(declare-fun f31 () S12)
(declare-fun f32 () S12)
(declare-fun f33 (S15 S12) S12)
(declare-fun f34 (S16 S12) S15)
(declare-fun f35 () S16)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 f5 (f6 f7 (f8 (f9 f10 (f11 f12 f13)) f14))) (f6 f7 f14)) f1)))
(assert (let ((?v_0 (f6 f7 f14))) (= (f3 (f4 f5 (f15 (f16 f17 f13) ?v_0)) (f15 (f16 f17 f18) ?v_0)) f1)))
(assert (= (f3 (f4 f19 f20) f13) f1))
(assert (= (f3 (f4 f19 f20) f13) f1))
(assert (= (f3 (f4 f19 f13) f18) f1))
(assert (let ((?v_0 (f6 f7 f14))) (= (f3 (f4 f5 (f15 (f16 f17 f13) ?v_0)) (f15 (f16 f17 f18) ?v_0)) f1)))
(assert (= (f3 (f4 f19 f20) f21) f1))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f3 (f4 f5 (f6 f7 (f8 (f9 f10 ?v0) ?v1))) (f15 (f16 f17 (f6 f7 ?v0)) (f6 f7 ?v1))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f5 (f15 f22 (f15 (f16 f17 ?v0) ?v1))) (f15 (f16 f17 (f15 f22 ?v0)) (f15 f22 ?v1))) f1)))
(assert (forall ((?v0 S12)) (= (f23 (f24 f25 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f15 f26 (f15 (f16 f17 ?v0) ?v1)) (f15 (f16 f17 (f15 f26 ?v0)) (f15 f26 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f11 f12 (f15 (f16 f17 ?v0) ?v1)) (f8 (f9 f10 (f11 f12 ?v0)) (f11 f12 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f6 f7 (f8 (f9 f10 ?v0) ?v1)) (f15 (f16 f17 (f6 f7 ?v0)) (f6 f7 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f15 f22 (f15 (f16 f17 ?v0) ?v1)) (f15 (f16 f17 (f15 f22 ?v0)) (f15 f22 ?v1)))))
(assert (not (= f14 f27)))
(assert (exists ((?v0 S3)) (forall ((?v1 S6) (?v2 S6)) (= (f3 (f4 f5 (f6 f7 (f8 (f9 f10 ?v1) ?v2))) (f15 (f16 f17 (f15 (f16 f17 (f6 f7 ?v1)) (f6 f7 ?v2))) ?v0)) f1))))
(assert (exists ((?v0 S3)) (forall ((?v1 S3) (?v2 S3)) (= (f3 (f4 f5 (f15 f22 (f15 (f16 f17 ?v1) ?v2))) (f15 (f16 f17 (f15 (f16 f17 (f15 f22 ?v1)) (f15 f22 ?v2))) ?v0)) f1))))
(assert (forall ((?v0 S6)) (exists ((?v1 S3)) (forall ((?v2 S6)) (= (f3 (f4 f5 (f6 f7 (f8 (f9 f10 ?v0) ?v2))) (f15 (f16 f17 (f6 f7 ?v2)) ?v1)) f1)))))
(assert (forall ((?v0 S3)) (exists ((?v1 S3)) (forall ((?v2 S3)) (= (f3 (f4 f5 (f15 f22 (f15 (f16 f17 ?v0) ?v2))) (f15 (f16 f17 (f15 f22 ?v2)) ?v1)) f1)))))
(assert (forall ((?v0 S6)) (exists ((?v1 S3)) (forall ((?v2 S6)) (= (f3 (f4 f5 (f6 f7 (f8 (f9 f10 ?v2) ?v0))) (f15 (f16 f17 (f6 f7 ?v2)) ?v1)) f1)))))
(assert (forall ((?v0 S3)) (exists ((?v1 S3)) (forall ((?v2 S3)) (= (f3 (f4 f5 (f15 f22 (f15 (f16 f17 ?v2) ?v0))) (f15 (f16 f17 (f15 f22 ?v2)) ?v1)) f1)))))
(assert (forall ((?v0 S6)) (= (f3 (f4 f5 f20) (f6 f7 ?v0)) f1)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f20) (f15 f22 ?v0)) f1)))
(assert (exists ((?v0 S3)) (forall ((?v1 S3)) (= (f3 (f4 f5 (f15 f22 (f15 f26 ?v1))) (f15 (f16 f17 (f15 f22 ?v1)) ?v0)) f1))))
(assert (exists ((?v0 S3)) (forall ((?v1 S3)) (= (f3 (f4 f5 (f6 f7 (f11 f12 ?v1))) (f15 (f16 f17 (f15 f22 ?v1)) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f15 f26 ?v0) (f15 f26 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f11 f12 ?v0) (f11 f12 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S3) (?v2 S6) (?v3 S3)) (=> (= (f3 (f4 f19 (f6 f7 ?v0)) ?v1) f1) (=> (= (f3 (f4 f19 (f6 f7 ?v2)) ?v3) f1) (= (f3 (f4 f19 (f6 f7 (f8 (f9 f10 ?v0) ?v2))) (f15 (f16 f17 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f4 f19 (f15 f22 ?v0)) ?v1) f1) (=> (= (f3 (f4 f19 (f15 f22 ?v2)) ?v3) f1) (= (f3 (f4 f19 (f15 f22 (f15 (f16 f17 ?v0) ?v2))) (f15 (f16 f17 ?v1) ?v3)) f1)))))
(assert (not (= f28 f27)))
(assert (forall ((?v0 S3)) (=> (= (f3 (f4 f19 f20) ?v0) f1) (exists ((?v1 S3)) (let ((?v_0 (f4 f19 ?v1))) (and (= (f3 (f4 f19 f20) ?v1) f1) (and (= (f3 ?v_0 f18) f1) (= (f3 ?v_0 ?v0) f1))))))))
(assert (forall ((?v0 S12)) (not (= (f23 (f24 f29 ?v0) ?v0) f1))))
(assert (forall ((?v0 S3)) (not (= (f3 (f4 f19 ?v0) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (not (= ?v0 ?v1)) (or (= (f23 (f24 f29 ?v0) ?v1) f1) (= (f23 (f24 f29 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (not (= ?v0 ?v1)) (or (= (f3 (f4 f19 ?v0) ?v1) f1) (= (f3 (f4 f19 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (not (= (f23 (f24 f29 ?v0) ?v1) f1)) (or (= (f23 (f24 f29 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (not (= (f3 (f4 f19 ?v0) ?v1) f1)) (or (= (f3 (f4 f19 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (or (= (f23 (f24 f29 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f23 (f24 f29 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f3 (f4 f19 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f4 f19 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= (f23 (f24 f29 ?v0) ?v1) f1)) (= (not (= (f23 (f24 f29 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= (f3 (f4 f19 ?v0) ?v1) f1)) (= (not (= (f3 (f4 f19 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f23 (f24 f29 ?v0) ?v1) f1) false) (=> (=> (= (f23 (f24 f29 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 (f4 f19 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f19 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (not (= (f23 (f24 f29 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (not (= (f3 (f4 f19 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (= (not (= (f23 (f24 f29 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (= (not (= (f3 (f4 f19 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S1)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (= (=> (= (f23 (f24 f29 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S1)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (= (=> (= (f3 (f4 f19 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (=> (= (f23 (f24 f29 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (=> (= (f3 (f4 f19 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (=> (= (f23 (f24 f29 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (=> (= (f3 (f4 f19 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= ?v0 ?v1) (=> (= (f23 (f24 f29 ?v1) ?v2) f1) (= (f23 (f24 f29 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= ?v0 ?v1) (=> (= (f3 (f4 f19 ?v1) ?v2) f1) (= (f3 (f4 f19 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f24 f29 ?v2))) (=> (= ?v0 ?v1) (=> (= (f23 ?v_0 ?v1) f1) (= (f23 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f19 ?v2))) (=> (= ?v0 ?v1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f24 f29 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f19 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f23 (f24 f29 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f3 (f4 f19 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f24 f29 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (=> (= (f23 (f24 f29 ?v1) ?v2) f1) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f19 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f19 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f24 f29 ?v2))) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (=> (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f19 ?v2))) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (=> (=> (not false) (= (f23 (f24 f29 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (=> (=> (not false) (= (f3 (f4 f19 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (=> (= (f23 (f24 f29 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f23 (f24 f29 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (=> (= (f3 (f4 f19 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f3 (f4 f19 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f19 f20) (f15 f22 ?v0)) f1) (not (= ?v0 f20)))))
(assert (forall ((?v0 S6)) (= (= (f3 (f4 f19 f20) (f6 f7 ?v0)) f1) (not (= ?v0 f27)))))
(assert (= (f6 f7 f30) f18))
(assert (= (f15 f22 f18) f18))
(assert (forall ((?v0 S6)) (not (= (f3 (f4 f19 (f6 f7 ?v0)) f20) f1))))
(assert (forall ((?v0 S3)) (not (= (f3 (f4 f19 (f15 f22 ?v0)) f20) f1))))
(assert (forall ((?v0 S3)) (= (= (f15 f22 ?v0) f20) (= ?v0 f20))))
(assert (forall ((?v0 S6)) (= (= (f6 f7 ?v0) f20) (= ?v0 f27))))
(assert (= (f15 f22 f20) f20))
(assert (= (f6 f7 f27) f20))
(assert (= (f15 f26 f18) f18))
(assert (= (f11 f12 f18) f30))
(assert (forall ((?v0 S3)) (= (= (f15 f26 ?v0) f20) (= ?v0 f20))))
(assert (forall ((?v0 S3)) (= (= (f11 f12 ?v0) f27) (= ?v0 f20))))
(assert (= (f15 f26 f20) f20))
(assert (= (f11 f12 f20) f27))
(assert (= (f15 f26 f20) f20))
(assert (= (f11 f12 f20) f27))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f24 f29 ?v2))) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f19 ?v2))) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 (f24 f29 ?v1) ?v2) f1) (= (f23 (f24 f29 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 (f4 f19 ?v1) ?v2) f1) (= (f3 (f4 f19 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (=> (= (f23 (f24 f25 ?v2) ?v0) f1) (= (f23 (f24 f29 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v2) ?v0) f1) (= (f3 (f4 f19 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f24 f29 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (=> (= (f23 (f24 f25 ?v1) ?v2) f1) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f19 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (not (= ?v1 ?v0)) (= (f23 (f24 f29 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (not (= ?v1 ?v0)) (= (f3 (f4 f19 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f23 (f24 f29 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f3 (f4 f19 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (or (= (f23 (f24 f29 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (or (= (f3 (f4 f19 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (= (not (= (f23 (f24 f29 ?v0) ?v1) f1)) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (= (not (= (f3 (f4 f19 ?v0) ?v1) f1)) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (= (f23 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (not (= (f23 (f24 f29 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (not (= (f3 (f4 f19 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= ?v0 ?v1)) (=> (= (f23 (f24 f25 ?v1) ?v0) f1) (= (f23 (f24 f29 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 ?v1)) (=> (= (f3 (f4 f5 ?v1) ?v0) f1) (= (f3 (f4 f19 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= ?v0 ?v1)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (= (f23 (f24 f29 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 ?v1)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (= (f3 (f4 f19 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= (f23 (f24 f29 ?v0) ?v1) f1)) (= (= (f23 (f24 f25 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= (f3 (f4 f19 ?v0) ?v1) f1)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= (f23 (f24 f25 ?v0) ?v1) f1)) (= (f23 (f24 f29 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= (f3 (f4 f5 ?v0) ?v1) f1)) (= (f3 (f4 f19 ?v1) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= (f23 (f24 f29 ?v0) ?v1) f1)) (= (f23 (f24 f25 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= (f3 (f4 f19 ?v0) ?v1) f1)) (= (f3 (f4 f5 ?v1) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f23 (f24 f25 ?v0) ?v1) f1) (or (= (f23 (f24 f29 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (or (= (f3 (f4 f19 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f23 (f24 f29 ?v0) ?v1) f1) (and (= (f23 (f24 f25 ?v0) ?v1) f1) (not (= (f23 (f24 f25 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f19 ?v0) ?v1) f1) (and (= (f3 (f4 f5 ?v0) ?v1) f1) (not (= (f3 (f4 f5 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= (f23 (f24 f29 ?v0) ?v1) f1) (and (= (f23 (f24 f25 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f19 ?v0) ?v1) f1) (and (= (f3 (f4 f5 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (or (= (f23 (f24 f25 ?v0) ?v1) f1) (= (f23 (f24 f29 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f3 (f4 f5 ?v0) ?v1) f1) (= (f3 (f4 f19 ?v1) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (not (= (f23 (f24 f25 ?v0) ?v1) f1)) (= (f23 (f24 f29 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (not (= (f3 (f4 f5 ?v0) ?v1) f1)) (= (f3 (f4 f19 ?v1) ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (not (= (f23 (f24 f29 ?v0) ?v1) f1)) (= (f23 (f24 f25 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (not (= (f3 (f4 f19 ?v0) ?v1) f1)) (= (f3 (f4 f5 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f15 (f16 f17 ?v0) f20) f20)))
(assert (forall ((?v0 S6)) (= (f8 (f9 f10 ?v0) f27) f27)))
(assert (forall ((?v0 S3)) (= (f15 (f16 f17 ?v0) f20) f20)))
(assert (forall ((?v0 S6)) (= (f8 (f9 f10 ?v0) f27) f27)))
(assert (forall ((?v0 S3)) (= (f15 (f16 f17 f20) ?v0) f20)))
(assert (forall ((?v0 S6)) (= (f8 (f9 f10 f27) ?v0) f27)))
(assert (forall ((?v0 S3)) (= (f15 (f16 f17 f20) ?v0) f20)))
(assert (forall ((?v0 S6)) (= (f8 (f9 f10 f27) ?v0) f27)))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 (f15 f22 ?v0)) f20) f1) (= ?v0 f20))))
(assert (forall ((?v0 S6)) (= (= (f3 (f4 f5 (f6 f7 ?v0)) f20) f1) (= ?v0 f27))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (=> (= (f23 (f24 f25 ?v0) ?v1) f1) false) (=> (=> (= (f23 (f24 f25 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (=> (= (f3 (f4 f5 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f5 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f24 f25 ?v2))) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 ?v_0 ?v0) f1) (= (f23 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v2))) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 (f24 f25 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (=> (= (f23 (f24 f25 ?v1) ?v2) f1) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= (f23 (f24 f25 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f23 (f24 f25 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f3 (f4 f5 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f24 f25 ?v0))) (=> (= (f23 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f23 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f24 f25 ?v2))) (=> (= ?v0 ?v1) (=> (= (f23 ?v_0 ?v1) f1) (= (f23 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v2))) (=> (= ?v0 ?v1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (=> (= ?v0 ?v1) (=> (= (f23 (f24 f25 ?v1) ?v2) f1) (= (f23 (f24 f25 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= ?v0 ?v1) (=> (= (f3 (f4 f5 ?v1) ?v2) f1) (= (f3 (f4 f5 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= (f23 (f24 f25 ?v0) ?v1) f1) (= (= (f23 (f24 f25 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (= (= (f3 (f4 f5 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (= ?v0 ?v1) (= (f23 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S12) (?v1 S12)) (= (= ?v0 ?v1) (and (= (f23 (f24 f25 ?v0) ?v1) f1) (= (f23 (f24 f25 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (and (= (f3 (f4 f5 ?v0) ?v1) f1) (= (f3 (f4 f5 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S12)) (or (= (f23 (f24 f25 ?v0) ?v1) f1) (= (f23 (f24 f25 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f3 (f4 f5 ?v0) ?v1) f1) (= (f3 (f4 f5 ?v1) ?v0) f1))))
(assert (exists ((?v0 S3)) (and (= (f3 (f4 f19 f20) ?v0) f1) (forall ((?v1 S3)) (= (f3 (f4 f5 (f15 f22 (f15 f26 ?v1))) (f15 (f16 f17 (f15 f22 ?v1)) ?v0)) f1)))))
(assert (exists ((?v0 S3)) (and (= (f3 (f4 f19 f20) ?v0) f1) (forall ((?v1 S3)) (= (f3 (f4 f5 (f6 f7 (f11 f12 ?v1))) (f15 (f16 f17 (f15 f22 ?v1)) ?v0)) f1)))))
(assert (exists ((?v0 S3)) (and (= (f3 (f4 f5 f20) ?v0) f1) (forall ((?v1 S3)) (= (f3 (f4 f5 (f15 f22 (f15 f26 ?v1))) (f15 (f16 f17 (f15 f22 ?v1)) ?v0)) f1)))))
(assert (exists ((?v0 S3)) (and (= (f3 (f4 f5 f20) ?v0) f1) (forall ((?v1 S3)) (= (f3 (f4 f5 (f6 f7 (f11 f12 ?v1))) (f15 (f16 f17 (f15 f22 ?v1)) ?v0)) f1)))))
(assert (forall ((?v0 S6)) (exists ((?v1 S3)) (and (= (f3 (f4 f19 f20) ?v1) f1) (forall ((?v2 S6)) (= (f3 (f4 f5 (f6 f7 (f8 (f9 f10 ?v2) ?v0))) (f15 (f16 f17 (f6 f7 ?v2)) ?v1)) f1))))))
(assert (forall ((?v0 S3)) (exists ((?v1 S3)) (and (= (f3 (f4 f19 f20) ?v1) f1) (forall ((?v2 S3)) (= (f3 (f4 f5 (f15 f22 (f15 (f16 f17 ?v2) ?v0))) (f15 (f16 f17 (f15 f22 ?v2)) ?v1)) f1))))))
(assert (forall ((?v0 S6)) (exists ((?v1 S3)) (and (= (f3 (f4 f19 f20) ?v1) f1) (forall ((?v2 S6)) (= (f3 (f4 f5 (f6 f7 (f8 (f9 f10 ?v0) ?v2))) (f15 (f16 f17 (f6 f7 ?v2)) ?v1)) f1))))))
(assert (forall ((?v0 S3)) (exists ((?v1 S3)) (and (= (f3 (f4 f19 f20) ?v1) f1) (forall ((?v2 S3)) (= (f3 (f4 f5 (f15 f22 (f15 (f16 f17 ?v0) ?v2))) (f15 (f16 f17 (f15 f22 ?v2)) ?v1)) f1))))))
(assert (exists ((?v0 S3)) (and (= (f3 (f4 f19 f20) ?v0) f1) (forall ((?v1 S6) (?v2 S6)) (= (f3 (f4 f5 (f6 f7 (f8 (f9 f10 ?v1) ?v2))) (f15 (f16 f17 (f15 (f16 f17 (f6 f7 ?v1)) (f6 f7 ?v2))) ?v0)) f1)))))
(assert (exists ((?v0 S3)) (and (= (f3 (f4 f19 f20) ?v0) f1) (forall ((?v1 S3) (?v2 S3)) (= (f3 (f4 f5 (f15 f22 (f15 (f16 f17 ?v1) ?v2))) (f15 (f16 f17 (f15 (f16 f17 (f15 f22 ?v1)) (f15 f22 ?v2))) ?v0)) f1)))))
(assert (forall ((?v0 S6)) (exists ((?v1 S3)) (and (= (f3 (f4 f5 f20) ?v1) f1) (forall ((?v2 S6)) (= (f3 (f4 f5 (f6 f7 (f8 (f9 f10 ?v2) ?v0))) (f15 (f16 f17 (f6 f7 ?v2)) ?v1)) f1))))))
(assert (forall ((?v0 S3)) (exists ((?v1 S3)) (and (= (f3 (f4 f5 f20) ?v1) f1) (forall ((?v2 S3)) (= (f3 (f4 f5 (f15 f22 (f15 (f16 f17 ?v2) ?v0))) (f15 (f16 f17 (f15 f22 ?v2)) ?v1)) f1))))))
(assert (forall ((?v0 S6)) (exists ((?v1 S3)) (and (= (f3 (f4 f5 f20) ?v1) f1) (forall ((?v2 S6)) (= (f3 (f4 f5 (f6 f7 (f8 (f9 f10 ?v0) ?v2))) (f15 (f16 f17 (f6 f7 ?v2)) ?v1)) f1))))))
(assert (forall ((?v0 S3)) (exists ((?v1 S3)) (and (= (f3 (f4 f5 f20) ?v1) f1) (forall ((?v2 S3)) (= (f3 (f4 f5 (f15 f22 (f15 (f16 f17 ?v0) ?v2))) (f15 (f16 f17 (f15 f22 ?v2)) ?v1)) f1))))))
(assert (exists ((?v0 S3)) (and (= (f3 (f4 f5 f20) ?v0) f1) (forall ((?v1 S6) (?v2 S6)) (= (f3 (f4 f5 (f6 f7 (f8 (f9 f10 ?v1) ?v2))) (f15 (f16 f17 (f15 (f16 f17 (f6 f7 ?v1)) (f6 f7 ?v2))) ?v0)) f1)))))
(assert (exists ((?v0 S3)) (and (= (f3 (f4 f5 f20) ?v0) f1) (forall ((?v1 S3) (?v2 S3)) (= (f3 (f4 f5 (f15 f22 (f15 (f16 f17 ?v1) ?v2))) (f15 (f16 f17 (f15 (f16 f17 (f15 f22 ?v1)) (f15 f22 ?v2))) ?v0)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f5 ?v0) f20) f1) (=> (= (f3 (f4 f5 (f15 f22 ?v1)) (f15 (f16 f17 ?v0) (f15 f22 ?v2))) f1) (= ?v1 f20)))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (=> (= (f3 (f4 f5 ?v0) f20) f1) (=> (= (f3 (f4 f5 (f6 f7 ?v1)) (f15 (f16 f17 ?v0) (f6 f7 ?v2))) f1) (= ?v1 f27)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 f17 ?v0))) (=> (= (f3 (f4 f19 f20) ?v0) f1) (= (= (f3 (f4 f5 (f15 ?v_0 ?v1)) (f15 ?v_0 ?v2)) f1) (= (f3 (f4 f5 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f3 (f4 f5 ?v0) ?v1) f1) (= (f3 (f4 f5 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 f17 ?v0))) (= (f15 (f16 f17 (f15 ?v_0 ?v1)) ?v2) (f15 ?v_0 (f15 (f16 f17 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f15 (f16 f17 ?v0) ?v1) (f15 (f16 f17 ?v1) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f19 ?v0) ?v1) f1) (and (= (f3 (f4 f5 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (or (= (f3 (f4 f19 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 f17 ?v0))) (=> (not (= ?v0 f20)) (= (= (f15 ?v_0 ?v1) (f15 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (not (= ?v0 f20)) (= (= (f15 (f16 f17 ?v1) ?v0) (f15 (f16 f17 ?v2) ?v0)) (= ?v1 ?v2)))))
(assert (not (= f20 f18)))
(assert (forall ((?v0 S3)) (= (f15 (f16 f17 f18) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 f17 ?v0))) (=> (= (f3 (f4 f19 f20) ?v0) f1) (=> (= (f3 (f4 f19 ?v1) ?v2) f1) (= (f3 (f4 f19 (f15 ?v_0 ?v1)) (f15 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f19 f20))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f15 (f16 f17 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f19 f20) ?v0) f1) (= (= (f3 (f4 f19 (f15 (f16 f17 ?v1) ?v0)) (f15 (f16 f17 ?v2) ?v0)) f1) (= (f3 (f4 f19 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f19 f20) ?v0) f1) (= (= (f3 (f4 f5 (f15 (f16 f17 ?v1) ?v0)) (f15 (f16 f17 ?v2) ?v0)) f1) (= (f3 (f4 f5 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f20))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f5 ?v1) f18) f1) (= (f3 (f4 f5 (f15 (f16 f17 ?v0) ?v1)) ?v0) f1)))))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f24 f25 f31))) (=> (= (f23 ?v_0 ?v0) f1) (=> (= (f23 ?v_0 ?v1) f1) (=> (= (f23 (f24 f25 ?v1) f32) f1) (= (f23 (f24 f25 (f33 (f34 f35 ?v0) ?v1)) ?v0) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f20))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f5 ?v1) f18) f1) (= (f3 (f4 f5 (f15 (f16 f17 ?v1) ?v0)) ?v0) f1)))))))
(assert (forall ((?v0 S12) (?v1 S12)) (let ((?v_0 (f24 f25 f31))) (=> (= (f23 ?v_0 ?v0) f1) (=> (= (f23 ?v_0 ?v1) f1) (=> (= (f23 (f24 f25 ?v1) f32) f1) (= (f23 (f24 f25 (f33 (f34 f35 ?v1) ?v0)) ?v0) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 f17 ?v0))) (=> (= (f3 (f4 f19 f20) ?v0) f1) (= (= (f3 (f4 f5 (f15 ?v_0 ?v1)) (f15 ?v_0 ?v2)) f1) (= (f3 (f4 f5 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f34 f35 ?v0))) (=> (= (f23 (f24 f29 f31) ?v0) f1) (= (= (f23 (f24 f25 (f33 ?v_0 ?v1)) (f33 ?v_0 ?v2)) f1) (= (f23 (f24 f25 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f16 f17 ?v0))) (=> (= (f3 (f4 f19 ?v0) f20) f1) (= (= (f3 (f4 f5 (f15 ?v_0 ?v1)) (f15 ?v_0 ?v2)) f1) (= (f3 (f4 f5 ?v2) ?v1) f1))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12)) (let ((?v_0 (f34 f35 ?v0))) (=> (= (f23 (f24 f29 ?v0) f31) f1) (= (= (f23 (f24 f25 (f33 ?v_0 ?v1)) (f33 ?v_0 ?v2)) f1) (= (f23 (f24 f25 ?v2) ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f4 f19 ?v0) ?v1) f1) (=> (= (f3 (f4 f19 ?v2) ?v3) f1) (=> (= (f3 (f4 f19 f20) ?v1) f1) (=> (= (f3 (f4 f5 f20) ?v2) f1) (= (f3 (f4 f19 (f15 (f16 f17 ?v0) ?v2)) (f15 (f16 f17 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S12) (?v3 S12)) (=> (= (f23 (f24 f29 ?v0) ?v1) f1) (=> (= (f23 (f24 f29 ?v2) ?v3) f1) (=> (= (f23 (f24 f29 f31) ?v1) f1) (=> (= (f23 (f24 f25 f31) ?v2) f1) (= (f23 (f24 f29 (f33 (f34 f35 ?v0) ?v2)) (f33 (f34 f35 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S12) (?v1 S12)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f23 (f24 f29 ?v0) ?v1) f1) false) (=> (=> (= (f23 (f24 f29 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 (f4 f19 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f19 ?v1) ?v0) f1) false) false)))))
(check-sat)
(exit)