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
(declare-sort S17 0)
(declare-sort S18 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S6) S3)
(declare-fun f7 (S7 S3) S5)
(declare-fun f8 () S7)
(declare-fun f9 () S3)
(declare-fun f10 (S8 S9) S6)
(declare-fun f11 () S8)
(declare-fun f12 (S10 S9) S9)
(declare-fun f13 () S10)
(declare-fun f14 () S10)
(declare-fun f15 () S9)
(declare-fun f16 () S3)
(declare-fun f17 () S3)
(declare-fun f18 (S11 S12) S3)
(declare-fun f19 () S11)
(declare-fun f20 () S12)
(declare-fun f21 (S3 S3) S12)
(declare-fun f22 (S13 S6) S9)
(declare-fun f23 (S14 S9) S13)
(declare-fun f24 () S14)
(declare-fun f25 () S9)
(declare-fun f26 (S15 S6) S6)
(declare-fun f27 (S16 S6) S15)
(declare-fun f28 () S16)
(declare-fun f29 () S6)
(declare-fun f30 (S17 S9) S3)
(declare-fun f31 () S17)
(declare-fun f32 (S18 S9) S10)
(declare-fun f33 () S18)
(declare-fun f34 () S10)
(declare-fun f35 () S16)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f10 f11 (f12 f13 (f12 f14 f15))))) (not (= (f3 (f4 f5 (f6 (f7 f8 f9) ?v_0)) (f6 (f7 f8 f16) ?v_0)) f17))))
(assert (= (f18 f19 f20) f17))
(assert (= f20 (f21 f9 f16)))
(assert (= (f18 f19 f20) f17))
(assert (= f20 (f21 f9 f16)))
(assert (= (f6 (f7 f8 f17) (f10 f11 (f12 f13 (f12 f14 f15)))) f17))
(assert (= (f22 (f23 f24 f25) (f10 f11 (f12 f13 (f12 f14 f15)))) f25))
(assert (= (f26 (f27 f28 f29) (f10 f11 (f12 f13 (f12 f14 f15)))) f29))
(assert (= (f3 (f4 f5 f17) f17) (f30 f31 (f12 f13 (f12 f14 f15)))))
(assert (= (f12 (f32 f33 f25) f25) (f12 f34 (f12 f13 (f12 f14 f15)))))
(assert (= (f3 (f4 f5 f17) f17) (f30 f31 (f12 f13 (f12 f14 f15)))))
(assert (= (f12 (f32 f33 f25) f25) (f12 f34 (f12 f13 (f12 f14 f15)))))
(assert (= (f26 (f27 f35 f29) f29) (f10 f11 (f12 f13 (f12 f14 f15)))))
(assert (forall ((?v0 S9)) (= (f3 (f4 f5 f17) (f30 f31 ?v0)) (f30 f31 (f12 (f32 f33 (f12 f14 f15)) ?v0)))))
(assert (forall ((?v0 S9)) (= (f12 (f32 f33 f25) (f12 f34 ?v0)) (f12 f34 (f12 (f32 f33 (f12 f14 f15)) ?v0)))))
(assert (forall ((?v0 S9)) (= (f3 (f4 f5 (f30 f31 ?v0)) f17) (f30 f31 (f12 (f32 f33 ?v0) (f12 f14 f15))))))
(assert (forall ((?v0 S9)) (= (f12 (f32 f33 (f12 f34 ?v0)) f25) (f12 f34 (f12 (f32 f33 ?v0) (f12 f14 f15))))))
(assert (= f17 (f30 f31 (f12 f14 f15))))
(assert (= f25 (f12 f34 (f12 f14 f15))))
(assert (= (f30 f31 (f12 f14 f15)) f17))
(assert (= (f12 f34 (f12 f14 f15)) f25))
(assert (= (f30 f31 (f12 f14 f15)) f17))
(assert (= (f12 f34 (f12 f14 f15)) f25))
(assert (= (f10 f11 (f12 f14 f15)) f29))
(assert (forall ((?v0 S9)) (let ((?v_0 (f30 f31 ?v0))) (= (f30 f31 (f12 f14 ?v0)) (f3 (f4 f5 (f3 (f4 f5 f17) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S9)) (let ((?v_0 (f12 f34 ?v0))) (= (f12 f34 (f12 f14 ?v0)) (f12 (f32 f33 (f12 (f32 f33 f25) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) (f30 f31 f15)) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f32 f33 ?v0) (f12 f34 f15)) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 (f30 f31 f15)) ?v0) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f32 f33 (f12 f34 f15)) ?v0) ?v0)))
(assert (=> (forall ((?v0 S3) (?v1 S3)) (=> (= f20 (f21 ?v0 ?v1)) false)) false))
(assert (forall ((?v0 S9)) (= (f12 f14 ?v0) (f12 (f32 f33 (f12 (f32 f33 f25) ?v0)) ?v0))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 (f32 f33 ?v0) ?v1) (f12 (f32 f33 ?v1) ?v0))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_1 (f32 f33 ?v0)) (?v_0 (f32 f33 ?v1))) (= (f12 ?v_1 (f12 ?v_0 ?v2)) (f12 ?v_0 (f12 ?v_1 ?v2))))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 (f32 f33 (f12 f34 ?v0)) (f12 f34 ?v1)) (f12 f34 (f12 (f32 f33 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f32 f33 ?v0))) (= (f12 (f32 f33 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f32 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S9)) (= (f12 (f32 f33 ?v0) f15) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f32 f33 f15) ?v0) ?v0)))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 (f32 f33 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f12 (f32 f33 ?v0) ?v1)))))
(assert (forall ((?v0 S9)) (= (f12 f13 ?v0) (f12 (f32 f33 ?v0) ?v0))))
(assert (= f25 (f12 f34 (f12 f14 f15))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 (f32 f33 (f12 f14 ?v0)) (f12 f13 ?v1)) (f12 f14 (f12 (f32 f33 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f12 (f32 f33 (f12 f13 ?v0)) (f12 f14 ?v1)) (f12 f14 (f12 (f32 f33 ?v0) ?v1)))))
(assert (= (f26 (f27 f35 f29) f29) (f10 f11 (f12 f13 (f12 f14 f15)))))
(assert (= (f10 f11 (f12 f14 f15)) f29))
(assert (= f29 (f10 f11 (f12 f14 f15))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f30 f31 ?v0) (f30 f31 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f12 f34 ?v0) (f12 f34 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S9) (?v1 S3)) (let ((?v_0 (f30 f31 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S6)) (let ((?v_0 (f10 f11 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_0 (f12 f34 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f12 f14 ?v0) (f12 f14 ?v1)) (= ?v0 ?v1))))
(check-sat)
(exit)