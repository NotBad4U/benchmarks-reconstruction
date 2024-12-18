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
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S2 S3) S1)
(declare-fun f6 (S4) S3)
(declare-fun f7 () S4)
(declare-fun f8 (S5 S6 S6) S3)
(declare-fun f9 () S5)
(declare-fun f10 () S6)
(declare-fun f11 (S9 S8) S1)
(declare-fun f12 (S5 S7) S9)
(declare-fun f13 (S6 S7) S5)
(declare-fun f14 (S7 S7) S1)
(declare-fun f15 () S7)
(declare-fun f16 (S10 S7) S7)
(declare-fun f17 (S11 S7) S10)
(declare-fun f18 () S11)
(declare-fun f19 () S7)
(declare-fun f20 (S12 S8) S7)
(declare-fun f21 () S12)
(declare-fun f22 (S13 S4) S8)
(declare-fun f23 (S14 S15) S13)
(declare-fun f24 () S14)
(declare-fun f25 () S15)
(declare-fun f26 (S3 S4) S4)
(declare-fun f27 (S7 S7) S1)
(declare-fun f28 (S3) S3)
(declare-fun f29 (S2 S8) S1)
(declare-fun f30 (S16 S8) S8)
(declare-fun f31 (S17 S7) S16)
(declare-fun f32 () S17)
(declare-fun f33 () S8)
(declare-fun f34 (S15 S2) S7)
(declare-fun f35 (S4) S18)
(declare-fun f36 () S18)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (and (= (f5 ?v0 (f6 f7)) f1) (= (f3 (f8 f9 f10 f10) ?v0) f1)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S8)) (= (= (f11 (f12 (f13 f10 ?v0) ?v1) ?v2) f1) true)))
(assert (forall ((?v0 S7) (?v1 S8)) (= (= (f11 (f12 f9 ?v0) ?v1) f1) false)))
(assert (let ((?v_1 (f20 f21 (f22 (f23 f24 f25) (f26 (f8 f9 f10 f10) f7))))) (let ((?v_0 (f16 (f17 f18 f19) ?v_1))) (not (and (= (f14 f15 ?v_0) f1) (and (= (f27 ?v_0 ?v_1) f1) (forall ((?v0 S2)) (=> (= (f5 ?v0 (f28 f4)) f1) (= (f29 ?v0 (f30 (f31 f32 ?v_0) f33)) f1)))))))))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 (f28 f4)) f1) (= (= (f29 ?v0 (f30 (f31 f32 (f16 (f17 f18 f19) (f20 f21 (f22 (f23 f24 f25) (f26 (f8 f9 f10 f10) f7))))) f33)) f1) (= (f29 ?v0 (f30 (f31 f32 f19) f33)) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 (f6 f7)) f1) (= (f29 ?v0 (f30 (f31 f32 f19) f33)) f1))))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 (f6 f7)) f1) (not (= (f34 f25 ?v0) f15)))))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 (f6 f7)) f1) (not (= (f34 f25 ?v0) f15)))))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 (f6 f7)) f1) (= (f29 ?v0 (f30 (f31 f32 f19) f33)) f1))))
(assert (exists ((?v0 S7)) (forall ((?v1 S2)) (=> (= (f5 ?v1 (f6 f7)) f1) (= (f29 ?v1 (f30 (f31 f32 ?v0) f33)) f1)))))
(assert (=> (forall ((?v0 S7)) (=> (forall ((?v1 S2)) (=> (= (f5 ?v1 (f6 f7)) f1) (= (f29 ?v1 (f30 (f31 f32 ?v0) f33)) f1))) false)) false))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f27 f15 ?v0) f1) (= (f14 f15 (f16 (f17 f18 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f16 (f17 f18 ?v1) ?v0))) (=> (= (f27 f15 ?v0) f1) (and (= (f14 f15 ?v_0) f1) (= (f27 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f14 f15 ?v0) f1) (=> (= (f27 ?v0 ?v1) f1) (= (f16 (f17 f18 ?v0) ?v1) ?v0)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f27 ?v0 f15) f1) (= (f14 (f16 (f17 f18 ?v1) ?v0) f15) f1))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f16 (f17 f18 ?v1) ?v0))) (=> (= (f27 ?v0 f15) f1) (and (= (f14 ?v_0 f15) f1) (= (f27 ?v0 ?v_0) f1))))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f14 ?v0 f15) f1) (=> (= (f27 ?v1 ?v0) f1) (= (f16 (f17 f18 ?v0) ?v1) ?v0)))))
(assert (= (f35 f7) f36))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f27 f15 ?v0) f1) (= (f27 (f16 (f17 f18 ?v1) ?v0) ?v0) f1))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f27 ?v0 f15) f1) (= (f27 ?v0 (f16 (f17 f18 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f14 f15 ?v0) f1) (= (f14 (f16 (f17 f18 ?v0) ?v1) ?v0) f1))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f14 f15 ?v0) f1) (=> (= (f14 f15 ?v1) f1) (= (f14 f15 (f16 (f17 f18 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S7)) (= (f14 ?v0 ?v0) f1)))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (=> (= (f14 ?v0 ?v1) f1) false) (=> (=> (= (f14 ?v1 ?v0) f1) false) false))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= (f14 ?v0 ?v1) f1) (=> (= (f14 ?v2 ?v0) f1) (= (f14 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f14 ?v0 ?v1) f1) (=> (= (f14 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= (f14 ?v0 ?v1) f1) (=> (= (f14 ?v1 ?v2) f1) (= (f14 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f14 ?v0 ?v1) f1) (=> (= (f14 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= (f14 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f14 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= (f14 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f14 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= ?v0 ?v1) (=> (= (f14 ?v2 ?v1) f1) (= (f14 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= ?v0 ?v1) (=> (= (f14 ?v1 ?v2) f1) (= (f14 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f14 ?v0 ?v1) f1) (= (= (f14 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= ?v0 ?v1) (= (f14 ?v0 ?v1) f1))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= ?v0 ?v1) (and (= (f14 ?v0 ?v1) f1) (= (f14 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (or (= (f14 ?v0 ?v1) f1) (= (f14 ?v1 ?v0) f1))))
(check-sat)
(exit)
