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
(declare-sort S17 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S4 S4 S5) S2)
(declare-fun f5 () S4)
(declare-fun f6 () S4)
(declare-fun f7 (S6 S5) S5)
(declare-fun f8 (S7 S8) S6)
(declare-fun f9 () S7)
(declare-fun f10 (S9 S4) S8)
(declare-fun f11 () S9)
(declare-fun f12 (S10 S5) S6)
(declare-fun f13 () S10)
(declare-fun f14 () S5)
(declare-fun f15 (S11 S4) S5)
(declare-fun f16 () S11)
(declare-fun f17 () S4)
(declare-fun f18 (S12 S8) S5)
(declare-fun f19 () S12)
(declare-fun f20 () S8)
(declare-fun f21 () S5)
(declare-fun f22 (S13) S3)
(declare-fun f23 () S13)
(declare-fun f24 (S5 S14) S1)
(declare-fun f25 (S14) S14)
(declare-fun f26 (S15 S13) S14)
(declare-fun f27 (S4) S15)
(declare-fun f28 () S4)
(declare-fun f29 (S4 S16) S1)
(declare-fun f30 () S16)
(declare-fun f31 (S13 S17) S1)
(declare-fun f32 () S17)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 f5 f6 (f7 (f8 f9 (f10 f11 f6)) (f7 (f12 f13 f14) (f7 (f12 f13 (f15 f16 f17)) (f7 (f12 f13 (f18 f19 f20)) f21))))) (f22 f23)) f1)))
(assert (= (f24 (f7 (f8 f9 (f10 f11 f6)) (f7 (f12 f13 f14) (f7 (f12 f13 (f15 f16 f17)) (f7 (f12 f13 (f18 f19 f20)) f21)))) (f25 (f26 (f27 f28) f23))) f1))
(assert (not (= (f29 f6 f30) f1)))
(assert (= (f31 f23 f32) f1))
(assert (forall ((?v0 S13) (?v1 S4)) (=> (= (f31 ?v0 f32) f1) (= (= (f24 (f18 f19 (f10 f11 ?v1)) (f25 (f26 (f27 f28) ?v0))) f1) (= (f29 ?v1 f30) f1)))))
(assert (forall ((?v0 S4) (?v1 S5) (?v2 S5) (?v3 S5) (?v4 S5) (?v5 S13)) (=> (= (f3 (f4 f5 ?v0 (f7 (f8 f9 (f10 f11 ?v0)) (f7 (f12 f13 ?v1) (f7 (f12 f13 ?v2) (f7 (f12 f13 ?v3) ?v4))))) (f22 ?v5)) f1) (= (f24 ?v3 (f25 (f26 (f27 f28) ?v5))) f1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S8) (?v3 S5) (?v4 S5) (?v5 S5) (?v6 S5) (?v7 S13)) (=> (= (f3 (f4 ?v0 ?v1 (f7 (f8 f9 ?v2) (f7 (f12 f13 ?v3) (f7 (f12 f13 ?v4) (f7 (f12 f13 ?v5) ?v6))))) (f22 ?v7)) f1) (= (f24 ?v6 (f25 (f26 (f27 f28) ?v7))) f1))))
(assert (forall ((?v0 S4) (?v1 S13)) (=> (= (f29 ?v0 f30) f1) (= (f24 (f18 f19 (f10 f11 ?v0)) (f26 (f27 f28) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S13)) (= (f24 (f18 f19 (f10 f11 ?v0)) (f26 (f27 ?v0) ?v1)) f1)))
(assert (= (f29 f28 f30) f1))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S5) (?v3 S13)) (=> (= (f3 (f4 ?v0 ?v1 ?v2) (f22 ?v3)) f1) (=> (=> (= (f24 ?v2 (f25 (f26 (f27 f28) ?v3))) f1) false) false))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S14)) (let ((?v_0 (f25 ?v2))) (=> (= (f24 (f7 (f12 f13 ?v0) ?v1) ?v_0) f1) (=> (=> (= (f24 ?v0 ?v_0) f1) (=> (= (f24 ?v1 ?v_0) f1) false)) false)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S5) (?v3 S13)) (=> (= (f3 (f4 ?v0 ?v1 ?v2) (f22 ?v3)) f1) (= (f24 ?v2 (f26 (f27 f28) ?v3)) f1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S5) (?v3 S13)) (=> (= (f3 (f4 ?v0 ?v1 ?v2) (f22 ?v3)) f1) (= (f24 ?v2 (f26 (f27 ?v0) ?v3)) f1))))
(assert (forall ((?v0 S5) (?v1 S14)) (=> (= (f24 ?v0 ?v1) f1) (= (f24 ?v0 (f25 ?v1)) f1))))
(assert (not (= (f29 f5 f30) f1)))
(assert (not (= f28 f5)))
(assert (not (= f5 f28)))
(assert (forall ((?v0 S4) (?v1 S8) (?v2 S5)) (not (= (f15 f16 ?v0) (f7 (f8 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S14)) (let ((?v_0 (f25 ?v1))) (=> (= (f24 ?v0 (f25 ?v_0)) f1) (= (f24 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S14)) (let ((?v_0 (f25 ?v0))) (= (f25 ?v_0) ?v_0))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f18 f19 ?v0) (f18 f19 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (= (= (f7 (f12 f13 ?v0) ?v1) (f7 (f12 f13 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S8) (?v1 S5) (?v2 S8) (?v3 S5)) (= (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f15 f16 ?v0) (f15 f16 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S5) (?v3 S4) (?v4 S4) (?v5 S5)) (= (= (f4 ?v0 ?v1 ?v2) (f4 ?v3 ?v4 ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f10 f11 ?v0) (f10 f11 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S14)) (let ((?v_0 (f25 ?v2))) (=> (= (f24 (f7 (f12 f13 ?v0) ?v1) ?v_0) f1) (= (f24 ?v1 ?v_0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S14)) (let ((?v_0 (f25 ?v2))) (=> (= (f24 (f7 (f12 f13 ?v0) ?v1) ?v_0) f1) (= (f24 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S8)) (not (= (f7 (f12 f13 ?v0) ?v1) (f18 f19 ?v2)))))
(assert (forall ((?v0 S8) (?v1 S5) (?v2 S5)) (not (= (f18 f19 ?v0) (f7 (f12 f13 ?v1) ?v2)))))
(assert (forall ((?v0 S8) (?v1 S5) (?v2 S14)) (let ((?v_0 (f25 ?v2))) (=> (= (f24 (f7 (f8 f9 ?v0) ?v1) ?v_0) f1) (=> (=> (= (f24 ?v1 ?v_0) f1) false) false)))))
(assert (forall ((?v0 S8) (?v1 S5) (?v2 S14)) (let ((?v_0 (f25 ?v2))) (=> (= (f24 (f7 (f8 f9 ?v0) ?v1) ?v_0) f1) (= (f24 ?v1 ?v_0) f1)))))
(assert (forall ((?v0 S8) (?v1 S5) (?v2 S8)) (not (= (f7 (f8 f9 ?v0) ?v1) (f18 f19 ?v2)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S5)) (not (= (f18 f19 ?v0) (f7 (f8 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S8) (?v3 S5)) (not (= (f7 (f12 f13 ?v0) ?v1) (f7 (f8 f9 ?v2) ?v3)))))
(check-sat)
(exit)