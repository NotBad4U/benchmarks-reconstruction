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
(declare-sort S14 0)
(declare-sort S15 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 () S2)
(declare-fun f5 (S4 S3) S3)
(declare-fun f6 (S5 S3) S4)
(declare-fun f7 () S5)
(declare-fun f8 () S5)
(declare-fun f9 () S4)
(declare-fun f10 () S4)
(declare-fun f11 () S4)
(declare-fun f12 () S3)
(declare-fun f13 () S3)
(declare-fun f14 () S3)
(declare-fun f15 (S6 S7) S3)
(declare-fun f16 () S6)
(declare-fun f17 (S8 S7) S7)
(declare-fun f18 (S9 S7) S8)
(declare-fun f19 () S9)
(declare-fun f20 (S10 S3) S7)
(declare-fun f21 () S10)
(declare-fun f22 () S3)
(declare-fun f23 () S7)
(declare-fun f24 (S11 S3) S2)
(declare-fun f25 () S11)
(declare-fun f26 () S7)
(declare-fun f27 () S7)
(declare-fun f28 () S2)
(declare-fun f29 () S9)
(declare-fun f30 () S10)
(declare-fun f31 () S9)
(declare-fun f32 () S3)
(declare-fun f33 (S12 S7) S1)
(declare-fun f34 (S13 S7) S12)
(declare-fun f35 () S13)
(declare-fun f36 () S5)
(declare-fun f37 () S8)
(declare-fun f38 (S14 S3) S6)
(declare-fun f39 () S14)
(declare-fun f40 () S3)
(declare-fun f41 () S9)
(declare-fun f42 () S11)
(declare-fun f43 () S3)
(declare-fun f44 () S5)
(declare-fun f45 () S11)
(declare-fun f46 (S15 S3) S11)
(declare-fun f47 () S15)
(declare-fun f48 () S3)
(assert (not (= f1 f2)))
(assert (not (not (= (f3 f4 (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) (f5 (f6 f8 f14) (f15 f16 (f17 (f18 f19 (f20 f21 f22)) f23))))) f1))))
(assert (let ((?v_0 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) (?v_1 (f5 (f6 f8 f14) (f15 f16 f26)))) (=> (= (f3 (f24 f25 ?v_1) ?v_0) f1) (not (= (f3 f4 (f5 (f6 f7 ?v_0) ?v_1)) f1)))))
(assert (and (= (f3 (f24 f25 (f5 (f6 f8 f14) (f15 f16 f26))) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f1) (= f26 (f17 (f18 f19 (f20 f21 f22)) f23))))
(assert (= (f3 (f24 f25 f14) f22) f1))
(assert (= f26 (f17 (f18 f19 (f20 f21 f22)) f23)))
(assert (let ((?v_0 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) (?v_1 (f5 (f6 f8 f14) (f15 f16 f26)))) (=> (= (f3 (f24 f25 ?v_1) ?v_0) f1) (not (= (f3 f4 (f5 (f6 f7 ?v_0) ?v_1)) f1)))))
(assert (and (= (f3 (f24 f25 (f5 (f6 f8 f14) (f15 f16 f26))) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f1) (= f26 (f17 (f18 f19 (f20 f21 f22)) f23))))
(assert (= (f3 f4 (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f22)) f1))
(assert (= (f3 (f24 f25 f22) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f1))
(assert (not (= (f3 f4 (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) (f5 (f6 f8 f14) (f15 f16 f27)))) f1)))
(assert (= (f3 f28 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 f4 ?v0) f1) (=> (= (f3 f4 ?v1) f1) (= (f3 f4 (f5 (f6 f7 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 f14) (f5 f9 ?v0)) (f5 f9 (f5 (f6 f8 (f5 f11 f12)) ?v0)))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 (f5 f9 ?v0)) f14) (f5 f9 (f5 (f6 f8 ?v0) (f5 f11 f12))))))
(assert (= (f5 (f6 f8 f14) f14) (f5 f9 (f5 f10 (f5 f11 f12)))))
(assert (= (f5 (f6 f8 f14) f14) (f5 f9 (f5 f10 (f5 f11 f12)))))
(assert (= (f17 (f18 f29 f23) f23) (f20 f30 (f5 f10 (f5 f11 f12)))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 ?v0) (f5 f9 (f5 f10 (f5 f11 f12)))) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 ?v0) (f5 f9 (f5 f10 (f5 f11 f12)))) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S7)) (= (f17 (f18 f31 ?v0) (f20 f30 (f5 f10 (f5 f11 f12)))) (f17 (f18 f29 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f11 f12)))) ?v0) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f11 f12)))) ?v0) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S7)) (= (f17 (f18 f31 (f20 f30 (f5 f10 (f5 f11 f12)))) ?v0) (f17 (f18 f29 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 (f5 (f6 f8 f14) f14)) (f5 f9 ?v0)) (f5 f9 (f5 f10 ?v0)))))
(assert (= (f3 (f24 f25 f32) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f7 (f5 f11 ?v0)) ?v1) (f5 (f6 f8 (f5 f10 (f5 (f6 f7 ?v0) ?v1))) ?v1))))
(assert (= f14 (f5 f9 (f5 f11 f12))))
(assert (= (f33 (f34 f35 f27) f26) f1))
(assert (= (f20 f21 f32) f27))
(assert (= (f15 f16 f27) f32))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f3 (f24 f25 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f24 f25 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S7)) (= (= (f15 f16 ?v0) f32) (= ?v0 f27))))
(assert (forall ((?v0 S3)) (= (= (f3 (f24 f25 (f5 (f6 f8 ?v0) ?v0)) f32) f1) (= (f3 (f24 f25 ?v0) f32) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f24 f25 (f5 f11 ?v0)) f32) f1) (= (f3 (f24 f25 ?v0) f32) f1))))
(assert (= (= (f3 (f24 f25 f12) f32) f1) false))
(assert (forall ((?v0 S3)) (= (= (f3 (f24 f25 (f5 f10 ?v0)) f32) f1) (= (f3 (f24 f25 ?v0) f32) f1))))
(assert (= (f3 (f24 f25 f32) f14) f1))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v2))) (=> (= (f3 (f24 f25 ?v0) ?v1) f1) (=> (= (f3 (f24 f25 f32) ?v2) f1) (= (f3 (f24 f25 (f5 ?v_0 ?v0)) (f5 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S7)) (not (= (f3 (f24 f25 (f15 f16 ?v0)) f32) f1))))
(assert (forall ((?v0 S3)) (= (= (f5 (f6 f8 ?v0) ?v0) f32) (= ?v0 f32))))
(assert (= f12 f32))
(assert (not (= f32 f14)))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 ?v0) f32) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 f32) ?v0) ?v0)))
(assert (forall ((?v0 S12) (?v1 S3)) (= (= (f33 ?v0 (f20 f21 ?v1)) f1) (and (forall ((?v2 S7)) (=> (= ?v1 (f15 f16 ?v2)) (= (f33 ?v0 ?v2) f1))) (=> (= (f3 (f24 f25 ?v1) f32) f1) (= (f33 ?v0 f27) f1))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f24 f25 (f5 f9 ?v0)) f32) f1) (= (f3 (f24 f25 ?v0) f12) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f24 f25 f32) (f5 f9 ?v0)) f1) (= (f3 (f24 f25 f12) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f24 f25 (f5 f9 ?v0)) (f5 f9 ?v1)) f1) (= (f3 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f24 f25 f32) ?v0) f1) (= (= (f5 (f6 f7 ?v0) ?v1) f14) (and (= ?v0 f14) (= ?v1 f14))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f24 f25 (f5 (f6 f8 (f5 (f6 f8 f14) ?v0)) ?v0)) f32) f1) (= (f3 (f24 f25 ?v0) f32) f1))))
(assert (= (f20 f30 f12) f27))
(assert (= (f5 f9 f12) f32))
(assert (= (f5 f9 f12) f32))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S3)) (= (f5 (f6 f8 (f15 f16 ?v0)) (f5 (f6 f8 (f15 f16 ?v1)) ?v2)) (f5 (f6 f8 (f15 f16 (f17 (f18 f29 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f5 (f6 f8 (f15 f16 ?v0)) (f15 f16 ?v1)) (f15 f16 (f17 (f18 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f5 (f6 f7 (f15 f16 ?v0)) (f15 f16 ?v1)) (f15 f16 (f17 (f18 f31 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f15 f16 (f17 (f18 f31 ?v0) ?v1)) (f5 (f6 f7 (f15 f16 ?v0)) (f15 f16 ?v1)))))
(assert (= f32 (f5 f9 f12)))
(assert (forall ((?v0 S3)) (not (= (f5 (f6 f8 (f5 (f6 f8 f14) ?v0)) ?v0) f32))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f24 f25 (f5 f11 ?v0)) (f5 f11 ?v1)) f1) (= (f3 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f24 f25 (f5 f11 ?v0)) (f5 f11 ?v1)) f1) (= (f3 (f24 f25 ?v0) ?v1) f1))))
(assert (= (= (f3 (f24 f25 f12) f12) f1) false))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f24 f25 (f5 f10 ?v0)) (f5 f10 ?v1)) f1) (= (f3 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f24 f25 (f5 f10 ?v0)) (f5 f10 ?v1)) f1) (= (f3 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f24 f25 (f5 f9 ?v0)) (f5 f9 ?v1)) f1) (= (f3 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f24 f25 ?v0) ?v1) f1) (= (f3 (f24 f25 (f5 (f6 f8 ?v0) ?v2)) (f5 (f6 f8 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f5 f9 ?v0))) (= (f5 f9 (f5 f10 ?v0)) (f5 (f6 f8 (f5 (f6 f8 f32) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f9 ?v0) (f5 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f5 f9 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S7)) (let ((?v_0 (f20 f30 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f11 ?v0) (f5 f11 ?v1)) (= ?v0 ?v1))))
(assert (= (= f12 f12) true))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f10 ?v0) (f5 f10 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f7 ?v0) ?v1) (f5 (f6 f7 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 f9 ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f8 ?v0))) (= (f5 (f6 f8 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f8 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f6 f8 ?v0)) (?v_0 (f6 f8 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f8 ?v0) ?v1) (f5 (f6 f8 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (= (= (f3 (f24 f25 (f5 f11 ?v0)) f12) f1) (= (f3 (f24 f25 ?v0) f12) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f24 f25 (f5 f11 ?v0)) (f5 f10 ?v1)) f1) (= (f3 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f24 f25 (f5 f11 ?v0)) (f5 f10 ?v1)) f1) (= (f3 (f24 f25 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f24 f25 (f5 f10 ?v0)) f12) f1) (= (f3 (f24 f25 ?v0) f12) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f24 f25 f12))) (= (= (f3 ?v_0 (f5 f10 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f15 f16 ?v0) (f15 f16 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f24 f25 ?v0))) (= (= (f3 ?v_0 (f5 (f6 f8 ?v1) f14)) f1) (or (= (f3 ?v_0 ?v1) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f24 f25 (f5 f9 ?v0)) f14) f1) (= (f3 (f24 f25 ?v0) (f5 f11 f12)) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f24 f25 f14) (f5 f9 ?v0)) f1) (= (f3 (f24 f25 (f5 f11 f12)) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 f9 (f5 (f6 f36 ?v0) ?v1)) (f5 (f6 f36 (f5 f9 ?v0)) (f5 f9 ?v1)))))
(assert (forall ((?v0 S3)) (= (= (f5 f11 ?v0) f12) false)))
(assert (forall ((?v0 S3)) (= (= f12 (f5 f11 ?v0)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f11 ?v0) (f5 f10 ?v1)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f10 ?v0) (f5 f11 ?v1)) false)))
(assert (forall ((?v0 S3)) (= (= (f5 f10 ?v0) f12) (= ?v0 f12))))
(assert (forall ((?v0 S3)) (= (= f12 (f5 f10 ?v0)) (= f12 ?v0))))
(assert (= (f5 f10 f12) f12))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 f12) ?v0) f12)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f7 (f5 f10 ?v0)) ?v1) (f5 f10 (f5 (f6 f7 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 ?v0) f12) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 f12) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f8 (f5 f10 ?v0)) (f5 f10 ?v1)) (f5 f10 (f5 (f6 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f5 f10 ?v0) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 ?v0) f14) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 f14) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f7 (f5 f9 ?v0)) (f5 f9 ?v1)) (f5 f9 (f5 (f6 f7 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f6 f7 (f5 (f6 f8 ?v0) ?v1)) ?v2) (f5 (f6 f8 (f5 (f6 f7 ?v0) ?v2)) (f5 (f6 f7 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 ?v_0 (f5 (f6 f8 ?v1) ?v2)) (f5 (f6 f8 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f8 (f5 f9 ?v0)) (f5 f9 ?v1)) (f5 f9 (f5 (f6 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S7)) (= (f20 f21 (f15 f16 ?v0)) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f5 f9 ?v2))) (= (f5 (f6 f7 (f5 (f6 f8 ?v0) ?v1)) ?v_0) (f5 (f6 f8 (f5 (f6 f7 ?v0) ?v_0)) (f5 (f6 f7 ?v1) ?v_0))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S3)) (let ((?v_0 (f20 f30 ?v2))) (= (f17 (f18 f31 (f17 (f18 f29 ?v0) ?v1)) ?v_0) (f17 (f18 f29 (f17 (f18 f31 ?v0) ?v_0)) (f17 (f18 f31 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 (f5 f9 ?v0)))) (= (f5 ?v_0 (f5 (f6 f8 ?v1) ?v2)) (f5 (f6 f8 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S7)) (let ((?v_0 (f18 f31 (f20 f30 ?v0)))) (= (f17 ?v_0 (f17 (f18 f29 ?v1) ?v2)) (f17 (f18 f29 (f17 ?v_0 ?v1)) (f17 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f5 f9 ?v2))) (= (f5 (f6 f7 (f5 (f6 f36 ?v0) ?v1)) ?v_0) (f5 (f6 f36 (f5 (f6 f7 ?v0) ?v_0)) (f5 (f6 f7 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 (f5 f9 ?v0)))) (= (f5 ?v_0 (f5 (f6 f36 ?v1) ?v2)) (f5 (f6 f36 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 (f5 f9 f12)) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 ?v0) (f5 f9 f12)) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f6 f7 (f5 f9 ?v0)) (f5 (f6 f7 (f5 f9 ?v1)) ?v2)) (f5 (f6 f7 (f5 f9 (f5 (f6 f7 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f7 (f5 f9 ?v0)) (f5 f9 ?v1)) (f5 f9 (f5 (f6 f7 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 f9 (f5 (f6 f7 ?v0) ?v1)) (f5 (f6 f7 (f5 f9 ?v0)) (f5 f9 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f6 f8 (f5 f9 ?v0)) (f5 (f6 f8 (f5 f9 ?v1)) ?v2)) (f5 (f6 f8 (f5 f9 (f5 (f6 f8 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f8 (f5 f9 ?v0)) (f5 f9 ?v1)) (f5 f9 (f5 (f6 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 f9 (f5 (f6 f8 ?v0) ?v1)) (f5 (f6 f8 (f5 f9 ?v0)) (f5 f9 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f8 (f5 f11 ?v0)) (f5 f10 ?v1)) (f5 f11 (f5 (f6 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f8 (f5 f10 ?v0)) (f5 f11 ?v1)) (f5 f11 (f5 (f6 f8 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f5 f11 ?v0) (f5 (f6 f8 (f5 (f6 f8 f14) ?v0)) ?v0))))
(assert (forall ((?v0 S7)) (let ((?v_0 (f15 f16 ?v0))) (= (f5 f9 ?v_0) ?v_0))))
(assert (forall ((?v0 S7)) (= (f20 f30 (f15 f16 ?v0)) (f17 f37 ?v0))))
(assert (= (f15 f16 f23) f14))
(assert (forall ((?v0 S3)) (let ((?v_0 (f5 f9 ?v0))) (= (f5 f9 (f5 f11 ?v0)) (f5 (f6 f8 (f5 (f6 f8 f14) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 (f5 f9 (f5 f11 f12))) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 ?v0) (f5 f9 (f5 f11 f12))) ?v0)))
(assert (= (f5 f9 (f5 f11 f12)) f14))
(assert (= (f20 f30 (f5 f11 f12)) f23))
(assert (= (f5 f9 (f5 f11 f12)) f14))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f6 f8 (f5 f9 ?v0)) (f5 (f6 f36 (f5 f9 ?v1)) ?v2)) (f5 (f6 f36 (f5 f9 (f5 (f6 f8 ?v0) ?v1))) ?v2))))
(assert (= (f3 f28 (f5 f9 (f5 f10 (f5 f11 f12)))) f1))
(assert (let ((?v_0 (f5 f10 (f5 f11 f12)))) (= (f5 f9 ?v_0) (f15 f16 (f20 f30 ?v_0)))))
(assert (let ((?v_0 (f5 f10 (f5 f11 f12)))) (= (f20 f30 ?v_0) (f20 f21 (f5 f9 ?v_0)))))
(assert (let ((?v_0 (f5 f10 (f5 f11 f12)))) (= (f5 (f6 f8 (f15 (f38 f39 f40) (f20 f30 ?v_0))) f14) (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_0))) f13)) f14)) f22))))
(assert (let ((?v_0 (f5 f11 (f5 f11 f12)))) (= (f5 f9 ?v_0) (f15 f16 (f20 f30 ?v_0)))))
(assert (let ((?v_0 (f5 f11 (f5 f11 f12)))) (= (f20 f30 ?v_0) (f20 f21 (f5 f9 ?v_0)))))
(assert (= (f17 (f18 f29 f23) f23) (f20 f30 (f5 f10 (f5 f11 f12)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7)) (= (f17 (f18 f31 (f20 f30 ?v0)) (f17 (f18 f31 (f20 f30 ?v1)) ?v2)) (ite (= (f3 (f24 f25 ?v0) f12) f1) f27 (f17 (f18 f31 (f20 f30 (f5 (f6 f7 ?v0) ?v1))) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f17 (f18 f31 (f20 f30 ?v0)) (f20 f30 ?v1)) (ite (= (f3 (f24 f25 ?v0) f12) f1) f27 (f20 f30 (f5 (f6 f7 ?v0) ?v1))))))
(assert (= f14 (f5 f9 (f5 f11 f12))))
(assert (=> (forall ((?v0 S7)) (=> (= ?v0 (f17 (f18 f19 (f20 f21 f22)) f23)) (=> (= (f33 (f34 f35 f27) ?v0) f1) false))) false))
(assert (=> (forall ((?v0 S3)) (let ((?v_0 (f5 f10 (f5 f11 f12)))) (=> (= (f5 (f6 f8 (f15 (f38 f39 f40) (f20 f30 ?v_0))) f14) (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_0))) f13)) f14)) ?v0)) false))) false))
(assert (=> (= f22 f14) (exists ((?v0 S3) (?v1 S3)) (let ((?v_1 (f5 f10 (f5 f11 f12)))) (let ((?v_0 (f20 f30 ?v_1))) (= (f5 (f6 f8 (f15 (f38 f39 ?v0) ?v_0)) (f15 (f38 f39 ?v1) ?v_0)) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_1))) f13)) f14)))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S7)) (let ((?v_0 (f38 f39 ?v0))) (= (f15 (f38 f39 (f15 ?v_0 ?v1)) ?v2) (f15 ?v_0 (f17 (f18 f31 ?v1) ?v2))))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f36 ?v0) f12) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f36 (f5 f10 ?v0)) (f5 f10 ?v1)) (f5 f10 (f5 (f6 f36 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S7)) (let ((?v_0 (f38 f39 ?v0))) (= (f15 ?v_0 (f17 (f18 f29 ?v1) ?v2)) (f5 (f6 f7 (f15 ?v_0 ?v1)) (f15 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 ?v_0 (f5 (f6 f36 ?v1) ?v2)) (f5 (f6 f36 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f5 (f6 f7 (f5 (f6 f36 ?v0) ?v1)) ?v2) (f5 (f6 f36 (f5 (f6 f7 ?v0) ?v2)) (f5 (f6 f7 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f33 (f34 f35 (f20 f30 ?v0)) (f20 f30 ?v1)) f1) (ite (= (f3 (f24 f25 ?v0) ?v1) f1) (= (f3 (f24 f25 f12) ?v1) f1) false))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f3 (f24 f25 (f15 f16 ?v0)) (f15 f16 ?v1)) f1) (= (f33 (f34 f35 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f20 f30 (f5 f10 (f5 f11 f12))))) (= (f5 (f6 f7 (f5 (f6 f8 ?v0) ?v1)) (f5 (f6 f36 ?v0) ?v1)) (f5 (f6 f36 (f15 (f38 f39 ?v0) ?v_0)) (f15 (f38 f39 ?v1) ?v_0))))))
(assert (forall ((?v0 S3)) (= (f15 (f38 f39 ?v0) (f20 f30 (f5 f11 (f5 f11 f12)))) (f5 (f6 f7 (f5 (f6 f7 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S7)) (= (f17 (f18 f41 ?v0) (f20 f30 (f5 f11 (f5 f11 f12)))) (f17 (f18 f31 (f17 (f18 f31 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S3) (?v1 S7)) (let ((?v_1 (f20 f30 (f5 f10 (f5 f11 f12)))) (?v_0 (f38 f39 ?v0))) (= (f15 ?v_0 (f17 (f18 f31 ?v_1) ?v1)) (f15 (f38 f39 (f15 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_1 (f20 f30 (f5 f10 (f5 f11 f12)))) (?v_0 (f18 f41 ?v0))) (= (f17 ?v_0 (f17 (f18 f31 ?v_1) ?v1)) (f17 (f18 f41 (f17 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S3)) (let ((?v_2 (f5 f10 (f5 f11 f12)))) (let ((?v_0 (f20 f30 ?v_2)) (?v_1 (f38 f39 ?v0))) (= (f15 (f38 f39 (f15 ?v_1 ?v_0)) ?v_0) (f15 ?v_1 (f20 f30 (f5 f10 ?v_2))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f36 (f5 f11 ?v0)) (f5 f10 ?v1)) (f5 f11 (f5 (f6 f36 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f36 (f5 f11 ?v0)) (f5 f11 ?v1)) (f5 f10 (f5 (f6 f36 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f6 f36 f12))) (= (f5 ?v_0 (f5 f10 ?v0)) (f5 f10 (f5 ?v_0 ?v0))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f24 f25 ?v0) ?v1) f1) (= (f3 (f24 f25 (f5 (f6 f36 ?v0) ?v1)) f32) f1))))
(assert (forall ((?v0 S3)) (= (= (f33 (f34 f35 f27) (f20 f30 ?v0)) f1) (= (f3 (f24 f25 f12) ?v0) f1))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f3 (f24 f25 (f15 f16 ?v0)) (f15 f16 ?v1)) f1) (= (f33 (f34 f35 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f5 f10 (f5 f11 f12)))) (let ((?v_0 (f20 f30 ?v_1))) (= (f15 (f38 f39 (f5 (f6 f36 ?v0) ?v1)) ?v_0) (f5 (f6 f8 (f5 (f6 f36 (f15 (f38 f39 ?v0) ?v_0)) (f5 (f6 f7 (f5 (f6 f7 (f5 f9 ?v_1)) ?v0)) ?v1))) (f15 (f38 f39 ?v1) ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_3 (f5 f11 f12))) (let ((?v_5 (f20 f30 (f5 f10 ?v_3))) (?v_1 (f5 f11 ?v_3))) (let ((?v_0 (f20 f30 ?v_1)) (?v_2 (f38 f39 ?v0)) (?v_4 (f6 f7 (f5 f9 ?v_1))) (?v_6 (f38 f39 ?v1))) (= (f15 (f38 f39 (f5 (f6 f36 ?v0) ?v1)) ?v_0) (f5 (f6 f36 (f5 (f6 f8 (f5 (f6 f36 (f15 ?v_2 ?v_0)) (f5 (f6 f7 (f5 ?v_4 (f15 ?v_2 ?v_5))) ?v1))) (f5 (f6 f7 (f5 ?v_4 ?v0)) (f15 ?v_6 ?v_5)))) (f15 ?v_6 ?v_0))))))))
(assert (= (f17 (f18 f41 f27) (f20 f30 (f5 f10 (f5 f11 f12)))) f27))
(assert (= (f15 (f38 f39 f32) (f20 f30 (f5 f10 (f5 f11 f12)))) f32))
(assert (forall ((?v0 S3)) (= (= (f15 (f38 f39 ?v0) (f20 f30 (f5 f10 (f5 f11 f12)))) f32) (= ?v0 f32))))
(assert (forall ((?v0 S3)) (= (f15 (f38 f39 ?v0) (f20 f30 (f5 f10 (f5 f11 f12)))) (f5 (f6 f7 ?v0) ?v0))))
(assert (forall ((?v0 S7)) (= (f17 (f18 f41 ?v0) (f20 f30 (f5 f10 (f5 f11 f12)))) (f17 (f18 f31 ?v0) ?v0))))
(assert (= (f15 (f38 f39 f14) (f20 f30 (f5 f10 (f5 f11 f12)))) f14))
(assert (= (f17 (f18 f41 f23) (f20 f30 (f5 f10 (f5 f11 f12)))) f23))
(assert (forall ((?v0 S3)) (let ((?v_1 (f5 f11 f12)) (?v_0 (f38 f39 ?v0))) (= (f5 (f6 f7 ?v0) (f15 ?v_0 (f20 f30 (f5 f10 ?v_1)))) (f15 ?v_0 (f20 f30 (f5 f11 ?v_1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f24 f25 f32) ?v0) f1) (= (= (f33 (f34 f35 (f20 f21 ?v1)) (f20 f21 ?v0)) f1) (= (f3 (f24 f25 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f33 (f34 f35 (f20 f21 ?v0)) (f20 f21 ?v1)) f1) (and (= (f3 (f24 f25 f32) ?v1) f1) (= (f3 (f24 f25 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S7) (?v1 S3)) (= (= (f33 (f34 f35 ?v0) (f20 f21 ?v1)) f1) (= (f3 (f24 f25 (f15 f16 ?v0)) ?v1) f1))))
(assert (forall ((?v0 S3)) (not (= (f3 (f24 f25 (f15 (f38 f39 ?v0) (f20 f30 (f5 f10 (f5 f11 f12))))) f32) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f24 f25 f32) (f15 (f38 f39 ?v0) (f20 f30 (f5 f10 (f5 f11 f12))))) f1) (not (= ?v0 f32)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f20 f30 (f5 f10 (f5 f11 f12))))) (= (= (f5 (f6 f8 (f15 (f38 f39 ?v0) ?v_0)) (f15 (f38 f39 ?v1) ?v_0)) f32) (and (= ?v0 f32) (= ?v1 f32))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f5 f9 ?v0))) (= (f15 (f38 f39 ?v_0) (f20 f30 (f5 f10 (f5 f11 f12)))) (f5 (f6 f7 ?v_0) ?v_0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f20 f30 ?v0))) (= (f17 (f18 f41 ?v_0) (f20 f30 (f5 f10 (f5 f11 f12)))) (f17 (f18 f31 ?v_0) ?v_0)))))
(assert (forall ((?v0 S1) (?v1 S3) (?v2 S3)) (let ((?v_0 (= ?v0 f1))) (= (ite ?v_0 (f20 f21 ?v1) (f20 f21 ?v2)) (f20 f21 (ite ?v_0 ?v1 ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f15 f16 ?v0) (f15 f16 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S1) (?v1 S7) (?v2 S7)) (let ((?v_0 (= ?v0 f1))) (= (ite ?v_0 (f15 f16 ?v1) (f15 f16 ?v2)) (f15 f16 (ite ?v_0 ?v1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f20 f30 (f5 f10 (f5 f11 f12))))) (not (= (f3 (f24 f25 (f5 (f6 f8 (f15 (f38 f39 ?v0) ?v_0)) (f15 (f38 f39 ?v1) ?v_0))) f32) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f20 f30 (f5 f10 (f5 f11 f12))))) (= (= (f3 (f24 f25 f32) (f5 (f6 f8 (f15 (f38 f39 ?v0) ?v_0)) (f15 (f38 f39 ?v1) ?v_0))) f1) (or (not (= ?v0 f32)) (not (= ?v1 f32)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f5 f10 (f5 f11 f12)))) (let ((?v_0 (f20 f30 ?v_1))) (= (f15 (f38 f39 (f5 (f6 f8 ?v0) ?v1)) ?v_0) (f5 (f6 f8 (f5 (f6 f8 (f15 (f38 f39 ?v0) ?v_0)) (f15 (f38 f39 ?v1) ?v_0))) (f5 (f6 f7 (f5 (f6 f7 (f5 f9 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f20 f30 (f5 f10 (f5 f11 f12))))) (= (f17 (f18 f41 (f17 (f18 f29 ?v0) ?v1)) ?v_0) (f17 (f18 f29 (f17 (f18 f29 (f17 (f18 f41 ?v0) ?v_0)) (f17 (f18 f41 ?v1) ?v_0))) (f17 (f18 f31 (f17 (f18 f31 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S3)) (= (= (f33 (f34 f35 f27) (f20 f21 ?v0)) f1) (= (f3 (f24 f25 f32) ?v0) f1))))
(assert (forall ((?v0 S7)) (= (= (f3 (f24 f25 f32) (f15 f16 ?v0)) f1) (= (f33 (f34 f35 f27) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7)) (let ((?v_0 (f6 f7 (f15 f16 ?v2)))) (=> (= (f3 (f24 f25 ?v0) ?v1) f1) (=> (= (f33 (f34 f35 f27) ?v2) f1) (= (f3 (f24 f25 (f5 ?v_0 ?v0)) (f5 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f5 f10 (f5 f11 f12)))) (let ((?v_0 (f20 f30 ?v_1))) (= (f15 (f38 f39 (f5 (f6 f8 ?v0) ?v1)) ?v_0) (f5 (f6 f8 (f5 (f6 f8 (f15 (f38 f39 ?v0) ?v_0)) (f5 (f6 f7 (f5 (f6 f7 (f5 f9 ?v_1)) ?v0)) ?v1))) (f15 (f38 f39 ?v1) ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_3 (f5 f11 f12))) (let ((?v_5 (f20 f30 (f5 f10 ?v_3))) (?v_1 (f5 f11 ?v_3))) (let ((?v_0 (f20 f30 ?v_1)) (?v_4 (f6 f7 (f5 f9 ?v_1))) (?v_2 (f38 f39 ?v0)) (?v_6 (f38 f39 ?v1))) (= (f15 (f38 f39 (f5 (f6 f8 ?v0) ?v1)) ?v_0) (f5 (f6 f8 (f5 (f6 f8 (f5 (f6 f8 (f15 ?v_2 ?v_0)) (f5 (f6 f7 (f5 ?v_4 (f15 ?v_2 ?v_5))) ?v1))) (f5 (f6 f7 (f5 ?v_4 ?v0)) (f15 ?v_6 ?v_5)))) (f15 ?v_6 ?v_0))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f5 f10 (f5 f11 f12)))) (let ((?v_0 (f20 f30 ?v_1))) (= (f15 (f38 f39 (f5 (f6 f36 ?v0) ?v1)) ?v_0) (f5 (f6 f36 (f5 (f6 f8 (f15 (f38 f39 ?v0) ?v_0)) (f15 (f38 f39 ?v1) ?v_0))) (f5 (f6 f7 (f5 (f6 f7 (f5 f9 ?v_1)) ?v0)) ?v1)))))))
(assert (= (f20 f30 f12) f27))
(assert (= f27 (f20 f30 f12)))
(assert (forall ((?v0 S3)) (= (f20 f30 ?v0) (f20 f21 (f5 f9 ?v0)))))
(assert (forall ((?v0 S3)) (= (f20 f21 (f5 f9 ?v0)) (f20 f30 ?v0))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f5 (f6 f7 (f15 f16 ?v0)) (f15 f16 ?v1)) (f15 f16 (f17 (f18 f31 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f5 (f6 f8 (f15 f16 ?v0)) (f15 f16 ?v1)) (f15 f16 (f17 (f18 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 (f6 f8 (f5 (f6 f7 ?v0) ?v0)) (f5 (f6 f7 ?v1) ?v1)) f32) (and (= ?v0 f32) (= ?v1 f32)))))
(assert (= f32 (f5 f9 f12)))
(assert (forall ((?v0 S7)) (= (f17 (f18 f31 ?v0) (f20 f30 (f5 f10 (f5 f11 f12)))) (f17 (f18 f29 ?v0) ?v0))))
(assert (forall ((?v0 S7)) (= (f17 (f18 f31 (f20 f30 (f5 f10 (f5 f11 f12)))) ?v0) (f17 (f18 f29 ?v0) ?v0))))
(assert (= f23 (f20 f30 (f5 f11 f12))))
(assert (= (f20 f30 (f5 f11 f12)) f23))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f24 f25 f32))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 (f5 (f6 f7 ?v0) ?v1)) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f20 f30 ?v0)) (?v_0 (f20 f30 ?v1))) (= (f17 (f18 f29 ?v_1) ?v_0) (ite (= (f3 (f24 f25 ?v0) f12) f1) ?v_0 (ite (= (f3 (f24 f25 ?v1) f12) f1) ?v_1 (f20 f30 (f5 (f6 f8 ?v0) ?v1))))))))
(assert (= f27 (f20 f21 f32)))
(assert (= f32 (f15 f16 f27)))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f17 (f18 f31 ?v0) ?v1) (ite (= ?v0 f27) f27 (f17 (f18 f29 ?v1) (f17 (f18 f31 (f17 (f18 f19 ?v0) f23)) ?v1))))))
(assert (= f23 (f20 f21 f14)))
(assert (= f14 (f15 f16 f23)))
(assert (forall ((?v0 S3) (?v1 S3)) (not (= (f3 (f24 f25 (f5 (f6 f8 (f5 (f6 f7 ?v0) ?v0)) (f5 (f6 f7 ?v1) ?v1))) f32) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f24 f25 f32) (f5 (f6 f8 (f5 (f6 f7 ?v0) ?v0)) (f5 (f6 f7 ?v1) ?v1))) f1) (or (not (= ?v0 f32)) (not (= ?v1 f32))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f5 f10 (f5 f11 f12)))) (let ((?v_1 (f5 f9 ?v_0))) (=> (= (f3 (f24 f25 ?v_1) ?v0) f1) (= (f17 (f18 f19 (f20 f21 ?v0)) (f20 f30 ?v_0)) (f20 f21 (f5 (f6 f36 ?v0) ?v_1))))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f5 f9 (f5 f10 (f5 f11 f12))))) (=> (= (f3 (f24 f25 ?v_0) ?v0) f1) (= (f33 (f34 f35 f27) (f20 f21 (f5 (f6 f36 ?v0) ?v_0))) f1)))))
(assert (let ((?v_0 (f5 f10 (f5 f11 f12)))) (= (f3 (f24 f42 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_0))) f13)) f14)) (f5 (f6 f8 (f15 (f38 f39 f40) (f20 f30 ?v_0))) f14)) f1)))
(assert (let ((?v_0 (f15 (f38 f39 f40) (f20 f30 (f5 f10 (f5 f11 f12)))))) (= (f5 (f6 f36 ?v_0) (f5 f9 f43)) (f5 (f6 f8 ?v_0) f14))))
(assert (let ((?v_0 (f5 f10 (f5 f11 f12)))) (= (f3 (f24 f42 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_0))) f13)) f14)) (f5 (f6 f36 (f15 (f38 f39 f40) (f20 f30 ?v_0))) (f5 f9 f43))) f1)))
(assert (= (f5 (f6 f44 (f5 f9 f43)) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f14))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f24 f42 ?v0))) (=> (= (f3 ?v_0 (f5 (f6 f36 ?v1) ?v2)) f1) (=> (= (f3 ?v_0 ?v2) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (= (f5 f11 f43) f43))
(assert (forall ((?v0 S3)) (= (= f43 (f5 f11 ?v0)) (= f43 ?v0))))
(assert (forall ((?v0 S3)) (= (= (f5 f11 ?v0) f43) (= ?v0 f43))))
(assert (= (= f43 f12) false))
(assert (= (= f12 f43) false))
(assert (forall ((?v0 S3)) (= (= f43 (f5 f10 ?v0)) false)))
(assert (forall ((?v0 S3)) (= (= (f5 f10 ?v0) f43) false)))
(assert (= (= (f3 (f24 f25 f43) f43) f1) false))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f24 f42 ?v0))) (=> (= (f3 f28 ?v0) f1) (=> (= (f3 ?v_0 (f5 (f6 f7 ?v1) ?v2)) f1) (or (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v2) f1)))))))
(assert (= (= f43 f43) true))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f24 f25 f32) ?v0) f1) (=> (= (f3 (f24 f25 ?v0) ?v1) f1) (not (= (f3 (f24 f42 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f3 (f24 f42 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2)) f1) (=> (not (= ?v0 f32)) (= (f3 (f24 f42 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S7) (?v1 S3) (?v2 S3)) (let ((?v_0 (f24 f42 ?v1))) (=> (= (f33 (f34 f35 f27) ?v0) f1) (=> (= (f3 ?v_0 ?v2) f1) (= (f3 ?v_0 (f15 (f38 f39 ?v2) ?v0)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f24 f42 ?v0)) (?v_1 (f6 f8 ?v2))) (=> (= (f3 ?v_0 ?v1) f1) (= (= (f3 ?v_0 (f5 ?v_1 ?v3)) f1) (= (f3 ?v_0 (f5 (f6 f8 (f5 ?v_1 (f5 (f6 f7 ?v4) ?v1))) ?v3)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f24 f42 ?v0))) (= (= (f3 ?v_0 (f5 (f6 f8 ?v1) (f5 (f6 f7 ?v0) ?v2))) f1) (= (f3 ?v_0 ?v1) f1)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f24 f25 (f5 f11 ?v0)) f43) f1) (= (f3 (f24 f25 ?v0) f43) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f24 f25 f43))) (= (= (f3 ?v_0 (f5 f11 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (= (= (f3 (f24 f25 f12) f43) f1) false))
(assert (= (= (f3 (f24 f25 f43) f12) f1) true))
(assert (forall ((?v0 S3)) (let ((?v_0 (f24 f25 f43))) (= (= (f3 ?v_0 (f5 f10 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (= (= (f3 (f24 f25 f43) f32) f1) true))
(assert (not (= (f5 f9 f12) (f5 f9 f43))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f15 (f38 f39 (f15 f16 ?v0)) ?v1) (f15 f16 (f17 (f18 f41 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f15 (f38 f39 (f15 f16 ?v0)) ?v1) (f15 f16 (f17 (f18 f41 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f15 f16 (f17 (f18 f41 ?v0) ?v1)) (f15 (f38 f39 (f15 f16 ?v0)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7)) (let ((?v_0 (f24 f42 ?v0))) (=> (= (f3 f28 ?v0) f1) (=> (= (f3 ?v_0 (f15 (f38 f39 ?v1) ?v2)) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7)) (let ((?v_0 (f24 f42 ?v0))) (=> (= (f3 f28 ?v0) f1) (=> (= (f3 ?v_0 (f15 (f38 f39 ?v1) ?v2)) f1) (=> (= (f33 (f34 f35 f27) ?v2) f1) (= (f3 ?v_0 ?v1) f1)))))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f36 f12) (f5 f11 ?v0)) (f5 f11 (f5 (f6 f36 f43) ?v0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f6 f36 f43))) (= (f5 ?v_0 (f5 f11 ?v0)) (f5 f10 (f5 ?v_0 ?v0))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f6 f36 f43))) (= (f5 ?v_0 (f5 f10 ?v0)) (f5 f11 (f5 ?v_0 ?v0))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f5 (f6 f7 ?v0) ?v1) f14) (or (= ?v0 f14) (= ?v0 (f5 f9 f43))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f5 f9 f43))) (= (= (f5 (f6 f7 ?v0) ?v1) f14) (or (and (= ?v0 f14) (= ?v1 f14)) (and (= ?v0 ?v_0) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7) (?v3 S3)) (let ((?v_0 (f24 f42 (f15 (f38 f39 ?v0) ?v2)))) (=> (= (f3 f28 ?v0) f1) (=> (not (= (f3 (f24 f42 ?v0) ?v1) f1)) (=> (= (f3 ?v_0 (f5 (f6 f7 ?v1) ?v3)) f1) (= (f3 ?v_0 ?v3) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7) (?v3 S3)) (let ((?v_0 (f24 f42 (f15 (f38 f39 ?v0) ?v2)))) (=> (= (f3 f28 ?v0) f1) (=> (not (= (f3 (f24 f42 ?v0) ?v1) f1)) (=> (= (f3 ?v_0 (f5 (f6 f7 ?v3) ?v1)) f1) (= (f3 ?v_0 ?v3) f1)))))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f18 f41 ?v0))) (= (f17 ?v_0 ?v1) (ite (= ?v1 f27) f23 (f17 (f18 f31 ?v0) (f17 ?v_0 (f17 (f18 f19 ?v1) f23))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f5 (f6 f36 ?v0) ?v1) ?v2) (= ?v0 (f5 (f6 f8 ?v2) ?v1)))))
(assert (forall ((?v0 S7)) (= (f15 (f38 f39 (f5 f9 f43)) (f17 (f18 f31 (f20 f30 (f5 f10 (f5 f11 f12)))) ?v0)) f14)))
(assert (= (f3 (f24 f45 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) (f5 f9 f43)) f1))
(assert (let ((?v_0 (f5 f10 (f5 f11 f12)))) (= (f3 (f24 (f46 f47 (f15 (f38 f39 f40) (f20 f30 ?v_0))) (f5 f9 f43)) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_0))) f13)) f14)) f1)))
(assert (let ((?v_1 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) (?v_0 (f5 f9 f43))) (=> (not (= (f3 (f24 f45 ?v_1) ?v_0) f1)) (not (= (f5 (f6 f44 ?v_0) ?v_1) f14)))))
(assert (let ((?v_0 (f5 f10 (f5 f11 f12)))) (= (f3 (f24 (f46 f47 (f15 (f38 f39 f48) (f20 f30 ?v_0))) (f5 f9 f43)) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_0))) f13)) f14)) f1)))
(check-sat)
(exit)