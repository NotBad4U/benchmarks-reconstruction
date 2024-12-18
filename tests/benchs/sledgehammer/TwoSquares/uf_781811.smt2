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
(declare-fun f17 () S7)
(declare-fun f18 (S8 S3) S2)
(declare-fun f19 () S8)
(declare-fun f20 () S7)
(declare-fun f21 () S3)
(declare-fun f22 () S2)
(declare-fun f23 () S3)
(declare-fun f24 (S9 S7) S7)
(declare-fun f25 (S10 S7) S9)
(declare-fun f26 () S10)
(declare-fun f27 () S7)
(declare-fun f28 (S11 S3) S7)
(declare-fun f29 () S11)
(declare-fun f30 () S10)
(declare-fun f31 (S12 S7) S1)
(declare-fun f32 (S13 S7) S12)
(declare-fun f33 () S13)
(declare-fun f34 () S3)
(declare-fun f35 () S9)
(declare-fun f36 () S8)
(declare-fun f37 (S14 S3) S6)
(declare-fun f38 () S14)
(declare-fun f39 () S3)
(declare-fun f40 () S7)
(declare-fun f41 () S3)
(declare-fun f42 () S3)
(declare-fun f43 () S8)
(declare-fun f44 () S10)
(declare-fun f45 () S13)
(assert (not (= f1 f2)))
(assert (not (= (f3 f4 (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) (f5 (f6 f8 f14) (f15 f16 f17)))) f1)))
(assert (let ((?v_0 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) (?v_1 (f5 (f6 f8 f14) (f15 f16 f20)))) (and (= (f3 (f18 f19 ?v_1) ?v_0) f1) (= (f3 f4 (f5 (f6 f7 ?v_0) ?v_1)) f1))))
(assert (let ((?v_0 (f5 (f6 f8 f14) (f15 f16 f20)))) (or (= ?v_0 f14) (= ?v_0 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)))))
(assert (let ((?v_0 (f5 (f6 f8 f14) (f15 f16 f20)))) (or (= ?v_0 f14) (= ?v_0 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)))))
(assert (let ((?v_0 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) (?v_1 (f5 (f6 f8 f14) (f15 f16 f20)))) (and (= (f3 (f18 f19 ?v_1) ?v_0) f1) (= (f3 f4 (f5 (f6 f7 ?v_0) ?v_1)) f1))))
(assert (not (= (f3 f4 (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) (f5 (f6 f8 f14) (f15 f16 f17)))) f1)))
(assert (= (f3 (f18 f19 f14) f21) f1))
(assert (let ((?v_0 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) (?v_1 (f5 (f6 f8 f14) (f15 f16 f20)))) (not (=> (= (f3 (f18 f19 ?v_1) ?v_0) f1) (not (= (f3 f4 (f5 (f6 f7 ?v_0) ?v_1)) f1))))))
(assert (= (f3 f22 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 f4 ?v0) f1) (=> (= (f3 f4 ?v1) f1) (= (f3 f4 (f5 (f6 f7 ?v0) ?v1)) f1)))))
(assert (= (f3 f4 (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f23)) f1))
(assert (= (f3 f4 (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f21)) f1))
(assert (= (f3 (f18 f19 f21) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f1))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 f14) (f5 f9 ?v0)) (f5 f9 (f5 (f6 f8 (f5 f11 f12)) ?v0)))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 (f5 f9 ?v0)) f14) (f5 f9 (f5 (f6 f8 ?v0) (f5 f11 f12))))))
(assert (= (f5 (f6 f8 f14) f14) (f5 f9 (f5 f10 (f5 f11 f12)))))
(assert (= (f5 (f6 f8 f14) f14) (f5 f9 (f5 f10 (f5 f11 f12)))))
(assert (= (f24 (f25 f26 f27) f27) (f28 f29 (f5 f10 (f5 f11 f12)))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 ?v0) (f5 f9 (f5 f10 (f5 f11 f12)))) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 ?v0) (f5 f9 (f5 f10 (f5 f11 f12)))) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S7)) (= (f24 (f25 f30 ?v0) (f28 f29 (f5 f10 (f5 f11 f12)))) (f24 (f25 f26 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f11 f12)))) ?v0) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f11 f12)))) ?v0) (f5 (f6 f8 ?v0) ?v0))))
(assert (forall ((?v0 S7)) (= (f24 (f25 f30 (f28 f29 (f5 f10 (f5 f11 f12)))) ?v0) (f24 (f25 f26 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 (f5 (f6 f8 f14) f14)) (f5 f9 ?v0)) (f5 f9 (f5 f10 ?v0)))))
(assert (= (f3 (f18 f19 f23) (f5 (f6 f8 f14) (f15 f16 f20))) f1))
(assert (= (f31 (f32 f33 f17) f20) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f3 (f18 f19 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f18 f19 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 (f5 f9 ?v0)) (f5 f9 ?v1)) f1) (= (f3 (f18 f19 ?v0) ?v1) f1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S3)) (= (f5 (f6 f8 (f15 f16 ?v0)) (f5 (f6 f8 (f15 f16 ?v1)) ?v2)) (f5 (f6 f8 (f15 f16 (f24 (f25 f26 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f5 (f6 f8 (f15 f16 ?v0)) (f15 f16 ?v1)) (f15 f16 (f24 (f25 f26 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f5 (f6 f7 (f15 f16 ?v0)) (f15 f16 ?v1)) (f15 f16 (f24 (f25 f30 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f15 f16 (f24 (f25 f30 ?v0) ?v1)) (f5 (f6 f7 (f15 f16 ?v0)) (f15 f16 ?v1)))))
(assert (= (f15 f16 f27) f14))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 (f5 f11 ?v0)) (f5 f11 ?v1)) f1) (= (f3 (f18 f19 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 (f5 f11 ?v0)) (f5 f11 ?v1)) f1) (= (f3 (f18 f19 ?v0) ?v1) f1))))
(assert (= (= (f3 (f18 f19 f12) f12) f1) false))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 (f5 f10 ?v0)) (f5 f10 ?v1)) f1) (= (f3 (f18 f19 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 (f5 f10 ?v0)) (f5 f10 ?v1)) f1) (= (f3 (f18 f19 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 (f5 f9 ?v0)) (f5 f9 ?v1)) f1) (= (f3 (f18 f19 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f18 f19 ?v0) ?v1) f1) (= (f3 (f18 f19 (f5 (f6 f8 ?v0) ?v2)) (f5 (f6 f8 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f9 ?v0) (f5 f9 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f5 f9 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S7)) (let ((?v_0 (f28 f29 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f11 ?v0) (f5 f11 ?v1)) (= ?v0 ?v1))))
(assert (= (= f12 f12) true))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 f10 ?v0) (f5 f10 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f19 (f5 (f6 f8 ?v0) ?v0)) f34) f1) (= (f3 (f18 f19 ?v0) f34) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f7 ?v0) ?v1) (f5 (f6 f7 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (= (f5 f9 ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f8 ?v0))) (= (f5 (f6 f8 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f8 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f6 f8 ?v0)) (?v_0 (f6 f8 ?v1))) (= (f5 ?v_1 (f5 ?v_0 ?v2)) (f5 ?v_0 (f5 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f8 ?v0) ?v1) (f5 (f6 f8 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f19 (f5 f9 ?v0)) f34) f1) (= (f3 (f18 f19 ?v0) f12) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f19 f34) (f5 f9 ?v0)) f1) (= (f3 (f18 f19 f12) ?v0) f1))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f15 f16 ?v0) (f15 f16 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f19 (f5 f11 ?v0)) f12) f1) (= (f3 (f18 f19 ?v0) f12) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 (f5 f11 ?v0)) (f5 f10 ?v1)) f1) (= (f3 (f18 f19 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 (f5 f11 ?v0)) (f5 f10 ?v1)) f1) (= (f3 (f18 f19 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f19 (f5 f10 ?v0)) f12) f1) (= (f3 (f18 f19 ?v0) f12) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f18 f19 f12))) (= (= (f3 ?v_0 (f5 f10 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f18 f19 ?v0))) (= (= (f3 ?v_0 (f5 (f6 f8 ?v1) f14)) f1) (or (= (f3 ?v_0 ?v1) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f19 (f5 f9 ?v0)) f14) f1) (= (f3 (f18 f19 ?v0) (f5 f11 f12)) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f19 f14) (f5 f9 ?v0)) f1) (= (f3 (f18 f19 (f5 f11 f12)) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (= (f5 (f6 f8 ?v0) ?v0) f34) (= ?v0 f34))))
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
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f5 f9 ?v2))) (= (f5 (f6 f7 (f5 (f6 f8 ?v0) ?v1)) ?v_0) (f5 (f6 f8 (f5 (f6 f7 ?v0) ?v_0)) (f5 (f6 f7 ?v1) ?v_0))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S3)) (let ((?v_0 (f28 f29 ?v2))) (= (f24 (f25 f30 (f24 (f25 f26 ?v0) ?v1)) ?v_0) (f24 (f25 f26 (f24 (f25 f30 ?v0) ?v_0)) (f24 (f25 f30 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 (f5 f9 ?v0)))) (= (f5 ?v_0 (f5 (f6 f8 ?v1) ?v2)) (f5 (f6 f8 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S7)) (let ((?v_0 (f25 f30 (f28 f29 ?v0)))) (= (f24 ?v_0 (f24 (f25 f26 ?v1) ?v2)) (f24 (f25 f26 (f24 ?v_0 ?v1)) (f24 ?v_0 ?v2))))))
(assert (= (f28 f29 f12) f17))
(assert (= (f5 f9 f12) f34))
(assert (= (f5 f9 f12) f34))
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
(assert (forall ((?v0 S7)) (= (f28 f29 (f15 f16 ?v0)) (f24 f35 ?v0))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f5 f9 ?v0))) (= (f5 f9 (f5 f10 ?v0)) (f5 (f6 f8 (f5 (f6 f8 f34) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f5 f9 ?v0))) (= (f5 f9 (f5 f11 ?v0)) (f5 (f6 f8 (f5 (f6 f8 f14) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 (f5 f9 (f5 f11 f12))) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 ?v0) (f5 f9 (f5 f11 f12))) ?v0)))
(assert (= (f5 f9 (f5 f11 f12)) f14))
(assert (= (f28 f29 (f5 f11 f12)) f27))
(assert (= (f5 f9 (f5 f11 f12)) f14))
(assert (= f14 (f5 f9 (f5 f11 f12))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 (f6 f7 (f5 f11 ?v0)) ?v1) (f5 (f6 f8 (f5 f10 (f5 (f6 f7 ?v0) ?v1))) ?v1))))
(assert (= (f3 (f18 f19 f34) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f1))
(assert (let ((?v_0 (f5 (f6 f8 f14) (f15 f16 f20)))) (let ((?v_1 (f6 f7 ?v_0))) (= (f3 (f18 f36 (f5 ?v_1 ?v_0)) (f5 ?v_1 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14))) f1))))
(assert (= (f3 (f18 f36 (f5 (f6 f8 f14) (f15 f16 f20))) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f1))
(assert (= (f3 (f18 f19 f34) (f5 (f6 f8 f14) (f15 f16 f20))) f1))
(assert (= (f3 f22 (f5 f9 (f5 f10 (f5 f11 f12)))) f1))
(assert (let ((?v_0 (f5 f10 (f5 f11 f12)))) (= (f5 f9 ?v_0) (f15 f16 (f28 f29 ?v_0)))))
(assert (=> (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f5 f10 (f5 f11 f12)))) (let ((?v_0 (f28 f29 ?v_1))) (=> (= (f5 (f6 f8 (f15 (f37 f38 ?v0) ?v_0)) (f15 (f37 f38 ?v1) ?v_0)) (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_1))) f13)) f14)) (f5 (f6 f8 f14) (f15 f16 f20)))) false)))) false))
(assert (not (= (f5 (f6 f8 f14) (f15 f16 f20)) f34)))
(assert (let ((?v_0 (f5 f10 (f5 f11 f12)))) (= (f5 (f6 f8 (f15 (f37 f38 f39) (f28 f29 ?v_0))) f14) (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_0))) f13)) f14)) f21))))
(assert (let ((?v_0 (f5 f11 (f5 f11 f12)))) (= (f5 f9 ?v_0) (f15 f16 (f28 f29 ?v_0)))))
(assert (= (f31 (f32 f33 f17) f40) f1))
(assert (let ((?v_0 (f5 f10 (f5 f11 f12)))) (= (f3 (f18 f36 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_0))) f13)) f14)) (f5 (f6 f8 (f15 (f37 f38 f39) (f28 f29 ?v_0))) f14)) f1)))
(assert (=> (forall ((?v0 S3)) (let ((?v_0 (f5 f10 (f5 f11 f12)))) (=> (= (f5 (f6 f8 (f15 (f37 f38 f39) (f28 f29 ?v_0))) f14) (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_0))) f13)) f14)) ?v0)) false))) false))
(assert (=> (= f21 f14) (exists ((?v0 S3) (?v1 S3)) (let ((?v_1 (f5 f10 (f5 f11 f12)))) (let ((?v_0 (f28 f29 ?v_1))) (= (f5 (f6 f8 (f15 (f37 f38 ?v0) ?v_0)) (f15 (f37 f38 ?v1) ?v_0)) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_1))) f13)) f14)))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S7)) (let ((?v_0 (f37 f38 ?v0))) (= (f15 (f37 f38 (f15 ?v_0 ?v1)) ?v2) (f15 ?v_0 (f24 (f25 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7)) (let ((?v_0 (f18 f36 ?v0))) (=> (= (f3 f22 ?v0) f1) (=> (= (f3 ?v_0 (f15 (f37 f38 ?v1) ?v2)) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f18 f19 f34) ?v0) f1) (=> (= (f3 (f18 f19 ?v0) ?v1) f1) (not (= (f3 (f18 f36 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f3 (f18 f36 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2)) f1) (=> (not (= ?v0 f34)) (= (f3 (f18 f36 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7) (?v3 S3)) (let ((?v_0 (f18 f36 (f15 (f37 f38 ?v0) ?v2)))) (=> (= (f3 f22 ?v0) f1) (=> (not (= (f3 (f18 f36 ?v0) ?v1) f1)) (=> (= (f3 ?v_0 (f5 (f6 f7 ?v3) ?v1)) f1) (= (f3 ?v_0 ?v3) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7) (?v3 S3)) (let ((?v_0 (f18 f36 (f15 (f37 f38 ?v0) ?v2)))) (=> (= (f3 f22 ?v0) f1) (=> (not (= (f3 (f18 f36 ?v0) ?v1) f1)) (=> (= (f3 ?v_0 (f5 (f6 f7 ?v1) ?v3)) f1) (= (f3 ?v_0 ?v3) f1)))))))
(assert (forall ((?v0 S3) (?v1 S7) (?v2 S7)) (let ((?v_0 (f37 f38 ?v0))) (= (f15 ?v_0 (f24 (f25 f26 ?v1) ?v2)) (f5 (f6 f7 (f15 ?v_0 ?v1)) (f15 ?v_0 ?v2))))))
(assert (= f12 f34))
(assert (not (= f34 f14)))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 f34) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 ?v0) f34) ?v0)))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f3 (f18 f19 (f15 f16 ?v0)) (f15 f16 ?v1)) f1) (= (f31 (f32 f33 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f18 f19 f34))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 (f5 (f6 f7 ?v0) ?v1)) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (= f34 (f15 f16 f17)))
(assert (forall ((?v0 S7)) (= (= (f3 (f18 f19 f34) (f15 f16 ?v0)) f1) (= (f31 (f32 f33 f17) ?v0) f1))))
(assert (forall ((?v0 S3)) (let ((?v_2 (f5 f10 (f5 f11 f12)))) (let ((?v_0 (f28 f29 ?v_2)) (?v_1 (f37 f38 ?v0))) (= (f15 (f37 f38 (f15 ?v_1 ?v_0)) ?v_0) (f15 ?v_1 (f28 f29 (f5 f10 ?v_2))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f18 f36 ?v0))) (= (= (f3 ?v_0 (f5 (f6 f8 ?v1) (f5 (f6 f7 ?v0) ?v2))) f1) (= (f3 ?v_0 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f18 f36 ?v0)) (?v_1 (f6 f8 ?v2))) (=> (= (f3 ?v_0 ?v1) f1) (= (= (f3 ?v_0 (f5 ?v_1 ?v3)) f1) (= (f3 ?v_0 (f5 (f6 f8 (f5 ?v_1 (f5 (f6 f7 ?v4) ?v1))) ?v3)) f1))))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f3 (f18 f19 (f15 f16 ?v0)) (f15 f16 ?v1)) f1) (= (f31 (f32 f33 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f19 (f5 f11 ?v0)) f34) f1) (= (f3 (f18 f19 ?v0) f34) f1))))
(assert (= (= (f3 (f18 f19 f12) f34) f1) false))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f19 (f5 f10 ?v0)) f34) f1) (= (f3 (f18 f19 ?v0) f34) f1))))
(assert (= f34 (f5 f9 f12)))
(assert (= (f3 (f18 f19 f34) f14) f1))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f7 ?v2))) (=> (= (f3 (f18 f19 ?v0) ?v1) f1) (=> (= (f3 (f18 f19 f34) ?v2) f1) (= (f3 (f18 f19 (f5 ?v_0 ?v0)) (f5 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3)) (not (= (f5 (f6 f8 (f5 (f6 f8 f14) ?v0)) ?v0) f34))))
(assert (= (f15 f16 f17) f34))
(assert (forall ((?v0 S7)) (= (= (f15 f16 ?v0) f34) (= ?v0 f17))))
(assert (forall ((?v0 S7)) (not (= (f3 (f18 f19 (f15 f16 ?v0)) f34) f1))))
(assert (forall ((?v0 S3)) (let ((?v_1 (f5 f11 f12)) (?v_0 (f37 f38 ?v0))) (= (f5 (f6 f7 ?v0) (f15 ?v_0 (f28 f29 (f5 f10 ?v_1)))) (f15 ?v_0 (f28 f29 (f5 f11 ?v_1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f18 f19 f34) ?v0) f1) (= (= (f5 (f6 f7 ?v0) ?v1) f14) (and (= ?v0 f14) (= ?v1 f14))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f19 (f5 (f6 f8 (f5 (f6 f8 f14) ?v0)) ?v0)) f34) f1) (= (f3 (f18 f19 ?v0) f34) f1))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f15 f16 ?v0) (f15 f16 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S1) (?v1 S7) (?v2 S7)) (let ((?v_0 (= ?v0 f1))) (= (ite ?v_0 (f15 f16 ?v1) (f15 f16 ?v2)) (f15 f16 (ite ?v_0 ?v1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S7)) (let ((?v_0 (f6 f7 (f15 f16 ?v2)))) (=> (= (f3 (f18 f19 ?v0) ?v1) f1) (=> (= (f31 (f32 f33 f17) ?v2) f1) (= (f3 (f18 f19 (f5 ?v_0 ?v0)) (f5 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f5 f10 (f5 f11 f12)))) (let ((?v_0 (f28 f29 ?v_1))) (= (f15 (f37 f38 (f5 (f6 f8 ?v0) ?v1)) ?v_0) (f5 (f6 f8 (f5 (f6 f8 (f15 (f37 f38 ?v0) ?v_0)) (f5 (f6 f7 (f5 (f6 f7 (f5 f9 ?v_1)) ?v0)) ?v1))) (f15 (f37 f38 ?v1) ?v_0)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_3 (f5 f11 f12))) (let ((?v_5 (f28 f29 (f5 f10 ?v_3))) (?v_1 (f5 f11 ?v_3))) (let ((?v_0 (f28 f29 ?v_1)) (?v_2 (f37 f38 ?v0)) (?v_4 (f6 f7 (f5 f9 ?v_1))) (?v_6 (f37 f38 ?v1))) (= (f15 (f37 f38 (f5 (f6 f8 ?v0) ?v1)) ?v_0) (f5 (f6 f8 (f5 (f6 f8 (f5 (f6 f8 (f15 ?v_2 ?v_0)) (f5 (f6 f7 (f5 ?v_4 (f15 ?v_2 ?v_5))) ?v1))) (f5 (f6 f7 (f5 ?v_4 ?v0)) (f15 ?v_6 ?v_5)))) (f15 ?v_6 ?v_0))))))))
(assert (= f14 (f15 f16 f27)))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f5 (f6 f7 (f15 f16 ?v0)) (f15 f16 ?v1)) (f15 f16 (f24 (f25 f30 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f5 (f6 f8 (f15 f16 ?v0)) (f15 f16 ?v1)) (f15 f16 (f24 (f25 f26 ?v0) ?v1)))))
(assert (let ((?v_1 (f5 f10 (f5 f11 f12)))) (let ((?v_0 (f28 f29 ?v_1))) (= (f5 (f6 f8 (f15 (f37 f38 f41) ?v_0)) (f15 (f37 f38 f42) ?v_0)) (f5 (f6 f7 (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 ?v_1))) f13)) f14)) (f5 (f6 f8 f14) (f15 f16 f20)))))))
(assert (let ((?v_0 (f5 (f6 f8 f14) (f15 f16 f20)))) (and (= (f3 (f18 f43 f34) ?v_0) f1) (= (f3 (f18 f36 ?v_0) (f5 (f6 f8 (f5 (f6 f7 (f5 f9 (f5 f10 (f5 f10 (f5 f11 f12))))) f13)) f14)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f5 f10 (f5 f11 f12)))) (let ((?v_0 (f28 f29 ?v_1))) (= (f15 (f37 f38 (f5 (f6 f8 ?v0) ?v1)) ?v_0) (f5 (f6 f8 (f5 (f6 f8 (f15 (f37 f38 ?v0) ?v_0)) (f15 (f37 f38 ?v1) ?v_0))) (f5 (f6 f7 (f5 (f6 f7 (f5 f9 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f28 f29 (f5 f10 (f5 f11 f12))))) (= (f24 (f25 f44 (f24 (f25 f26 ?v0) ?v1)) ?v_0) (f24 (f25 f26 (f24 (f25 f26 (f24 (f25 f44 ?v0) ?v_0)) (f24 (f25 f44 ?v1) ?v_0))) (f24 (f25 f30 (f24 (f25 f30 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f28 f29 (f5 f10 (f5 f11 f12))))) (not (= (f3 (f18 f19 (f5 (f6 f8 (f15 (f37 f38 ?v0) ?v_0)) (f15 (f37 f38 ?v1) ?v_0))) f34) f1)))))
(assert (= (f3 (f18 f43 f14) f21) f1))
(assert (let ((?v_0 (f18 f36 (f5 (f6 f8 f14) (f15 f16 f20))))) (and (= (f3 ?v_0 f41) f1) (= (f3 ?v_0 f42) f1))))
(assert (let ((?v_0 (f28 f29 (f5 f10 (f5 f11 f12))))) (let ((?v_1 (f18 f36 (f15 (f37 f38 (f5 (f6 f8 f14) (f15 f16 f20))) ?v_0)))) (and (= (f3 ?v_1 (f15 (f37 f38 f41) ?v_0)) f1) (= (f3 ?v_1 (f15 (f37 f38 f42) ?v_0)) f1)))))
(assert (let ((?v_0 (f28 f29 (f5 f10 (f5 f11 f12))))) (= (f3 (f18 f36 (f15 (f37 f38 (f5 (f6 f8 f14) (f15 f16 f20))) ?v_0)) (f5 (f6 f8 (f15 (f37 f38 f41) ?v_0)) (f15 (f37 f38 f42) ?v_0))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 (f5 f9 ?v0)) (f5 f9 ?v1)) f1) (= (f3 (f18 f43 ?v0) ?v1) f1))))
(assert (= (f3 (f18 f43 f34) f34) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 (f5 f11 ?v0)) (f5 f11 ?v1)) f1) (= (f3 (f18 f43 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 (f5 f11 ?v0)) (f5 f11 ?v1)) f1) (= (f3 (f18 f43 ?v0) ?v1) f1))))
(assert (= (= (f3 (f18 f43 f12) f12) f1) true))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 (f5 f10 ?v0)) (f5 f10 ?v1)) f1) (= (f3 (f18 f43 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 (f5 f10 ?v0)) (f5 f10 ?v1)) f1) (= (f3 (f18 f43 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 ?v0) ?v1) f1) (and (= (f3 (f18 f43 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 (f5 f9 ?v0)) (f5 f9 ?v1)) f1) (= (f3 (f18 f43 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f8 ?v2))) (=> (= (f3 (f18 f43 ?v0) ?v1) f1) (= (f3 (f18 f43 (f5 ?v_0 ?v0)) (f5 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f18 f43 ?v0) ?v1) f1) (=> (= (f3 (f18 f43 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f18 f43 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f18 f43 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f3 (f18 f43 ?v0) ?v1) f1) (= (f3 (f18 f43 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f3 (f18 f43 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f43 (f5 f9 ?v0)) f34) f1) (= (f3 (f18 f43 ?v0) f12) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f43 f34) (f5 f9 ?v0)) f1) (= (f3 (f18 f43 f12) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f43 (f5 f9 ?v0)) f14) f1) (= (f3 (f18 f43 ?v0) (f5 f11 f12)) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f43 f14) (f5 f9 ?v0)) f1) (= (f3 (f18 f43 (f5 f11 f12)) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 (f5 (f6 f8 (f5 (f6 f7 ?v0) ?v0)) (f5 (f6 f7 ?v1) ?v1))) f34) f1) (and (= ?v0 f34) (= ?v1 f34)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f18 f43 f34) (f5 (f6 f8 (f5 (f6 f7 ?v0) ?v0)) (f5 (f6 f7 ?v1) ?v1))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f5 f9 ?v0)) (?v_0 (f5 f9 ?v1))) (= (= (f3 (f18 f43 ?v_1) ?v_0) f1) (not (= (f3 (f18 f19 ?v_0) ?v_1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f28 f29 ?v0)) (?v_0 (f28 f29 ?v1))) (= (= (f31 (f32 f45 ?v_1) ?v_0) f1) (not (= (f31 (f32 f33 ?v_0) ?v_1) f1))))))
(assert (forall ((?v0 S3)) (= (= (f28 f29 ?v0) f17) (= (f3 (f18 f43 ?v0) f12) f1))))
(assert (forall ((?v0 S3)) (= (= f17 (f28 f29 ?v0)) (= (f3 (f18 f43 ?v0) f12) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f18 f43 f12))) (= (= (f3 ?v_0 (f5 f11 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 (f5 f10 ?v0)) (f5 f11 ?v1)) f1) (= (f3 (f18 f43 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 (f5 f10 ?v0)) (f5 f11 ?v1)) f1) (= (f3 (f18 f43 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f43 (f5 f10 ?v0)) f12) f1) (= (f3 (f18 f43 ?v0) f12) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f18 f43 f12))) (= (= (f3 ?v_0 (f5 f10 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f15 (f37 f38 (f15 f16 ?v0)) ?v1) (f15 f16 (f24 (f25 f44 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f15 (f37 f38 (f15 f16 ?v0)) ?v1) (f15 f16 (f24 (f25 f44 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f15 f16 (f24 (f25 f44 ?v0) ?v1)) (f15 (f37 f38 (f15 f16 ?v0)) ?v1))))
(assert (= (f3 (f18 f43 f34) f14) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f18 f43 f34))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f5 (f6 f7 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f18 f43 f34))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f5 (f6 f8 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f18 f19 ?v0) ?v1) f1) (=> (= (f3 (f18 f43 ?v2) ?v3) f1) (= (f3 (f18 f19 (f5 (f6 f8 ?v0) ?v2)) (f5 (f6 f8 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S7)) (= (f3 (f18 f43 f34) (f15 f16 ?v0)) f1)))
(assert (forall ((?v0 S7)) (= (f3 (f18 f43 f34) (f15 f16 ?v0)) f1)))
(assert (forall ((?v0 S2)) (= (exists ((?v1 S3)) (and (= (f3 (f18 f43 f34) ?v1) f1) (= (f3 ?v0 ?v1) f1))) (exists ((?v1 S7)) (= (f3 ?v0 (f15 f16 ?v1)) f1)))))
(assert (forall ((?v0 S2)) (= (forall ((?v1 S3)) (=> (= (f3 (f18 f43 f34) ?v1) f1) (= (f3 ?v0 ?v1) f1))) (forall ((?v1 S7)) (= (f3 ?v0 (f15 f16 ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f18 f43 f34))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f18 f36 ?v0) ?v1) f1) (=> (= (f3 (f18 f36 ?v1) ?v0) f1) (= ?v0 ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S7)) (let ((?v_0 (f18 f43 f34))) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 (f15 (f37 f38 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 ?v0) ?v1) f1) (exists ((?v2 S7)) (= ?v1 (f5 (f6 f8 ?v0) (f15 f16 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f18 f43 f12))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f5 (f6 f7 (f5 f9 ?v0)) (f5 f9 ?v1)) (f5 f9 (f5 (f6 f7 ?v0) ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f18 f43 f12))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f24 (f25 f30 (f28 f29 ?v0)) (f28 f29 ?v1)) (f28 f29 (f5 (f6 f7 ?v0) ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f18 f43 f12))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f5 (f6 f8 (f5 f9 ?v0)) (f5 f9 ?v1)) (f5 f9 (f5 (f6 f8 ?v0) ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f18 f43 f12))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f24 (f25 f26 (f28 f29 ?v0)) (f28 f29 ?v1)) (f28 f29 (f5 (f6 f8 ?v0) ?v1))))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f43 (f5 f11 ?v0)) f12) f1) (= (f3 (f18 f19 ?v0) f12) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f19 f12) (f5 f11 ?v0)) f1) (= (f3 (f18 f43 f12) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 (f5 f11 ?v0)) (f5 f10 ?v1)) f1) (= (f3 (f18 f19 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 (f5 f11 ?v0)) (f5 f10 ?v1)) f1) (= (f3 (f18 f19 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 (f5 f10 ?v0)) (f5 f11 ?v1)) f1) (= (f3 (f18 f43 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 (f5 f10 ?v0)) (f5 f11 ?v1)) f1) (= (f3 (f18 f43 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f18 f43 f14) ?v0) f1) (= (f3 (f18 f19 f34) ?v0) f1))))
(assert (forall ((?v0 S7)) (= (= (f3 (f18 f43 (f15 f16 ?v0)) f34) f1) (= ?v0 f17))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f18 f19 ?v0) ?v1) f1) (= (f3 (f18 f43 (f5 (f6 f8 ?v0) f14)) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f43 (f5 (f6 f8 ?v0) f14)) ?v1) f1) (= (f3 (f18 f19 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 ?v0) (f5 (f6 f8 ?v1) f14)) f1) (= (f3 (f18 f43 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f18 f36 ?v0) ?v1) f1) (=> (= (f3 (f18 f19 f34) ?v1) f1) (= (f3 (f18 f43 ?v0) ?v1) f1)))))
(assert (= (f3 (f18 f43 f34) (f5 f9 (f5 f11 (f5 f11 f12)))) f1))
(assert (forall ((?v0 S3)) (=> (= (f3 (f18 f43 f34) ?v0) f1) (= (f3 (f18 f19 f34) (f5 (f6 f8 f14) ?v0)) f1))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f28 f29 (f5 f10 (f5 f11 f12)))) (?v_1 (f32 f45 f17))) (=> (= (f24 (f25 f44 ?v0) ?v_0) (f24 (f25 f44 ?v1) ?v_0)) (=> (= (f31 ?v_1 ?v0) f1) (=> (= (f31 ?v_1 ?v1) f1) (= ?v0 ?v1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f28 f29 (f5 f10 (f5 f11 f12)))) (?v_1 (f18 f43 f34))) (=> (= (f15 (f37 f38 ?v0) ?v_0) (f15 (f37 f38 ?v1) ?v_0)) (=> (= (f3 ?v_1 ?v0) f1) (=> (= (f3 ?v_1 ?v1) f1) (= ?v0 ?v1)))))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f28 f29 (f5 f10 (f5 f11 f12))))) (=> (= (f31 (f32 f45 (f24 (f25 f44 ?v0) ?v_0)) (f24 (f25 f44 ?v1) ?v_0)) f1) (=> (= (f31 (f32 f45 f17) ?v1) f1) (= (f31 (f32 f45 ?v0) ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f28 f29 (f5 f10 (f5 f11 f12))))) (=> (= (f3 (f18 f43 (f15 (f37 f38 ?v0) ?v_0)) (f15 (f37 f38 ?v1) ?v_0)) f1) (=> (= (f3 (f18 f43 f34) ?v1) f1) (= (f3 (f18 f43 ?v0) ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (f3 (f18 f43 f34) (f15 (f37 f38 ?v0) (f28 f29 (f5 f10 (f5 f11 f12))))) f1)))
(assert (forall ((?v0 S3)) (let ((?v_0 (f5 f9 ?v0))) (= (f15 f16 (f28 f29 ?v0)) (ite (= (f3 (f18 f43 f34) ?v_0) f1) ?v_0 f34)))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f28 f29 (f5 f10 (f5 f11 f12))))) (=> (= (f31 (f32 f33 (f24 (f25 f44 ?v0) ?v_0)) (f24 (f25 f44 ?v1) ?v_0)) f1) (=> (= (f31 (f32 f45 f17) ?v1) f1) (= (f31 (f32 f33 ?v0) ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f28 f29 (f5 f10 (f5 f11 f12))))) (=> (= (f3 (f18 f19 (f15 (f37 f38 ?v0) ?v_0)) (f15 (f37 f38 ?v1) ?v_0)) f1) (=> (= (f3 (f18 f43 f34) ?v1) f1) (= (f3 (f18 f19 ?v0) ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f28 f29 (f5 f10 (f5 f11 f12))))) (= (= (f3 (f18 f43 (f5 (f6 f8 (f15 (f37 f38 ?v0) ?v_0)) (f15 (f37 f38 ?v1) ?v_0))) f34) f1) (and (= ?v0 f34) (= ?v1 f34))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f28 f29 (f5 f10 (f5 f11 f12))))) (= (f3 (f18 f43 f34) (f5 (f6 f8 (f15 (f37 f38 ?v0) ?v_0)) (f15 (f37 f38 ?v1) ?v_0))) f1))))
(assert (= (f3 (f18 f43 f34) (f5 f9 (f5 f10 (f5 f11 f12)))) f1))
(assert (forall ((?v0 S3) (?v1 S7)) (= (f3 (f18 f43 f34) (f15 (f37 f38 ?v0) (f24 (f25 f30 (f28 f29 (f5 f10 (f5 f11 f12)))) ?v1))) f1)))
(assert (forall ((?v0 S3)) (= (f3 (f18 f43 ?v0) (f15 (f37 f38 ?v0) (f28 f29 (f5 f10 (f5 f11 f12))))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f5 (f6 f8 (f5 (f6 f7 ?v0) ?v0)) (f5 (f6 f7 ?v1) ?v1)) f34) (and (= ?v0 f34) (= ?v1 f34)))))
(assert (= f34 (f5 f9 f12)))
(assert (= (f28 f29 f12) f17))
(assert (= f17 (f28 f29 f12)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f18 f19 f34) (f5 (f6 f8 (f5 (f6 f7 ?v0) ?v0)) (f5 (f6 f7 ?v1) ?v1))) f1) (or (not (= ?v0 f34)) (not (= ?v1 f34))))))
(assert (forall ((?v0 S3) (?v1 S3)) (not (= (f3 (f18 f19 (f5 (f6 f8 (f5 (f6 f7 ?v0) ?v0)) (f5 (f6 f7 ?v1) ?v1))) f34) f1))))
(assert (= f14 (f5 f9 (f5 f11 f12))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f31 (f32 f33 (f28 f29 ?v0)) (f28 f29 ?v1)) f1) (ite (= (f3 (f18 f19 ?v0) ?v1) f1) (= (f3 (f18 f19 f12) ?v1) f1) false))))
(assert (= (f28 f29 (f5 f11 f12)) f27))
(assert (= f27 (f28 f29 (f5 f11 f12))))
(assert (forall ((?v0 S3)) (= (f15 (f37 f38 ?v0) (f28 f29 (f5 f11 (f5 f11 f12)))) (f5 (f6 f7 (f5 (f6 f7 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S7)) (= (f24 (f25 f44 ?v0) (f28 f29 (f5 f11 (f5 f11 f12)))) (f24 (f25 f30 (f24 (f25 f30 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S3)) (= (= (f31 (f32 f33 f17) (f28 f29 ?v0)) f1) (= (f3 (f18 f19 f12) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f28 f29 ?v0)) (?v_0 (f28 f29 ?v1))) (= (f24 (f25 f26 ?v_1) ?v_0) (ite (= (f3 (f18 f19 ?v0) f12) f1) ?v_0 (ite (= (f3 (f18 f19 ?v1) f12) f1) ?v_1 (f28 f29 (f5 (f6 f8 ?v0) ?v1))))))))
(assert (forall ((?v0 S3)) (= (= (f15 (f37 f38 ?v0) (f28 f29 (f5 f10 (f5 f11 f12)))) f34) (= ?v0 f34))))
(assert (= (f24 (f25 f44 f17) (f28 f29 (f5 f10 (f5 f11 f12)))) f17))
(assert (= (f15 (f37 f38 f34) (f28 f29 (f5 f10 (f5 f11 f12)))) f34))
(assert (forall ((?v0 S3)) (= (f15 (f37 f38 ?v0) (f28 f29 (f5 f10 (f5 f11 f12)))) (f5 (f6 f7 ?v0) ?v0))))
(assert (forall ((?v0 S7)) (= (f24 (f25 f44 ?v0) (f28 f29 (f5 f10 (f5 f11 f12)))) (f24 (f25 f30 ?v0) ?v0))))
(assert (= (f15 (f37 f38 f14) (f28 f29 (f5 f10 (f5 f11 f12)))) f14))
(assert (= (f24 (f25 f44 f27) (f28 f29 (f5 f10 (f5 f11 f12)))) f27))
(assert (forall ((?v0 S3) (?v1 S7)) (let ((?v_1 (f28 f29 (f5 f10 (f5 f11 f12)))) (?v_0 (f37 f38 ?v0))) (= (f15 ?v_0 (f24 (f25 f30 ?v_1) ?v1)) (f15 (f37 f38 (f15 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_1 (f28 f29 (f5 f10 (f5 f11 f12)))) (?v_0 (f25 f44 ?v0))) (= (f24 ?v_0 (f24 (f25 f30 ?v_1) ?v1)) (f24 (f25 f44 (f24 ?v_0 ?v1)) ?v_1)))))
(check-sat)
(exit)
