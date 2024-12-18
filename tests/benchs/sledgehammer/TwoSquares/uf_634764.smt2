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
(declare-fun f3 () S1)
(declare-fun f4 (S3 S2) S1)
(declare-fun f5 (S4 S2) S3)
(declare-fun f6 () S4)
(declare-fun f7 () S2)
(declare-fun f8 () S4)
(declare-fun f9 (S5 S2) S2)
(declare-fun f10 (S6 S2) S5)
(declare-fun f11 () S6)
(declare-fun f12 () S6)
(declare-fun f13 () S5)
(declare-fun f14 () S5)
(declare-fun f15 () S5)
(declare-fun f16 () S2)
(declare-fun f17 () S2)
(declare-fun f18 () S2)
(declare-fun f19 (S7 S2) S4)
(declare-fun f20 () S7)
(declare-fun f21 () S2)
(declare-fun f22 () S3)
(declare-fun f23 (S8 S9) S9)
(declare-fun f24 (S10 S9) S8)
(declare-fun f25 () S10)
(declare-fun f26 () S9)
(declare-fun f27 (S11 S2) S9)
(declare-fun f28 () S11)
(declare-fun f29 (S12 S9) S1)
(declare-fun f30 (S13 S9) S12)
(declare-fun f31 () S13)
(declare-fun f32 () S13)
(declare-fun f33 () S10)
(declare-fun f34 () S9)
(declare-fun f35 (S14 S9) S2)
(declare-fun f36 (S15 S2) S14)
(declare-fun f37 () S15)
(declare-fun f38 () S2)
(declare-fun f39 () S6)
(declare-fun f40 () S10)
(assert (not (= f1 f2)))
(assert (not (= f3 f1)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f9 (f10 f11 (f9 (f10 f12 (f9 f13 (f9 f14 (f9 f14 (f9 f15 f16))))) f17)) f18))) (=> (and (= (f4 (f5 f6 f7) ?v0) f1) (and (= (f4 (f5 f8 ?v0) ?v_0) f1) (= (f4 (f5 (f19 f20 f21) ?v0) ?v_0) f1))) (= f3 f1)))))
(assert (exists ((?v0 S2)) (let ((?v_0 (f9 (f10 f11 (f9 (f10 f12 (f9 f13 (f9 f14 (f9 f14 (f9 f15 f16))))) f17)) f18))) (and (and (= (f4 (f5 f6 f7) ?v0) f1) (and (= (f4 (f5 f8 ?v0) ?v_0) f1) (= (f4 (f5 (f19 f20 f21) ?v0) ?v_0) f1))) (forall ((?v1 S2)) (=> (and (= (f4 (f5 f6 f7) ?v1) f1) (and (= (f4 (f5 f8 ?v1) ?v_0) f1) (= (f4 (f5 (f19 f20 f21) ?v1) ?v_0) f1))) (= ?v1 ?v0)))))))
(assert (exists ((?v0 S2)) (let ((?v_0 (f9 (f10 f11 (f9 (f10 f12 (f9 f13 (f9 f14 (f9 f14 (f9 f15 f16))))) f17)) f18))) (and (and (= (f4 (f5 f6 f7) ?v0) f1) (and (= (f4 (f5 f8 ?v0) ?v_0) f1) (= (f4 (f5 (f19 f20 f21) ?v0) ?v_0) f1))) (forall ((?v1 S2)) (=> (and (= (f4 (f5 f6 f7) ?v1) f1) (and (= (f4 (f5 f8 ?v1) ?v_0) f1) (= (f4 (f5 (f19 f20 f21) ?v1) ?v_0) f1))) (= ?v1 ?v0)))))))
(assert (= (f4 (f5 f8 f7) (f9 (f10 f11 (f9 (f10 f12 (f9 f13 (f9 f14 (f9 f14 (f9 f15 f16))))) f17)) f18)) f1))
(assert (= (f4 f22 (f9 (f10 f11 (f9 (f10 f12 (f9 f13 (f9 f14 (f9 f14 (f9 f15 f16))))) f17)) f18)) f1))
(assert (forall ((?v0 S2)) (=> (= (f4 (f5 f6 f7) ?v0) f1) (=> (= (f4 (f5 f8 ?v0) (f9 f13 (f9 f14 (f9 f15 f16)))) f1) (or (= ?v0 f7) (= ?v0 f18))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f5 f8 f7) ?v0) f1) (=> (= ?v0 (f9 (f10 f11 ?v1) (f9 (f10 f12 ?v0) ?v2))) (=> (= (f4 (f5 f6 f7) ?v1) f1) (= (f4 (f5 f6 ?v2) f18) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f5 f8 f7) ?v0) f1) (=> (= ?v0 (f9 (f10 f11 ?v1) (f9 (f10 f12 ?v0) ?v2))) (=> (= (f4 (f5 f8 ?v1) ?v0) f1) (= (f4 (f5 f6 f18) ?v2) f1))))))
(assert (= (f4 (f5 f6 f7) (f9 f13 (f9 f14 (f9 f15 f16)))) f1))
(assert (forall ((?v0 S2)) (= (f9 (f10 f11 f18) (f9 f13 ?v0)) (f9 f13 (f9 (f10 f11 (f9 f15 f16)) ?v0)))))
(assert (forall ((?v0 S2)) (= (f9 (f10 f11 (f9 f13 ?v0)) f18) (f9 f13 (f9 (f10 f11 ?v0) (f9 f15 f16))))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f6 f18) (f9 f13 ?v0)) f1) (= (f4 (f5 f6 (f9 f15 f16)) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f6 (f9 f13 ?v0)) f18) f1) (= (f4 (f5 f6 ?v0) (f9 f15 f16)) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 f18) (f9 f13 ?v0)) f1) (= (f4 (f5 f8 (f9 f15 f16)) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 (f9 f13 ?v0)) f18) f1) (= (f4 (f5 f8 ?v0) (f9 f15 f16)) f1))))
(assert (= (f9 (f10 f11 f18) f18) (f9 f13 (f9 f14 (f9 f15 f16)))))
(assert (= (f9 (f10 f11 f18) f18) (f9 f13 (f9 f14 (f9 f15 f16)))))
(assert (= (f23 (f24 f25 f26) f26) (f27 f28 (f9 f14 (f9 f15 f16)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f9 f13 ?v0) (f9 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f9 f13 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S9)) (let ((?v_0 (f27 f28 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f9 f15 ?v0) (f9 f15 ?v1)) (= ?v0 ?v1))))
(assert (= (= f16 f16) true))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f9 f14 ?v0) (f9 f14 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f4 (f5 f8 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f4 (f5 f8 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f5 f6 ?v0) ?v1) f1) (=> (= (f4 (f5 f6 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 ?v0))) (=> (= (f4 ?v_0 ?v1) f1) (=> (= (f4 (f5 f6 ?v1) ?v2) f1) (= (f4 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f4 (f5 f6 ?v0) ?v1) f1) (= (f4 (f5 f6 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f10 f12 ?v0))) (= (f9 (f10 f12 (f9 ?v_0 ?v1)) ?v2) (f9 ?v_0 (f9 (f10 f12 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f10 f12 ?v0) ?v1) (f9 (f10 f12 ?v1) ?v0))))
(assert (forall ((?v0 S2)) (= (f9 f13 ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f10 f11 ?v0))) (= (f9 (f10 f11 (f9 ?v_0 ?v1)) ?v2) (f9 ?v_0 (f9 (f10 f11 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f10 f11 ?v0)) (?v_0 (f10 f11 ?v1))) (= (f9 ?v_1 (f9 ?v_0 ?v2)) (f9 ?v_0 (f9 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f10 f11 ?v0) ?v1) (f9 (f10 f11 ?v1) ?v0))))
(assert (forall ((?v0 S2)) (= (= (f9 (f10 f11 ?v0) ?v0) f7) (= ?v0 f7))))
(assert (forall ((?v0 S2)) (= (= (f9 f15 ?v0) f16) false)))
(assert (forall ((?v0 S2)) (= (= f16 (f9 f15 ?v0)) false)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f9 f15 ?v0) (f9 f14 ?v1)) false)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f9 f14 ?v0) (f9 f15 ?v1)) false)))
(assert (= f16 f7))
(assert (forall ((?v0 S2)) (= (= (f9 f14 ?v0) f16) (= ?v0 f16))))
(assert (forall ((?v0 S2)) (= (= f16 (f9 f14 ?v0)) (= f16 ?v0))))
(assert (= (f9 f14 f16) f16))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f8 (f9 f15 ?v0)) (f9 f15 ?v1)) f1) (= (f4 (f5 f8 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f8 (f9 f15 ?v0)) (f9 f15 ?v1)) f1) (= (f4 (f5 f8 ?v0) ?v1) f1))))
(assert (= (= (f4 (f5 f8 f16) f16) f1) false))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f8 (f9 f14 ?v0)) (f9 f14 ?v1)) f1) (= (f4 (f5 f8 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f8 (f9 f14 ?v0)) (f9 f14 ?v1)) f1) (= (f4 (f5 f8 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f6 (f9 f15 ?v0)) (f9 f15 ?v1)) f1) (= (f4 (f5 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f6 (f9 f15 ?v0)) (f9 f15 ?v1)) f1) (= (f4 (f5 f6 ?v0) ?v1) f1))))
(assert (= (= (f4 (f5 f6 f16) f16) f1) true))
(assert (= (f4 (f5 f6 f7) f7) f1))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f6 (f9 f14 ?v0)) (f9 f14 ?v1)) f1) (= (f4 (f5 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f6 (f9 f14 ?v0)) (f9 f14 ?v1)) f1) (= (f4 (f5 f6 ?v0) ?v1) f1))))
(assert (not (= f7 f18)))
(assert (forall ((?v0 S2)) (= (f9 (f10 f12 f16) ?v0) f16)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f10 f12 (f9 f14 ?v0)) ?v1) (f9 f14 (f9 (f10 f12 ?v0) ?v1)))))
(assert (forall ((?v0 S2)) (= (f9 (f10 f11 ?v0) f16) ?v0)))
(assert (forall ((?v0 S2)) (= (f9 (f10 f11 f16) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f8 ?v0) ?v1) f1) (and (= (f4 (f5 f6 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S2)) (= (f9 (f10 f11 ?v0) f7) ?v0)))
(assert (forall ((?v0 S2)) (= (f9 (f10 f11 f7) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f10 f11 (f9 f14 ?v0)) (f9 f14 ?v1)) (f9 f14 (f9 (f10 f11 ?v0) ?v1)))))
(assert (forall ((?v0 S2)) (= (f9 f14 ?v0) (f9 (f10 f11 ?v0) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f8 (f9 f13 ?v0)) (f9 f13 ?v1)) f1) (= (f4 (f5 f8 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2)) (= (f9 (f10 f12 ?v0) f18) ?v0)))
(assert (forall ((?v0 S2)) (= (f9 (f10 f12 f18) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f6 (f9 f13 ?v0)) (f9 f13 ?v1)) f1) (= (f4 (f5 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f5 f8 ?v0) ?v1) f1) (= (f4 (f5 f8 (f9 (f10 f11 ?v0) ?v2)) (f9 (f10 f11 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f10 f12 (f9 f13 ?v0)) (f9 f13 ?v1)) (f9 f13 (f9 (f10 f12 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f10 f11 ?v2))) (=> (= (f4 (f5 f6 ?v0) ?v1) f1) (= (f4 (f5 f6 (f9 ?v_0 ?v0)) (f9 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f9 (f10 f12 (f9 (f10 f11 ?v0) ?v1)) ?v2) (f9 (f10 f11 (f9 (f10 f12 ?v0) ?v2)) (f9 (f10 f12 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f10 f12 ?v0))) (= (f9 ?v_0 (f9 (f10 f11 ?v1) ?v2)) (f9 (f10 f11 (f9 ?v_0 ?v1)) (f9 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f10 f11 (f9 f13 ?v0)) (f9 f13 ?v1)) (f9 f13 (f9 (f10 f11 ?v0) ?v1)))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 (f9 (f10 f11 ?v0) ?v0)) f7) f1) (= (f4 (f5 f8 ?v0) f7) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f9 f13 ?v0)) (?v_0 (f9 f13 ?v1))) (= (= (f4 (f5 f6 ?v_1) ?v_0) f1) (not (= (f4 (f5 f8 ?v_0) ?v_1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f27 f28 ?v0)) (?v_0 (f27 f28 ?v1))) (= (= (f29 (f30 f31 ?v_1) ?v_0) f1) (not (= (f29 (f30 f32 ?v_0) ?v_1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f9 f13 ?v2))) (= (f9 (f10 f12 (f9 (f10 f11 ?v0) ?v1)) ?v_0) (f9 (f10 f11 (f9 (f10 f12 ?v0) ?v_0)) (f9 (f10 f12 ?v1) ?v_0))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S2)) (let ((?v_0 (f27 f28 ?v2))) (= (f23 (f24 f33 (f23 (f24 f25 ?v0) ?v1)) ?v_0) (f23 (f24 f25 (f23 (f24 f33 ?v0) ?v_0)) (f23 (f24 f33 ?v1) ?v_0))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f10 f12 (f9 f13 ?v0)))) (= (f9 ?v_0 (f9 (f10 f11 ?v1) ?v2)) (f9 (f10 f11 (f9 ?v_0 ?v1)) (f9 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S9) (?v2 S9)) (let ((?v_0 (f24 f33 (f27 f28 ?v0)))) (= (f23 ?v_0 (f23 (f24 f25 ?v1) ?v2)) (f23 (f24 f25 (f23 ?v_0 ?v1)) (f23 ?v_0 ?v2))))))
(assert (= (f9 f13 f16) f7))
(assert (= (f27 f28 f16) f34))
(assert (= (f9 f13 f16) f7))
(assert (forall ((?v0 S2)) (= (f9 (f10 f11 (f9 f13 f16)) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f9 (f10 f11 ?v0) (f9 f13 f16)) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f8 (f9 f13 ?v0)) (f9 f13 ?v1)) f1) (= (f4 (f5 f8 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f6 (f9 f13 ?v0)) (f9 f13 ?v1)) f1) (= (f4 (f5 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f9 (f10 f12 (f9 f13 ?v0)) (f9 (f10 f12 (f9 f13 ?v1)) ?v2)) (f9 (f10 f12 (f9 f13 (f9 (f10 f12 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f10 f12 (f9 f13 ?v0)) (f9 f13 ?v1)) (f9 f13 (f9 (f10 f12 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 f13 (f9 (f10 f12 ?v0) ?v1)) (f9 (f10 f12 (f9 f13 ?v0)) (f9 f13 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f9 (f10 f11 (f9 f13 ?v0)) (f9 (f10 f11 (f9 f13 ?v1)) ?v2)) (f9 (f10 f11 (f9 f13 (f9 (f10 f11 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f10 f11 (f9 f13 ?v0)) (f9 f13 ?v1)) (f9 f13 (f9 (f10 f11 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 f13 (f9 (f10 f11 ?v0) ?v1)) (f9 (f10 f11 (f9 f13 ?v0)) (f9 f13 ?v1)))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 (f9 f15 ?v0)) f16) f1) (= (f4 (f5 f8 ?v0) f16) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 (f9 f15 ?v0)) f7) f1) (= (f4 (f5 f8 ?v0) f7) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f8 (f9 f15 ?v0)) (f9 f14 ?v1)) f1) (= (f4 (f5 f8 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f8 (f9 f15 ?v0)) (f9 f14 ?v1)) f1) (= (f4 (f5 f8 ?v0) ?v1) f1))))
(assert (= (= (f4 (f5 f8 f16) f7) f1) false))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 (f9 f14 ?v0)) f16) f1) (= (f4 (f5 f8 ?v0) f16) f1))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f8 f16))) (= (= (f4 ?v_0 (f9 f14 ?v0)) f1) (= (f4 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 (f9 f14 ?v0)) f7) f1) (= (f4 (f5 f8 ?v0) f7) f1))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f6 f16))) (= (= (f4 ?v_0 (f9 f15 ?v0)) f1) (= (f4 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f6 (f9 f14 ?v0)) (f9 f15 ?v1)) f1) (= (f4 (f5 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f6 (f9 f14 ?v0)) (f9 f15 ?v1)) f1) (= (f4 (f5 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f6 (f9 f14 ?v0)) f16) f1) (= (f4 (f5 f6 ?v0) f16) f1))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f6 f16))) (= (= (f4 ?v_0 (f9 f14 ?v0)) f1) (= (f4 ?v_0 ?v0) f1)))))
(assert (= f7 (f9 f13 f16)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f10 f11 (f9 f15 ?v0)) (f9 f14 ?v1)) (f9 f15 (f9 (f10 f11 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f10 f11 (f9 f14 ?v0)) (f9 f15 ?v1)) (f9 f15 (f9 (f10 f11 ?v0) ?v1)))))
(assert (= (f4 (f5 f8 f7) f18) f1))
(assert (= (f4 (f5 f6 f7) f18) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f10 f12 ?v2))) (=> (= (f4 (f5 f8 ?v0) ?v1) f1) (=> (= (f4 (f5 f8 f7) ?v2) f1) (= (f4 (f5 f8 (f9 ?v_0 ?v0)) (f9 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f5 f6 f7))) (=> (= (f4 ?v_0 ?v0) f1) (=> (= (f4 ?v_0 ?v1) f1) (= (f4 ?v_0 (f9 (f10 f12 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S2)) (= (f9 f15 ?v0) (f9 (f10 f11 (f9 (f10 f11 f18) ?v0)) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f5 f6 f7))) (=> (= (f4 ?v_0 ?v0) f1) (=> (= (f4 ?v_0 ?v1) f1) (= (f4 ?v_0 (f9 (f10 f11 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S2)) (not (= (f9 (f10 f11 (f9 (f10 f11 f18) ?v0)) ?v0) f7))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f4 (f5 f8 ?v0) ?v1) f1) (=> (= (f4 (f5 f6 ?v2) ?v3) f1) (= (f4 (f5 f8 (f9 (f10 f11 ?v0) ?v2)) (f9 (f10 f11 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f5 f8 ?v0))) (= (= (f4 ?v_0 (f9 (f10 f11 ?v1) f18)) f1) (or (= (f4 ?v_0 ?v1) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f9 f13 ?v0))) (= (f9 f13 (f9 f14 ?v0)) (f9 (f10 f11 (f9 (f10 f11 f7) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f9 f13 ?v0))) (= (f9 f13 (f9 f15 ?v0)) (f9 (f10 f11 (f9 (f10 f11 f18) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S2)) (= (f9 (f10 f12 (f9 f13 (f9 f15 f16))) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f9 (f10 f12 ?v0) (f9 f13 (f9 f15 f16))) ?v0)))
(assert (= (f9 f13 (f9 f15 f16)) f18))
(assert (= (f27 f28 (f9 f15 f16)) f26))
(assert (= (f9 f13 (f9 f15 f16)) f18))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f6 (f9 f15 ?v0)) f16) f1) (= (f4 (f5 f8 ?v0) f16) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 f16) (f9 f15 ?v0)) f1) (= (f4 (f5 f6 f16) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f6 (f9 f15 ?v0)) (f9 f14 ?v1)) f1) (= (f4 (f5 f8 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f6 (f9 f15 ?v0)) (f9 f14 ?v1)) f1) (= (f4 (f5 f8 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f8 (f9 f14 ?v0)) (f9 f15 ?v1)) f1) (= (f4 (f5 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f8 (f9 f14 ?v0)) (f9 f15 ?v1)) f1) (= (f4 (f5 f6 ?v0) ?v1) f1))))
(assert (= f18 (f9 f13 (f9 f15 f16))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f6 f18) ?v0) f1) (= (f4 (f5 f8 f7) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f10 f12 (f9 f15 ?v0)) ?v1) (f9 (f10 f11 (f9 f14 (f9 (f10 f12 ?v0) ?v1))) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f5 f8 f7) ?v0) f1) (= (= (f9 (f10 f12 ?v0) ?v1) f18) (and (= ?v0 f18) (= ?v1 f18))))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 (f9 (f10 f11 (f9 (f10 f11 f18) ?v0)) ?v0)) f7) f1) (= (f4 (f5 f8 ?v0) f7) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f5 f8 ?v0) ?v1) f1) (= (f4 (f5 f6 (f9 (f10 f11 ?v0) f18)) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f6 (f9 (f10 f11 ?v0) f18)) ?v1) f1) (= (f4 (f5 f8 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f8 ?v0) (f9 (f10 f11 ?v1) f18)) f1) (= (f4 (f5 f6 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2)) (= (f9 (f10 f12 (f9 (f10 f11 f18) f18)) (f9 f13 ?v0)) (f9 f13 (f9 f14 ?v0)))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 (f9 f13 ?v0)) f7) f1) (= (f4 (f5 f8 ?v0) f16) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 f7) (f9 f13 ?v0)) f1) (= (f4 (f5 f8 f16) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f6 (f9 f13 ?v0)) f7) f1) (= (f4 (f5 f6 ?v0) f16) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f6 f7) (f9 f13 ?v0)) f1) (= (f4 (f5 f6 f16) ?v0) f1))))
(assert (= (f4 (f5 f6 f7) (f9 f13 (f9 f15 (f9 f15 f16)))) f1))
(assert (forall ((?v0 S2)) (=> (= (f4 (f5 f6 f7) ?v0) f1) (= (f4 (f5 f8 f7) (f9 (f10 f11 f18) ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2) (?v5 S2)) (let ((?v_0 (f9 (f10 f11 (f9 (f10 f12 ?v3) ?v4)) ?v5))) (=> (= (f9 (f10 f11 (f9 (f10 f12 ?v0) ?v1)) ?v2) ?v_0) (=> (= (f4 (f5 f8 ?v_0) f7) f1) (=> (= (f4 (f5 f8 ?v2) ?v0) f1) (=> (= (f4 (f5 f6 f7) ?v5) f1) (=> (= (f4 (f5 f8 f7) ?v3) f1) (=> (= (f4 (f5 f6 ?v3) ?v0) f1) (= (f4 (f5 f6 ?v4) ?v1) f1))))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (let ((?v_0 (f10 f12 ?v0)) (?v_1 (f5 f8 ?v0))) (=> (= (f4 (f5 f6 (f9 (f10 f11 (f9 ?v_0 ?v1)) ?v2)) (f9 (f10 f11 (f9 ?v_0 ?v3)) ?v4)) f1) (=> (= (f4 (f5 f6 ?v4) f7) f1) (=> (= (f4 ?v_1 ?v4) f1) (=> (= (f4 ?v_1 ?v2) f1) (= (f4 (f5 f6 ?v3) ?v1) f1))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2) (?v5 S2)) (let ((?v_1 (f5 f6 f7)) (?v_0 (f9 (f10 f11 (f9 (f10 f12 ?v3) ?v4)) ?v5))) (=> (= (f9 (f10 f11 (f9 (f10 f12 ?v0) ?v1)) ?v2) ?v_0) (=> (= (f4 ?v_1 ?v_0) f1) (=> (= (f4 (f5 f8 ?v5) ?v3) f1) (=> (= (f4 ?v_1 ?v2) f1) (=> (= (f4 (f5 f8 f7) ?v3) f1) (=> (= (f4 (f5 f6 ?v3) ?v0) f1) (= (f4 (f5 f6 ?v1) ?v4) f1))))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (let ((?v_0 (f10 f12 ?v0))) (=> (= (f4 (f5 f6 (f9 (f10 f11 (f9 ?v_0 ?v1)) ?v2)) (f9 (f10 f11 (f9 ?v_0 ?v3)) ?v4)) f1) (=> (= (f4 (f5 f6 f7) ?v2) f1) (=> (= (f4 (f5 f8 ?v2) ?v0) f1) (=> (= (f4 (f5 f8 ?v4) ?v0) f1) (= (f4 (f5 f6 ?v1) ?v3) f1))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 (f5 f8 (f9 (f10 f11 (f9 (f10 f12 ?v0) ?v1)) ?v2)) f7) f1) (=> (= (f4 (f5 f6 f7) ?v2) f1) (=> (= (f4 (f5 f8 f7) ?v0) f1) (= (f4 (f5 f6 ?v1) f7) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f6 f7))) (=> (= (f4 ?v_0 (f9 (f10 f11 (f9 (f10 f12 ?v0) ?v1)) ?v2)) f1) (=> (= (f4 (f5 f8 ?v2) ?v0) f1) (=> (= (f4 (f5 f8 f7) ?v0) f1) (= (f4 ?v_0 ?v1) f1)))))))
(assert (forall ((?v0 S2)) (= (f9 (f10 f12 (f9 f13 (f9 f14 (f9 f15 f16)))) ?v0) (f9 (f10 f11 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f23 (f24 f33 (f27 f28 (f9 f14 (f9 f15 f16)))) ?v0) (f23 (f24 f25 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f9 (f10 f12 (f9 f13 (f9 f14 (f9 f15 f16)))) ?v0) (f9 (f10 f11 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f9 (f10 f12 ?v0) (f9 f13 (f9 f14 (f9 f15 f16)))) (f9 (f10 f11 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f23 (f24 f33 ?v0) (f27 f28 (f9 f14 (f9 f15 f16)))) (f23 (f24 f25 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f9 (f10 f12 ?v0) (f9 f13 (f9 f14 (f9 f15 f16)))) (f9 (f10 f11 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f9 f15 f16))) (let ((?v_1 (f9 f14 ?v_0))) (=> (= (f4 f22 ?v0) f1) (=> (not (= ?v0 (f9 f13 ?v_1))) (=> (not (= ?v0 (f9 f13 (f9 f15 ?v_0)))) (= (f4 (f5 f6 (f9 f13 (f9 f15 ?v_1))) ?v0) f1))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (let ((?v_0 (f5 f6 f7))) (=> (= (f4 (f5 f8 ?v0) ?v1) f1) (=> (= (f4 (f5 f8 ?v2) ?v1) f1) (=> (= (f4 ?v_0 ?v3) f1) (=> (= (f4 ?v_0 ?v4) f1) (=> (= (f9 (f10 f11 ?v3) ?v4) f18) (= (f4 (f5 f8 (f9 (f10 f11 (f9 (f10 f12 ?v3) ?v0)) (f9 (f10 f12 ?v4) ?v2))) ?v1) f1)))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 f22 ?v0) f1) (=> (= (f4 (f5 f8 f7) ?v1) f1) (=> (= (f4 (f5 (f19 f20 (f9 (f10 f12 ?v1) ?v2)) f7) ?v0) f1) (or (= (f4 (f5 (f19 f20 ?v1) f7) ?v0) f1) (= (f4 (f5 (f19 f20 ?v2) f7) ?v0) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f4 f22 ?v0) f1) (=> (= (f4 (f5 f8 f7) ?v1) f1) (=> (and (not (= (f4 (f5 (f19 f20 ?v1) f7) ?v0) f1)) (not (= (f4 (f5 (f19 f20 ?v2) f7) ?v0) f1))) (not (= (f4 (f5 (f19 f20 (f9 (f10 f12 ?v1) ?v2)) f7) ?v0) f1)))))))
(assert (= (f4 f22 (f9 f13 (f9 f14 (f9 f15 f16)))) f1))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f6 f7))) (=> (= (f4 ?v_0 (f9 f13 ?v0)) f1) (and (= (f4 ?v_0 (f9 f13 (f9 f14 ?v0))) f1) (= (f4 ?v_0 (f9 f13 (f9 f15 ?v0))) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f5 f6 f16))) (=> (= (f4 ?v_0 ?v0) f1) (=> (= (f4 ?v_0 ?v1) f1) (= (f9 (f10 f11 (f9 f13 ?v0)) (f9 f13 ?v1)) (f9 f13 (f9 (f10 f11 ?v0) ?v1))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f5 f6 f16))) (=> (= (f4 ?v_0 ?v0) f1) (=> (= (f4 ?v_0 ?v1) f1) (= (f23 (f24 f25 (f27 f28 ?v0)) (f27 f28 ?v1)) (f27 f28 (f9 (f10 f11 ?v0) ?v1))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f5 f6 f16))) (=> (= (f4 ?v_0 ?v0) f1) (=> (= (f4 ?v_0 ?v1) f1) (= (f9 (f10 f12 (f9 f13 ?v0)) (f9 f13 ?v1)) (f9 f13 (f9 (f10 f12 ?v0) ?v1))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f5 f6 f16))) (=> (= (f4 ?v_0 ?v0) f1) (=> (= (f4 ?v_0 ?v1) f1) (= (f23 (f24 f33 (f27 f28 ?v0)) (f27 f28 ?v1)) (f27 f28 (f9 (f10 f12 ?v0) ?v1))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (let ((?v_0 (f5 f6 f7))) (=> (= (f4 (f5 f6 ?v0) ?v1) f1) (=> (= (f4 (f5 f6 ?v2) ?v1) f1) (=> (= (f4 ?v_0 ?v3) f1) (=> (= (f4 ?v_0 ?v4) f1) (=> (= (f9 (f10 f11 ?v3) ?v4) f18) (= (f4 (f5 f6 (f9 (f10 f11 (f9 (f10 f12 ?v3) ?v0)) (f9 (f10 f12 ?v4) ?v2))) ?v1) f1)))))))))
(assert (let ((?v_0 (f9 f14 (f9 f15 f16)))) (= (f4 (f5 (f19 f20 (f35 (f36 f37 f21) (f27 f28 ?v_0))) (f9 f13 f38)) (f9 (f10 f11 (f9 (f10 f12 (f9 f13 (f9 f14 ?v_0))) f17)) f18)) f1)))
(assert (=> (forall ((?v0 S2)) (let ((?v_0 (f9 f14 (f9 f15 f16)))) (=> (= (f4 (f5 (f19 f20 (f35 (f36 f37 ?v0) (f27 f28 ?v_0))) (f9 f13 f38)) (f9 (f10 f11 (f9 (f10 f12 (f9 f13 (f9 f14 ?v_0))) f17)) f18)) f1) false))) false))
(assert (= (f9 (f10 f39 (f9 f13 f38)) (f9 (f10 f11 (f9 (f10 f12 (f9 f13 (f9 f14 (f9 f14 (f9 f15 f16))))) f17)) f18)) f18))
(assert (= (= f38 f38) true))
(assert (forall ((?v0 S2) (?v1 S9) (?v2 S9)) (let ((?v_0 (f36 f37 ?v0))) (= (f35 (f36 f37 (f35 ?v_0 ?v1)) ?v2) (f35 ?v_0 (f23 (f24 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S9)) (=> (= (f4 (f5 (f19 f20 ?v0) ?v1) ?v2) f1) (= (f4 (f5 (f19 f20 (f35 (f36 f37 ?v0) ?v3)) (f35 (f36 f37 ?v1) ?v3)) ?v2) f1))))
(assert (= (f27 f28 f16) f34))
(assert (= f34 (f27 f28 f16)))
(assert (forall ((?v0 S2) (?v1 S9) (?v2 S2) (?v3 S9)) (let ((?v_0 (f36 f37 ?v0))) (=> (= (f4 (f5 (f19 f20 (f35 ?v_0 ?v1)) f18) ?v2) f1) (= (f4 (f5 (f19 f20 (f35 ?v_0 (f23 (f24 f33 ?v1) ?v3))) f18) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f27 f28 ?v1))) (= (= (f35 (f36 f37 ?v0) ?v_0) f7) (and (= ?v0 f7) (not (= ?v_0 f34)))))))
(assert (forall ((?v0 S9) (?v1 S2)) (let ((?v_0 (f27 f28 ?v1))) (= (= (f23 (f24 f40 ?v0) ?v_0) f34) (and (= ?v0 f34) (not (= ?v_0 f34)))))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_1 (f27 f28 (f9 f14 (f9 f15 f16)))) (?v_0 (f24 f40 ?v0))) (= (f23 ?v_0 (f23 (f24 f33 ?v_1) ?v1)) (f23 (f24 f40 (f23 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S9)) (let ((?v_1 (f27 f28 (f9 f14 (f9 f15 f16)))) (?v_0 (f36 f37 ?v0))) (= (f35 ?v_0 (f23 (f24 f33 ?v_1) ?v1)) (f35 (f36 f37 (f35 ?v_0 ?v1)) ?v_1)))))
(assert (= (f9 f15 f38) f38))
(assert (forall ((?v0 S2)) (= (= f38 (f9 f15 ?v0)) (= f38 ?v0))))
(assert (forall ((?v0 S2)) (= (= (f9 f15 ?v0) f38) (= ?v0 f38))))
(assert (= (= f38 f16) false))
(assert (= (= f16 f38) false))
(assert (forall ((?v0 S2)) (= (= f38 (f9 f14 ?v0)) false)))
(assert (forall ((?v0 S2)) (= (= (f9 f14 ?v0) f38) false)))
(assert (forall ((?v0 S2) (?v1 S9) (?v2 S9)) (let ((?v_0 (f36 f37 ?v0))) (= (f35 ?v_0 (f23 (f24 f25 ?v1) ?v2)) (f9 (f10 f12 (f35 ?v_0 ?v1)) (f35 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f23 (f24 f33 (f27 f28 ?v0)) (f27 f28 ?v1)) (ite (= (f4 (f5 f8 ?v0) f16) f1) f34 (f27 f28 (f9 (f10 f12 ?v0) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S9)) (= (f23 (f24 f33 (f27 f28 ?v0)) (f23 (f24 f33 (f27 f28 ?v1)) ?v2)) (ite (= (f4 (f5 f8 ?v0) f16) f1) f34 (f23 (f24 f33 (f27 f28 (f9 (f10 f12 ?v0) ?v1))) ?v2)))))
(assert (= (= (f4 (f5 f8 f38) f38) f1) false))
(assert (= (= (f4 (f5 f6 f38) f38) f1) true))
(assert (forall ((?v0 S9)) (= (f35 (f36 f37 (f9 f13 f38)) (f23 (f24 f33 (f27 f28 (f9 f14 (f9 f15 f16)))) ?v0)) f18)))
(assert (not (= (f9 f13 f16) (f9 f13 f38))))
(assert (forall ((?v0 S2)) (= (= (f29 (f30 f32 f34) (f27 f28 ?v0)) f1) (= (f4 (f5 f8 f16) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= f34 (f27 f28 ?v0)) (= (f4 (f5 f6 ?v0) f16) f1))))
(assert (forall ((?v0 S2)) (= (= (f27 f28 ?v0) f34) (= (f4 (f5 f6 ?v0) f16) f1))))
(assert (forall ((?v0 S2) (?v1 S9)) (= (f4 (f5 f6 f7) (f35 (f36 f37 ?v0) (f23 (f24 f33 (f27 f28 (f9 f14 (f9 f15 f16)))) ?v1))) f1)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f27 f28 ?v0))) (= (f35 (f36 f37 f7) ?v_0) (ite (= ?v_0 f34) f18 f7)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f27 f28 ?v0))) (= (f23 (f24 f40 f34) ?v_0) (ite (= ?v_0 f34) f26 f34)))))
(assert (forall ((?v0 S9)) (= (f23 (f24 f40 ?v0) (f27 f28 (f9 f15 (f9 f15 f16)))) (f23 (f24 f33 (f23 (f24 f33 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S2)) (= (f35 (f36 f37 ?v0) (f27 f28 (f9 f15 (f9 f15 f16)))) (f9 (f10 f12 (f9 (f10 f12 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S2)) (let ((?v_2 (f9 f14 (f9 f15 f16)))) (let ((?v_0 (f27 f28 ?v_2)) (?v_1 (f36 f37 ?v0))) (= (f35 (f36 f37 (f35 ?v_1 ?v_0)) ?v_0) (f35 ?v_1 (f27 f28 (f9 f14 ?v_2))))))))
(assert (forall ((?v0 S2) (?v1 S9)) (let ((?v_0 (f5 f6 f7))) (=> (= (f4 ?v_0 ?v0) f1) (= (f4 ?v_0 (f35 (f36 f37 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S9)) (= (f23 (f24 f33 ?v0) (f27 f28 (f9 f14 (f9 f15 f16)))) (f23 (f24 f25 ?v0) ?v0))))
(assert (forall ((?v0 S9)) (= (f23 (f24 f33 (f27 f28 (f9 f14 (f9 f15 f16)))) ?v0) (f23 (f24 f25 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f8 f38))) (= (= (f4 ?v_0 (f9 f15 ?v0)) f1) (= (f4 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 (f9 f15 ?v0)) f38) f1) (= (f4 (f5 f8 ?v0) f38) f1))))
(assert (= (= (f4 (f5 f8 f38) f16) f1) true))
(assert (= (= (f4 (f5 f8 f16) f38) f1) false))
(assert (= (= (f4 (f5 f8 f38) f7) f1) true))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f8 f38))) (= (= (f4 ?v_0 (f9 f14 ?v0)) f1) (= (f4 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f6 f38))) (= (= (f4 ?v_0 (f9 f15 ?v0)) f1) (= (f4 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f6 (f9 f15 ?v0)) f38) f1) (= (f4 (f5 f6 ?v0) f38) f1))))
(assert (= (= (f4 (f5 f6 f38) f16) f1) true))
(assert (= (= (f4 (f5 f6 f16) f38) f1) false))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f6 (f9 f14 ?v0)) f38) f1) (= (f4 (f5 f6 ?v0) f38) f1))))
(assert (forall ((?v0 S2) (?v1 S9)) (=> (= (f4 (f5 f6 (f35 (f36 f37 ?v0) (f23 (f24 f33 (f27 f28 (f9 f14 (f9 f15 f16)))) ?v1))) f7) f1) (= ?v0 f7))))
(assert (= (f35 (f36 f37 f7) (f27 f28 (f9 f14 (f9 f15 f16)))) f7))
(assert (= (f23 (f24 f40 f34) (f27 f28 (f9 f14 (f9 f15 f16)))) f34))
(assert (forall ((?v0 S2)) (= (= (f35 (f36 f37 ?v0) (f27 f28 (f9 f14 (f9 f15 f16)))) f7) (= ?v0 f7))))
(assert (forall ((?v0 S9)) (= (f23 (f24 f40 ?v0) (f27 f28 (f9 f14 (f9 f15 f16)))) (f23 (f24 f33 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f35 (f36 f37 ?v0) (f27 f28 (f9 f14 (f9 f15 f16)))) (f9 (f10 f12 ?v0) ?v0))))
(assert (= (f35 (f36 f37 f18) (f27 f28 (f9 f14 (f9 f15 f16)))) f18))
(assert (= (f23 (f24 f40 f26) (f27 f28 (f9 f14 (f9 f15 f16)))) f26))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f35 (f36 f37 ?v0) (f27 f28 (f9 f14 (f9 f15 f16))))) f1)))
(assert (forall ((?v0 S2)) (let ((?v_1 (f9 f15 f16)) (?v_0 (f36 f37 ?v0))) (= (f9 (f10 f12 ?v0) (f35 ?v_0 (f27 f28 (f9 f14 ?v_1)))) (f35 ?v_0 (f27 f28 (f9 f15 ?v_1)))))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f6 f38) (f9 f14 ?v0)) f1) (= (f4 (f5 f8 f38) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 (f9 f14 ?v0)) f38) f1) (= (f4 (f5 f6 ?v0) f38) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f9 f13 f38))) (= (= (f9 (f10 f12 ?v0) ?v1) f18) (or (and (= ?v0 f18) (= ?v1 f18)) (and (= ?v0 ?v_0) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f9 (f10 f12 ?v0) ?v1) f18) (or (= ?v0 f18) (= ?v0 (f9 f13 f38))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f4 (f5 f8 ?v0) ?v1) f1) false) (=> (=> (= (f4 (f5 f8 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f7) (f35 (f36 f37 ?v0) (f27 f28 (f9 f14 (f9 f15 f16))))) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f27 f28 (f9 f14 (f9 f15 f16))))) (=> (= (f4 (f5 f6 (f35 (f36 f37 ?v0) ?v_0)) (f35 (f36 f37 ?v1) ?v_0)) f1) (=> (= (f4 (f5 f6 f7) ?v1) f1) (= (f4 (f5 f6 ?v0) ?v1) f1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_0 (f27 f28 (f9 f14 (f9 f15 f16))))) (=> (= (f29 (f30 f31 (f23 (f24 f40 ?v0) ?v_0)) (f23 (f24 f40 ?v1) ?v_0)) f1) (=> (= (f29 (f30 f31 f34) ?v1) f1) (= (f29 (f30 f31 ?v0) ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f5 f6 f7)) (?v_0 (f27 f28 (f9 f14 (f9 f15 f16))))) (=> (= (f35 (f36 f37 ?v0) ?v_0) (f35 (f36 f37 ?v1) ?v_0)) (=> (= (f4 ?v_1 ?v0) f1) (=> (= (f4 ?v_1 ?v1) f1) (= ?v0 ?v1)))))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_0 (f27 f28 (f9 f14 (f9 f15 f16)))) (?v_1 (f30 f31 f34))) (=> (= (f23 (f24 f40 ?v0) ?v_0) (f23 (f24 f40 ?v1) ?v_0)) (=> (= (f29 ?v_1 ?v0) f1) (=> (= (f29 ?v_1 ?v1) f1) (= ?v0 ?v1)))))))
(assert (forall ((?v0 S2)) (not (= (f4 (f5 f8 (f35 (f36 f37 ?v0) (f27 f28 (f9 f14 (f9 f15 f16))))) f7) f1))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f8 f7) (f35 (f36 f37 ?v0) (f27 f28 (f9 f14 (f9 f15 f16))))) f1) (not (= ?v0 f7)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f27 f28 (f9 f14 (f9 f15 f16))))) (= (= (f9 (f10 f11 (f35 (f36 f37 ?v0) ?v_0)) (f35 (f36 f37 ?v1) ?v_0)) f7) (and (= ?v0 f7) (= ?v1 f7))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f27 f28 ?v0))) (= (f23 (f24 f40 ?v_0) (f27 f28 (f9 f14 (f9 f15 f16)))) (f23 (f24 f33 ?v_0) ?v_0)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f9 f13 ?v0))) (= (f35 (f36 f37 ?v_0) (f27 f28 (f9 f14 (f9 f15 f16)))) (f9 (f10 f12 ?v_0) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f4 (f5 ?v_0 ?v1) ?v2) f1) (=> (= ?v1 ?v3) (=> (= (f4 (f5 (f19 f20 ?v3) ?v4) ?v2) f1) (= (f4 (f5 ?v_0 ?v4) ?v2) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f27 f28 (f9 f14 (f9 f15 f16))))) (=> (= (f4 (f5 f8 (f35 (f36 f37 ?v0) ?v_0)) (f35 (f36 f37 ?v1) ?v_0)) f1) (=> (= (f4 (f5 f6 f7) ?v1) f1) (= (f4 (f5 f8 ?v0) ?v1) f1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_0 (f27 f28 (f9 f14 (f9 f15 f16))))) (=> (= (f29 (f30 f32 (f23 (f24 f40 ?v0) ?v_0)) (f23 (f24 f40 ?v1) ?v_0)) f1) (=> (= (f29 (f30 f31 f34) ?v1) f1) (= (f29 (f30 f32 ?v0) ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f27 f28 (f9 f14 (f9 f15 f16))))) (= (f4 (f5 f6 f7) (f9 (f10 f11 (f35 (f36 f37 ?v0) ?v_0)) (f35 (f36 f37 ?v1) ?v_0))) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f27 f28 (f9 f14 (f9 f15 f16))))) (= (= (f4 (f5 f6 (f9 (f10 f11 (f35 (f36 f37 ?v0) ?v_0)) (f35 (f36 f37 ?v1) ?v_0))) f7) f1) (and (= ?v0 f7) (= ?v1 f7))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f27 f28 (f9 f14 (f9 f15 f16))))) (not (= (f4 (f5 f8 (f9 (f10 f11 (f35 (f36 f37 ?v0) ?v_0)) (f35 (f36 f37 ?v1) ?v_0))) f7) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f27 f28 (f9 f14 (f9 f15 f16))))) (= (= (f4 (f5 f8 f7) (f9 (f10 f11 (f35 (f36 f37 ?v0) ?v_0)) (f35 (f36 f37 ?v1) ?v_0))) f1) (or (not (= ?v0 f7)) (not (= ?v1 f7)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f9 f14 (f9 f15 f16)))) (let ((?v_0 (f27 f28 ?v_1))) (= (f35 (f36 f37 (f9 (f10 f11 ?v0) ?v1)) ?v_0) (f9 (f10 f11 (f9 (f10 f11 (f35 (f36 f37 ?v0) ?v_0)) (f35 (f36 f37 ?v1) ?v_0))) (f9 (f10 f12 (f9 (f10 f12 (f9 f13 ?v_1)) ?v0)) ?v1)))))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_0 (f27 f28 (f9 f14 (f9 f15 f16))))) (= (f23 (f24 f40 (f23 (f24 f25 ?v0) ?v1)) ?v_0) (f23 (f24 f25 (f23 (f24 f25 (f23 (f24 f40 ?v0) ?v_0)) (f23 (f24 f40 ?v1) ?v_0))) (f23 (f24 f33 (f23 (f24 f33 ?v_0) ?v0)) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_1 (f9 f14 (f9 f15 f16)))) (let ((?v_0 (f27 f28 ?v_1))) (= (f35 (f36 f37 (f9 (f10 f11 ?v0) ?v1)) ?v_0) (f9 (f10 f11 (f9 (f10 f11 (f35 (f36 f37 ?v0) ?v_0)) (f9 (f10 f12 (f9 (f10 f12 (f9 f13 ?v_1)) ?v0)) ?v1))) (f35 (f36 f37 ?v1) ?v_0)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_3 (f9 f15 f16))) (let ((?v_5 (f27 f28 (f9 f14 ?v_3))) (?v_1 (f9 f15 ?v_3))) (let ((?v_0 (f27 f28 ?v_1)) (?v_2 (f36 f37 ?v0)) (?v_4 (f10 f12 (f9 f13 ?v_1))) (?v_6 (f36 f37 ?v1))) (= (f35 (f36 f37 (f9 (f10 f11 ?v0) ?v1)) ?v_0) (f9 (f10 f11 (f9 (f10 f11 (f9 (f10 f11 (f35 ?v_2 ?v_0)) (f9 (f10 f12 (f9 ?v_4 (f35 ?v_2 ?v_5))) ?v1))) (f9 (f10 f12 (f9 ?v_4 ?v0)) (f35 ?v_6 ?v_5)))) (f35 ?v_6 ?v_0))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f19 f20 ?v1))) (=> (= (f4 (f5 f8 (f9 f13 (f9 f14 (f9 f15 f16)))) ?v0) f1) (=> (= (f4 (f5 ?v_0 (f9 f13 f38)) ?v0) f1) (not (= (f4 (f5 ?v_0 f18) ?v0) f1)))))))
(assert (forall ((?v0 S2)) (= (f9 (f10 f12 f7) ?v0) f7)))
(assert (forall ((?v0 S9)) (= (f23 (f24 f33 f34) ?v0) f34)))
(assert (forall ((?v0 S2)) (= (f9 (f10 f12 ?v0) f7) f7)))
(assert (forall ((?v0 S9)) (= (f23 (f24 f33 ?v0) f34) f34)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f9 (f10 f12 ?v0) ?v1) f7) (or (= ?v0 f7) (= ?v1 f7)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 f7)) (=> (not (= ?v1 f7)) (not (= (f9 (f10 f12 ?v0) ?v1) f7))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (not (= ?v0 f34)) (=> (not (= ?v1 f34)) (not (= (f23 (f24 f33 ?v0) ?v1) f34))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f9 (f10 f12 ?v0) ?v1) f7) (or (= ?v0 f7) (= ?v1 f7)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f23 (f24 f33 ?v0) ?v1) f34) (or (= ?v0 f34) (= ?v1 f34)))))
(assert (not (= f18 f7)))
(assert (not (= f26 f34)))
(assert (not (= f7 f18)))
(assert (not (= f34 f26)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f9 (f10 f12 (f9 (f10 f11 ?v0) ?v1)) ?v2) (f9 (f10 f11 (f9 (f10 f12 ?v0) ?v2)) (f9 (f10 f12 ?v1) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (= (f23 (f24 f33 (f23 (f24 f25 ?v0) ?v1)) ?v2) (f23 (f24 f25 (f23 (f24 f33 ?v0) ?v2)) (f23 (f24 f33 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (f9 (f10 f11 (f9 (f10 f12 ?v0) ?v1)) (f9 (f10 f11 (f9 (f10 f12 ?v2) ?v1)) ?v3)) (f9 (f10 f11 (f9 (f10 f12 (f9 (f10 f11 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (= (f23 (f24 f25 (f23 (f24 f33 ?v0) ?v1)) (f23 (f24 f25 (f23 (f24 f33 ?v2) ?v1)) ?v3)) (f23 (f24 f25 (f23 (f24 f33 (f23 (f24 f25 ?v0) ?v2)) ?v1)) ?v3))))
(assert (= f26 (f27 f28 (f9 f15 f16))))
(assert (= (f27 f28 (f9 f15 f16)) f26))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f29 (f30 f32 (f27 f28 ?v0)) (f27 f28 ?v1)) f1) (ite (= (f4 (f5 f8 ?v0) ?v1) f1) (= (f4 (f5 f8 f16) ?v1) f1) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f5 f6 ?v0))) (= (= (f29 (f30 f31 (f27 f28 ?v0)) (f27 f28 ?v1)) f1) (ite (= (f4 ?v_0 ?v1) f1) true (= (f4 ?v_0 f16) f1))))))
(assert (forall ((?v0 S2) (?v1 S1) (?v2 S1)) (let ((?v_0 (= (f4 (f5 f6 f7) ?v0) f1)) (?v_1 (= ?v1 f1)) (?v_2 (= ?v2 f1))) (=> (=> ?v_0 (= ?v_1 ?v_2)) (= (and ?v_0 ?v_1) (and ?v_0 ?v_2))))))
(assert (forall ((?v0 S2) (?v1 S1) (?v2 S1)) (let ((?v_0 (= (f4 (f5 f6 f7) ?v0) f1)) (?v_1 (= ?v1 f1)) (?v_2 (= ?v2 f1))) (=> (=> ?v_0 (= ?v_1 ?v_2)) (= (=> ?v_0 ?v_1) (=> ?v_0 ?v_2))))))
(assert (forall ((?v0 S2)) (= (f4 (f5 (f19 f20 ?v0) f7) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (let ((?v_0 (f19 f20 ?v3))) (=> (= (f4 (f5 (f19 f20 ?v0) ?v1) ?v2) f1) (= (= (f4 (f5 ?v_0 (f9 (f10 f12 ?v0) ?v4)) ?v2) f1) (= (f4 (f5 ?v_0 (f9 (f10 f12 ?v1) ?v4)) ?v2) f1))))))
(check-sat)
(exit)
