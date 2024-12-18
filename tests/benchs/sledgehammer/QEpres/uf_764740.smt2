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
(declare-sort S19 0)
(declare-sort S20 0)
(declare-sort S21 0)
(declare-sort S22 0)
(declare-sort S23 0)
(declare-sort S24 0)
(declare-sort S25 0)
(declare-sort S26 0)
(declare-sort S27 0)
(declare-sort S28 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S4 S3) S1)
(declare-fun f6 (S5 S2) S4)
(declare-fun f7 () S5)
(declare-fun f8 (S6 S7) S3)
(declare-fun f9 () S6)
(declare-fun f10 () S7)
(declare-fun f11 (S8 S9) S3)
(declare-fun f12 (S10 S9) S8)
(declare-fun f13 (S11 S12) S10)
(declare-fun f14 () S11)
(declare-fun f15 () S12)
(declare-fun f16 () S9)
(declare-fun f17 (S15 S14) S1)
(declare-fun f18 (S12 S13) S15)
(declare-fun f19 (S9 S13) S12)
(declare-fun f20 (S16 S13) S1)
(declare-fun f21 (S17 S13) S16)
(declare-fun f22 () S17)
(declare-fun f23 () S13)
(declare-fun f24 (S18 S13) S13)
(declare-fun f25 (S19 S13) S18)
(declare-fun f26 () S19)
(declare-fun f27 () S13)
(declare-fun f28 (S20 S14) S13)
(declare-fun f29 () S20)
(declare-fun f30 (S21 S7) S14)
(declare-fun f31 (S22 S23) S21)
(declare-fun f32 () S22)
(declare-fun f33 () S23)
(declare-fun f34 (S3 S7) S7)
(declare-fun f35 () S17)
(declare-fun f36 (S24 S3) S3)
(declare-fun f37 () S24)
(declare-fun f38 (S25 S2) S15)
(declare-fun f39 () S25)
(declare-fun f40 (S26 S14) S14)
(declare-fun f41 (S27 S13) S26)
(declare-fun f42 () S27)
(declare-fun f43 () S14)
(declare-fun f44 (S23 S2) S13)
(declare-fun f45 (S7) S28)
(declare-fun f46 () S28)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (and (= (f5 (f6 f7 ?v0) (f8 f9 f10)) f1) (= (f3 (f11 (f12 (f13 f14 f15) f16) f16) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S14)) (= (= (f17 (f18 (f19 f16 ?v0) ?v1) ?v2) f1) true)))
(assert (forall ((?v0 S13) (?v1 S14)) (= (= (f17 (f18 f15 ?v0) ?v1) f1) false)))
(assert (let ((?v_1 (f28 f29 (f30 (f31 f32 f33) (f34 (f11 (f12 (f13 f14 f15) f16) f16) f10))))) (let ((?v_0 (f24 (f25 f26 f27) ?v_1))) (not (and (= (f20 (f21 f22 f23) ?v_0) f1) (and (= (f20 (f21 f35 ?v_0) ?v_1) f1) (forall ((?v0 S2)) (=> (= (f5 (f6 f7 ?v0) (f36 f37 f4)) f1) (= (f17 (f38 f39 ?v0) (f40 (f41 f42 ?v_0) f43)) f1)))))))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f38 f39 ?v0))) (=> (= (f5 (f6 f7 ?v0) (f36 f37 f4)) f1) (= (= (f17 ?v_0 (f40 (f41 f42 (f24 (f25 f26 f27) (f28 f29 (f30 (f31 f32 f33) (f34 (f11 (f12 (f13 f14 f15) f16) f16) f10))))) f43)) f1) (= (f17 ?v_0 (f40 (f41 f42 f27) f43)) f1))))))
(assert (forall ((?v0 S2)) (=> (= (f5 (f6 f7 ?v0) (f8 f9 f10)) f1) (= (f17 (f38 f39 ?v0) (f40 (f41 f42 f27) f43)) f1))))
(assert (forall ((?v0 S2)) (=> (= (f5 (f6 f7 ?v0) (f8 f9 f10)) f1) (not (= (f44 f33 ?v0) f23)))))
(assert (forall ((?v0 S2)) (=> (= (f5 (f6 f7 ?v0) (f8 f9 f10)) f1) (not (= (f44 f33 ?v0) f23)))))
(assert (forall ((?v0 S2)) (=> (= (f5 (f6 f7 ?v0) (f8 f9 f10)) f1) (= (f17 (f38 f39 ?v0) (f40 (f41 f42 f27) f43)) f1))))
(assert (exists ((?v0 S13)) (forall ((?v1 S2)) (=> (= (f5 (f6 f7 ?v1) (f8 f9 f10)) f1) (= (f17 (f38 f39 ?v1) (f40 (f41 f42 ?v0) f43)) f1)))))
(assert (=> (forall ((?v0 S13)) (=> (forall ((?v1 S2)) (=> (= (f5 (f6 f7 ?v1) (f8 f9 f10)) f1) (= (f17 (f38 f39 ?v1) (f40 (f41 f42 ?v0) f43)) f1))) false)) false))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f35 f23) ?v0) f1) (= (f20 (f21 f22 f23) (f24 (f25 f26 ?v1) ?v0)) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f24 (f25 f26 ?v1) ?v0))) (=> (= (f20 (f21 f35 f23) ?v0) f1) (and (= (f20 (f21 f22 f23) ?v_0) f1) (= (f20 (f21 f35 ?v_0) ?v0) f1))))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f22 f23) ?v0) f1) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (= (f24 (f25 f26 ?v0) ?v1) ?v0)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f35 ?v0) f23) f1) (= (f20 (f21 f22 (f24 (f25 f26 ?v1) ?v0)) f23) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f21 f35 ?v0)) (?v_1 (f24 (f25 f26 ?v1) ?v0))) (=> (= (f20 ?v_0 f23) f1) (and (= (f20 (f21 f22 ?v_1) f23) f1) (= (f20 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f22 ?v0) f23) f1) (=> (= (f20 (f21 f35 ?v1) ?v0) f1) (= (f24 (f25 f26 ?v0) ?v1) ?v0)))))
(assert (= (f45 f10) f46))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f35 f23) ?v0) f1) (= (f20 (f21 f35 (f24 (f25 f26 ?v1) ?v0)) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f21 f35 ?v0))) (=> (= (f20 ?v_0 f23) f1) (= (f20 ?v_0 (f24 (f25 f26 ?v1) ?v0)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f22 f23) ?v0) f1) (= (f20 (f21 f22 (f24 (f25 f26 ?v0) ?v1)) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f21 f22 f23))) (=> (= (f20 ?v_0 ?v0) f1) (=> (= (f20 ?v_0 ?v1) f1) (= (f20 ?v_0 (f24 (f25 f26 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S13)) (= (f20 (f21 f22 ?v0) ?v0) f1)))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (=> (= (f20 (f21 f22 ?v0) ?v1) f1) false) (=> (=> (= (f20 (f21 f22 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f21 f22 ?v2))) (=> (= (f20 (f21 f22 ?v0) ?v1) f1) (=> (= (f20 ?v_0 ?v0) f1) (= (f20 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f22 ?v0) ?v1) f1) (=> (= (f20 (f21 f22 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f21 f22 ?v0))) (=> (= (f20 ?v_0 ?v1) f1) (=> (= (f20 (f21 f22 ?v1) ?v2) f1) (= (f20 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f22 ?v0) ?v1) f1) (=> (= (f20 (f21 f22 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f20 (f21 f22 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f20 (f21 f22 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f21 f22 ?v0))) (=> (= (f20 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f20 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f21 f22 ?v2))) (=> (= ?v0 ?v1) (=> (= (f20 ?v_0 ?v1) f1) (= (f20 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= ?v0 ?v1) (=> (= (f20 (f21 f22 ?v1) ?v2) f1) (= (f20 (f21 f22 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f22 ?v0) ?v1) f1) (= (= (f20 (f21 f22 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= ?v0 ?v1) (= (f20 (f21 f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= ?v0 ?v1) (and (= (f20 (f21 f22 ?v0) ?v1) f1) (= (f20 (f21 f22 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (or (= (f20 (f21 f22 ?v0) ?v1) f1) (= (f20 (f21 f22 ?v1) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (=> (= (f20 (f21 f35 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f20 (f21 f35 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (=> (=> (not false) (= (f20 (f21 f35 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f21 f35 ?v2))) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (=> (= (f20 ?v_0 ?v0) f1) (= (f20 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f21 f35 ?v0))) (=> (= (f20 ?v_0 ?v1) f1) (=> (= (f20 (f21 f35 ?v1) ?v2) f1) (= (f20 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f20 (f21 f35 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f21 f35 ?v0))) (=> (= (f20 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f20 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f21 f35 ?v2))) (=> (= ?v0 ?v1) (=> (= (f20 ?v_0 ?v1) f1) (= (f20 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= ?v0 ?v1) (=> (= (f20 (f21 f35 ?v1) ?v2) f1) (= (f20 (f21 f35 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (=> (= (f20 (f21 f35 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (=> (= (f20 (f21 f35 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S1)) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (= (=> (= (f20 (f21 f35 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (= (not (= (f20 (f21 f35 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (not (= (f20 (f21 f35 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f20 (f21 f35 ?v0) ?v1) f1) false) (=> (=> (= (f20 (f21 f35 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (not (= (f20 (f21 f35 ?v0) ?v1) f1)) (= (not (= (f20 (f21 f35 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S13) (?v1 S13)) (or (= (f20 (f21 f35 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f20 (f21 f35 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (not (= (f20 (f21 f35 ?v0) ?v1) f1)) (or (= (f20 (f21 f35 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (not (= ?v0 ?v1)) (or (= (f20 (f21 f35 ?v0) ?v1) f1) (= (f20 (f21 f35 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13)) (not (= (f20 (f21 f35 ?v0) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (let ((?v_0 (f24 (f25 f26 ?v0) ?v1))) (= (f24 (f25 f26 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f21 f35 ?v2))) (=> (= (f20 (f21 f22 ?v0) ?v1) f1) (=> (= (f20 ?v_0 ?v0) f1) (= (f20 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f20 (f21 f22 ?v0) ?v1) f1) (=> (= (f20 (f21 f35 ?v1) ?v2) f1) (= (f20 (f21 f35 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f20 (f21 f35 ?v0) ?v1) f1) (=> (= (f20 (f21 f22 ?v2) ?v0) f1) (= (f20 (f21 f35 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f21 f35 ?v0))) (=> (= (f20 ?v_0 ?v1) f1) (=> (= (f20 (f21 f22 ?v1) ?v2) f1) (= (f20 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f22 ?v0) ?v1) f1) (=> (not (= ?v1 ?v0)) (= (f20 (f21 f35 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f22 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f20 (f21 f35 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f22 ?v0) ?v1) f1) (or (= (f20 (f21 f35 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f20 (f21 f22 ?v0) ?v1) f1) (= (not (= (f20 (f21 f35 ?v0) ?v1) f1)) (= ?v0 ?v1)))))
(check-sat)
(exit)
