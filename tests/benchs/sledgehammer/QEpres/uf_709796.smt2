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
(declare-fun f11 (S5 S7) S8)
(declare-fun f12 (S1 S5) S8)
(declare-fun f13 () S5)
(declare-fun f14 (S9 S7) S1)
(declare-fun f15 () S9)
(declare-fun f16 (S11 S7) S7)
(declare-fun f17 (S12 S7) S11)
(declare-fun f18 () S12)
(declare-fun f19 (S13 S10) S7)
(declare-fun f20 (S14 S10) S13)
(declare-fun f21 () S14)
(declare-fun f22 (S15 S10) S10)
(declare-fun f23 () S15)
(declare-fun f24 () S10)
(declare-fun f25 (S16 S10) S2)
(declare-fun f26 (S17 S7) S16)
(declare-fun f27 () S17)
(declare-fun f28 (S3) S3)
(declare-fun f29 (S8 S10) S1)
(declare-fun f30 (S7 S7) S1)
(declare-fun f31 () S7)
(declare-fun f32 (S6 S7) S5)
(declare-fun f33 () S6)
(declare-fun f34 () S5)
(declare-fun f35 () S12)
(declare-fun f36 () S7)
(declare-fun f37 () S12)
(declare-fun f38 () S12)
(declare-fun f39 () S12)
(declare-fun f40 (S18 S9) S7)
(declare-fun f41 () S18)
(declare-fun f42 (S9) S9)
(declare-fun f43 () S13)
(declare-fun f44 (S19 S4) S10)
(declare-fun f45 (S20 S21) S19)
(declare-fun f46 () S20)
(declare-fun f47 () S21)
(declare-fun f48 (S3 S4) S4)
(declare-fun f49 () S7)
(declare-fun f50 (S21 S2) S7)
(declare-fun f51 () S2)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (and (= (f5 ?v0 (f6 f7)) f1) (= (f3 (f8 f9 f10 f10) ?v0) f1)))))
(assert (forall ((?v0 S7)) (= (f11 f9 ?v0) (f12 f2 f13))))
(assert (forall ((?v0 S7)) (= (= (f14 f15 ?v0) f1) (exists ((?v1 S10) (?v2 S7)) (and (= ?v0 (f16 (f17 f18 (f19 (f20 f21 (f22 f23 ?v1)) f24)) ?v2)) (= (f5 (f25 (f26 f27 ?v2) ?v1) (f28 f4)) f1))))))
(assert (forall ((?v0 S7) (?v1 S10)) (= (= (f29 (f11 f13 ?v0) ?v1) f1) (= (f30 ?v0 f31) f1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S10)) (= (= (f29 (f11 (f32 f10 ?v0) ?v1) ?v2) f1) false)))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S10)) (= (= (f29 (f11 (f32 f33 ?v0) ?v1) ?v2) f1) true)))
(assert (forall ((?v0 S7) (?v1 S10)) (= (= (f29 (f11 f34 ?v0) ?v1) f1) false)))
(assert (let ((?v_0 (f17 f18 f36)) (?v_1 (f19 f43 (f44 (f45 f46 f47) (f48 (f8 f34 f33 f33) f7)))) (?v_2 (f50 f47 f51))) (not (= (f16 (f17 f35 (f16 ?v_0 (f16 (f17 f37 (f16 (f17 f38 (f16 (f17 f39 (f16 ?v_0 (f40 f41 (f42 f15)))) ?v_1)) f49)) ?v_1))) ?v_2) (f16 (f17 f35 f36) ?v_2)))))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 (f6 f7)) f1) (not (= (f50 f47 ?v0) f31)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_1 (f17 f35 ?v1)) (?v_0 (f17 f37 ?v2))) (=> (= (f30 f31 ?v0) f1) (= (f16 ?v_1 (f16 ?v_0 ?v0)) (f16 (f17 f38 (f16 ?v_0 (f16 (f17 f35 (f16 (f17 f39 ?v1) ?v2)) ?v0))) (f16 ?v_1 ?v2)))))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f16 (f17 f35 ?v0) ?v1) (f16 (f17 f18 ?v0) (f16 (f17 f37 (f16 (f17 f39 ?v0) ?v1)) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f16 (f17 f37 ?v0) (f16 (f17 f39 ?v1) ?v0)) (f16 (f17 f18 ?v1) (f16 (f17 f35 ?v1) ?v0)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= ?v0 (f16 (f17 f38 (f16 (f17 f37 ?v1) (f16 (f17 f39 ?v0) ?v1))) (f16 (f17 f35 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f37 ?v0))) (= (f16 (f17 f39 (f16 ?v_0 ?v1)) ?v2) (f16 (f17 f38 (f16 ?v_0 (f16 (f17 f39 ?v1) ?v2))) (f16 (f17 f39 (f16 ?v_0 (f16 (f17 f35 ?v1) ?v2))) ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f38 (f16 (f17 f38 (f16 (f17 f37 ?v0) (f16 (f17 f39 ?v1) ?v0))) (f16 (f17 f35 ?v1) ?v0))) ?v2) (f16 (f17 f38 ?v1) ?v2))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f38 (f16 (f17 f38 (f16 (f17 f37 (f16 (f17 f39 ?v0) ?v1)) ?v1)) (f16 (f17 f35 ?v0) ?v1))) ?v2) (f16 (f17 f38 ?v0) ?v2))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f39 ?v1))) (=> (= (f30 f31 ?v0) f1) (= (f16 ?v_0 (f16 (f17 f37 ?v2) ?v0)) (f16 (f17 f39 (f16 ?v_0 ?v2)) ?v0))))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f30 f31 ?v0) f1) (=> (= (f30 f49 ?v1) f1) (= (f30 (f16 (f17 f39 ?v0) ?v1) ?v0) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f30 f31 ?v0) f1) (= (= (f16 (f17 f37 ?v0) ?v1) f49) (and (= ?v0 f49) (= ?v1 f49))))))
(assert (forall ((?v0 S7)) (= (= (f30 (f16 (f17 f38 (f16 (f17 f38 f49) ?v0)) ?v0) f31) f1) (= (f30 ?v0 f31) f1))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f16 (f17 f38 (f16 (f17 f35 ?v0) ?v1)) (f16 (f17 f37 (f16 (f17 f39 ?v0) ?v1)) ?v1)) ?v0)))
(assert (forall ((?v0 S7) (?v1 S7)) (or (= (f30 ?v0 ?v1) f1) (or (= ?v0 ?v1) (= (f30 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f16 (f17 f35 ?v0) ?v1))) (= (f16 (f17 f35 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f38 ?v0))) (= (f16 (f17 f38 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f17 f38 ?v1) ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_1 (f17 f38 ?v0)) (?v_0 (f17 f38 ?v1))) (= (f16 ?v_1 (f16 ?v_0 ?v2)) (f16 ?v_0 (f16 ?v_1 ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f16 (f17 f38 ?v0) ?v1) (f16 (f17 f38 ?v1) ?v0))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f37 ?v0))) (= (f16 (f17 f37 (f16 ?v_0 ?v1)) ?v2) (f16 ?v_0 (f16 (f17 f37 ?v1) ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f16 (f17 f37 ?v0) ?v1) (f16 (f17 f37 ?v1) ?v0))))
(assert (forall ((?v0 S7)) (= (= (f16 (f17 f38 ?v0) ?v0) f31) (= ?v0 f31))))
(assert (forall ((?v0 S7)) (= (f16 (f17 f35 ?v0) ?v0) f31)))
(assert (forall ((?v0 S7)) (= (f16 (f17 f35 ?v0) f31) ?v0)))
(assert (forall ((?v0 S7)) (= (f16 (f17 f35 f31) ?v0) f31)))
(assert (forall ((?v0 S7)) (= (f16 (f17 f39 ?v0) f31) f31)))
(assert (forall ((?v0 S7)) (= (f16 (f17 f39 f31) ?v0) f31)))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7) (?v4 S7)) (=> (= (f16 (f17 f35 ?v0) ?v1) (f16 (f17 f35 ?v2) ?v1)) (=> (= (f16 (f17 f35 ?v3) ?v1) (f16 (f17 f35 ?v4) ?v1)) (= (f16 (f17 f35 (f16 (f17 f37 ?v0) ?v3)) ?v1) (f16 (f17 f35 (f16 (f17 f37 ?v2) ?v4)) ?v1))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f35 (f16 (f17 f37 (f16 (f17 f35 ?v0) ?v1)) ?v2)) ?v1) (f16 (f17 f35 (f16 (f17 f37 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f35 (f16 (f17 f37 ?v0) ?v1)) (f16 (f17 f37 ?v2) ?v1)) (f16 (f17 f37 (f16 (f17 f35 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f37 ?v0))) (= (f16 (f17 f35 (f16 ?v_0 ?v1)) (f16 ?v_0 ?v2)) (f16 ?v_0 (f16 (f17 f35 ?v1) ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f35 (f16 (f17 f37 ?v0) ?v1)) ?v2) (f16 (f17 f35 (f16 (f17 f37 (f16 (f17 f35 ?v0) ?v2)) (f16 (f17 f35 ?v1) ?v2))) ?v2))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f35 (f16 (f17 f37 ?v0) ?v1)) ?v2) (f16 (f17 f35 (f16 (f17 f37 (f16 (f17 f35 ?v0) ?v2)) ?v1)) ?v2))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f37 ?v0))) (= (f16 (f17 f35 (f16 ?v_0 ?v1)) ?v2) (f16 (f17 f35 (f16 ?v_0 (f16 (f17 f35 ?v1) ?v2))) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7) (?v4 S7)) (=> (= (f16 (f17 f35 ?v0) ?v1) (f16 (f17 f35 ?v2) ?v1)) (=> (= (f16 (f17 f35 ?v3) ?v1) (f16 (f17 f35 ?v4) ?v1)) (= (f16 (f17 f35 (f16 (f17 f38 ?v0) ?v3)) ?v1) (f16 (f17 f35 (f16 (f17 f38 ?v2) ?v4)) ?v1))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f35 (f16 (f17 f38 (f16 (f17 f35 ?v0) ?v1)) ?v2)) ?v1) (f16 (f17 f35 (f16 (f17 f38 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f38 ?v0))) (= (f16 (f17 f35 (f16 ?v_0 (f16 (f17 f35 ?v1) ?v2))) ?v2) (f16 (f17 f35 (f16 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f35 (f16 (f17 f38 ?v0) ?v1)) ?v2) (f16 (f17 f35 (f16 (f17 f38 (f16 (f17 f35 ?v0) ?v2)) (f16 (f17 f35 ?v1) ?v2))) ?v2))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f35 (f16 (f17 f38 ?v0) ?v1)) ?v2) (f16 (f17 f35 (f16 (f17 f38 (f16 (f17 f35 ?v0) ?v2)) ?v1)) ?v2))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f38 ?v0))) (= (f16 (f17 f35 (f16 ?v_0 ?v1)) ?v2) (f16 (f17 f35 (f16 ?v_0 (f16 (f17 f35 ?v1) ?v2))) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f16 (f17 f35 (f16 (f17 f38 ?v0) ?v1)) ?v0) (f16 (f17 f35 ?v1) ?v0))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f16 (f17 f35 (f16 (f17 f38 ?v0) ?v1)) ?v1) (f16 (f17 f35 ?v0) ?v1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7) (?v4 S7)) (=> (= (f16 (f17 f35 ?v0) ?v1) (f16 (f17 f35 ?v2) ?v1)) (=> (= (f16 (f17 f35 ?v3) ?v1) (f16 (f17 f35 ?v4) ?v1)) (= (f16 (f17 f35 (f16 (f17 f18 ?v0) ?v3)) ?v1) (f16 (f17 f35 (f16 (f17 f18 ?v2) ?v4)) ?v1))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f35 (f16 (f17 f18 ?v0) ?v1)) ?v2) (f16 (f17 f35 (f16 (f17 f18 (f16 (f17 f35 ?v0) ?v2)) (f16 (f17 f35 ?v1) ?v2))) ?v2))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f35 (f16 (f17 f18 ?v0) ?v1)) ?v2) (f16 (f17 f35 (f16 (f17 f18 (f16 (f17 f35 ?v0) ?v2)) ?v1)) ?v2))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f18 ?v0))) (= (f16 (f17 f35 (f16 ?v_0 ?v1)) ?v2) (f16 (f17 f35 (f16 ?v_0 (f16 (f17 f35 ?v1) ?v2))) ?v2)))))
(assert (forall ((?v0 S7)) (= (f16 (f17 f38 ?v0) f31) ?v0)))
(assert (forall ((?v0 S7)) (= (f16 (f17 f38 f31) ?v0) ?v0)))
(assert (forall ((?v0 S7)) (= (f16 (f17 f39 ?v0) f49) ?v0)))
(assert (not (= f31 f49)))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (=> (= (f30 ?v0 ?v1) f1) (= (f30 (f16 (f17 f38 ?v0) ?v2) (f16 (f17 f38 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S7)) (= (f16 (f17 f35 ?v0) ?v0) f31)))
(assert (forall ((?v0 S7)) (= (f16 (f17 f35 f31) ?v0) f31)))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f37 (f16 (f17 f38 ?v0) ?v1)) ?v2) (f16 (f17 f38 (f16 (f17 f37 ?v0) ?v2)) (f16 (f17 f37 ?v1) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f37 ?v0))) (= (f16 ?v_0 (f16 (f17 f38 ?v1) ?v2)) (f16 (f17 f38 (f16 ?v_0 ?v1)) (f16 ?v_0 ?v2))))))
(assert (forall ((?v0 S7)) (= (f16 (f17 f39 f31) ?v0) f31)))
(assert (forall ((?v0 S7)) (= (f16 (f17 f37 ?v0) f49) ?v0)))
(assert (forall ((?v0 S7)) (= (f16 (f17 f37 f49) ?v0) ?v0)))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f37 (f16 (f17 f18 ?v0) ?v1)) ?v2) (f16 (f17 f18 (f16 (f17 f37 ?v0) ?v2)) (f16 (f17 f37 ?v1) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f37 ?v0))) (= (f16 ?v_0 (f16 (f17 f18 ?v1) ?v2)) (f16 (f17 f18 (f16 ?v_0 ?v1)) (f16 ?v_0 ?v2))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f37 ?v0))) (= (f16 (f17 f35 (f16 ?v_0 (f16 (f17 f35 ?v1) ?v2))) ?v2) (f16 (f17 f35 (f16 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f37 ?v0))) (= (f16 (f17 f35 (f16 ?v_0 ?v1)) ?v2) (f16 (f17 f35 (f16 ?v_0 (f16 (f17 f35 ?v1) ?v2))) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f16 (f17 f35 (f16 (f17 f18 (f16 (f17 f35 ?v0) ?v1)) ?v2)) ?v1) (f16 (f17 f35 (f16 (f17 f18 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (let ((?v_0 (f17 f18 ?v0))) (= (f16 (f17 f35 (f16 ?v_0 (f16 (f17 f35 ?v1) ?v2))) ?v2) (f16 (f17 f35 (f16 ?v_0 ?v1)) ?v2)))))
(check-sat)
(exit)