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
(declare-sort S29 0)
(declare-sort S30 0)
(declare-sort S31 0)
(declare-sort S32 0)
(declare-sort S33 0)
(declare-sort S34 0)
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
(declare-fun f17 (S12 S13) S14)
(declare-fun f18 (S15 S12) S14)
(declare-fun f19 (S16 S1) S15)
(declare-fun f20 () S16)
(declare-fun f21 () S12)
(declare-fun f22 (S17 S13) S1)
(declare-fun f23 () S17)
(declare-fun f24 (S19 S13) S13)
(declare-fun f25 (S20 S13) S19)
(declare-fun f26 () S20)
(declare-fun f27 (S21 S18) S13)
(declare-fun f28 (S22 S18) S21)
(declare-fun f29 () S22)
(declare-fun f30 (S23 S18) S18)
(declare-fun f31 () S23)
(declare-fun f32 () S18)
(declare-fun f33 (S24 S18) S2)
(declare-fun f34 (S25 S13) S24)
(declare-fun f35 () S25)
(declare-fun f36 (S26 S3) S3)
(declare-fun f37 () S26)
(declare-fun f38 (S14 S18) S1)
(declare-fun f39 (S27 S13) S17)
(declare-fun f40 () S27)
(declare-fun f41 () S13)
(declare-fun f42 (S9 S13) S12)
(declare-fun f43 () S27)
(declare-fun f44 (S28 S17) S13)
(declare-fun f45 () S28)
(declare-fun f46 (S29 S17) S17)
(declare-fun f47 () S29)
(declare-fun f48 () S18)
(declare-fun f49 () S13)
(declare-fun f50 (S30 S17) S1)
(declare-fun f51 (S31 S13) S30)
(declare-fun f52 () S31)
(declare-fun f53 () S2)
(declare-fun f54 (S32 S2) S13)
(declare-fun f55 () S32)
(declare-fun f56 (S7) S33)
(declare-fun f57 () S33)
(declare-fun f58 (S34 S18) S23)
(declare-fun f59 () S34)
(declare-fun f60 () S18)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (and (= (f5 (f6 f7 ?v0) (f8 f9 f10)) f1) (= (f3 (f11 (f12 (f13 f14 f15) f16) f16) ?v0) f1)))))
(assert (forall ((?v0 S13)) (= (f17 f15 ?v0) (f18 (f19 f20 f2) f21))))
(assert (forall ((?v0 S13)) (= (= (f22 f23 ?v0) f1) (exists ((?v1 S18) (?v2 S13)) (and (= ?v0 (f24 (f25 f26 (f27 (f28 f29 (f30 f31 ?v1)) f32)) ?v2)) (= (f5 (f6 f7 (f33 (f34 f35 ?v2) ?v1)) (f36 f37 f4)) f1))))))
(assert (forall ((?v0 S13) (?v1 S18)) (= (= (f38 (f17 f21 ?v0) ?v1) f1) (= (f22 (f39 f40 ?v0) f41) f1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S18)) (= (= (f38 (f17 (f42 f16 ?v0) ?v1) ?v2) f1) false)))
(assert (not (= (f22 (f39 f43 (f44 f45 (f46 f47 f23))) (f24 (f25 f26 (f27 (f28 f29 f48) f32)) f49)) f1)))
(assert (forall ((?v0 S13)) (= (= (f22 (f39 f43 (f44 f45 (f46 f47 f23))) ?v0) f1) (exists ((?v1 S13)) (and (= (f50 (f51 f52 ?v1) (f46 f47 f23)) f1) (= (f22 (f39 f43 ?v1) ?v0) f1))))))
(assert (= (f5 (f6 f7 f53) (f36 f37 f4)) f1))
(assert (forall ((?v0 S2)) (=> (= (f5 (f6 f7 ?v0) (f8 f9 f10)) f1) (not (= (f54 f55 ?v0) f41)))))
(assert (= (f56 f10) f57))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f22 (f39 f40 ?v0) ?v1) f1) (= (f22 (f39 f40 (f24 (f25 f26 ?v0) ?v1)) f41) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f22 (f39 f40 ?v0) ?v1) f1) (= (f22 (f39 f40 (f24 (f25 f26 ?v0) ?v1)) f41) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f22 (f39 f43 ?v0) ?v1) f1) (= (f22 (f39 f43 (f24 (f25 f26 ?v0) ?v1)) f41) f1))))
(assert (forall ((?v0 S12) (?v1 S9) (?v2 S9) (?v3 S13) (?v4 S18)) (= (= (f3 (f11 (f12 (f13 f14 ?v0) ?v1) ?v2) (f33 (f34 f35 ?v3) ?v4)) f1) (= (f38 (f17 ?v0 ?v3) ?v4) f1))))
(assert (forall ((?v0 S13)) (= (f22 (f39 f43 ?v0) ?v0) f1)))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (= (f27 (f28 f29 (f30 (f58 f59 ?v0) ?v1)) ?v2) (f24 (f25 f26 (f27 (f28 f29 ?v0) ?v2)) (f27 (f28 f29 ?v1) ?v2)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f22 (f39 f40 ?v0) ?v1) f1) (and (= (f22 (f39 f43 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (= (f22 (f39 f43 f41) f41) f1))
(assert (forall ((?v0 S13) (?v1 S1) (?v2 S1)) (let ((?v_0 (= (f22 (f39 f43 f41) ?v0) f1)) (?v_1 (= ?v1 f1)) (?v_2 (= ?v2 f1))) (=> (=> ?v_0 (= ?v_1 ?v_2)) (= (and ?v_0 ?v_1) (and ?v_0 ?v_2))))))
(assert (forall ((?v0 S13) (?v1 S1) (?v2 S1)) (let ((?v_0 (= (f22 (f39 f43 f41) ?v0) f1)) (?v_1 (= ?v1 f1)) (?v_2 (= ?v2 f1))) (=> (=> ?v_0 (= ?v_1 ?v_2)) (= (=> ?v_0 ?v_1) (=> ?v_0 ?v_2))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13) (?v3 S13)) (=> (= (f24 (f25 f26 ?v0) ?v1) (f24 (f25 f26 ?v2) ?v3)) (= (= (f22 (f39 f40 ?v0) ?v1) f1) (= (f22 (f39 f40 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S18)) (= (f30 (f58 f59 ?v0) f60) ?v0)))
(assert (forall ((?v0 S18)) (= (f27 (f28 f29 ?v0) f60) f41)))
(assert (forall ((?v0 S18)) (= (f27 (f28 f29 f60) ?v0) f41)))
(assert (forall ((?v0 S13)) (= (= f41 ?v0) (= ?v0 f41))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (=> (= (f22 (f39 f43 ?v0) ?v1) f1) false) (=> (=> (= (f22 (f39 f43 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f39 f43 ?v2))) (=> (= (f22 (f39 f43 ?v0) ?v1) f1) (=> (= (f22 ?v_0 ?v0) f1) (= (f22 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f22 (f39 f43 ?v0) ?v1) f1) (=> (= (f22 (f39 f43 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f39 f43 ?v0))) (=> (= (f22 ?v_0 ?v1) f1) (=> (= (f22 (f39 f43 ?v1) ?v2) f1) (= (f22 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f22 (f39 f43 ?v0) ?v1) f1) (=> (= (f22 (f39 f43 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f22 (f39 f43 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f22 (f39 f43 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f39 f43 ?v0))) (=> (= (f22 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f22 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f39 f43 ?v2))) (=> (= ?v0 ?v1) (=> (= (f22 ?v_0 ?v1) f1) (= (f22 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= ?v0 ?v1) (=> (= (f22 (f39 f43 ?v1) ?v2) f1) (= (f22 (f39 f43 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f22 (f39 f43 ?v0) ?v1) f1) (= (= (f22 (f39 f43 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= ?v0 ?v1) (= (f22 (f39 f43 ?v0) ?v1) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= ?v0 ?v1) (and (= (f22 (f39 f43 ?v0) ?v1) f1) (= (f22 (f39 f43 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (or (= (f22 (f39 f43 ?v0) ?v1) f1) (= (f22 (f39 f43 ?v1) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (=> (= (f22 (f39 f40 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f22 (f39 f40 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f22 (f39 f40 ?v0) ?v1) f1) (=> (=> (not false) (= (f22 (f39 f40 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f39 f40 ?v2))) (=> (= (f22 (f39 f40 ?v0) ?v1) f1) (=> (= (f22 ?v_0 ?v0) f1) (= (f22 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f39 f40 ?v0))) (=> (= (f22 ?v_0 ?v1) f1) (=> (= (f22 (f39 f40 ?v1) ?v2) f1) (= (f22 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= (f22 (f39 f40 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f22 (f39 f40 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f39 f40 ?v0))) (=> (= (f22 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f22 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f39 f40 ?v2))) (=> (= ?v0 ?v1) (=> (= (f22 ?v_0 ?v1) f1) (= (f22 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (=> (= ?v0 ?v1) (=> (= (f22 (f39 f40 ?v1) ?v2) f1) (= (f22 (f39 f40 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f22 (f39 f40 ?v0) ?v1) f1) (=> (= (f22 (f39 f40 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f22 (f39 f40 ?v0) ?v1) f1) (=> (= (f22 (f39 f40 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S1)) (=> (= (f22 (f39 f40 ?v0) ?v1) f1) (= (=> (= (f22 (f39 f40 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f22 (f39 f40 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f22 (f39 f40 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f22 (f39 f40 ?v0) ?v1) f1) (= (not (= (f22 (f39 f40 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f22 (f39 f40 ?v0) ?v1) f1) (not (= (f22 (f39 f40 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f22 (f39 f40 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f22 (f39 f40 ?v0) ?v1) f1) false) (=> (=> (= (f22 (f39 f40 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (not (= (f22 (f39 f40 ?v0) ?v1) f1)) (= (not (= (f22 (f39 f40 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S13) (?v1 S13)) (or (= (f22 (f39 f40 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f22 (f39 f40 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (not (= (f22 (f39 f40 ?v0) ?v1) f1)) (or (= (f22 (f39 f40 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (not (= ?v0 ?v1)) (or (= (f22 (f39 f40 ?v0) ?v1) f1) (= (f22 (f39 f40 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13)) (not (= (f22 (f39 f40 ?v0) ?v0) f1))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13) (?v3 S13)) (=> (= (f24 (f25 f26 ?v0) ?v1) (f24 (f25 f26 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S13) (?v1 S13)) (=> (= (f22 (f39 f43 ?v0) ?v1) f1) (=> (= (f22 (f39 f43 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f39 f43 ?v0))) (=> (= (f22 ?v_0 ?v1) f1) (=> (= (f22 (f39 f43 ?v1) ?v2) f1) (= (f22 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S13) (?v1 S13)) (or (= (f22 (f39 f43 ?v0) ?v1) f1) (= (f22 (f39 f43 ?v1) ?v0) f1))))
(assert (forall ((?v0 S13)) (= (f22 (f39 f43 ?v0) ?v0) f1)))
(assert (forall ((?v0 S13) (?v1 S13)) (or (= (f22 (f39 f40 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f22 (f39 f40 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S13) (?v1 S18) (?v2 S13) (?v3 S18)) (= (= (f33 (f34 f35 ?v0) ?v1) (f33 (f34 f35 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S13)) (let ((?v_0 (f39 f40 ?v2))) (=> (= (f22 (f39 f43 ?v0) ?v1) f1) (=> (= (f22 ?v_0 ?v0) f1) (= (f22 ?v_0 ?v1) f1))))))
(check-sat)
(exit)