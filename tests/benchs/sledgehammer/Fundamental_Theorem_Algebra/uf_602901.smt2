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
(declare-fun f4 (S4 S2) S3)
(declare-fun f5 () S4)
(declare-fun f6 () S2)
(declare-fun f7 () S4)
(declare-fun f8 (S6 S5) S2)
(declare-fun f9 () S6)
(declare-fun f10 () S2)
(declare-fun f11 (S7 S5) S5)
(declare-fun f12 (S8 S9) S7)
(declare-fun f13 () S8)
(declare-fun f14 () S9)
(declare-fun f15 (S10 S2) S2)
(declare-fun f16 () S10)
(declare-fun f17 () S5)
(declare-fun f18 () S9)
(declare-fun f19 (S12 S11) S11)
(declare-fun f20 (S13 S14) S12)
(declare-fun f21 () S13)
(declare-fun f22 () S14)
(declare-fun f23 () S11)
(declare-fun f24 (S15 S16) S10)
(declare-fun f25 () S15)
(declare-fun f26 () S16)
(declare-fun f27 (S18 S17) S17)
(declare-fun f28 (S19 S20) S18)
(declare-fun f29 () S19)
(declare-fun f30 () S20)
(declare-fun f31 () S17)
(declare-fun f32 (S22 S21) S21)
(declare-fun f33 (S23 S24) S22)
(declare-fun f34 () S23)
(declare-fun f35 () S24)
(declare-fun f36 () S21)
(declare-fun f37 (S26 S25) S25)
(declare-fun f38 (S27 S28) S26)
(declare-fun f39 () S27)
(declare-fun f40 () S28)
(declare-fun f41 () S25)
(declare-fun f42 (S29 S16) S16)
(declare-fun f43 (S30 S25) S29)
(declare-fun f44 () S30)
(declare-fun f45 (S31 S14) S14)
(declare-fun f46 (S32 S21) S31)
(declare-fun f47 () S32)
(declare-fun f48 (S33 S9) S9)
(declare-fun f49 (S34 S17) S33)
(declare-fun f50 () S34)
(assert (not (= f1 f2)))
(assert (not (exists ((?v0 S2)) (and (= (f3 (f4 f5 f6) ?v0) f1) (forall ((?v1 S5)) (=> (= (f3 (f4 f7 (f8 f9 ?v1)) f10) f1) (= (f3 (f4 f7 (f8 f9 (f11 (f12 f13 f14) ?v1))) ?v0) f1)))))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f5 f6) (f15 f16 ?v0)) f1) (not (= ?v0 f6)))))
(assert (forall ((?v0 S5)) (= (= (f3 (f4 f5 f6) (f8 f9 ?v0)) f1) (not (= ?v0 f17)))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 f7 (f15 f16 ?v0)) f6) f1) (= ?v0 f6))))
(assert (forall ((?v0 S5)) (= (= (f3 (f4 f7 (f8 f9 ?v0)) f6) f1) (= ?v0 f17))))
(assert (forall ((?v0 S5)) (not (= (f3 (f4 f5 (f8 f9 ?v0)) f6) f1))))
(assert (forall ((?v0 S2)) (not (= (f3 (f4 f5 (f15 f16 ?v0)) f6) f1))))
(assert (forall ((?v0 S5)) (= (f3 (f4 f7 f6) (f8 f9 ?v0)) f1)))
(assert (forall ((?v0 S2)) (= (f3 (f4 f7 f6) (f15 f16 ?v0)) f1)))
(assert (= (f15 f16 f6) f6))
(assert (= (f8 f9 f17) f6))
(assert (forall ((?v0 S2)) (= (= (f15 f16 ?v0) f6) (= ?v0 f6))))
(assert (forall ((?v0 S5)) (= (= (f8 f9 ?v0) f6) (= ?v0 f17))))
(assert (forall ((?v0 S2)) (= (f3 (f4 f7 ?v0) ?v0) f1)))
(assert (forall ((?v0 S5)) (= (f11 (f12 f13 f18) ?v0) f17)))
(assert (forall ((?v0 S11)) (= (f19 (f20 f21 f22) ?v0) f23)))
(assert (forall ((?v0 S2)) (= (f15 (f24 f25 f26) ?v0) f6)))
(assert (forall ((?v0 S17)) (= (f27 (f28 f29 f30) ?v0) f31)))
(assert (forall ((?v0 S21)) (= (f32 (f33 f34 f35) ?v0) f36)))
(assert (forall ((?v0 S25)) (= (f37 (f38 f39 f40) ?v0) f41)))
(assert (forall ((?v0 S16)) (= (f42 (f43 f44 f41) ?v0) f26)))
(assert (forall ((?v0 S14)) (= (f45 (f46 f47 f36) ?v0) f22)))
(assert (forall ((?v0 S9)) (= (f48 (f49 f50 f31) ?v0) f18)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (and (= (f3 (f4 f7 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f7 ?v0) ?v1) f1) (or (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f4 f5 ?v0) ?v1) f1)) (= (f3 (f4 f7 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f4 f7 ?v0) ?v1) f1)) (= (f3 (f4 f5 ?v1) ?v0) f1))))
(assert (forall ((?v0 S9)) (= (= (f12 f13 ?v0) (f12 f13 f18)) (= ?v0 f18))))
(assert (forall ((?v0 S21)) (= (= (f46 f47 ?v0) (f46 f47 f36)) (= ?v0 f36))))
(assert (forall ((?v0 S25)) (= (= (f43 f44 ?v0) (f43 f44 f41)) (= ?v0 f41))))
(assert (forall ((?v0 S16)) (= (= (f24 f25 ?v0) (f24 f25 f26)) (= ?v0 f26))))
(assert (forall ((?v0 S14)) (= (= (f20 f21 ?v0) (f20 f21 f22)) (= ?v0 f22))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f3 (f4 f7 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f7 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f7 ?v2))) (=> (= (f3 (f4 f7 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f7 ?v0) ?v1) f1) (=> (= (f3 (f4 f7 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f7 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f7 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f7 ?v0) ?v1) f1) (=> (= (f3 (f4 f7 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f7 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f3 (f4 f7 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f7 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f7 ?v2))) (=> (= ?v0 ?v1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f3 (f4 f7 ?v1) ?v2) f1) (= (f3 (f4 f7 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f7 ?v0) ?v1) f1) (= (= (f3 (f4 f7 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= ?v0 ?v1) (= (f3 (f4 f7 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 ?v1) (and (= (f3 (f4 f7 ?v0) ?v1) f1) (= (f3 (f4 f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f7 ?v0) ?v1) f1) (= (f3 (f4 f7 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f3 (f4 f5 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f3 (f4 f5 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (=> (not false) (= (f3 (f4 f5 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f5 ?v2))) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f5 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f3 (f4 f5 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f5 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f5 ?v2))) (=> (= ?v0 ?v1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f3 (f4 f5 ?v1) ?v2) f1) (= (f3 (f4 f5 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S1)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (= (=> (= (f3 (f4 f5 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (= (not (= (f3 (f4 f5 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (not (= (f3 (f4 f5 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 (f4 f5 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f5 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f4 f5 ?v0) ?v1) f1)) (= (not (= (f3 (f4 f5 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f5 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f4 f5 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f4 f5 ?v0) ?v1) f1)) (or (= (f3 (f4 f5 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= ?v0 ?v1)) (or (= (f3 (f4 f5 ?v0) ?v1) f1) (= (f3 (f4 f5 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2)) (not (= (f3 (f4 f5 ?v0) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f7 ?v0) ?v1) f1) (=> (= (f3 (f4 f7 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f7 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f7 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f4 f7 ?v0) ?v1) f1) (= (f3 (f4 f7 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (f3 (f4 f7 ?v0) ?v0) f1)))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f12 f13 ?v0) (f12 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S21) (?v1 S21)) (= (= (f46 f47 ?v0) (f46 f47 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S25) (?v1 S25)) (= (= (f43 f44 ?v0) (f43 f44 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S16) (?v1 S16)) (= (= (f24 f25 ?v0) (f24 f25 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f20 f21 ?v0) (f20 f21 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f5 ?v2))) (=> (= (f3 (f4 f7 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f7 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v2) f1) (= (f3 (f4 f5 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 (f4 f7 ?v2) ?v0) f1) (= (f3 (f4 f5 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f4 f5 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f7 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f7 ?v0) ?v1) f1) (=> (not (= ?v1 ?v0)) (= (f3 (f4 f5 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f7 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f3 (f4 f5 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f4 f7 ?v0) ?v1) f1) (or (= (f3 (f4 f5 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(check-sat)
(exit)