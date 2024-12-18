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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S4) S1)
(declare-fun f6 () S5)
(declare-fun f7 (S7 S6) S1)
(declare-fun f8 () S7)
(declare-fun f9 (S9 S8) S1)
(declare-fun f10 () S9)
(declare-fun f11 (S11 S10) S1)
(declare-fun f12 () S11)
(declare-fun f13 (S3 S5) S1)
(declare-fun f14 (S2 S3) S1)
(declare-fun f15 (S4 S5) S1)
(declare-fun f16 (S12 S2) S4)
(declare-fun f17 (S13 S2) S12)
(declare-fun f18 () S13)
(declare-fun f19 (S5 S7) S1)
(declare-fun f20 (S6 S7) S1)
(declare-fun f21 (S14 S4) S6)
(declare-fun f22 (S15 S4) S14)
(declare-fun f23 () S15)
(declare-fun f24 (S9 S11) S1)
(declare-fun f25 (S8 S9) S1)
(declare-fun f26 (S10 S11) S1)
(declare-fun f27 (S16 S8) S10)
(declare-fun f28 (S17 S8) S16)
(declare-fun f29 () S17)
(declare-fun f30 (S18 S19) S1)
(declare-fun f31 (S20 S18) S1)
(declare-fun f32 (S21 S19) S1)
(declare-fun f33 (S20 S20) S21)
(declare-fun f34 (S11 S18) S1)
(declare-fun f35 (S22 S10) S20)
(declare-fun f36 (S23 S10) S22)
(declare-fun f37 () S23)
(declare-fun f38 (S7 S9) S1)
(declare-fun f39 (S24 S6) S8)
(declare-fun f40 (S25 S6) S24)
(declare-fun f41 () S25)
(declare-fun f42 () S5)
(declare-fun f43 () S3)
(declare-fun f44 () S9)
(declare-fun f45 () S18)
(declare-fun f46 () S11)
(declare-fun f47 () S7)
(declare-fun f48 (S3) S3)
(declare-fun f49 (S7) S7)
(declare-fun f50 (S11) S11)
(declare-fun f51 (S9) S9)
(declare-fun f52 (S5) S5)
(declare-fun f53 (S5) S1)
(declare-fun f54 (S9) S1)
(declare-fun f55 (S18) S1)
(declare-fun f56 (S11) S1)
(declare-fun f57 (S7) S1)
(declare-fun f58 (S5) S1)
(declare-fun f59 (S9) S1)
(declare-fun f60 (S18) S1)
(declare-fun f61 (S11) S1)
(declare-fun f62 (S7) S1)
(declare-fun f63 (S26 S27) S5)
(declare-fun f64 (S26) S5)
(declare-fun f65 () S27)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) true)))
(assert (forall ((?v0 S4)) (= (= (f5 f6 ?v0) f1) true)))
(assert (forall ((?v0 S6)) (= (= (f7 f8 ?v0) f1) true)))
(assert (forall ((?v0 S8)) (= (= (f9 f10 ?v0) f1) true)))
(assert (forall ((?v0 S10)) (= (= (f11 f12 ?v0) f1) true)))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f13 ?v0 ?v1) f1) (forall ((?v2 S2)) (=> (= (f14 ?v2 ?v0) f1) (forall ((?v3 S2)) (=> (= (f14 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f15 (f16 (f17 f18 ?v2) ?v3) ?v1) f1) (= (f15 (f16 (f17 f18 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S5) (?v1 S7)) (= (= (f19 ?v0 ?v1) f1) (forall ((?v2 S4)) (=> (= (f15 ?v2 ?v0) f1) (forall ((?v3 S4)) (=> (= (f15 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f20 (f21 (f22 f23 ?v2) ?v3) ?v1) f1) (= (f20 (f21 (f22 f23 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S9) (?v1 S11)) (= (= (f24 ?v0 ?v1) f1) (forall ((?v2 S8)) (=> (= (f25 ?v2 ?v0) f1) (forall ((?v3 S8)) (=> (= (f25 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f26 (f27 (f28 f29 ?v2) ?v3) ?v1) f1) (= (f26 (f27 (f28 f29 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S18) (?v1 S19)) (= (= (f30 ?v0 ?v1) f1) (forall ((?v2 S20)) (=> (= (f31 ?v2 ?v0) f1) (forall ((?v3 S20)) (=> (= (f31 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f32 (f33 ?v2 ?v3) ?v1) f1) (= (f32 (f33 ?v3 ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S11) (?v1 S18)) (= (= (f34 ?v0 ?v1) f1) (forall ((?v2 S10)) (=> (= (f26 ?v2 ?v0) f1) (forall ((?v3 S10)) (=> (= (f26 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f31 (f35 (f36 f37 ?v2) ?v3) ?v1) f1) (= (f31 (f35 (f36 f37 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S7) (?v1 S9)) (= (= (f38 ?v0 ?v1) f1) (forall ((?v2 S6)) (=> (= (f20 ?v2 ?v0) f1) (forall ((?v3 S6)) (=> (= (f20 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f25 (f39 (f40 f41 ?v2) ?v3) ?v1) f1) (= (f25 (f39 (f40 f41 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S4)) (= (= (f15 ?v0 f42) f1) true)))
(assert (forall ((?v0 S2)) (= (= (f14 ?v0 f43) f1) true)))
(assert (forall ((?v0 S8)) (= (= (f25 ?v0 f44) f1) true)))
(assert (forall ((?v0 S20)) (= (= (f31 ?v0 f45) f1) true)))
(assert (forall ((?v0 S10)) (= (= (f26 ?v0 f46) f1) true)))
(assert (forall ((?v0 S6)) (= (= (f20 ?v0 f47) f1) true)))
(assert (= f43 (f48 f4)))
(assert (= f47 (f49 f8)))
(assert (= f46 (f50 f12)))
(assert (= f44 (f51 f10)))
(assert (= f42 (f52 f6)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f16 (f17 f18 ?v0) ?v1) (f16 (f17 f18 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (= (f39 (f40 f41 ?v0) ?v1) (f39 (f40 f41 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (= (= (f35 (f36 f37 ?v0) ?v1) (f35 (f36 f37 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (= (= (f27 (f28 f29 ?v0) ?v1) (f27 (f28 f29 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (= (= (f21 (f22 f23 ?v0) ?v1) (f21 (f22 f23 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5)) (= (= (f53 ?v0) f1) (forall ((?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f17 f18 ?v1))) (=> (= (f15 (f16 ?v_0 ?v2) ?v0) f1) (=> (= (f15 (f16 (f17 f18 ?v2) ?v3) ?v0) f1) (= (f15 (f16 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S9)) (= (= (f54 ?v0) f1) (forall ((?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f40 f41 ?v1))) (=> (= (f25 (f39 ?v_0 ?v2) ?v0) f1) (=> (= (f25 (f39 (f40 f41 ?v2) ?v3) ?v0) f1) (= (f25 (f39 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S18)) (= (= (f55 ?v0) f1) (forall ((?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f36 f37 ?v1))) (=> (= (f31 (f35 ?v_0 ?v2) ?v0) f1) (=> (= (f31 (f35 (f36 f37 ?v2) ?v3) ?v0) f1) (= (f31 (f35 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S11)) (= (= (f56 ?v0) f1) (forall ((?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f28 f29 ?v1))) (=> (= (f26 (f27 ?v_0 ?v2) ?v0) f1) (=> (= (f26 (f27 (f28 f29 ?v2) ?v3) ?v0) f1) (= (f26 (f27 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S7)) (= (= (f57 ?v0) f1) (forall ((?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f22 f23 ?v1))) (=> (= (f20 (f21 ?v_0 ?v2) ?v0) f1) (=> (= (f20 (f21 (f22 f23 ?v2) ?v3) ?v0) f1) (= (f20 (f21 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S5)) (= (= (f58 ?v0) f1) (forall ((?v1 S2)) (not (= (f15 (f16 (f17 f18 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S9)) (= (= (f59 ?v0) f1) (forall ((?v1 S6)) (not (= (f25 (f39 (f40 f41 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S18)) (= (= (f60 ?v0) f1) (forall ((?v1 S10)) (not (= (f31 (f35 (f36 f37 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S11)) (= (= (f61 ?v0) f1) (forall ((?v1 S8)) (not (= (f26 (f27 (f28 f29 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S7)) (= (= (f62 ?v0) f1) (forall ((?v1 S4)) (not (= (f20 (f21 (f22 f23 ?v1) ?v1) ?v0) f1))))))
(assert (not (forall ((?v0 S26) (?v1 S2) (?v2 S2)) (let ((?v_0 (f16 (f17 f18 ?v1) ?v2))) (=> (forall ((?v3 S26)) (let ((?v_1 (f64 ?v3))) (=> (forall ((?v4 S27)) (let ((?v_2 (f63 ?v3 ?v4))) (and (= (f53 ?v_2) f1) (and (= (f58 ?v_2) f1) (= (f13 f43 ?v_2) f1))))) (and (= (f53 ?v_1) f1) (and (= (f58 ?v_1) f1) (= (f13 f43 ?v_1) f1)))))) (=> (forall ((?v3 S26)) (=> (forall ((?v4 S27)) (let ((?v_3 (f63 ?v3 ?v4))) (and (= (f53 ?v_3) f1) (and (= (f58 ?v_3) f1) (= (f13 f43 ?v_3) f1))))) (forall ((?v4 S2) (?v5 S2)) (let ((?v_4 (f16 (f17 f18 ?v4) ?v5))) (=> (not (= ?v4 ?v5)) (=> (= (f15 ?v_4 (f63 ?v3 f65)) f1) (= (f15 ?v_4 (f64 ?v3)) f1))))))) (=> (forall ((?v3 S27)) (let ((?v_5 (f63 ?v0 ?v3))) (and (= (f53 ?v_5) f1) (and (= (f58 ?v_5) f1) (= (f13 f43 ?v_5) f1))))) (=> (= (f15 ?v_0 (f64 ?v0)) f1) (= (f15 ?v_0 (f63 ?v0 f65)) f1)))))))))
(check-sat)
(exit)
