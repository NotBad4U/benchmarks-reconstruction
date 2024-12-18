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
(declare-fun f13 (S4 S5) S1)
(declare-fun f14 (S8 S9) S1)
(declare-fun f15 (S12 S13) S1)
(declare-fun f16 (S13 S12) S1)
(declare-fun f17 (S10 S11) S1)
(declare-fun f18 (S6 S7) S1)
(declare-fun f19 (S2 S3) S1)
(declare-fun f20 (S14 S2) S4)
(declare-fun f21 (S15 S2) S14)
(declare-fun f22 () S15)
(declare-fun f23 (S16 S6) S8)
(declare-fun f24 (S17 S6) S16)
(declare-fun f25 () S17)
(declare-fun f26 (S18 S10) S12)
(declare-fun f27 (S19 S10) S18)
(declare-fun f28 () S19)
(declare-fun f29 (S20 S8) S10)
(declare-fun f30 (S21 S8) S20)
(declare-fun f31 () S21)
(declare-fun f32 (S22 S4) S6)
(declare-fun f33 (S23 S4) S22)
(declare-fun f34 () S23)
(declare-fun f35 (S5) S1)
(declare-fun f36 (S9) S1)
(declare-fun f37 (S13) S1)
(declare-fun f38 (S11) S1)
(declare-fun f39 (S7) S1)
(declare-fun f40 (S5) S1)
(declare-fun f41 (S9) S1)
(declare-fun f42 (S13) S1)
(declare-fun f43 (S11) S1)
(declare-fun f44 (S7) S1)
(declare-fun f45 (S3 S5) S1)
(declare-fun f46 (S5 S7) S1)
(declare-fun f47 (S9 S11) S1)
(declare-fun f48 (S13 S24) S1)
(declare-fun f49 (S25 S24) S1)
(declare-fun f50 (S12 S12) S25)
(declare-fun f51 (S11 S13) S1)
(declare-fun f52 (S7 S9) S1)
(declare-fun f53 () S5)
(declare-fun f54 () S3)
(declare-fun f55 () S9)
(declare-fun f56 () S13)
(declare-fun f57 () S11)
(declare-fun f58 () S7)
(declare-fun f59 (S3) S3)
(declare-fun f60 (S7) S7)
(declare-fun f61 (S11) S11)
(declare-fun f62 (S9) S9)
(declare-fun f63 (S5) S5)
(declare-fun f64 (S26 S27) S5)
(declare-fun f65 () S27)
(declare-fun f66 (S26) S5)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) true)))
(assert (forall ((?v0 S4)) (= (= (f5 f6 ?v0) f1) true)))
(assert (forall ((?v0 S6)) (= (= (f7 f8 ?v0) f1) true)))
(assert (forall ((?v0 S8)) (= (= (f9 f10 ?v0) f1) true)))
(assert (forall ((?v0 S10)) (= (= (f11 f12 ?v0) f1) true)))
(assert (forall ((?v0 S4) (?v1 S5)) (= (= (f13 ?v0 ?v1) f1) (= (f5 ?v1 ?v0) f1))))
(assert (forall ((?v0 S8) (?v1 S9)) (= (= (f14 ?v0 ?v1) f1) (= (f9 ?v1 ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S13)) (= (= (f15 ?v0 ?v1) f1) (= (f16 ?v1 ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S11)) (= (= (f17 ?v0 ?v1) f1) (= (f11 ?v1 ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S7)) (= (= (f18 ?v0 ?v1) f1) (= (f7 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f19 ?v0 ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f20 (f21 f22 ?v0) ?v1) (f20 (f21 f22 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (= (f23 (f24 f25 ?v0) ?v1) (f23 (f24 f25 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10)) (= (= (f26 (f27 f28 ?v0) ?v1) (f26 (f27 f28 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (= (= (f29 (f30 f31 ?v0) ?v1) (f29 (f30 f31 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (= (= (f32 (f33 f34 ?v0) ?v1) (f32 (f33 f34 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5)) (= (= (f35 ?v0) f1) (forall ((?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f21 f22 ?v1))) (=> (= (f13 (f20 ?v_0 ?v2) ?v0) f1) (=> (= (f13 (f20 (f21 f22 ?v2) ?v3) ?v0) f1) (= (f13 (f20 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S9)) (= (= (f36 ?v0) f1) (forall ((?v1 S6) (?v2 S6) (?v3 S6)) (let ((?v_0 (f24 f25 ?v1))) (=> (= (f14 (f23 ?v_0 ?v2) ?v0) f1) (=> (= (f14 (f23 (f24 f25 ?v2) ?v3) ?v0) f1) (= (f14 (f23 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S13)) (= (= (f37 ?v0) f1) (forall ((?v1 S10) (?v2 S10) (?v3 S10)) (let ((?v_0 (f27 f28 ?v1))) (=> (= (f15 (f26 ?v_0 ?v2) ?v0) f1) (=> (= (f15 (f26 (f27 f28 ?v2) ?v3) ?v0) f1) (= (f15 (f26 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S11)) (= (= (f38 ?v0) f1) (forall ((?v1 S8) (?v2 S8) (?v3 S8)) (let ((?v_0 (f30 f31 ?v1))) (=> (= (f17 (f29 ?v_0 ?v2) ?v0) f1) (=> (= (f17 (f29 (f30 f31 ?v2) ?v3) ?v0) f1) (= (f17 (f29 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S7)) (= (= (f39 ?v0) f1) (forall ((?v1 S4) (?v2 S4) (?v3 S4)) (let ((?v_0 (f33 f34 ?v1))) (=> (= (f18 (f32 ?v_0 ?v2) ?v0) f1) (=> (= (f18 (f32 (f33 f34 ?v2) ?v3) ?v0) f1) (= (f18 (f32 ?v_0 ?v3) ?v0) f1))))))))
(assert (forall ((?v0 S5)) (= (= (f40 ?v0) f1) (forall ((?v1 S2)) (not (= (f13 (f20 (f21 f22 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S9)) (= (= (f41 ?v0) f1) (forall ((?v1 S6)) (not (= (f14 (f23 (f24 f25 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S13)) (= (= (f42 ?v0) f1) (forall ((?v1 S10)) (not (= (f15 (f26 (f27 f28 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S11)) (= (= (f43 ?v0) f1) (forall ((?v1 S8)) (not (= (f17 (f29 (f30 f31 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S7)) (= (= (f44 ?v0) f1) (forall ((?v1 S4)) (not (= (f18 (f32 (f33 f34 ?v1) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f45 ?v0 ?v1) f1) (forall ((?v2 S2)) (=> (= (f19 ?v2 ?v0) f1) (forall ((?v3 S2)) (=> (= (f19 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f13 (f20 (f21 f22 ?v2) ?v3) ?v1) f1) (= (f13 (f20 (f21 f22 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S5) (?v1 S7)) (= (= (f46 ?v0 ?v1) f1) (forall ((?v2 S4)) (=> (= (f13 ?v2 ?v0) f1) (forall ((?v3 S4)) (=> (= (f13 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f18 (f32 (f33 f34 ?v2) ?v3) ?v1) f1) (= (f18 (f32 (f33 f34 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S9) (?v1 S11)) (= (= (f47 ?v0 ?v1) f1) (forall ((?v2 S8)) (=> (= (f14 ?v2 ?v0) f1) (forall ((?v3 S8)) (=> (= (f14 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f17 (f29 (f30 f31 ?v2) ?v3) ?v1) f1) (= (f17 (f29 (f30 f31 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S13) (?v1 S24)) (= (= (f48 ?v0 ?v1) f1) (forall ((?v2 S12)) (=> (= (f15 ?v2 ?v0) f1) (forall ((?v3 S12)) (=> (= (f15 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f49 (f50 ?v2 ?v3) ?v1) f1) (= (f49 (f50 ?v3 ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S11) (?v1 S13)) (= (= (f51 ?v0 ?v1) f1) (forall ((?v2 S10)) (=> (= (f17 ?v2 ?v0) f1) (forall ((?v3 S10)) (=> (= (f17 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f15 (f26 (f27 f28 ?v2) ?v3) ?v1) f1) (= (f15 (f26 (f27 f28 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S7) (?v1 S9)) (= (= (f52 ?v0 ?v1) f1) (forall ((?v2 S6)) (=> (= (f18 ?v2 ?v0) f1) (forall ((?v3 S6)) (=> (= (f18 ?v3 ?v0) f1) (=> (not (= ?v2 ?v3)) (or (= (f14 (f23 (f24 f25 ?v2) ?v3) ?v1) f1) (= (f14 (f23 (f24 f25 ?v3) ?v2) ?v1) f1))))))))))
(assert (forall ((?v0 S4)) (= (= (f13 ?v0 f53) f1) true)))
(assert (forall ((?v0 S2)) (= (= (f19 ?v0 f54) f1) true)))
(assert (forall ((?v0 S8)) (= (= (f14 ?v0 f55) f1) true)))
(assert (forall ((?v0 S12)) (= (= (f15 ?v0 f56) f1) true)))
(assert (forall ((?v0 S10)) (= (= (f17 ?v0 f57) f1) true)))
(assert (forall ((?v0 S6)) (= (= (f18 ?v0 f58) f1) true)))
(assert (= f54 (f59 f4)))
(assert (= f58 (f60 f8)))
(assert (= f57 (f61 f12)))
(assert (= f55 (f62 f10)))
(assert (= f53 (f63 f6)))
(assert (not (forall ((?v0 S26) (?v1 S2) (?v2 S2)) (let ((?v_0 (forall ((?v3 S27)) (let ((?v_3 (f64 ?v0 ?v3))) (and (= (f35 ?v_3) f1) (and (= (f40 ?v_3) f1) (= (f45 f54 ?v_3) f1)))))) (?v_2 (f20 (f21 f22 ?v1) ?v2)) (?v_1 (f66 ?v0))) (=> (forall ((?v3 S26)) (=> (forall ((?v4 S27)) (let ((?v_4 (f64 ?v3 ?v4))) (and (= (f35 ?v_4) f1) (and (= (f40 ?v_4) f1) (= (f45 f54 ?v_4) f1))))) (forall ((?v4 S2) (?v5 S2)) (let ((?v_5 (f20 (f21 f22 ?v4) ?v5))) (=> (not (= ?v4 ?v5)) (=> (= (f13 ?v_5 (f64 ?v3 f65)) f1) (= (f13 ?v_5 (f66 ?v3)) f1))))))) (=> ?v_0 (=> (= (f13 ?v_2 ?v_1) f1) (=> (=> ?v_0 (and (= (f35 ?v_1) f1) (and (= (f40 ?v_1) f1) (= (f45 f54 ?v_1) f1)))) (= (f13 ?v_2 (f64 ?v0 f65)) f1)))))))))
(check-sat)
(exit)
