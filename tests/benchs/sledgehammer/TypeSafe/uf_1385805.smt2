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
(declare-sort S35 0)
(declare-sort S36 0)
(declare-sort S37 0)
(declare-sort S38 0)
(declare-sort S39 0)
(declare-sort S40 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S4 S5) S2)
(declare-fun f5 (S6) S4)
(declare-fun f6 () S6)
(declare-fun f7 () S5)
(declare-fun f8 () S3)
(declare-fun f9 (S6 S7 S5 S8 S9) S1)
(declare-fun f10 (S10 S3) S7)
(declare-fun f11 () S10)
(declare-fun f12 () S3)
(declare-fun f13 () S8)
(declare-fun f14 () S9)
(declare-fun f15 (S11 S12) S1)
(declare-fun f16 (S13 S14) S11)
(declare-fun f17 (S15 S14) S13)
(declare-fun f18 () S15)
(declare-fun f19 (S16 S3) S14)
(declare-fun f20 (S17 S8) S16)
(declare-fun f21 () S17)
(declare-fun f22 () S8)
(declare-fun f23 (S12) S12)
(declare-fun f24 (S6) S12)
(declare-fun f25 (S18 S6) S1)
(declare-fun f26 () S18)
(declare-fun f27 (S19 S9) S1)
(declare-fun f28 (S20 S9) S19)
(declare-fun f29 (S6) S20)
(declare-fun f30 () S10)
(declare-fun f31 (S7 S7) S1)
(declare-fun f32 (S5 S5) S1)
(declare-fun f33 (S21 S8) S8)
(declare-fun f34 (S22 S8) S21)
(declare-fun f35 () S22)
(declare-fun f36 (S6 S7 S5 S8 S9) S1)
(declare-fun f37 (S25 S26) S1)
(declare-fun f38 (S27 S28) S25)
(declare-fun f39 (S29 S28) S27)
(declare-fun f40 () S29)
(declare-fun f41 (S30 S3) S28)
(declare-fun f42 (S31 S23) S30)
(declare-fun f43 () S31)
(declare-fun f44 (S6) S26)
(declare-fun f45 (S6 S7 S5 S23 S24) S1)
(declare-fun f46 (S6 S5 S8 S9) S1)
(declare-fun f47 (S26) S26)
(declare-fun f48 (S20 S24 S24) S1)
(declare-fun f49 (S32 S11) S14)
(declare-fun f50 () S32)
(declare-fun f51 (S33 S14) S8)
(declare-fun f52 () S33)
(declare-fun f53 (S34 S25) S28)
(declare-fun f54 () S34)
(declare-fun f55 (S35 S28) S23)
(declare-fun f56 () S35)
(declare-fun f57 (S37 S36) S3)
(declare-fun f58 (S38 S7) S37)
(declare-fun f59 () S38)
(declare-fun f60 (S12 S11) S1)
(declare-fun f61 (S39 S14) S1)
(declare-fun f62 (S26 S25) S1)
(declare-fun f63 (S40 S28) S1)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 (f5 f6) f7) f8) f1)))
(assert (= (f9 f6 (f10 f11 f12) f7 f13 f14) f1))
(assert (= (f3 (f4 (f5 f6) f7) f12) f1))
(assert (= (f15 (f16 (f17 f18 (f19 (f20 f21 f13) f12)) (f19 (f20 f21 f22) f8)) (f23 (f24 f6))) f1))
(assert (= (f15 (f16 (f17 f18 (f19 (f20 f21 f13) f12)) (f19 (f20 f21 f22) f8)) (f23 (f24 f6))) f1))
(assert (= (f25 f26 f6) f1))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S8) (?v3 S3) (?v4 S6) (?v5 S5) (?v6 S9)) (let ((?v_0 (f4 (f5 ?v4) ?v5))) (=> (= (f15 (f16 (f17 f18 (f19 (f20 f21 ?v0) ?v1)) (f19 (f20 f21 ?v2) ?v3)) (f24 ?v4)) f1) (=> (= (f9 ?v4 (f10 f11 ?v1) ?v5 ?v0 ?v6) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v3) f1)))))))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S3) (?v3 S8) (?v4 S3) (?v5 S5) (?v6 S9)) (=> (= (f25 f26 ?v0) f1) (=> (= (f15 (f16 (f17 f18 (f19 (f20 f21 ?v1) ?v2)) (f19 (f20 f21 ?v3) ?v4)) (f24 ?v0)) f1) (=> (= (f3 (f4 (f5 ?v0) ?v5) ?v2) f1) (=> (= (f9 ?v0 (f10 f11 ?v2) ?v5 ?v1 ?v6) f1) (exists ((?v7 S9)) (and (= (f9 ?v0 (f10 f11 ?v4) ?v5 ?v3 ?v7) f1) (= (f27 (f28 (f29 ?v0) ?v7) ?v6) f1)))))))))
(assert (= f11 f30))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S5) (?v3 S8) (?v4 S9) (?v5 S7)) (=> (= (f9 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f31 ?v1 ?v5) f1) (= (f9 ?v0 ?v5 ?v2 ?v3 ?v4) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S5) (?v3 S8) (?v4 S9) (?v5 S5)) (=> (= (f9 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f32 ?v2 ?v5) f1) (= (f9 ?v0 ?v1 ?v5 ?v3 ?v4) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S5) (?v3 S8) (?v4 S9) (?v5 S8) (?v6 S9)) (=> (= (f9 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f9 ?v0 ?v1 ?v2 ?v5 ?v6) f1) (= (f9 ?v0 ?v1 ?v2 (f33 (f34 f35 ?v3) ?v5) ?v6) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S5) (?v3 S8) (?v4 S9)) (= (= (f36 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (= (f9 ?v0 ?v1 ?v2 ?v3 ?v4) f1))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S5) (?v3 S8) (?v4 S9)) (=> (= (f36 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (= (f9 ?v0 ?v1 ?v2 ?v3 ?v4) f1))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S5) (?v3 S8) (?v4 S9)) (=> (= (f9 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (= (f36 ?v0 ?v1 ?v2 ?v3 ?v4) f1))))
(assert (forall ((?v0 S23) (?v1 S3) (?v2 S23) (?v3 S3) (?v4 S6) (?v5 S5) (?v6 S24)) (let ((?v_0 (f4 (f5 ?v4) ?v5))) (=> (= (f37 (f38 (f39 f40 (f41 (f42 f43 ?v0) ?v1)) (f41 (f42 f43 ?v2) ?v3)) (f44 ?v4)) f1) (=> (= (f45 ?v4 (f10 f11 ?v1) ?v5 ?v0 ?v6) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v3) f1)))))))
(assert (forall ((?v0 S6) (?v1 S5) (?v2 S8) (?v3 S9) (?v4 S7)) (=> (= (f46 ?v0 ?v1 ?v2 ?v3) f1) (= (f9 ?v0 ?v4 ?v1 ?v2 ?v3) f1))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S5) (?v3 S23) (?v4 S24) (?v5 S7)) (=> (= (f45 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f31 ?v1 ?v5) f1) (= (f45 ?v0 ?v5 ?v2 ?v3 ?v4) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S5) (?v3 S8) (?v4 S9) (?v5 S8) (?v6 S9)) (=> (= (f36 ?v0 ?v1 ?v2 ?v3 ?v4) f1) (=> (= (f36 ?v0 ?v1 ?v2 ?v5 ?v6) f1) (= (f36 ?v0 ?v1 ?v2 (f33 (f34 f35 ?v3) ?v5) ?v6) f1)))))
(assert (forall ((?v0 S6) (?v1 S5) (?v2 S8) (?v3 S9) (?v4 S8) (?v5 S9)) (=> (= (f46 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f46 ?v0 ?v1 ?v4 ?v5) f1) (= (f46 ?v0 ?v1 (f33 (f34 f35 ?v2) ?v4) ?v5) f1)))))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S8) (?v3 S3) (?v4 S6) (?v5 S8)) (let ((?v_0 (f23 (f24 ?v4)))) (=> (= (f15 (f16 (f17 f18 (f19 (f20 f21 ?v0) ?v1)) (f19 (f20 f21 ?v2) ?v3)) ?v_0) f1) (= (f15 (f16 (f17 f18 (f19 (f20 f21 (f33 (f34 f35 ?v0) ?v5)) ?v1)) (f19 (f20 f21 (f33 (f34 f35 ?v2) ?v5)) ?v3)) ?v_0) f1)))))
(assert (forall ((?v0 S14) (?v1 S12)) (= (f15 (f16 (f17 f18 ?v0) ?v0) (f23 ?v1)) f1)))
(assert (forall ((?v0 S28) (?v1 S26)) (= (f37 (f38 (f39 f40 ?v0) ?v0) (f47 ?v1)) f1)))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S8) (?v3 S3) (?v4 S6) (?v5 S8)) (let ((?v_0 (f24 ?v4))) (=> (= (f15 (f16 (f17 f18 (f19 (f20 f21 ?v0) ?v1)) (f19 (f20 f21 ?v2) ?v3)) ?v_0) f1) (= (f15 (f16 (f17 f18 (f19 (f20 f21 (f33 (f34 f35 ?v0) ?v5)) ?v1)) (f19 (f20 f21 (f33 (f34 f35 ?v2) ?v5)) ?v3)) ?v_0) f1)))))
(assert (forall ((?v0 S6) (?v1 S5) (?v2 S8) (?v3 S9) (?v4 S5)) (=> (= (f46 ?v0 ?v1 ?v2 ?v3) f1) (=> (= (f32 ?v1 ?v4) f1) (= (f46 ?v0 ?v4 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S7)) (= (f31 ?v0 ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S9)) (= (f27 (f28 (f29 ?v0) ?v1) ?v1) f1)))
(assert (forall ((?v0 S11) (?v1 S12)) (=> (= (f15 ?v0 ?v1) f1) (= (f15 ?v0 (f23 ?v1)) f1))))
(assert (forall ((?v0 S25) (?v1 S26)) (=> (= (f37 ?v0 ?v1) f1) (= (f37 ?v0 (f47 ?v1)) f1))))
(assert (forall ((?v0 S6) (?v1 S23) (?v2 S3) (?v3 S23) (?v4 S3) (?v5 S5) (?v6 S24)) (=> (= (f25 f26 ?v0) f1) (=> (= (f37 (f38 (f39 f40 (f41 (f42 f43 ?v1) ?v2)) (f41 (f42 f43 ?v3) ?v4)) (f44 ?v0)) f1) (=> (= (f3 (f4 (f5 ?v0) ?v5) ?v2) f1) (=> (= (f45 ?v0 (f10 f11 ?v2) ?v5 ?v1 ?v6) f1) (exists ((?v7 S24)) (and (= (f45 ?v0 (f10 f11 ?v4) ?v5 ?v3 ?v7) f1) (= (f48 (f29 ?v0) ?v7 ?v6) f1)))))))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f49 f50 (f16 (f17 f18 ?v0) ?v1)) ?v0)))
(assert (forall ((?v0 S8) (?v1 S3)) (= (f51 f52 (f19 (f20 f21 ?v0) ?v1)) ?v0)))
(assert (forall ((?v0 S28) (?v1 S28)) (= (f53 f54 (f38 (f39 f40 ?v0) ?v1)) ?v0)))
(assert (forall ((?v0 S23) (?v1 S3)) (= (f55 f56 (f41 (f42 f43 ?v0) ?v1)) ?v0)))
(assert (forall ((?v0 S7) (?v1 S36)) (= (f10 f30 (f57 (f58 f59 ?v0) ?v1)) ?v0)))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (=> (= (f49 f50 (f16 (f17 f18 ?v0) ?v1)) ?v2) (= ?v0 ?v2))))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S8)) (=> (= (f51 f52 (f19 (f20 f21 ?v0) ?v1)) ?v2) (= ?v0 ?v2))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (=> (= (f53 f54 (f38 (f39 f40 ?v0) ?v1)) ?v2) (= ?v0 ?v2))))
(assert (forall ((?v0 S23) (?v1 S3) (?v2 S23)) (=> (= (f55 f56 (f41 (f42 f43 ?v0) ?v1)) ?v2) (= ?v0 ?v2))))
(assert (forall ((?v0 S7) (?v1 S36) (?v2 S7)) (=> (= (f10 f30 (f57 (f58 f59 ?v0) ?v1)) ?v2) (= ?v0 ?v2))))
(assert (forall ((?v0 S6) (?v1 S24)) (= (f48 (f29 ?v0) ?v1 ?v1) f1)))
(assert (forall ((?v0 S6) (?v1 S24) (?v2 S24) (?v3 S24)) (let ((?v_0 (f29 ?v0))) (=> (= (f48 ?v_0 ?v1 ?v2) f1) (=> (= (f48 ?v_0 ?v2 ?v3) f1) (= (f48 ?v_0 ?v1 ?v3) f1))))))
(assert (forall ((?v0 S8) (?v1 S7) (?v2 S36) (?v3 S8) (?v4 S7) (?v5 S36) (?v6 S6)) (=> (= (f15 (f16 (f17 f18 (f19 (f20 f21 ?v0) (f57 (f58 f59 ?v1) ?v2))) (f19 (f20 f21 ?v3) (f57 (f58 f59 ?v4) ?v5))) (f24 ?v6)) f1) (= (f31 ?v1 ?v4) f1))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (=> (= (f16 (f17 f18 ?v0) ?v1) (f16 (f17 f18 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S8) (?v3 S3)) (=> (= (f19 (f20 f21 ?v0) ?v1) (f19 (f20 f21 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f38 (f39 f40 ?v0) ?v1) (f38 (f39 f40 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S23) (?v1 S3) (?v2 S23) (?v3 S3)) (=> (= (f41 (f42 f43 ?v0) ?v1) (f41 (f42 f43 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S7) (?v1 S36) (?v2 S7) (?v3 S36)) (=> (= (f57 (f58 f59 ?v0) ?v1) (f57 (f58 f59 ?v2) ?v3)) (=> (=> (= ?v0 ?v2) (=> (= ?v1 ?v3) false)) false))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14) (?v3 S14)) (= (= (f16 (f17 f18 ?v0) ?v1) (f16 (f17 f18 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S8) (?v1 S3) (?v2 S8) (?v3 S3)) (= (= (f19 (f20 f21 ?v0) ?v1) (f19 (f20 f21 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (= (= (f38 (f39 f40 ?v0) ?v1) (f38 (f39 f40 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S23) (?v1 S3) (?v2 S23) (?v3 S3)) (= (= (f41 (f42 f43 ?v0) ?v1) (f41 (f42 f43 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S7) (?v1 S36) (?v2 S7) (?v3 S36)) (= (= (f57 (f58 f59 ?v0) ?v1) (f57 (f58 f59 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S12)) (= (forall ((?v1 S11)) (= (f60 ?v0 ?v1) f1)) (forall ((?v1 S14) (?v2 S14)) (= (f60 ?v0 (f16 (f17 f18 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S39)) (= (forall ((?v1 S14)) (= (f61 ?v0 ?v1) f1)) (forall ((?v1 S8) (?v2 S3)) (= (f61 ?v0 (f19 (f20 f21 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S26)) (= (forall ((?v1 S25)) (= (f62 ?v0 ?v1) f1)) (forall ((?v1 S28) (?v2 S28)) (= (f62 ?v0 (f38 (f39 f40 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S40)) (= (forall ((?v1 S28)) (= (f63 ?v0 ?v1) f1)) (forall ((?v1 S23) (?v2 S3)) (= (f63 ?v0 (f41 (f42 f43 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2)) (= (forall ((?v1 S3)) (= (f3 ?v0 ?v1) f1)) (forall ((?v1 S7) (?v2 S36)) (= (f3 ?v0 (f57 (f58 f59 ?v1) ?v2)) f1)))))
(check-sat)
(exit)
