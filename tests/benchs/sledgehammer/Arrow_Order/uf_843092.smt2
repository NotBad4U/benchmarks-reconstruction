(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")
(set-info :status unknown)
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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S5) S1)
(declare-fun f6 (S6 S2) S5)
(declare-fun f7 () S6)
(declare-fun f8 (S7 S5) S5)
(declare-fun f9 (S8 S5) S7)
(declare-fun f10 () S8)
(declare-fun f11 () S5)
(declare-fun f12 () S5)
(declare-fun f13 () S4)
(declare-fun f14 () S4)
(declare-fun f15 () S3)
(declare-fun f16 (S9 S10) S4)
(declare-fun f17 (S4) S9)
(declare-fun f18 () S3)
(declare-fun f19 () S10)
(declare-fun f20 (S11 S10) S9)
(declare-fun f21 (S4) S11)
(declare-fun f22 () S10)
(declare-fun f23 (S4) S9)
(declare-fun f24 (S5) S3)
(declare-fun f25 (S5) S3)
(declare-fun f26 (S12 S10) S1)
(declare-fun f27 (S13 S10) S12)
(declare-fun f28 (S4) S13)
(declare-fun f29 (S14 S4) S1)
(declare-fun f30 (S15) S14)
(declare-fun f31 (S16 S10) S15)
(declare-fun f32 (S17 S10) S16)
(declare-fun f33 () S17)
(declare-fun f34 (S4) S3)
(declare-fun f35 (S18 S3) S14)
(declare-fun f36 () S18)
(declare-fun f37 () S14)
(declare-fun f38 () S10)
(declare-fun f39 () S10)
(declare-fun f40 () S10)
(declare-fun f41 (S3 S19) S1)
(declare-fun f42 () S19)
(declare-fun f43 (S20 S5) S2)
(declare-fun f44 (S21 S6) S20)
(declare-fun f45 (S22 S23) S21)
(declare-fun f46 () S22)
(declare-fun f47 () S23)
(declare-fun f48 (S6 S23) S1)
(declare-fun f49 (S4 S14) S1)
(declare-fun f50 (S24 S23) S5)
(declare-fun f51 () S24)
(declare-fun f52 (S25 S3) S4)
(declare-fun f53 () S25)
(declare-fun f54 (S5 S5) S1)
(declare-fun f55 (S25) S1)
(declare-fun f56 (S25) S1)
(declare-fun f57 (S25 S26) S1)
(declare-fun f58 (S27 S18) S26)
(declare-fun f59 (S19) S27)
(declare-fun f60 (S28 S28) S1)
(declare-fun f61 (S29 S28) S28)
(declare-fun f62 (S30 S28) S29)
(declare-fun f63 () S30)
(declare-fun f64 () S28)
(declare-fun f65 (S28 S28) S1)
(declare-fun f66 (S23 S2) S1)
(declare-fun f67 (S4 S15) S1)
(declare-fun f68 () S4)
(declare-fun f69 (S19 S3) S1)
(declare-fun f70 () S19)
(declare-fun f71 () S14)
(declare-fun f72 (S26 S25) S1)
(declare-fun f73 () S26)
(declare-fun f74 (S2 S23) S1)
(declare-fun f75 (S13 S13) S1)
(declare-fun f76 (S4) S14)
(declare-fun f77 (S23 S23) S1)
(declare-fun f78 (S19 S19) S1)
(declare-fun f79 (S14 S14) S1)
(declare-fun f80 (S26 S26) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (ite (= (f5 (f6 f7 ?v0) (f8 (f9 f10 f11) f12)) f1) f13 f14))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f6 f7 ?v0)) (?v_1 (f3 f18 ?v0))) (= (f3 f15 ?v0) (ite (= (f5 ?v_0 f11) f1) (f16 (f17 ?v_1) f19) (ite (= ?v_0 f11) (f16 (f20 (f21 ?v_1) f22) f19) (f16 (f23 ?v_1) f19)))))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (f3 (f24 ?v0) ?v1) (ite (= (f5 (f6 f7 ?v1) (f8 (f9 f10 ?v0) f12)) f1) f13 f14))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (f3 (f25 ?v0) ?v1) (ite (= (f5 (f6 f7 ?v1) ?v0) f1) f13 f14))))
(assert (forall ((?v0 S4) (?v1 S10) (?v2 S10)) (= (= (f26 (f27 (f28 ?v0) ?v1) ?v2) f1) (= (f29 (f30 (f31 (f32 f33 ?v1) ?v2)) ?v0) f1))))
(assert (forall ((?v0 S4) (?v1 S2)) (= (f3 (f34 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S3)) (= (f35 f36 ?v0) f37)))
(assert (not (forall ((?v0 S2)) (let ((?v_0 (f6 f7 ?v0))) (let ((?v_2 (= (f5 ?v_0 f11) f1)) (?v_1 (f3 f18 ?v0))) (= (= (f29 (f30 (f31 (f32 f33 f19) f38)) (ite ?v_2 (f16 (f17 ?v_1) f19) (ite (= ?v_0 f11) (f16 (f20 (f21 ?v_1) f22) f19) (f16 (f23 ?v_1) f19)))) f1) (= (f29 (f30 (f31 (f32 f33 f39) f40)) (ite ?v_2 f13 f14)) f1)))))))
(assert (distinct f22 f38 f19))
(assert (= (f41 f18 f42) f1))
(assert (= (f29 (f30 (f31 (f32 f33 f22) f38)) (f3 f18 (f43 (f44 (f45 f46 f47) f7) f11))) f1))
(assert (= (f48 f7 f47) f1))
(assert (= (f41 f18 f42) f1))
(assert (= (f48 f7 f47) f1))
(assert (not (= f40 f39)))
(assert (not (= f22 f38)))
(assert (distinct f22 f38 f19))
(assert (= (f49 f13 f37) f1))
(assert (= (f49 f14 f37) f1))
(assert (= (f29 (f30 (f31 (f32 f33 f40) f39)) f13) f1))
(assert (= (f29 (f30 (f31 (f32 f33 f39) f40)) f14) f1))
(assert (= (f29 (f30 (f31 (f32 f33 f22) f38)) (f3 f18 (f43 (f44 (f45 f46 f47) f7) f11))) f1))
(assert (not (= (f29 (f30 (f31 (f32 f33 f40) f39)) f14) f1)))
(assert (not (= (f29 (f30 (f31 (f32 f33 f39) f40)) f13) f1)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f30 (f31 (f32 f33 f22) f38))) (?v_1 (f3 f18 ?v0)) (?v_2 (f6 f7 ?v0))) (= (= (f29 ?v_0 ?v_1) f1) (= (f29 ?v_0 (ite (= (f5 ?v_2 f11) f1) (f16 (f17 ?v_1) f19) (ite (= ?v_2 f11) (f16 (f20 (f21 ?v_1) f22) f19) (f16 (f23 ?v_1) f19)))) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S4) (?v3 S10)) (let ((?v_0 (f30 (f31 (f32 f33 ?v0) ?v1)))) (= (= (f29 ?v_0 (f16 (f23 ?v2) ?v3)) f1) (and (not (= ?v1 ?v3)) (ite (= ?v0 ?v3) (not (= ?v0 ?v1)) (= (f29 ?v_0 ?v2) f1)))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S4) (?v3 S10)) (let ((?v_0 (f30 (f31 (f32 f33 ?v0) ?v1)))) (= (= (f29 ?v_0 (f16 (f17 ?v2) ?v3)) f1) (and (not (= ?v0 ?v3)) (ite (= ?v1 ?v3) (not (= ?v0 ?v1)) (= (f29 ?v_0 ?v2) f1)))))))
(assert (=> (forall ((?v0 S10)) (=> (distinct f22 f38 ?v0) false)) false))
(assert (= (f5 f11 (f50 f51 f47)) f1))
(assert (forall ((?v0 S2)) (let ((?v_0 (f6 f7 ?v0)) (?v_1 (f3 f18 ?v0))) (= (= (f29 (f30 (f31 (f32 f33 f22) f19)) (ite (= (f5 ?v_0 f11) f1) (f16 (f17 ?v_1) f19) (ite (= ?v_0 f11) (f16 (f20 (f21 ?v_1) f22) f19) (f16 (f23 ?v_1) f19)))) f1) (= (f29 (f30 (f31 (f32 f33 f40) f39)) (ite (= (f5 ?v_0 (f8 (f9 f10 f11) f12)) f1) f13 f14)) f1)))))
(assert (=> (forall ((?v0 S4)) (=> (= (f29 (f30 (f31 (f32 f33 f40) f39)) ?v0) f1) (=> (= (f49 ?v0 f37) f1) false))) false))
(assert (=> (forall ((?v0 S4)) (=> (= (f29 (f30 (f31 (f32 f33 f39) f40)) ?v0) f1) (=> (= (f49 ?v0 f37) f1) false))) false))
(assert (= (f41 f15 f42) f1))
(assert (let ((?v_0 (f30 (f31 (f32 f33 f22) f38)))) (= (= (f29 ?v_0 (f52 f53 f18)) f1) (= (f29 ?v_0 (f52 f53 f15)) f1))))
(assert (= (f29 (f30 (f31 (f32 f33 f22) f19)) (f52 f53 f15)) f1))
(assert (= (= (f29 (f30 (f31 (f32 f33 f22) f19)) (f52 f53 f15)) f1) (= (f29 (f30 (f31 (f32 f33 f40) f39)) (f52 f53 f4)) f1)))
(assert (forall ((?v0 S5)) (=> (= (f54 ?v0 f11) f1) (= (f29 (f30 (f31 (f32 f33 f39) f40)) (f52 f53 (f25 ?v0))) f1))))
(assert (forall ((?v0 S5)) (= (f41 (f25 ?v0) f42) f1)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S4) (?v3 S10) (?v4 S10)) (let ((?v_0 (f32 f33 ?v3))) (let ((?v_1 (f30 (f31 ?v_0 ?v4)))) (=> (not (= ?v0 ?v1)) (=> (= (f49 ?v2 f37) f1) (= (= (f29 ?v_1 (f16 (f20 (f21 ?v2) ?v0) ?v1)) f1) (and (not (= ?v3 ?v4)) (ite (= ?v3 ?v1) (= (f29 (f30 (f31 (f32 f33 ?v0) ?v4)) ?v2) f1) (ite (= ?v4 ?v1) (or (= ?v3 ?v0) (= (f29 (f30 (f31 ?v_0 ?v0)) ?v2) f1)) (= (f29 ?v_1 ?v2) f1)))))))))))
(assert (= (f55 f53) f1))
(assert (= (f56 f53) f1))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S3) (?v3 S3)) (=> (not (= ?v0 ?v1)) (=> (= (f41 ?v2 f42) f1) (=> (= (f41 ?v3 f42) f1) (=> (forall ((?v4 S2)) (= (= (f29 (f30 (f31 (f32 f33 ?v0) ?v1)) (f3 ?v2 ?v4)) f1) (= (f29 (f30 (f31 (f32 f33 ?v1) ?v0)) (f3 ?v3 ?v4)) f1))) (= (= (f29 (f30 (f31 (f32 f33 ?v0) ?v1)) (f52 f53 ?v2)) f1) (= (f29 (f30 (f31 (f32 f33 ?v1) ?v0)) (f52 f53 ?v3)) f1))))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10) (?v4 S3) (?v5 S3)) (=> (not (= ?v0 ?v1)) (=> (not (= ?v2 ?v3)) (=> (= (f41 ?v4 f42) f1) (=> (= (f41 ?v5 f42) f1) (=> (forall ((?v6 S2)) (= (= (f29 (f30 (f31 (f32 f33 ?v0) ?v1)) (f3 ?v4 ?v6)) f1) (= (f29 (f30 (f31 (f32 f33 ?v2) ?v3)) (f3 ?v5 ?v6)) f1))) (= (= (f29 (f30 (f31 (f32 f33 ?v0) ?v1)) (f52 f53 ?v4)) f1) (= (f29 (f30 (f31 (f32 f33 ?v2) ?v3)) (f52 f53 ?v5)) f1)))))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S3) (?v4 S3)) (=> (not (= ?v0 ?v1)) (=> (not (= ?v1 ?v2)) (=> (not (= ?v0 ?v2)) (=> (= (f41 ?v3 f42) f1) (=> (= (f41 ?v4 f42) f1) (=> (forall ((?v5 S2)) (= (= (f29 (f30 (f31 (f32 f33 ?v0) ?v1)) (f3 ?v3 ?v5)) f1) (= (f29 (f30 (f31 (f32 f33 ?v1) ?v2)) (f3 ?v4 ?v5)) f1))) (= (= (f29 (f30 (f31 (f32 f33 ?v0) ?v1)) (f52 f53 ?v3)) f1) (= (f29 (f30 (f31 (f32 f33 ?v1) ?v2)) (f52 f53 ?v4)) f1))))))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10) (?v4 S3) (?v5 S3)) (=> (not (= ?v0 ?v1)) (=> (not (= ?v2 ?v3)) (=> (not (= ?v0 ?v3)) (=> (not (= ?v1 ?v2)) (=> (= (f41 ?v4 f42) f1) (=> (= (f41 ?v5 f42) f1) (=> (forall ((?v6 S2)) (= (= (f29 (f30 (f31 (f32 f33 ?v0) ?v1)) (f3 ?v4 ?v6)) f1) (= (f29 (f30 (f31 (f32 f33 ?v2) ?v3)) (f3 ?v5 ?v6)) f1))) (=> (= (f29 (f30 (f31 (f32 f33 ?v0) ?v1)) (f52 f53 ?v4)) f1) (= (f29 (f30 (f31 (f32 f33 ?v2) ?v3)) (f52 f53 ?v5)) f1)))))))))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10) (?v3 S10) (?v4 S3) (?v5 S3)) (=> (not (= ?v0 ?v1)) (=> (not (= ?v2 ?v3)) (=> (not (= ?v0 ?v3)) (=> (not (= ?v1 ?v2)) (=> (= (f41 ?v4 f42) f1) (=> (= (f41 ?v5 f42) f1) (=> (forall ((?v6 S2)) (= (= (f29 (f30 (f31 (f32 f33 ?v0) ?v1)) (f3 ?v4 ?v6)) f1) (= (f29 (f30 (f31 (f32 f33 ?v2) ?v3)) (f3 ?v5 ?v6)) f1))) (= (= (f29 (f30 (f31 (f32 f33 ?v0) ?v1)) (f52 f53 ?v4)) f1) (= (f29 (f30 (f31 (f32 f33 ?v2) ?v3)) (f52 f53 ?v5)) f1)))))))))))
(assert (= (f29 (f30 (f31 (f32 f33 f40) f39)) (f52 f53 f4)) f1))
(assert (= (f57 f53 (f58 (f59 f42) f36)) f1))
(assert (exists ((?v0 S5)) (and (= (f5 ?v0 (f50 f51 f47)) f1) (and (forall ((?v1 S5)) (=> (= (f54 ?v1 ?v0) f1) (= (f29 (f30 (f31 (f32 f33 f39) f40)) (f52 f53 (f25 ?v1))) f1))) (= (f29 (f30 (f31 (f32 f33 f40) f39)) (f52 f53 (f24 ?v0))) f1)))))
(assert (=> (forall ((?v0 S5)) (=> (= (f5 ?v0 (f50 f51 f47)) f1) (=> (forall ((?v1 S5)) (=> (= (f54 ?v1 ?v0) f1) (= (f29 (f30 (f31 (f32 f33 f39) f40)) (f52 f53 (f25 ?v1))) f1))) (=> (= (f29 (f30 (f31 (f32 f33 f40) f39)) (f52 f53 (f24 ?v0))) f1) false)))) false))
(assert (forall ((?v0 S4)) (=> (= (f49 ?v0 f37) f1) (= (f41 (f34 ?v0) f42) f1))))
(assert (forall ((?v0 S4) (?v1 S10) (?v2 S10)) (=> (= (f49 ?v0 f37) f1) (=> (= (f29 (f30 (f31 (f32 f33 ?v1) ?v2)) ?v0) f1) (=> (= (f29 (f30 (f31 (f32 f33 ?v2) ?v1)) ?v0) f1) false)))))
(assert (forall ((?v0 S4) (?v1 S10) (?v2 S10)) (=> (= (f49 ?v0 f37) f1) (=> (not (= ?v1 ?v2)) (= (not (= (f29 (f30 (f31 (f32 f33 ?v1) ?v2)) ?v0) f1)) (= (f29 (f30 (f31 (f32 f33 ?v2) ?v1)) ?v0) f1))))))
(assert (forall ((?v0 S4) (?v1 S10)) (=> (= (f49 ?v0 f37) f1) (= (f49 (f16 (f17 ?v0) ?v1) f37) f1))))
(assert (forall ((?v0 S4) (?v1 S10)) (=> (= (f49 ?v0 f37) f1) (= (f49 (f16 (f23 ?v0) ?v1) f37) f1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S4)) (=> (not (= ?v0 ?v1)) (=> (= (f49 ?v2 f37) f1) (= (f49 (f16 (f20 (f21 ?v2) ?v0) ?v1) f37) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (not (= ?v0 ?v1)) (exists ((?v2 S10)) (distinct ?v0 ?v1 ?v2)))))
(assert (forall ((?v0 S6) (?v1 S2)) (=> (= (f48 ?v0 f47) f1) (= (f43 (f44 (f45 f46 f47) ?v0) (f6 ?v0 ?v1)) ?v1))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S5)) (=> (= (f48 ?v0 f47) f1) (=> (= (f6 ?v0 ?v1) ?v2) (= (f43 (f44 (f45 f46 f47) ?v0) ?v2) ?v1)))))
(assert (forall ((?v0 S5)) (= (f5 ?v0 (f8 (f9 f10 ?v0) f12)) f1)))
(assert (forall ((?v0 S28)) (= (f60 ?v0 (f61 (f62 f63 ?v0) f64)) f1)))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (=> (= (f5 ?v0 ?v1) f1) (=> (= (f54 ?v2 ?v3) f1) (= (f5 (f8 (f9 f10 ?v0) ?v2) (f8 (f9 f10 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f60 ?v0 ?v1) f1) (=> (= (f65 ?v2 ?v3) f1) (= (f60 (f61 (f62 f63 ?v0) ?v2) (f61 (f62 f63 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (=> (= (f54 ?v0 ?v1) f1) (=> (= (f5 ?v2 ?v3) f1) (= (f5 (f8 (f9 f10 ?v0) ?v2) (f8 (f9 f10 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28) (?v3 S28)) (=> (= (f65 ?v0 ?v1) f1) (=> (= (f60 ?v2 ?v3) f1) (= (f60 (f61 (f62 f63 ?v0) ?v2) (f61 (f62 f63 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (not (= ?v0 ?v1)) (exists ((?v2 S4)) (and (= (f49 ?v2 f37) f1) (= (f29 (f30 (f31 (f32 f33 ?v0) ?v1)) ?v2) f1))))))
(assert (forall ((?v0 S2)) (= (f66 f47 ?v0) f1)))
(assert (forall ((?v0 S15)) (= (f67 f68 ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f69 f70 ?v0) f1)))
(assert (forall ((?v0 S4)) (= (f29 f71 ?v0) f1)))
(assert (forall ((?v0 S25)) (= (f72 f73 ?v0) f1)))
(assert (forall ((?v0 S25)) (= (f57 ?v0 f73) f1)))
(assert (forall ((?v0 S4)) (= (f49 ?v0 f71) f1)))
(assert (forall ((?v0 S3)) (= (f41 ?v0 f70) f1)))
(assert (forall ((?v0 S15)) (= (f29 (f30 ?v0) f68) f1)))
(assert (forall ((?v0 S2)) (= (f74 ?v0 f47) f1)))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f75 (f28 ?v0) (f28 ?v1)) f1) (= (f29 (f76 ?v0) ?v1) f1))))
(assert (forall ((?v0 S23)) (= (f77 ?v0 f47) f1)))
(assert (forall ((?v0 S4)) (= (f29 (f76 ?v0) f68) f1)))
(assert (forall ((?v0 S19)) (= (f78 ?v0 f70) f1)))
(assert (forall ((?v0 S14)) (= (f79 ?v0 f71) f1)))
(assert (forall ((?v0 S26)) (= (f80 ?v0 f73) f1)))
(assert (forall ((?v0 S28) (?v1 S28)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f60 ?v0 ?v1) f1) false) (=> (=> (= (f60 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f8 (f9 f10 ?v0) ?v1) (f8 (f9 f10 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (=> (= (f61 (f62 f63 ?v0) ?v1) (f61 (f62 f63 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (=> (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f61 ?v_0 ?v1) (f61 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (=> (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f62 f63 ?v0))) (=> (= (f61 ?v_0 ?v1) (f61 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (= (= (f8 (f9 f10 ?v0) ?v1) (f8 (f9 f10 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (= (= (f61 (f62 f63 ?v0) ?v1) (f61 (f62 f63 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f62 f63 ?v0))) (= (= (f61 ?v_0 ?v1) (f61 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f9 f10 ?v0))) (= (f8 (f9 f10 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f9 f10 ?v1) ?v2))))))
(assert (forall ((?v0 S28) (?v1 S28) (?v2 S28)) (let ((?v_0 (f62 f63 ?v0))) (= (f61 (f62 f63 (f61 ?v_0 ?v1)) ?v2) (f61 ?v_0 (f61 (f62 f63 ?v1) ?v2))))))
(assert (forall ((?v0 S5)) (= (= f12 ?v0) (= ?v0 f12))))
(assert (forall ((?v0 S28)) (= (= f64 ?v0) (= ?v0 f64))))
(check-sat)
(exit)