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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S4 S5) S2)
(declare-fun f6 (S6 S7) S4)
(declare-fun f7 (S8 S7) S6)
(declare-fun f8 () S8)
(declare-fun f9 () S7)
(declare-fun f10 () S7)
(declare-fun f11 (S9 S5) S5)
(declare-fun f12 (S10 S11) S9)
(declare-fun f13 () S10)
(declare-fun f14 () S11)
(declare-fun f15 (S12 S11) S5)
(declare-fun f16 () S12)
(declare-fun f17 () S11)
(declare-fun f18 (S13 S7) S3)
(declare-fun f19 (S14 S7) S13)
(declare-fun f20 (S15 S11) S14)
(declare-fun f21 (S11) S15)
(declare-fun f22 (S2 S3) S1)
(declare-fun f23 (S16) S3)
(declare-fun f24 (S17 S16) S16)
(declare-fun f25 (S18 S3) S17)
(declare-fun f26 () S18)
(declare-fun f27 (S11 S20) S1)
(declare-fun f28 (S19) S20)
(declare-fun f29 (S20 S11) S1)
(declare-fun f30 (S21 S19) S19)
(declare-fun f31 (S22 S20) S21)
(declare-fun f32 () S22)
(declare-fun f33 (S16 S24) S1)
(declare-fun f34 (S23) S24)
(declare-fun f35 (S24 S16) S1)
(declare-fun f36 (S25 S23) S23)
(declare-fun f37 (S26 S24) S25)
(declare-fun f38 () S26)
(declare-fun f39 (S7 S28) S1)
(declare-fun f40 (S27) S28)
(declare-fun f41 (S28 S7) S1)
(declare-fun f42 (S29 S27) S27)
(declare-fun f43 (S30 S28) S29)
(declare-fun f44 () S30)
(declare-fun f45 (S5 S32) S1)
(declare-fun f46 (S31) S32)
(declare-fun f47 (S32 S5) S1)
(declare-fun f48 (S33 S31) S31)
(declare-fun f49 (S34 S32) S33)
(declare-fun f50 () S34)
(declare-fun f51 () S17)
(declare-fun f52 () S33)
(declare-fun f53 () S29)
(declare-fun f54 () S25)
(declare-fun f55 () S21)
(declare-fun f56 (S32) S32)
(declare-fun f57 (S35 S16) S32)
(declare-fun f58 (S7) S35)
(declare-fun f59 () S7)
(declare-fun f60 (S16) S32)
(declare-fun f61 () S28)
(declare-fun f62 () S24)
(declare-fun f63 () S20)
(declare-fun f64 (S36 S7) S11)
(declare-fun f65 () S36)
(declare-fun f66 (S37 S5) S9)
(declare-fun f67 () S37)
(declare-fun f68 () S12)
(declare-fun f69 (S38 S7) S5)
(declare-fun f70 () S38)
(declare-fun f71 (S32) S32)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (not (= ?v0 (f5 (f6 (f7 f8 f9) f10) (f11 (f12 f13 f14) (f15 f16 f17))))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S7) (?v3 S7) (?v4 S2)) (= (= (f3 (f18 (f19 (f20 (f21 ?v0) ?v1) ?v2) ?v3) ?v4) f1) (not (= ?v4 (f5 (f6 (f7 f8 ?v2) ?v3) (f11 (f12 f13 ?v1) (f15 f16 ?v0))))))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S3) (?v3 S3)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S2)) (=> (= (f22 ?v4 (f23 ?v0)) f1) (= (= (f3 ?v2 ?v4) f1) (= (f3 ?v3 ?v4) f1)))) (= (f24 (f25 f26 ?v2) ?v0) (f24 (f25 f26 ?v3) ?v1))))))
(assert (forall ((?v0 S19) (?v1 S19) (?v2 S20) (?v3 S20)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S11)) (=> (= (f27 ?v4 (f28 ?v0)) f1) (= (= (f29 ?v2 ?v4) f1) (= (f29 ?v3 ?v4) f1)))) (= (f30 (f31 f32 ?v2) ?v0) (f30 (f31 f32 ?v3) ?v1))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S24) (?v3 S24)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S16)) (=> (= (f33 ?v4 (f34 ?v0)) f1) (= (= (f35 ?v2 ?v4) f1) (= (f35 ?v3 ?v4) f1)))) (= (f36 (f37 f38 ?v2) ?v0) (f36 (f37 f38 ?v3) ?v1))))))
(assert (forall ((?v0 S27) (?v1 S27) (?v2 S28) (?v3 S28)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S7)) (=> (= (f39 ?v4 (f40 ?v0)) f1) (= (= (f41 ?v2 ?v4) f1) (= (f41 ?v3 ?v4) f1)))) (= (f42 (f43 f44 ?v2) ?v0) (f42 (f43 f44 ?v3) ?v1))))))
(assert (forall ((?v0 S31) (?v1 S31) (?v2 S32) (?v3 S32)) (=> (= ?v0 ?v1) (=> (forall ((?v4 S5)) (=> (= (f45 ?v4 (f46 ?v0)) f1) (= (= (f47 ?v2 ?v4) f1) (= (f47 ?v3 ?v4) f1)))) (= (f48 (f49 f50 ?v2) ?v0) (f48 (f49 f50 ?v3) ?v1))))))
(assert (forall ((?v0 S16)) (= (f23 (f24 f51 ?v0)) (f23 ?v0))))
(assert (forall ((?v0 S31)) (= (f46 (f48 f52 ?v0)) (f46 ?v0))))
(assert (forall ((?v0 S27)) (= (f40 (f42 f53 ?v0)) (f40 ?v0))))
(assert (forall ((?v0 S23)) (= (f34 (f36 f54 ?v0)) (f34 ?v0))))
(assert (forall ((?v0 S19)) (= (f28 (f30 f55 ?v0)) (f28 ?v0))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f22 ?v0 ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S11) (?v1 S20)) (= (= (f27 ?v0 ?v1) f1) (= (f29 ?v1 ?v0) f1))))
(assert (forall ((?v0 S16) (?v1 S24)) (= (= (f33 ?v0 ?v1) f1) (= (f35 ?v1 ?v0) f1))))
(assert (forall ((?v0 S7) (?v1 S28)) (= (= (f39 ?v0 ?v1) f1) (= (f41 ?v1 ?v0) f1))))
(assert (forall ((?v0 S5) (?v1 S32)) (= (= (f45 ?v0 ?v1) f1) (= (f47 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S16)) (= (= (f24 (f25 f26 ?v0) ?v1) ?v1) (forall ((?v2 S2)) (=> (= (f22 ?v2 (f23 ?v1)) f1) (= (f3 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S20) (?v1 S19)) (= (= (f30 (f31 f32 ?v0) ?v1) ?v1) (forall ((?v2 S11)) (=> (= (f27 ?v2 (f28 ?v1)) f1) (= (f29 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S24) (?v1 S23)) (= (= (f36 (f37 f38 ?v0) ?v1) ?v1) (forall ((?v2 S16)) (=> (= (f33 ?v2 (f34 ?v1)) f1) (= (f35 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S28) (?v1 S27)) (= (= (f42 (f43 f44 ?v0) ?v1) ?v1) (forall ((?v2 S7)) (=> (= (f39 ?v2 (f40 ?v1)) f1) (= (f41 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S32) (?v1 S31)) (= (= (f48 (f49 f50 ?v0) ?v1) ?v1) (forall ((?v2 S5)) (=> (= (f45 ?v2 (f46 ?v1)) f1) (= (f47 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S5) (?v1 S16)) (=> (= (f45 ?v0 (f56 (f57 (f58 f59) ?v1))) f1) (= (f45 ?v0 (f60 ?v1)) f1))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S32)) (let ((?v_0 (f56 ?v2))) (=> (= (f45 (f11 (f12 f13 ?v0) ?v1) ?v_0) f1) (=> (=> (= (f45 ?v1 ?v_0) f1) false) false)))))
(assert (forall ((?v0 S16)) (let ((?v_0 (f58 f59))) (= (f57 ?v_0 ?v0) (f57 ?v_0 (f24 f51 ?v0))))))
(assert (not (forall ((?v0 S16) (?v1 S11) (?v2 S11) (?v3 S7) (?v4 S7) (?v5 S7)) (let ((?v_1 (f11 (f12 f13 f14) (f15 f16 f17))) (?v_2 (f58 f59)) (?v_3 (f15 f16 ?v1)) (?v_0 (f23 ?v0)) (?v_4 (f24 f51 ?v0))) (=> (not (= (f39 f10 f61) f1)) (=> (not (= (f39 f9 f61) f1)) (=> (= (f33 ?v0 f62) f1) (=> (not (= (f45 ?v_3 (f60 ?v0)) f1)) (=> (= (f27 ?v2 f63) f1) (=> (= (f22 (f5 (f6 (f7 f8 ?v3) ?v4) (f11 (f12 f13 (f64 f65 ?v4)) (f11 (f66 f67 (f15 f68 ?v2)) (f69 f70 ?v5)))) ?v_0) f1) (=> (not (= (f45 (f15 f68 f14) (f71 (f57 ?v_2 ?v0))) f1)) (=> (=> (= (f22 (f5 (f6 (f7 f8 f9) f10) ?v_1) ?v_0) f1) (not (= (f45 ?v_1 (f56 (f57 ?v_2 (f24 (f25 f26 f4) ?v_4)))) f1))) (=> (and (= f9 ?v4) (and (= f10 ?v5) (and (= f14 ?v2) (= f17 ?v1)))) (not (= (f45 (f11 (f12 f13 ?v2) ?v_3) (f56 (f57 ?v_2 (f24 (f25 f26 (f18 (f19 (f20 (f21 ?v1) ?v2) ?v4) ?v5)) ?v_4)))) f1)))))))))))))))
(check-sat)
(exit)
