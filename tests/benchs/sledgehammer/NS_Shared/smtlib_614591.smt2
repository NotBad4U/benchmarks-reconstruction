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
(declare-sort S39 0)
(declare-sort S40 0)
(declare-sort S41 0)
(declare-sort S42 0)
(declare-sort S43 0)
(declare-sort S44 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S4 S5) S1)
(declare-fun f6 (S6 S4) S4)
(declare-fun f7 (S7 S4) S6)
(declare-fun f8 () S7)
(declare-fun f9 (S5) S5)
(declare-fun f10 (S9 S10) S6)
(declare-fun f11 () S9)
(declare-fun f12 (S11 S2) S10)
(declare-fun f13 () S11)
(declare-fun f14 (S12 S8) S5)
(declare-fun f15 (S2) S12)
(declare-fun f16 () S2)
(declare-fun f17 (S2 S3) S1)
(declare-fun f18 () S3)
(declare-fun f19 (S13 S2) S4)
(declare-fun f20 () S13)
(declare-fun f21 (S14 S10) S4)
(declare-fun f22 () S14)
(declare-fun f23 (S5) S5)
(declare-fun f24 (S8 S15) S1)
(declare-fun f25 () S15)
(declare-fun f26 (S10 S16) S1)
(declare-fun f27 (S17 S3) S16)
(declare-fun f28 (S11) S17)
(declare-fun f29 () S3)
(declare-fun f30 (S18 S19) S1)
(declare-fun f31 (S20 S4) S18)
(declare-fun f32 (S21 S2) S20)
(declare-fun f33 (S22 S2) S21)
(declare-fun f34 () S22)
(declare-fun f35 (S8) S19)
(declare-fun f36 (S24 S25) S1)
(declare-fun f37 (S23 S2) S24)
(declare-fun f38 (S26 S3) S25)
(declare-fun f39 (S23) S26)
(declare-fun f40 (S27 S24) S4)
(declare-fun f41 (S28 S25) S5)
(declare-fun f42 (S27) S28)
(declare-fun f43 () S25)
(declare-fun f44 (S29 S24) S2)
(declare-fun f45 (S30 S25) S3)
(declare-fun f46 (S29) S30)
(declare-fun f47 (S31 S24) S8)
(declare-fun f48 (S32 S25) S15)
(declare-fun f49 (S31) S32)
(declare-fun f50 (S33 S24) S10)
(declare-fun f51 (S34 S25) S16)
(declare-fun f52 (S33) S34)
(declare-fun f53 (S35 S24) S18)
(declare-fun f54 (S36 S25) S19)
(declare-fun f55 (S35) S36)
(declare-fun f56 (S3) S3)
(declare-fun f57 (S38 S5) S25)
(declare-fun f58 (S37) S38)
(declare-fun f59 (S37 S4) S24)
(declare-fun f60 (S40 S15) S25)
(declare-fun f61 (S39) S40)
(declare-fun f62 (S39 S8) S24)
(declare-fun f63 (S42 S16) S25)
(declare-fun f64 (S41) S42)
(declare-fun f65 (S41 S10) S24)
(declare-fun f66 (S44 S19) S25)
(declare-fun f67 (S43) S44)
(declare-fun f68 (S43 S18) S24)
(declare-fun f69 () S2)
(declare-fun f70 () S2)
(declare-fun f71 () S14)
(declare-fun f72 () S10)
(declare-fun f73 () S2)
(declare-fun f74 () S10)
(declare-fun f75 () S4)
(declare-fun f76 () S8)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) true)))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S5)) (let ((?v_0 (f9 ?v2))) (=> (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v_0) f1) (= (f5 ?v1 ?v_0) f1)))))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S8)) (let ((?v_0 (f9 (f14 (f15 f16) ?v2)))) (=> (= (f5 (f6 (f10 f11 (f12 f13 ?v0)) ?v1) ?v_0) f1) (=> (= (f17 ?v0 f18) f1) (= (f5 ?v1 ?v_0) f1))))))
(assert (forall ((?v0 S2) (?v1 S4) (?v2 S2) (?v3 S10) (?v4 S4) (?v5 S8)) (let ((?v_0 (f7 f8 (f21 f22 ?v3)))) (=> (= (f5 (f6 (f10 f11 (f12 f13 ?v0)) (f6 (f7 f8 ?v1) (f6 (f7 f8 (f19 f20 ?v2)) (f6 ?v_0 ?v4)))) (f23 (f14 (f15 f16) ?v5))) f1) (=> (not (= (f17 ?v0 f18) f1)) (=> (= (f24 ?v5 f25) f1) (and (not (= (f26 ?v3 (f27 (f28 f13) f29)) f1)) (= ?v4 (f6 (f10 f11 (f12 f13 ?v2)) (f6 ?v_0 (f19 f20 ?v0)))))))))))
(assert (forall ((?v0 S4) (?v1 S5)) (=> (not (= (f5 ?v0 (f23 ?v1)) f1)) (not (= (f5 ?v0 (f9 ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S4) (?v3 S8)) (=> (= (f30 (f31 (f32 (f33 f34 ?v0) ?v1) ?v2) (f35 ?v3)) f1) (= (f5 ?v2 (f9 (f14 (f15 f16) ?v3))) f1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S5)) (let ((?v_0 (f9 ?v2))) (=> (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v_0) f1) (=> (=> (= (f5 ?v0 ?v_0) f1) (=> (= (f5 ?v1 ?v_0) f1) false)) false)))))
(assert (forall ((?v0 S23) (?v1 S2)) (= (f36 (f37 ?v0 ?v1) (f38 (f39 ?v0) f29)) f1)))
(assert (forall ((?v0 S27) (?v1 S24)) (= (f5 (f40 ?v0 ?v1) (f41 (f42 ?v0) f43)) f1)))
(assert (forall ((?v0 S29) (?v1 S24)) (= (f17 (f44 ?v0 ?v1) (f45 (f46 ?v0) f43)) f1)))
(assert (forall ((?v0 S31) (?v1 S24)) (= (f24 (f47 ?v0 ?v1) (f48 (f49 ?v0) f43)) f1)))
(assert (forall ((?v0 S33) (?v1 S24)) (= (f26 (f50 ?v0 ?v1) (f51 (f52 ?v0) f43)) f1)))
(assert (forall ((?v0 S35) (?v1 S24)) (= (f30 (f53 ?v0 ?v1) (f54 (f55 ?v0) f43)) f1)))
(assert (forall ((?v0 S11) (?v1 S2)) (= (f26 (f12 ?v0 ?v1) (f27 (f28 ?v0) f29)) f1)))
(assert (= f29 (f56 f4)))
(assert (forall ((?v0 S4) (?v1 S27) (?v2 S25)) (= (= (f5 ?v0 (f41 (f42 ?v1) ?v2)) f1) (exists ((?v3 S24)) (and (= (f36 ?v3 ?v2) f1) (= ?v0 (f40 ?v1 ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S29) (?v2 S25)) (= (= (f17 ?v0 (f45 (f46 ?v1) ?v2)) f1) (exists ((?v3 S24)) (and (= (f36 ?v3 ?v2) f1) (= ?v0 (f44 ?v1 ?v3)))))))
(assert (forall ((?v0 S8) (?v1 S31) (?v2 S25)) (= (= (f24 ?v0 (f48 (f49 ?v1) ?v2)) f1) (exists ((?v3 S24)) (and (= (f36 ?v3 ?v2) f1) (= ?v0 (f47 ?v1 ?v3)))))))
(assert (forall ((?v0 S10) (?v1 S33) (?v2 S25)) (= (= (f26 ?v0 (f51 (f52 ?v1) ?v2)) f1) (exists ((?v3 S24)) (and (= (f36 ?v3 ?v2) f1) (= ?v0 (f50 ?v1 ?v3)))))))
(assert (forall ((?v0 S18) (?v1 S35) (?v2 S25)) (= (= (f30 ?v0 (f54 (f55 ?v1) ?v2)) f1) (exists ((?v3 S24)) (and (= (f36 ?v3 ?v2) f1) (= ?v0 (f53 ?v1 ?v3)))))))
(assert (forall ((?v0 S24) (?v1 S37) (?v2 S5)) (= (= (f36 ?v0 (f57 (f58 ?v1) ?v2)) f1) (exists ((?v3 S4)) (and (= (f5 ?v3 ?v2) f1) (= ?v0 (f59 ?v1 ?v3)))))))
(assert (forall ((?v0 S24) (?v1 S23) (?v2 S3)) (= (= (f36 ?v0 (f38 (f39 ?v1) ?v2)) f1) (exists ((?v3 S2)) (and (= (f17 ?v3 ?v2) f1) (= ?v0 (f37 ?v1 ?v3)))))))
(assert (forall ((?v0 S24) (?v1 S39) (?v2 S15)) (= (= (f36 ?v0 (f60 (f61 ?v1) ?v2)) f1) (exists ((?v3 S8)) (and (= (f24 ?v3 ?v2) f1) (= ?v0 (f62 ?v1 ?v3)))))))
(assert (forall ((?v0 S24) (?v1 S41) (?v2 S16)) (= (= (f36 ?v0 (f63 (f64 ?v1) ?v2)) f1) (exists ((?v3 S10)) (and (= (f26 ?v3 ?v2) f1) (= ?v0 (f65 ?v1 ?v3)))))))
(assert (forall ((?v0 S24) (?v1 S43) (?v2 S19)) (= (= (f36 ?v0 (f66 (f67 ?v1) ?v2)) f1) (exists ((?v3 S18)) (and (= (f30 ?v3 ?v2) f1) (= ?v0 (f68 ?v1 ?v3)))))))
(assert (forall ((?v0 S10) (?v1 S11) (?v2 S3)) (= (= (f26 ?v0 (f27 (f28 ?v1) ?v2)) f1) (exists ((?v3 S2)) (and (= (f17 ?v3 ?v2) f1) (= ?v0 (f12 ?v1 ?v3)))))))
(assert (let ((?v_0 (f7 f8 (f21 f22 f74)))) (not (=> (= (f30 (f31 (f32 (f33 f34 f69) f70) (f6 (f10 f11 (f12 f13 f70)) (f6 (f7 f8 (f21 f71 f72)) (f6 (f7 f8 (f19 f20 f73)) (f6 ?v_0 f75))))) (f35 f76)) f1) (=> (= (f24 f76 f25) f1) (or (and (not (= (f26 f74 (f27 (f28 f13) f29)) f1)) (= f75 (f6 (f10 f11 (f12 f13 f73)) (f6 ?v_0 (f19 f20 f70))))) (= (f5 f75 (f9 (f14 (f15 f16) f76))) f1)))))))
(check-sat)
(exit)