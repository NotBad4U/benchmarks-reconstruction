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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S3) S2)
(declare-fun f5 (S4 S5) S3)
(declare-fun f6 () S4)
(declare-fun f7 (S6 S5) S5)
(declare-fun f8 (S7 S5) S6)
(declare-fun f9 () S7)
(declare-fun f10 (S8 S9) S5)
(declare-fun f11 () S8)
(declare-fun f12 (S10 S9) S9)
(declare-fun f13 (S11 S10) S10)
(declare-fun f14 (S12 S10) S11)
(declare-fun f15 () S12)
(declare-fun f16 () S10)
(declare-fun f17 () S10)
(declare-fun f18 () S9)
(declare-fun f19 (S13 S3) S5)
(declare-fun f20 (S14 S3) S13)
(declare-fun f21 () S14)
(declare-fun f22 () S3)
(declare-fun f23 () S3)
(declare-fun f24 () S3)
(declare-fun f25 (S15 S3) S3)
(declare-fun f26 (S16 S3) S15)
(declare-fun f27 () S16)
(declare-fun f28 () S15)
(declare-fun f29 () S16)
(declare-fun f30 () S4)
(declare-fun f31 () S4)
(declare-fun f32 () S16)
(declare-fun f33 (S17 S18) S3)
(declare-fun f34 () S17)
(declare-fun f35 (S19 S18) S18)
(declare-fun f36 () S19)
(declare-fun f37 () S19)
(declare-fun f38 () S18)
(declare-fun f39 (S3) S2)
(declare-fun f40 (S10) S1)
(declare-fun f41 () S3)
(declare-fun f42 () S3)
(declare-fun f43 () S15)
(declare-fun f44 (S20 S18) S19)
(declare-fun f45 () S20)
(declare-fun f46 (S18 S18) S1)
(declare-fun f47 (S9 S9) S1)
(declare-fun f48 () S9)
(declare-fun f49 () S9)
(declare-fun f50 (S21 S9) S10)
(declare-fun f51 () S21)
(declare-fun f52 (S18 S18) S1)
(declare-fun f53 () S18)
(declare-fun f54 () S19)
(declare-fun f55 () S5)
(declare-fun f56 () S20)
(declare-fun f57 () S7)
(declare-fun f58 () S7)
(declare-fun f59 () S9)
(declare-fun f60 (S9 S9) S1)
(declare-fun f61 (S22 S18) S5)
(declare-fun f62 () S22)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 (f5 f6 (f7 (f8 f9 (f10 f11 (f12 (f13 (f14 f15 f16) f17) f18))) (f19 (f20 f21 f22) f23)))) f24) f1)))
(assert (let ((?v_0 (f10 f11 (f12 f16 (f12 f17 f18)))) (?v_1 (f25 (f26 f32 f24) (f33 f34 (f35 f36 (f35 f37 f38)))))) (= (f3 (f4 (f25 (f26 f27 (f25 f28 (f25 (f26 f29 (f5 f30 ?v_0)) f22))) (f25 f28 (f25 (f26 f29 (f5 f31 ?v_0)) f23)))) (f25 (f26 f27 ?v_1) ?v_1)) f1)))
(assert (let ((?v_1 (f19 (f20 f21 f22) f23)) (?v_0 (f10 f11 (f12 f16 (f12 f17 f18))))) (= (f3 (f39 (f5 f6 (f7 (f8 f9 ?v_0) ?v_1))) (f25 (f26 f27 (f25 f28 (f25 (f26 f29 (f5 f30 ?v_0)) (f5 f30 ?v_1)))) (f25 f28 (f25 (f26 f29 (f5 f31 ?v_0)) (f5 f31 ?v_1))))) f1)))
(assert (= (f40 f16) f1))
(assert (= (f40 f17) f1))
(assert (forall ((?v0 S9)) (= (f3 (f39 (f5 f6 (f10 f11 ?v0))) f41) f1)))
(assert (= (f3 (f4 f42) f24) f1))
(assert (let ((?v_1 (f19 (f20 f21 f22) f23)) (?v_0 (f10 f11 (f12 f16 (f12 f17 f18))))) (= (f3 (f39 (f5 f6 (f7 (f8 f9 ?v_0) ?v_1))) (f25 (f26 f27 (f25 f28 (f25 (f26 f29 (f5 f30 ?v_0)) (f5 f30 ?v_1)))) (f25 f28 (f25 (f26 f29 (f5 f31 ?v_0)) (f5 f31 ?v_1))))) f1)))
(assert (= (f40 (f13 (f14 f15 f16) f17)) f1))
(assert (let ((?v_0 (f10 f11 (f12 f16 (f12 f17 f18)))) (?v_1 (f25 (f26 f32 f24) (f33 f34 (f35 f36 (f35 f37 f38)))))) (= (f3 (f4 (f25 (f26 f27 (f25 f28 (f25 (f26 f29 (f5 f30 ?v_0)) f22))) (f25 f28 (f25 (f26 f29 (f5 f31 ?v_0)) f23)))) (f25 (f26 f27 ?v_1) ?v_1)) f1)))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f5 f6 (f7 (f8 f9 ?v0) ?v1)) (f5 f6 (f7 (f8 f9 ?v1) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f25 f43 (f25 (f26 f29 ?v0) ?v1)) (f25 f43 (f25 (f26 f29 ?v1) ?v0)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18) (?v3 S18)) (=> (= (f35 (f44 f45 ?v0) ?v1) (f35 (f44 f45 ?v2) ?v3)) (= (= (f46 ?v0 ?v1) f1) (= (f46 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f25 (f26 f29 ?v0) ?v1) (f25 (f26 f29 ?v2) ?v3)) (= (= (f3 (f4 ?v0) ?v1) f1) (= (f3 (f4 ?v2) ?v3) f1)))))
(assert (= (f47 f48 (f12 f17 f18)) f1))
(assert (forall ((?v0 S2)) (=> (exists ((?v1 S3)) (= (f3 ?v0 ?v1) f1)) (=> (exists ((?v1 S3)) (forall ((?v2 S3)) (=> (= (f3 ?v0 ?v2) f1) (= (f3 (f4 ?v2) ?v1) f1)))) (exists ((?v1 S3)) (forall ((?v2 S3)) (= (exists ((?v3 S3)) (and (= (f3 ?v0 ?v3) f1) (= (f3 (f4 ?v2) ?v3) f1))) (= (f3 (f4 ?v2) ?v1) f1))))))))
(assert (forall ((?v0 S9)) (=> (= (f47 f49 ?v0) f1) (= (f3 (f4 (f25 f28 (f25 (f26 f29 (f5 f31 (f10 f11 (f12 f16 (f12 f17 ?v0))))) f23))) (f25 (f26 f32 f24) (f33 f34 (f35 f36 (f35 f37 f38))))) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (f7 (f8 f9 (f19 (f20 f21 ?v0) ?v1)) (f19 (f20 f21 ?v2) ?v3)) (f19 (f20 f21 (f25 (f26 f29 ?v0) ?v2)) (f25 (f26 f29 ?v1) ?v3)))))
(assert (exists ((?v0 S9)) (forall ((?v1 S9)) (=> (= (f47 ?v0 ?v1) f1) (= (f3 (f4 (f25 f28 (f25 (f26 f29 (f5 f31 (f10 f11 (f12 f16 (f12 f17 ?v1))))) f23))) (f25 (f26 f32 f24) (f33 f34 (f35 f36 (f35 f37 f38))))) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (= (f19 (f20 f21 ?v0) ?v1) (f19 (f20 f21 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S9)) (=> (= (f47 f48 ?v0) f1) (= (f3 (f4 (f25 f28 (f25 (f26 f29 (f5 f30 (f10 f11 (f12 f16 ?v0)))) f22))) (f25 (f26 f32 f24) (f33 f34 (f35 f36 (f35 f37 f38))))) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f3 (f39 (f25 (f26 f29 (f5 f6 ?v0)) (f5 f6 ?v1))) (f5 f6 (f7 (f8 f9 ?v0) ?v1))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f39 (f25 (f26 f29 (f25 f43 ?v0)) (f25 f43 ?v1))) (f25 f43 (f25 (f26 f29 ?v0) ?v1))) f1)))
(assert (= (f3 (f39 f42) f41) f1))
(assert (= (f47 f49 f18) f1))
(assert (= (f3 (f4 f42) (f25 (f26 f32 f24) (f33 f34 (f35 f36 (f35 f37 f38))))) f1))
(assert (forall ((?v0 S3)) (=> (= (f3 (f4 f42) ?v0) f1) (exists ((?v1 S9)) (forall ((?v2 S9)) (=> (= (f47 ?v1 ?v2) f1) (= (f3 (f4 (f25 f28 (f25 (f26 f29 (f5 f30 (f10 f11 (f12 f16 ?v2)))) f22))) ?v0) f1)))))))
(assert (forall ((?v0 S3)) (=> (= (f3 (f4 f42) ?v0) f1) (exists ((?v1 S9)) (forall ((?v2 S9)) (=> (= (f47 ?v1 ?v2) f1) (= (f3 (f4 (f25 f28 (f25 (f26 f29 (f5 f31 (f10 f11 (f12 f16 (f12 f17 ?v2))))) f23))) ?v0) f1)))))))
(assert (= (f47 (f12 (f50 f51 f48) f49) f18) f1))
(assert (exists ((?v0 S9)) (forall ((?v1 S9)) (=> (= (f47 ?v0 ?v1) f1) (= (f3 (f4 (f25 f28 (f25 (f26 f29 (f5 f30 (f10 f11 (f12 f16 ?v1)))) f22))) (f25 (f26 f32 f24) (f33 f34 (f35 f36 (f35 f37 f38))))) f1)))))
(assert (forall ((?v0 S18)) (= (f52 f53 (f35 f54 ?v0)) f1)))
(assert (forall ((?v0 S3)) (= (f3 (f39 f42) (f25 f28 ?v0)) f1)))
(assert (forall ((?v0 S18)) (= (f52 ?v0 (f35 f54 ?v0)) f1)))
(assert (forall ((?v0 S3)) (= (f3 (f39 ?v0) (f25 f28 ?v0)) f1)))
(assert (= (f35 f54 f53) f53))
(assert (= (f25 f28 f42) f42))
(assert (= (f5 f6 f55) f42))
(assert (= (f25 f43 f42) f42))
(assert (forall ((?v0 S3)) (= (f25 f43 ?v0) (f25 f28 ?v0))))
(assert (forall ((?v0 S18)) (let ((?v_0 (f35 f54 ?v0))) (= (f35 f54 ?v_0) ?v_0))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f25 f28 ?v0))) (= (f25 f28 ?v_0) ?v_0))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f52 (f35 f54 (f35 (f44 f56 ?v0) ?v1)) (f35 (f44 f56 (f35 f54 ?v0)) (f35 f54 ?v1))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f39 (f25 f28 (f25 (f26 f27 ?v0) ?v1))) (f25 (f26 f27 (f25 f28 ?v0)) (f25 f28 ?v1))) f1)))
(assert (forall ((?v0 S18) (?v1 S18)) (let ((?v_0 (f35 (f44 f56 (f35 f54 ?v0)) (f35 f54 ?v1)))) (= (f35 f54 ?v_0) ?v_0))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f25 (f26 f27 (f25 f28 ?v0)) (f25 f28 ?v1)))) (= (f25 f28 ?v_0) ?v_0))))
(assert (forall ((?v0 S5)) (= (f7 (f8 f57 f55) ?v0) f55)))
(assert (forall ((?v0 S3)) (= (f25 (f26 f32 f42) ?v0) f42)))
(assert (forall ((?v0 S5)) (= (f7 (f8 f58 f55) ?v0) ?v0)))
(assert (forall ((?v0 S18)) (= (f35 (f44 f56 f53) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f25 (f26 f27 f42) ?v0) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f50 f51 f59) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (f7 (f8 f58 f55) ?v0) ?v0)))
(assert (forall ((?v0 S18)) (= (f35 (f44 f56 f53) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f25 (f26 f27 f42) ?v0) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f50 f51 f59) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (= (= f55 ?v0) (= ?v0 f55))))
(assert (forall ((?v0 S9)) (= (= f59 ?v0) (= ?v0 f59))))
(assert (forall ((?v0 S18)) (= (= f53 ?v0) (= ?v0 f53))))
(assert (forall ((?v0 S3)) (= (= f42 ?v0) (= ?v0 f42))))
(assert (forall ((?v0 S18)) (= (= (f52 f53 (f35 (f44 f56 ?v0) ?v0)) f1) (= (f52 f53 ?v0) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f39 f42))) (= (= (f3 ?v_0 (f25 (f26 f27 ?v0) ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S18)) (= (= f53 (f35 (f44 f56 ?v0) ?v0)) (= ?v0 f53))))
(assert (forall ((?v0 S3)) (= (= f42 (f25 (f26 f27 ?v0) ?v0)) (= ?v0 f42))))
(assert (forall ((?v0 S5)) (= (f7 (f8 f58 ?v0) f55) ?v0)))
(assert (forall ((?v0 S18)) (= (f35 (f44 f56 ?v0) f53) ?v0)))
(assert (forall ((?v0 S3)) (= (f25 (f26 f27 ?v0) f42) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f50 f51 ?v0) f59) ?v0)))
(assert (forall ((?v0 S5)) (= (f7 (f8 f58 ?v0) f55) ?v0)))
(assert (forall ((?v0 S18)) (= (f35 (f44 f56 ?v0) f53) ?v0)))
(assert (forall ((?v0 S3)) (= (f25 (f26 f27 ?v0) f42) ?v0)))
(assert (forall ((?v0 S9)) (= (f12 (f50 f51 ?v0) f59) ?v0)))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= ?v0 ?v1) (and (= (f5 f30 ?v0) (f5 f30 ?v1)) (= (f5 f31 ?v0) (f5 f31 ?v1))))))
(assert (forall ((?v0 S18)) (= (= (f35 f54 ?v0) f53) (= ?v0 f53))))
(assert (forall ((?v0 S3)) (= (= (f25 f28 ?v0) f42) (= ?v0 f42))))
(assert (forall ((?v0 S5)) (= (= (f5 f6 ?v0) f42) (= ?v0 f55))))
(assert (forall ((?v0 S3)) (= (= (f25 f43 ?v0) f42) (= ?v0 f42))))
(assert (forall ((?v0 S18)) (= (= (f52 (f35 f54 ?v0) f53) f1) (= ?v0 f53))))
(assert (forall ((?v0 S3)) (= (= (f3 (f39 (f25 f28 ?v0)) f42) f1) (= ?v0 f42))))
(assert (forall ((?v0 S5)) (= (= (f3 (f39 (f5 f6 ?v0)) f42) f1) (= ?v0 f55))))
(assert (forall ((?v0 S3)) (= (= (f3 (f39 (f25 f43 ?v0)) f42) f1) (= ?v0 f42))))
(assert (forall ((?v0 S18)) (= (= (f52 (f35 (f44 f56 ?v0) ?v0) f53) f1) (= (f52 ?v0 f53) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f39 (f25 (f26 f27 ?v0) ?v0)) f42) f1) (= (f3 (f39 ?v0) f42) f1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f8 f58 ?v0))) (= (f7 (f8 f58 (f7 ?v_0 ?v1)) ?v2) (f7 ?v_0 (f7 (f8 f58 ?v1) ?v2))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f44 f56 ?v0))) (= (f35 (f44 f56 (f35 ?v_0 ?v1)) ?v2) (f35 ?v_0 (f35 (f44 f56 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v0))) (= (f25 (f26 f27 (f25 ?v_0 ?v1)) ?v2) (f25 ?v_0 (f25 (f26 f27 ?v1) ?v2))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f50 f51 ?v0))) (= (f12 (f50 f51 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f50 f51 ?v1) ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (= (f7 (f8 f57 (f7 (f8 f58 ?v0) ?v1)) ?v2) (f7 (f8 f58 (f7 (f8 f57 ?v0) ?v2)) (f7 (f8 f57 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f25 (f26 f32 (f25 (f26 f27 ?v0) ?v1)) ?v2) (f25 (f26 f27 (f25 (f26 f32 ?v0) ?v2)) (f25 (f26 f32 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f8 f58 ?v0))) (= (= (f7 ?v_0 ?v1) (f7 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f44 f56 ?v0))) (= (= (f35 ?v_0 ?v1) (f35 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v0))) (= (= (f25 ?v_0 ?v1) (f25 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f50 f51 ?v0))) (= (= (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (= (= (f7 (f8 f58 ?v0) ?v1) (f7 (f8 f58 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (= (= (f35 (f44 f56 ?v0) ?v1) (f35 (f44 f56 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f25 (f26 f27 ?v0) ?v1) (f25 (f26 f27 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (= (= (f12 (f50 f51 ?v0) ?v1) (f12 (f50 f51 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (= (= (f52 (f35 (f44 f56 ?v0) ?v1) (f35 (f44 f56 ?v2) ?v1)) f1) (= (f52 ?v0 ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f3 (f39 (f25 (f26 f27 ?v0) ?v1)) (f25 (f26 f27 ?v2) ?v1)) f1) (= (f3 (f39 ?v0) ?v2) f1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (= (= (f47 (f12 (f50 f51 ?v0) ?v1) (f12 (f50 f51 ?v2) ?v1)) f1) (= (f47 ?v0 ?v2) f1))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f44 f56 ?v0))) (= (= (f52 (f35 ?v_0 ?v1) (f35 ?v_0 ?v2)) f1) (= (f52 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v0))) (= (= (f3 (f39 (f25 ?v_0 ?v1)) (f25 ?v_0 ?v2)) f1) (= (f3 (f39 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f50 f51 ?v0))) (= (= (f47 (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) f1) (= (f47 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S18)) (=> (= (f52 f53 ?v0) f1) (= (f35 f54 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (=> (= (f3 (f39 f42) ?v0) f1) (= (f25 f28 ?v0) ?v0))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f46 f53 ?v0) f1) (=> (= (f52 f53 ?v1) f1) (= (f46 f53 (f35 (f44 f56 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f42))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 (f39 f42) ?v1) f1) (= (f3 ?v_0 (f25 (f26 f27 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f60 f59 ?v0) f1) (=> (= (f47 f59 ?v1) f1) (= (f60 f59 (f12 (f50 f51 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f52 f53 ?v0) f1) (=> (= (f46 f53 ?v1) f1) (= (f46 f53 (f35 (f44 f56 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f42))) (=> (= (f3 (f39 f42) ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f25 (f26 f27 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f47 f59 ?v0) f1) (=> (= (f60 f59 ?v1) f1) (= (f60 f59 (f12 (f50 f51 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f52 f53 ?v0) f1) (=> (= (f52 f53 ?v1) f1) (= (f52 f53 (f35 (f44 f56 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f39 f42))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f25 (f26 f27 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f47 f59 ?v0) f1) (=> (= (f47 f59 ?v1) f1) (= (f47 f59 (f12 (f50 f51 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f52 f53 ?v0) f1) (=> (= (f52 f53 ?v1) f1) (= (= (f35 (f44 f56 ?v0) ?v1) f53) (and (= ?v0 f53) (= ?v1 f53)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f39 f42))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (= (f25 (f26 f27 ?v0) ?v1) f42) (and (= ?v0 f42) (= ?v1 f42))))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f47 f59 ?v0) f1) (=> (= (f47 f59 ?v1) f1) (= (= (f12 (f50 f51 ?v0) ?v1) f59) (and (= ?v0 f59) (= ?v1 f59)))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f46 f53 ?v0) f1) (=> (= (f52 ?v1 ?v2) f1) (= (f46 ?v1 (f35 (f44 f56 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f42) ?v0) f1) (=> (= (f3 (f39 ?v1) ?v2) f1) (= (f3 (f4 ?v1) (f25 (f26 f27 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f60 f59 ?v0) f1) (=> (= (f47 ?v1 ?v2) f1) (= (f60 ?v1 (f12 (f50 f51 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f52 f53 ?v0) f1) (=> (= (f46 ?v1 ?v2) f1) (= (f46 ?v1 (f35 (f44 f56 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 ?v1))) (=> (= (f3 (f39 f42) ?v0) f1) (=> (= (f3 ?v_0 ?v2) f1) (= (f3 ?v_0 (f25 (f26 f27 ?v0) ?v2)) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f47 f59 ?v0) f1) (=> (= (f60 ?v1 ?v2) f1) (= (f60 ?v1 (f12 (f50 f51 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f52 f53 ?v0) f1) (=> (= (f52 ?v1 ?v2) f1) (= (f52 ?v1 (f35 (f44 f56 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 ?v1))) (=> (= (f3 (f39 f42) ?v0) f1) (=> (= (f3 ?v_0 ?v2) f1) (= (f3 ?v_0 (f25 (f26 f27 ?v0) ?v2)) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f47 f59 ?v0) f1) (=> (= (f47 ?v1 ?v2) f1) (= (f47 ?v1 (f12 (f50 f51 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f52 f53 ?v0) f1) (=> (= (f52 ?v1 ?v2) f1) (= (f52 ?v1 (f35 (f44 f56 ?v2) ?v0)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f39 ?v1))) (=> (= (f3 (f39 f42) ?v0) f1) (=> (= (f3 ?v_0 ?v2) f1) (= (f3 ?v_0 (f25 (f26 f27 ?v2) ?v0)) f1))))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f47 f59 ?v0) f1) (=> (= (f47 ?v1 ?v2) f1) (= (f47 ?v1 (f12 (f50 f51 ?v2) ?v0)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f46 ?v0 f53) f1) (=> (= (f52 ?v1 f53) f1) (= (f46 (f35 (f44 f56 ?v0) ?v1) f53) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 ?v0) f42) f1) (=> (= (f3 (f39 ?v1) f42) f1) (= (f3 (f4 (f25 (f26 f27 ?v0) ?v1)) f42) f1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f60 ?v0 f59) f1) (=> (= (f47 ?v1 f59) f1) (= (f60 (f12 (f50 f51 ?v0) ?v1) f59) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f52 ?v0 f53) f1) (=> (= (f46 ?v1 f53) f1) (= (f46 (f35 (f44 f56 ?v0) ?v1) f53) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f39 ?v0) f42) f1) (=> (= (f3 (f4 ?v1) f42) f1) (= (f3 (f4 (f25 (f26 f27 ?v0) ?v1)) f42) f1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f47 ?v0 f59) f1) (=> (= (f60 ?v1 f59) f1) (= (f60 (f12 (f50 f51 ?v0) ?v1) f59) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f52 ?v0 f53) f1) (=> (= (f52 ?v1 f53) f1) (= (f52 (f35 (f44 f56 ?v0) ?v1) f53) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f39 ?v0) f42) f1) (=> (= (f3 (f39 ?v1) f42) f1) (= (f3 (f39 (f25 (f26 f27 ?v0) ?v1)) f42) f1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f47 ?v0 f59) f1) (=> (= (f47 ?v1 f59) f1) (= (f47 (f12 (f50 f51 ?v0) ?v1) f59) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f52 ?v0 ?v1) f1) (= (f52 (f35 (f44 f56 ?v0) ?v2) (f35 (f44 f56 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f39 ?v0) ?v1) f1) (= (f3 (f39 (f25 (f26 f27 ?v0) ?v2)) (f25 (f26 f27 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f47 ?v0 ?v1) f1) (= (f47 (f12 (f50 f51 ?v0) ?v2) (f12 (f50 f51 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f44 f56 ?v2))) (=> (= (f52 ?v0 ?v1) f1) (= (f52 (f35 ?v_0 ?v0) (f35 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v2))) (=> (= (f3 (f39 ?v0) ?v1) f1) (= (f3 (f39 (f25 ?v_0 ?v0)) (f25 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f50 f51 ?v2))) (=> (= (f47 ?v0 ?v1) f1) (= (f47 (f12 ?v_0 ?v0) (f12 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18) (?v3 S18)) (=> (= (f52 ?v0 ?v1) f1) (=> (= (f52 ?v2 ?v3) f1) (= (f52 (f35 (f44 f56 ?v0) ?v2) (f35 (f44 f56 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f39 ?v0) ?v1) f1) (=> (= (f3 (f39 ?v2) ?v3) f1) (= (f3 (f39 (f25 (f26 f27 ?v0) ?v2)) (f25 (f26 f27 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (=> (= (f47 ?v0 ?v1) f1) (=> (= (f47 ?v2 ?v3) f1) (= (f47 (f12 (f50 f51 ?v0) ?v2) (f12 (f50 f51 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f52 (f35 f54 ?v0) ?v1) f1) (= (f52 ?v0 ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f39 (f25 f28 ?v0)) ?v1) f1) (= (f3 (f39 ?v0) ?v1) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f5 f30 ?v0) (f5 f30 ?v1)) (=> (= (f5 f31 ?v0) (f5 f31 ?v1)) (= ?v0 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f8 f58 ?v0))) (=> (= (f7 ?v_0 ?v1) (f7 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f44 f56 ?v0))) (=> (= (f35 ?v_0 ?v1) (f35 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v0))) (=> (= (f25 ?v_0 ?v1) (f25 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f50 f51 ?v0))) (=> (= (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (let ((?v_0 (f8 f58 ?v0))) (=> (= (f7 ?v_0 ?v1) (f7 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f44 f56 ?v0))) (=> (= (f35 ?v_0 ?v1) (f35 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v0))) (=> (= (f25 ?v_0 ?v1) (f25 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f50 f51 ?v0))) (=> (= (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (=> (= (f7 (f8 f58 ?v0) ?v1) (f7 (f8 f58 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f35 (f44 f56 ?v0) ?v1) (f35 (f44 f56 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f25 (f26 f27 ?v0) ?v1) (f25 (f26 f27 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f12 (f50 f51 ?v0) ?v1) (f12 (f50 f51 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f52 (f35 (f44 f56 ?v0) ?v1) (f35 (f44 f56 ?v2) ?v1)) f1) (= (f52 ?v0 ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f39 (f25 (f26 f27 ?v0) ?v1)) (f25 (f26 f27 ?v2) ?v1)) f1) (= (f3 (f39 ?v0) ?v2) f1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f47 (f12 (f50 f51 ?v0) ?v1) (f12 (f50 f51 ?v2) ?v1)) f1) (= (f47 ?v0 ?v2) f1))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f44 f56 ?v0))) (=> (= (f52 (f35 ?v_0 ?v1) (f35 ?v_0 ?v2)) f1) (= (f52 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v0))) (=> (= (f3 (f39 (f25 ?v_0 ?v1)) (f25 ?v_0 ?v2)) f1) (= (f3 (f39 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f50 f51 ?v0))) (=> (= (f47 (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) f1) (= (f47 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (not (= ?v0 f55)) (= (f5 f6 (f7 (f8 f57 ?v1) ?v0)) (f25 (f26 f32 (f5 f6 ?v1)) (f5 f6 ?v0))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 f42)) (= (f25 f43 (f25 (f26 f32 ?v1) ?v0)) (f25 (f26 f32 (f25 f43 ?v1)) (f25 f43 ?v0))))))
(assert (forall ((?v0 S18)) (=> (= (f46 f53 ?v0) f1) (= (f35 f54 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (=> (= (f3 (f4 f42) ?v0) f1) (= (f25 f28 ?v0) ?v0))))
(assert (forall ((?v0 S18)) (= (= (f46 f53 (f35 f54 ?v0)) f1) (not (= ?v0 f53)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f42) (f25 f28 ?v0)) f1) (not (= ?v0 f42)))))
(assert (forall ((?v0 S18)) (not (= (f46 (f35 f54 ?v0) f53) f1))))
(assert (forall ((?v0 S3)) (not (= (f3 (f4 (f25 f28 ?v0)) f42) f1))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f46 ?v0 f53) f1) (=> (= (f46 ?v1 f53) f1) (= (f46 (f35 (f44 f56 ?v0) ?v1) f53) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 ?v0) f42) f1) (=> (= (f3 (f4 ?v1) f42) f1) (= (f3 (f4 (f25 (f26 f27 ?v0) ?v1)) f42) f1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f60 ?v0 f59) f1) (=> (= (f60 ?v1 f59) f1) (= (f60 (f12 (f50 f51 ?v0) ?v1) f59) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f46 f53 ?v0) f1) (=> (= (f46 f53 ?v1) f1) (= (f46 f53 (f35 (f44 f56 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f42))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f25 (f26 f27 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f60 f59 ?v0) f1) (=> (= (f60 f59 ?v1) f1) (= (f60 f59 (f12 (f50 f51 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S18)) (= (= (f46 (f35 (f44 f56 ?v0) ?v0) f53) f1) (= (f46 ?v0 f53) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 (f25 (f26 f27 ?v0) ?v0)) f42) f1) (= (f3 (f4 ?v0) f42) f1))))
(assert (forall ((?v0 S18)) (= (= (f46 f53 (f35 (f44 f56 ?v0) ?v0)) f1) (= (f46 f53 ?v0) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f42))) (= (= (f3 ?v_0 (f25 (f26 f27 ?v0) ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (= (f52 ?v0 ?v1) f1) (= (f52 (f35 (f44 f45 ?v0) ?v1) f53) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f39 ?v0) ?v1) f1) (= (f3 (f39 (f25 (f26 f29 ?v0) ?v1)) f42) f1))))
(assert (forall ((?v0 S5)) (= (f3 (f39 f42) (f5 f6 ?v0)) f1)))
(assert (forall ((?v0 S3)) (= (f3 (f39 f42) (f25 f43 ?v0)) f1)))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f7 (f8 f9 ?v0) ?v1) f55) (= ?v0 ?v1))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (= (f35 (f44 f45 ?v0) ?v1) f53) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f25 (f26 f29 ?v0) ?v1) f42) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= ?v0 ?v1) (= (f7 (f8 f9 ?v0) ?v1) f55))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (= ?v0 ?v1) (= (f35 (f44 f45 ?v0) ?v1) f53))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (= (f25 (f26 f29 ?v0) ?v1) f42))))
(assert (forall ((?v0 S5)) (= (f7 (f8 f9 ?v0) ?v0) f55)))
(assert (forall ((?v0 S18)) (= (f35 (f44 f45 ?v0) ?v0) f53)))
(assert (forall ((?v0 S3)) (= (f25 (f26 f29 ?v0) ?v0) f42)))
(assert (forall ((?v0 S5)) (= (f7 (f8 f9 ?v0) f55) ?v0)))
(assert (forall ((?v0 S18)) (= (f35 (f44 f45 ?v0) f53) ?v0)))
(assert (forall ((?v0 S3)) (= (f25 (f26 f29 ?v0) f42) ?v0)))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18) (?v3 S18)) (= (f52 (f35 f54 (f35 (f44 f45 (f35 (f44 f56 ?v0) ?v1)) (f35 (f44 f56 ?v2) ?v3))) (f35 (f44 f56 (f35 f54 (f35 (f44 f45 ?v0) ?v2))) (f35 f54 (f35 (f44 f45 ?v1) ?v3)))) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (f3 (f39 (f25 f28 (f25 (f26 f29 (f25 (f26 f27 ?v0) ?v1)) (f25 (f26 f27 ?v2) ?v3)))) (f25 (f26 f27 (f25 f28 (f25 (f26 f29 ?v0) ?v2))) (f25 f28 (f25 (f26 f29 ?v1) ?v3)))) f1)))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f52 (f35 f54 (f35 (f44 f45 ?v0) ?v1)) (f35 (f44 f56 (f35 f54 ?v0)) (f35 f54 ?v1))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f39 (f25 f28 (f25 (f26 f29 ?v0) ?v1))) (f25 (f26 f27 (f25 f28 ?v0)) (f25 f28 ?v1))) f1)))
(assert (forall ((?v0 S5)) (= (= (f3 (f4 f42) (f5 f6 ?v0)) f1) (not (= ?v0 f55)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f42) (f25 f43 ?v0)) f1) (not (= ?v0 f42)))))
(assert (forall ((?v0 S18)) (= (f5 f6 (f61 f62 ?v0)) (f25 f28 (f33 f34 ?v0)))))
(assert (forall ((?v0 S18)) (let ((?v_0 (f33 f34 ?v0))) (= (f25 f43 ?v_0) (f25 f28 ?v_0)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f3 (f39 (f25 (f26 f29 (f5 f6 ?v0)) (f5 f6 ?v1))) (f5 f6 (f7 (f8 f58 ?v0) ?v1))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f39 (f25 (f26 f29 (f25 f43 ?v0)) (f25 f43 ?v1))) (f25 f43 (f25 (f26 f27 ?v0) ?v1))) f1)))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f3 (f39 (f5 f6 (f7 (f8 f58 ?v0) ?v1))) (f25 (f26 f27 (f5 f6 ?v0)) (f5 f6 ?v1))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f39 (f25 f43 (f25 (f26 f27 ?v0) ?v1))) (f25 (f26 f27 (f25 f43 ?v0)) (f25 f43 ?v1))) f1)))
(assert (forall ((?v0 S5)) (= (f3 (f39 (f25 f28 (f5 f31 ?v0))) (f5 f6 ?v0)) f1)))
(assert (forall ((?v0 S5)) (= (f3 (f39 (f25 f28 (f5 f30 ?v0))) (f5 f6 ?v0)) f1)))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f52 (f35 (f44 f45 (f35 f54 ?v0)) (f35 f54 ?v1)) (f35 f54 (f35 (f44 f45 ?v1) ?v0))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f39 (f25 (f26 f29 (f25 f28 ?v0)) (f25 f28 ?v1))) (f25 f28 (f25 (f26 f29 ?v1) ?v0))) f1)))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f52 (f35 (f44 f45 (f35 f54 ?v0)) (f35 f54 ?v1)) (f35 f54 (f35 (f44 f45 ?v0) ?v1))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f39 (f25 (f26 f29 (f25 f28 ?v0)) (f25 f28 ?v1))) (f25 f28 (f25 (f26 f29 ?v0) ?v1))) f1)))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f52 (f35 f54 (f35 (f44 f45 (f35 f54 ?v0)) (f35 f54 ?v1))) (f35 f54 (f35 (f44 f45 ?v0) ?v1))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f39 (f25 f28 (f25 (f26 f29 (f25 f28 ?v0)) (f25 f28 ?v1)))) (f25 f28 (f25 (f26 f29 ?v0) ?v1))) f1)))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18) (?v3 S18)) (=> (= (f52 ?v0 ?v1) f1) (=> (= (f46 ?v2 ?v3) f1) (= (f46 (f35 (f44 f56 ?v0) ?v2) (f35 (f44 f56 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f39 ?v0) ?v1) f1) (=> (= (f3 (f4 ?v2) ?v3) f1) (= (f3 (f4 (f25 (f26 f27 ?v0) ?v2)) (f25 (f26 f27 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (=> (= (f47 ?v0 ?v1) f1) (=> (= (f60 ?v2 ?v3) f1) (= (f60 (f12 (f50 f51 ?v0) ?v2) (f12 (f50 f51 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18) (?v3 S18)) (=> (= (f46 ?v0 ?v1) f1) (=> (= (f52 ?v2 ?v3) f1) (= (f46 (f35 (f44 f56 ?v0) ?v2) (f35 (f44 f56 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f4 ?v0) ?v1) f1) (=> (= (f3 (f39 ?v2) ?v3) f1) (= (f3 (f4 (f25 (f26 f27 ?v0) ?v2)) (f25 (f26 f27 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (=> (= (f60 ?v0 ?v1) f1) (=> (= (f47 ?v2 ?v3) f1) (= (f60 (f12 (f50 f51 ?v0) ?v2) (f12 (f50 f51 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f5 f6 (f7 (f8 f57 ?v0) ?v1)) (f25 (f26 f32 (f5 f6 ?v0)) (f5 f6 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f25 f43 (f25 (f26 f32 ?v0) ?v1)) (f25 (f26 f32 (f25 f43 ?v0)) (f25 f43 ?v1)))))
(assert (forall ((?v0 S5)) (= (f19 (f20 f21 (f5 f30 ?v0)) (f5 f31 ?v0)) ?v0)))
(assert (forall ((?v0 S5)) (= (f3 (f39 (f5 f30 ?v0)) (f5 f6 ?v0)) f1)))
(assert (forall ((?v0 S18) (?v1 S18)) (= (= (f46 ?v0 ?v1) f1) (= (f46 (f35 (f44 f45 ?v0) ?v1) f53) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 ?v0) ?v1) f1) (= (f3 (f4 (f25 (f26 f29 ?v0) ?v1)) f42) f1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f5 f31 (f7 (f8 f9 ?v0) ?v1)) (f25 (f26 f29 (f5 f31 ?v0)) (f5 f31 ?v1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f5 f30 (f7 (f8 f9 ?v0) ?v1)) (f25 (f26 f29 (f5 f30 ?v0)) (f5 f30 ?v1)))))
(assert (forall ((?v0 S5)) (not (= (f3 (f4 (f5 f6 ?v0)) f42) f1))))
(assert (forall ((?v0 S3)) (not (= (f3 (f4 (f25 f43 ?v0)) f42) f1))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f35 f54 (f35 (f44 f45 ?v0) ?v1)) (f35 f54 (f35 (f44 f45 ?v1) ?v0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f25 f28 (f25 (f26 f29 ?v0) ?v1)) (f25 f28 (f25 (f26 f29 ?v1) ?v0)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f44 f56 ?v0))) (=> (= (f46 (f35 ?v_0 ?v1) (f35 ?v_0 ?v2)) f1) (= (f46 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v0))) (=> (= (f3 (f4 (f25 ?v_0 ?v1)) (f25 ?v_0 ?v2)) f1) (= (f3 (f4 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f50 f51 ?v0))) (=> (= (f60 (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) f1) (= (f60 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f46 (f35 (f44 f56 ?v0) ?v1) (f35 (f44 f56 ?v2) ?v1)) f1) (= (f46 ?v0 ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 (f25 (f26 f27 ?v0) ?v1)) (f25 (f26 f27 ?v2) ?v1)) f1) (= (f3 (f4 ?v0) ?v2) f1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f60 (f12 (f50 f51 ?v0) ?v1) (f12 (f50 f51 ?v2) ?v1)) f1) (= (f60 ?v0 ?v2) f1))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18) (?v3 S18)) (=> (= (f46 ?v0 ?v1) f1) (=> (= (f46 ?v2 ?v3) f1) (= (f46 (f35 (f44 f56 ?v0) ?v2) (f35 (f44 f56 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f4 ?v0) ?v1) f1) (=> (= (f3 (f4 ?v2) ?v3) f1) (= (f3 (f4 (f25 (f26 f27 ?v0) ?v2)) (f25 (f26 f27 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (=> (= (f60 ?v0 ?v1) f1) (=> (= (f60 ?v2 ?v3) f1) (= (f60 (f12 (f50 f51 ?v0) ?v2) (f12 (f50 f51 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f44 f56 ?v2))) (=> (= (f46 ?v0 ?v1) f1) (= (f46 (f35 ?v_0 ?v0) (f35 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v2))) (=> (= (f3 (f4 ?v0) ?v1) f1) (= (f3 (f4 (f25 ?v_0 ?v0)) (f25 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f50 f51 ?v2))) (=> (= (f60 ?v0 ?v1) f1) (= (f60 (f12 ?v_0 ?v0) (f12 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f46 ?v0 ?v1) f1) (= (f46 (f35 (f44 f56 ?v0) ?v2) (f35 (f44 f56 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 ?v0) ?v1) f1) (= (f3 (f4 (f25 (f26 f27 ?v0) ?v2)) (f25 (f26 f27 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f60 ?v0 ?v1) f1) (= (f60 (f12 (f50 f51 ?v0) ?v2) (f12 (f50 f51 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f44 f56 ?v0))) (= (= (f46 (f35 ?v_0 ?v1) (f35 ?v_0 ?v2)) f1) (= (f46 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f26 f27 ?v0))) (= (= (f3 (f4 (f25 ?v_0 ?v1)) (f25 ?v_0 ?v2)) f1) (= (f3 (f4 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (let ((?v_0 (f50 f51 ?v0))) (= (= (f60 (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) f1) (= (f60 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (= (= (f46 (f35 (f44 f56 ?v0) ?v1) (f35 (f44 f56 ?v2) ?v1)) f1) (= (f46 ?v0 ?v2) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (= (f3 (f4 (f25 (f26 f27 ?v0) ?v1)) (f25 (f26 f27 ?v2) ?v1)) f1) (= (f3 (f4 ?v0) ?v2) f1))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (= (= (f60 (f12 (f50 f51 ?v0) ?v1) (f12 (f50 f51 ?v2) ?v1)) f1) (= (f60 ?v0 ?v2) f1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5)) (= (f7 (f8 f57 (f7 (f8 f9 ?v0) ?v1)) ?v2) (f7 (f8 f9 (f7 (f8 f57 ?v0) ?v2)) (f7 (f8 f57 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f25 (f26 f32 (f25 (f26 f29 ?v0) ?v1)) ?v2) (f25 (f26 f29 (f25 (f26 f32 ?v0) ?v2)) (f25 (f26 f32 ?v1) ?v2)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f3 (f39 (f5 f6 (f7 (f8 f9 ?v0) ?v1))) (f25 (f26 f27 (f25 f28 (f25 (f26 f29 (f5 f30 ?v0)) (f5 f30 ?v1)))) (f25 f28 (f25 (f26 f29 (f5 f31 ?v0)) (f5 f31 ?v1))))) f1)))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f35 (f44 f45 (f35 (f44 f56 ?v0) ?v1)) ?v1) ?v0)))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f7 (f8 f9 (f7 (f8 f58 ?v0) ?v1)) ?v1) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f25 (f26 f29 (f25 (f26 f27 ?v0) ?v1)) ?v1) ?v0)))
(assert (forall ((?v0 S18) (?v1 S18)) (= (f35 (f44 f56 (f35 (f44 f45 ?v0) ?v1)) ?v1) ?v0)))
(assert (forall ((?v0 S5) (?v1 S5)) (= (f7 (f8 f58 (f7 (f8 f9 ?v0) ?v1)) ?v1) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f25 (f26 f27 (f25 (f26 f29 ?v0) ?v1)) ?v1) ?v0)))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18) (?v3 S18)) (=> (= (f35 (f44 f45 ?v0) ?v1) (f35 (f44 f45 ?v2) ?v3)) (= (= (f52 ?v0 ?v1) f1) (= (f52 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f25 (f26 f29 ?v0) ?v1) (f25 (f26 f29 ?v2) ?v3)) (= (= (f3 (f39 ?v0) ?v1) f1) (= (f3 (f39 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S5)) (let ((?v_0 (f5 f6 ?v0))) (= (f25 f28 ?v_0) ?v_0))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f25 f43 ?v0))) (= (f25 f28 ?v_0) ?v_0))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (= (f3 (f39 (f5 f6 (f7 (f8 f9 (f7 (f8 f58 ?v0) ?v1)) (f7 (f8 f58 ?v2) ?v3)))) (f25 (f26 f27 (f5 f6 (f7 (f8 f9 ?v0) ?v2))) (f5 f6 (f7 (f8 f9 ?v1) ?v3)))) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (= (f3 (f39 (f25 f43 (f25 (f26 f29 (f25 (f26 f27 ?v0) ?v1)) (f25 (f26 f27 ?v2) ?v3)))) (f25 (f26 f27 (f25 f43 (f25 (f26 f29 ?v0) ?v2))) (f25 f43 (f25 (f26 f29 ?v1) ?v3)))) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 f31 (f19 (f20 f21 ?v0) ?v1)) ?v1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f5 f30 (f19 (f20 f21 ?v0) ?v1)) ?v0)))
(check-sat)
(exit)