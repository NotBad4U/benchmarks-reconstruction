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
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 (S3 S2) S2)
(declare-fun f5 (S4 S2) S3)
(declare-fun f6 () S4)
(declare-fun f7 () S2)
(declare-fun f8 (S5 S6) S2)
(declare-fun f9 () S5)
(declare-fun f10 (S7 S6) S6)
(declare-fun f11 () S7)
(declare-fun f12 (S8 S6) S7)
(declare-fun f13 () S8)
(declare-fun f14 () S6)
(declare-fun f15 () S6)
(declare-fun f16 () S3)
(declare-fun f17 () S4)
(declare-fun f18 (S9 S10) S2)
(declare-fun f19 () S9)
(declare-fun f20 (S11 S10) S10)
(declare-fun f21 (S12 S13) S11)
(declare-fun f22 () S12)
(declare-fun f23 () S13)
(declare-fun f24 () S10)
(declare-fun f25 () S3)
(declare-fun f26 () S2)
(declare-fun f27 (S14 S15) S2)
(declare-fun f28 () S14)
(declare-fun f29 (S16 S15) S15)
(declare-fun f30 () S16)
(declare-fun f31 () S16)
(declare-fun f32 () S15)
(declare-fun f33 () S2)
(declare-fun f34 () S3)
(declare-fun f35 () S2)
(declare-fun f36 (S17 S10) S11)
(declare-fun f37 () S17)
(declare-fun f38 (S18 S15) S16)
(declare-fun f39 () S18)
(declare-fun f40 () S15)
(declare-fun f41 () S16)
(declare-fun f42 () S4)
(declare-fun f43 () S17)
(declare-fun f44 () S10)
(declare-fun f45 (S19 S15) S10)
(declare-fun f46 () S19)
(declare-fun f47 () S6)
(declare-fun f48 (S20 S15) S6)
(declare-fun f49 () S20)
(declare-fun f50 (S15 S15) S1)
(declare-fun f51 (S21 S6) S10)
(declare-fun f52 () S21)
(declare-fun f53 () S3)
(declare-fun f54 () S17)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 (f5 f6 f7) (f8 f9 (f10 f11 (f10 (f12 f13 f14) f15)))) (f4 (f5 f6 (f4 f16 (f4 (f5 f17 (f18 f19 (f20 (f21 f22 f23) f24))) (f4 f25 f26)))) (f27 f28 (f29 f30 (f29 f31 f32))))) f1)))
(assert (= (f3 f33 (f4 (f5 f6 (f4 f16 (f4 (f5 f17 (f18 f19 (f20 (f21 f22 f23) f24))) (f4 f25 f26)))) (f27 f28 (f29 f30 (f29 f31 f32))))) f1))
(assert (let ((?v_1 (f8 f9 (f10 f11 (f10 (f12 f13 f14) f15)))) (?v_0 (f4 (f5 f6 (f27 f28 (f29 f30 (f29 f31 f32)))) (f4 f16 (f4 (f5 f17 (f18 f19 (f20 (f21 f22 f23) f24))) (f4 f25 f26)))))) (=> (= (f3 ?v_0 ?v_1) f1) (=> (= (f3 f33 ?v_0) f1) (= (f3 (f4 f34 ?v_1) (f4 f34 ?v_0)) f1)))))
(assert (= (f3 (f4 (f5 f6 (f27 f28 (f29 f30 (f29 f31 f32)))) (f4 f16 (f4 (f5 f17 (f18 f19 (f20 (f21 f22 f23) f24))) (f4 f25 f26)))) (f8 f9 (f10 f11 (f10 (f12 f13 f14) f15)))) f1))
(assert (= (f3 f33 f35) f1))
(assert (= (f3 f33 (f4 (f5 f6 (f4 f16 (f4 (f5 f17 (f18 f19 (f20 (f21 f22 f23) f24))) (f4 f25 f26)))) (f27 f28 (f29 f30 (f29 f31 f32))))) f1))
(assert (= (f3 f33 (f4 f16 (f4 (f5 f17 (f18 f19 (f20 (f21 f22 f23) f24))) (f4 f25 f26)))) f1))
(assert (= (f3 (f4 (f5 f6 (f27 f28 (f29 f30 (f29 f31 f32)))) (f4 f16 (f4 (f5 f17 (f18 f19 (f20 (f21 f22 f23) f24))) (f4 f25 f26)))) (f8 f9 (f10 f11 (f10 (f12 f13 f14) f15)))) f1))
(assert (= (f3 (f4 (f5 f6 (f27 f28 (f29 f30 (f29 f31 f32)))) (f4 f16 (f4 (f5 f17 (f18 f19 (f20 (f21 f22 f23) f24))) (f4 f25 f26)))) (f8 f9 f15)) f1))
(assert (let ((?v_1 (f8 f9 (f10 f11 (f10 (f12 f13 f14) f15)))) (?v_0 (f4 (f5 f6 (f27 f28 (f29 f30 (f29 f31 f32)))) (f4 f16 (f4 (f5 f17 (f18 f19 (f20 (f21 f22 f23) f24))) (f4 f25 f26)))))) (=> (= (f3 ?v_0 ?v_1) f1) (=> (= (f3 f33 ?v_0) f1) (= (f3 (f4 f34 ?v_1) (f4 f34 ?v_0)) f1)))))
(assert (= (f3 f33 (f8 f9 (f10 f11 (f10 (f12 f13 f14) f15)))) f1))
(assert (exists ((?v0 S6)) (= (f3 (f4 (f5 f6 (f27 f28 (f29 f30 (f29 f31 f32)))) (f4 f16 (f4 (f5 f17 (f18 f19 (f20 (f21 f22 f23) f24))) (f4 f25 f26)))) (f8 f9 ?v0)) f1)))
(assert (=> (forall ((?v0 S6)) (=> (= (f3 (f4 (f5 f6 (f27 f28 (f29 f30 (f29 f31 f32)))) (f4 f16 (f4 (f5 f17 (f18 f19 (f20 (f21 f22 f23) f24))) (f4 f25 f26)))) (f8 f9 ?v0)) f1) false)) false))
(assert (forall ((?v0 S10)) (let ((?v_1 (f21 f22 f23))) (let ((?v_2 (f20 ?v_1 f24)) (?v_0 (f18 f19 (f20 (f36 f37 ?v0) f24)))) (=> (and (= (f3 f33 ?v_0) f1) (= (f3 ?v_0 f35) f1)) (= (f3 (f18 f19 (f20 (f36 f37 (f20 ?v_1 ?v0)) ?v_2)) (f4 (f5 f6 (f4 f16 (f4 (f5 f17 (f18 f19 ?v_2)) (f4 f25 f26)))) (f27 f28 (f29 f30 (f29 f31 f32))))) f1))))))
(assert (= (f29 (f38 f39 f40) f40) (f29 f41 (f29 f30 (f29 f31 f32)))))
(assert (= (f4 (f5 f42 f7) f7) (f27 f28 (f29 f30 (f29 f31 f32)))))
(assert (= (f20 (f36 f43 f44) f44) (f45 f46 (f29 f30 (f29 f31 f32)))))
(assert (= (f29 (f38 f39 f40) f40) (f29 f41 (f29 f30 (f29 f31 f32)))))
(assert (= (f4 (f5 f42 f7) f7) (f27 f28 (f29 f30 (f29 f31 f32)))))
(assert (= (f10 (f12 f13 f47) f47) (f48 f49 (f29 f30 (f29 f31 f32)))))
(assert (= (f20 (f36 f43 f44) f44) (f45 f46 (f29 f30 (f29 f31 f32)))))
(assert (exists ((?v0 S2)) (and (= (f3 f33 ?v0) f1) (forall ((?v1 S10)) (let ((?v_1 (f21 f22 f23))) (let ((?v_2 (f20 ?v_1 f24)) (?v_0 (f18 f19 (f20 (f36 f37 ?v1) f24)))) (=> (and (= (f3 f33 ?v_0) f1) (= (f3 ?v_0 ?v0) f1)) (= (f3 (f18 f19 (f20 (f36 f37 (f20 ?v_1 ?v1)) ?v_2)) (f4 (f5 f6 (f4 f16 (f4 (f5 f17 (f18 f19 ?v_2)) (f4 f25 f26)))) (f27 f28 (f29 f30 (f29 f31 f32))))) f1))))))))
(assert (forall ((?v0 S15)) (= (f29 (f38 f39 f40) (f29 f41 ?v0)) (f29 f41 (f29 (f38 f39 (f29 f31 f32)) ?v0)))))
(assert (forall ((?v0 S15)) (= (f4 (f5 f42 f7) (f27 f28 ?v0)) (f27 f28 (f29 (f38 f39 (f29 f31 f32)) ?v0)))))
(assert (forall ((?v0 S15)) (= (f20 (f36 f43 f44) (f45 f46 ?v0)) (f45 f46 (f29 (f38 f39 (f29 f31 f32)) ?v0)))))
(assert (forall ((?v0 S15)) (= (f29 (f38 f39 (f29 f41 ?v0)) f40) (f29 f41 (f29 (f38 f39 ?v0) (f29 f31 f32))))))
(assert (forall ((?v0 S15)) (= (f4 (f5 f42 (f27 f28 ?v0)) f7) (f27 f28 (f29 (f38 f39 ?v0) (f29 f31 f32))))))
(assert (forall ((?v0 S15)) (= (f20 (f36 f43 (f45 f46 ?v0)) f44) (f45 f46 (f29 (f38 f39 ?v0) (f29 f31 f32))))))
(assert (forall ((?v0 S15)) (= (= (f50 f40 (f29 f41 ?v0)) f1) (= (f50 (f29 f31 f32) ?v0) f1))))
(assert (forall ((?v0 S15)) (= (= (f3 f7 (f27 f28 ?v0)) f1) (= (f50 (f29 f31 f32) ?v0) f1))))
(assert (forall ((?v0 S15)) (= (= (f50 (f29 f41 ?v0) f40) f1) (= (f50 ?v0 (f29 f31 f32)) f1))))
(assert (forall ((?v0 S15)) (= (= (f3 (f27 f28 ?v0) f7) f1) (= (f50 ?v0 (f29 f31 f32)) f1))))
(assert (forall ((?v0 S6)) (= (f3 (f18 f19 (f20 (f21 f22 f23) (f51 f52 ?v0))) (f4 (f5 f42 (f4 f25 f26)) (f4 (f5 f6 f7) (f8 f9 (f10 f11 ?v0))))) f1)))
(assert (forall ((?v0 S10)) (let ((?v_0 (f21 f22 f23))) (let ((?v_1 (f20 ?v_0 f24))) (=> (= (f3 (f18 f19 (f20 (f36 f37 ?v0) f24)) f35) f1) (= (f3 (f18 f19 (f20 (f36 f37 (f20 ?v_0 ?v0)) ?v_1)) (f4 (f5 f6 (f4 f16 (f4 (f5 f17 (f18 f19 ?v_1)) (f4 f25 f26)))) (f27 f28 (f29 f30 (f29 f31 f32))))) f1))))))
(assert (forall ((?v0 S15)) (let ((?v_0 (f27 f28 ?v0))) (= (f4 f53 ?v_0) (f4 f16 ?v_0)))))
(assert (forall ((?v0 S15)) (= (f18 f19 (f45 f46 ?v0)) (f4 f16 (f27 f28 ?v0)))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f27 f28 (f29 f31 f32))) ?v0)))
(assert (forall ((?v0 S10)) (= (f20 (f36 f54 ?v0) (f45 f46 (f29 f31 f32))) ?v0)))
(assert (=> (forall ((?v0 S2)) (=> (= (f3 f33 ?v0) f1) (=> (forall ((?v1 S10)) (let ((?v_1 (f21 f22 f23))) (let ((?v_2 (f20 ?v_1 f24)) (?v_0 (f18 f19 (f20 (f36 f37 ?v1) f24)))) (=> (and (= (f3 f33 ?v_0) f1) (= (f3 ?v_0 ?v0) f1)) (= (f3 (f18 f19 (f20 (f36 f37 (f20 ?v_1 ?v1)) ?v_2)) (f4 (f5 f6 (f4 f16 (f4 (f5 f17 (f18 f19 ?v_2)) (f4 f25 f26)))) (f27 f28 (f29 f30 (f29 f31 f32))))) f1))))) false))) false))
(assert (forall ((?v0 S15)) (= (f29 f31 ?v0) (f29 (f38 f39 (f29 (f38 f39 f40) ?v0)) ?v0))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (f29 (f38 f39 ?v0) ?v1) (f29 (f38 f39 ?v1) ?v0))))
(assert (forall ((?v0 S15) (?v1 S15)) (or (= (f50 ?v0 ?v1) f1) (or (= ?v0 ?v1) (= (f50 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (= (f50 ?v0 (f29 (f38 f39 ?v1) f40)) f1) (or (= (f50 ?v0 ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_1 (f38 f39 ?v0)) (?v_0 (f38 f39 ?v1))) (= (f29 ?v_1 (f29 ?v_0 ?v2)) (f29 ?v_0 (f29 ?v_1 ?v2))))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (f29 (f38 f39 (f29 f41 ?v0)) (f29 f41 ?v1)) (f29 f41 (f29 (f38 f39 ?v0) ?v1)))))
(assert (forall ((?v0 S15) (?v1 S15)) (= (= (f50 (f29 f41 ?v0) (f29 f41 ?v1)) f1) (= (f50 ?v0 ?v1) f1))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (let ((?v_0 (f38 f39 ?v0))) (= (f29 (f38 f39 (f29 ?v_0 ?v1)) ?v2) (f29 ?v_0 (f29 (f38 f39 ?v1) ?v2))))))
(assert (forall ((?v0 S15) (?v1 S15) (?v2 S15)) (=> (= (f50 ?v0 ?v1) f1) (= (f50 (f29 (f38 f39 ?v0) ?v2) (f29 (f38 f39 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S15)) (= (f29 (f38 f39 ?v0) f32) ?v0)))
(check-sat)
(exit)
