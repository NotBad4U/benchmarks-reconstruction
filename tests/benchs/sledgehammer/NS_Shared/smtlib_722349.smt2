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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S4 S5) S2)
(declare-fun f5 () S4)
(declare-fun f6 () S5)
(declare-fun f7 (S3) S3)
(declare-fun f8 (S6 S7) S3)
(declare-fun f9 (S8) S6)
(declare-fun f10 () S8)
(declare-fun f11 (S9 S7) S7)
(declare-fun f12 (S10 S11) S9)
(declare-fun f13 () S10)
(declare-fun f14 (S8 S8 S2) S11)
(declare-fun f15 () S8)
(declare-fun f16 () S2)
(declare-fun f17 () S7)
(declare-fun f18 (S11 S12) S1)
(declare-fun f19 () S8)
(declare-fun f20 () S8)
(declare-fun f21 (S13 S2) S2)
(declare-fun f22 (S14 S5) S13)
(declare-fun f23 () S14)
(declare-fun f24 (S15 S8) S5)
(declare-fun f25 () S15)
(declare-fun f26 (S16 S2) S13)
(declare-fun f27 () S16)
(declare-fun f28 () S2)
(declare-fun f29 (S17 S8) S2)
(declare-fun f30 () S17)
(declare-fun f31 () S8)
(declare-fun f32 () S2)
(declare-fun f33 (S7) S12)
(declare-fun f34 () S4)
(declare-fun f35 () S5)
(declare-fun f36 (S3) S3)
(declare-fun f37 (S7 S18) S1)
(declare-fun f38 () S18)
(declare-fun f39 (S3) S3)
(declare-fun f40 (S8 S19) S1)
(declare-fun f41 () S19)
(declare-fun f42 (S7) S1)
(declare-fun f43 (S8 S2) S11)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f4 f5 f6)) (?v_1 (f11 (f12 f13 (f14 f10 f15 f16)) f17))) (let ((?v_2 (f8 (f9 f10) ?v_1))) (not (=> (not (= (f3 ?v_0 (f7 ?v_2)) f1)) (=> (= (f18 (f14 f19 f20 (f21 (f22 f23 (f24 f25 f20)) (f21 (f26 f27 f28) (f21 (f26 f27 (f29 f30 f31)) (f21 (f26 f27 ?v_0) f32))))) (f33 ?v_1)) f1) (=> (= (f3 (f21 (f22 f23 f6) (f4 f34 f35)) (f36 ?v_2)) f1) (exists ((?v0 S8)) (= (f18 (f14 ?v0 f31 f32) (f33 ?v_1)) f1)))))))))
(assert (= (f37 f17 f38) f1))
(assert (let ((?v_0 (f4 f5 f6)) (?v_1 (f8 (f9 f10) f17))) (=> (not (= (f3 ?v_0 (f7 ?v_1)) f1)) (=> (= (f18 (f14 f19 f20 (f21 (f22 f23 (f24 f25 f20)) (f21 (f26 f27 f28) (f21 (f26 f27 (f29 f30 f31)) (f21 (f26 f27 ?v_0) f32))))) (f33 f17)) f1) (=> (= (f3 (f21 (f22 f23 f6) (f4 f34 f35)) (f36 ?v_1)) f1) (exists ((?v0 S8)) (= (f18 (f14 ?v0 f31 f32) (f33 f17)) f1)))))))
(assert (= (f3 f16 (f39 (f7 (f8 (f9 f10) f17)))) f1))
(assert (forall ((?v0 S7) (?v1 S8) (?v2 S8) (?v3 S5) (?v4 S8) (?v5 S5) (?v6 S2)) (let ((?v_1 (f4 f34 ?v3)) (?v_0 (f26 f27 (f29 f30 ?v4))) (?v_2 (f33 ?v0))) (=> (= (f37 ?v0 f38) f1) (=> (not (= ?v1 f19)) (=> (= (f18 (f14 ?v2 ?v1 (f21 (f22 f23 (f24 f25 ?v1)) (f21 (f26 f27 ?v_1) (f21 ?v_0 (f21 (f26 f27 (f4 f5 ?v5)) ?v6))))) ?v_2) f1) (=> (= (f18 (f14 ?v1 f19 (f21 (f26 f27 (f29 f30 ?v1)) (f21 ?v_0 ?v_1))) ?v_2) f1) (= (f37 (f11 (f12 f13 (f14 ?v1 ?v4 ?v6)) ?v0) f38) f1))))))))
(assert (forall ((?v0 S7) (?v1 S5) (?v2 S8) (?v3 S2) (?v4 S8) (?v5 S2) (?v6 S5)) (let ((?v_0 (f4 f5 ?v1)) (?v_1 (f8 (f9 f10) ?v0)) (?v_3 (f33 ?v0)) (?v_2 (f21 (f22 f23 ?v1) (f4 f34 ?v6)))) (=> (= (f37 ?v0 f38) f1) (=> (not (= (f3 ?v_0 (f7 ?v_1)) f1)) (=> (= (f18 (f14 f19 ?v2 (f21 (f22 f23 (f24 f25 ?v2)) (f21 (f26 f27 ?v3) (f21 (f26 f27 (f29 f30 ?v4)) (f21 (f26 f27 ?v_0) ?v5))))) ?v_3) f1) (=> (= (f3 ?v_2 (f36 ?v_1)) f1) (= (f18 (f14 ?v4 ?v2 ?v_2) ?v_3) f1))))))))
(assert (forall ((?v0 S7) (?v1 S2) (?v2 S8)) (=> (= (f37 ?v0 f38) f1) (=> (= (f3 ?v1 (f39 (f7 (f8 (f9 f10) ?v0)))) f1) (= (f37 (f11 (f12 f13 (f14 f10 ?v2 ?v1)) ?v0) f38) f1)))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2) (?v5 S7)) (=> (= (f18 (f14 f19 ?v0 (f21 (f22 f23 (f24 f25 ?v0)) (f21 (f26 f27 ?v1) (f21 (f26 f27 ?v2) (f21 (f26 f27 ?v3) ?v4))))) (f33 ?v5)) f1) (= (f3 ?v3 (f36 (f8 (f9 f10) ?v5))) f1))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S8) (?v3 S5) (?v4 S2) (?v5 S7) (?v6 S8) (?v7 S2) (?v8 S8) (?v9 S2)) (let ((?v_0 (f26 f27 (f4 f5 ?v3))) (?v_1 (f33 ?v5))) (=> (= (f18 (f14 f19 ?v0 (f21 (f22 f23 (f24 f25 ?v0)) (f21 (f26 f27 ?v1) (f21 (f26 f27 (f29 f30 ?v2)) (f21 ?v_0 ?v4))))) ?v_1) f1) (=> (= (f18 (f14 f19 ?v6 (f21 (f22 f23 (f24 f25 ?v6)) (f21 (f26 f27 ?v7) (f21 (f26 f27 (f29 f30 ?v8)) (f21 ?v_0 ?v9))))) ?v_1) f1) (=> (= (f37 ?v5 f38) f1) (and (= ?v0 ?v6) (and (= ?v1 ?v7) (and (= ?v2 ?v8) (= ?v4 ?v9))))))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S5) (?v3 S2) (?v4 S2) (?v5 S2) (?v6 S2) (?v7 S7)) (=> (= (f18 (f14 ?v0 ?v1 (f21 (f22 f23 ?v2) (f21 (f26 f27 ?v3) (f21 (f26 f27 ?v4) (f21 (f26 f27 ?v5) ?v6))))) (f33 ?v7)) f1) (= (f3 ?v6 (f36 (f8 (f9 f10) ?v7))) f1))))
(assert (forall ((?v0 S8) (?v1 S7)) (= (f3 (f4 f5 (f24 f25 ?v0)) (f8 (f9 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S5)) (let ((?v_0 (f39 ?v1))) (=> (= (f3 ?v0 ?v_0) f1) (=> (= (f3 (f4 f5 ?v2) ?v1) f1) (= (f3 (f21 (f22 f23 ?v2) ?v0) ?v_0) f1))))))
(assert (forall ((?v0 S2) (?v1 S8) (?v2 S8) (?v3 S2) (?v4 S7)) (let ((?v_0 (f9 f10))) (=> (not (= (f3 ?v0 (f7 (f8 ?v_0 (f11 (f12 f13 (f14 ?v1 ?v2 ?v3)) ?v4)))) f1)) (not (= (f3 ?v0 (f7 (f8 ?v_0 ?v4))) f1))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S2) (?v3 S7)) (=> (= (f18 (f14 ?v0 ?v1 ?v2) (f33 ?v3)) f1) (=> (=> (= (f3 ?v2 (f36 (f8 (f9 f10) ?v3))) f1) false) false))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S2) (?v3 S7)) (=> (= (f18 (f14 ?v0 ?v1 ?v2) (f33 ?v3)) f1) (= (f3 ?v2 (f7 (f8 (f9 f10) ?v3))) f1))))
(assert (forall ((?v0 S8) (?v1 S3)) (= (f3 (f29 f30 ?v0) (f39 ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (let ((?v_0 (f39 ?v1))) (=> (= (f3 ?v0 ?v_0) f1) (=> (= (f3 ?v2 ?v_0) f1) (= (f3 (f21 (f26 f27 ?v0) ?v2) ?v_0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f36 ?v2))) (=> (= (f3 (f21 (f26 f27 ?v0) ?v1) ?v_0) f1) (=> (=> (= (f3 ?v0 ?v_0) f1) (=> (= (f3 ?v1 ?v_0) f1) false)) false)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_0 (f7 ?v2))) (=> (= (f3 (f21 (f26 f27 ?v0) ?v1) ?v_0) f1) (=> (=> (= (f3 ?v0 ?v_0) f1) (=> (= (f3 ?v1 ?v_0) f1) false)) false)))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S8) (?v3 S5) (?v4 S2) (?v5 S7)) (let ((?v_0 (f21 (f22 f23 (f24 f25 ?v0)) (f21 (f26 f27 ?v1) (f21 (f26 f27 (f29 f30 ?v2)) (f21 (f26 f27 (f4 f5 ?v3)) ?v4)))))) (=> (= (f3 ?v_0 (f36 (f8 (f9 f10) ?v5))) f1) (=> (not (= (f40 ?v0 f41) f1)) (=> (= (f37 ?v5 f38) f1) (= (f18 (f14 f19 ?v0 ?v_0) (f33 ?v5)) f1)))))))
(assert (forall ((?v0 S7) (?v1 S8) (?v2 S8) (?v3 S5) (?v4 S8) (?v5 S5) (?v6 S2)) (let ((?v_1 (f4 f34 ?v3)) (?v_0 (f26 f27 (f29 f30 ?v4))) (?v_2 (f33 ?v0))) (=> (= (f42 ?v0) f1) (=> (not (= ?v1 f19)) (=> (= (f18 (f14 ?v2 ?v1 (f21 (f22 f23 (f24 f25 ?v1)) (f21 (f26 f27 ?v_1) (f21 ?v_0 (f21 (f26 f27 (f4 f5 ?v5)) ?v6))))) ?v_2) f1) (=> (= (f18 (f14 ?v1 f19 (f21 (f26 f27 (f29 f30 ?v1)) (f21 ?v_0 ?v_1))) ?v_2) f1) (= (f42 (f11 (f12 f13 (f14 ?v1 ?v4 ?v6)) ?v0)) f1))))))))
(assert (forall ((?v0 S7) (?v1 S8) (?v2 S8) (?v3 S5) (?v4 S5) (?v5 S5) (?v6 S2)) (let ((?v_2 (f4 f34 ?v4)) (?v_0 (f33 ?v0)) (?v_1 (f26 f27 (f4 f34 ?v5))) (?v_3 (f4 f5 ?v3))) (=> (= (f37 ?v0 f38) f1) (=> (= (f18 (f14 ?v1 ?v2 (f21 (f22 f23 ?v3) ?v_2)) ?v_0) f1) (=> (= (f18 (f14 f19 ?v2 (f21 (f22 f23 (f24 f25 ?v2)) (f21 ?v_1 (f21 (f26 f27 (f29 f30 ?v1)) (f21 (f26 f27 ?v_3) ?v6))))) ?v_0) f1) (= (f37 (f11 (f12 f13 (f43 f10 (f21 ?v_1 (f21 (f26 f27 ?v_2) ?v_3)))) ?v0) f38) f1)))))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f3 ?v0 ?v1) f1) (= (f3 ?v0 (f7 ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f3 ?v0 ?v1) f1) (= (f3 ?v0 (f36 ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f3 ?v0 ?v1) f1) (= (f3 ?v0 (f39 ?v1)) f1))))
(assert (= (f40 f10 f41) f1))
(assert (forall ((?v0 S8) (?v1 S7)) (=> (= (f40 ?v0 f41) f1) (= (f3 (f4 f5 (f24 f25 ?v0)) (f8 (f9 f10) ?v1)) f1))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S8) (?v3 S2)) (= (= (f43 ?v0 ?v1) (f43 ?v2 ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S2) (?v3 S8) (?v4 S2)) (not (= (f14 ?v0 ?v1 ?v2) (f43 ?v3 ?v4)))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S8) (?v3 S8) (?v4 S2)) (not (= (f43 ?v0 ?v1) (f14 ?v2 ?v3 ?v4)))))
(assert (not (= (f40 f19 f41) f1)))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S7)) (=> (= (f18 (f43 ?v0 ?v1) (f33 ?v2)) f1) (=> (= (f40 ?v0 f41) f1) (= (f3 ?v1 (f8 (f9 f10) ?v2)) f1)))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S7)) (=> (= (f18 (f43 ?v0 ?v1) (f33 ?v2)) f1) (= (f3 ?v1 (f8 (f9 ?v0) ?v2)) f1))))
(assert (forall ((?v0 S7)) (= (= (f42 ?v0) f1) (= (f37 ?v0 f38) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f7 ?v1))) (=> (= (f3 ?v0 (f7 ?v_0)) f1) (= (f3 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f7 ?v0))) (= (f7 ?v_0) ?v_0))))
(check-sat)
(exit)