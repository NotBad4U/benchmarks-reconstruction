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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 (S3 S2) S2)
(declare-fun f5 (S4 S2) S3)
(declare-fun f6 () S4)
(declare-fun f7 (S5 S6) S2)
(declare-fun f8 () S5)
(declare-fun f9 (S7 S6) S6)
(declare-fun f10 (S8 S6) S7)
(declare-fun f11 () S8)
(declare-fun f12 (S9 S2) S6)
(declare-fun f13 () S9)
(declare-fun f14 () S6)
(declare-fun f15 () S8)
(declare-fun f16 () S6)
(declare-fun f17 () S8)
(declare-fun f18 (S10 S11) S6)
(declare-fun f19 (S12 S6) S10)
(declare-fun f20 () S12)
(declare-fun f21 () S6)
(declare-fun f22 () S11)
(declare-fun f23 () S2)
(declare-fun f24 () S11)
(declare-fun f25 () S6)
(declare-fun f26 (S11) S1)
(declare-fun f27 () S11)
(declare-fun f28 (S13 S11) S3)
(declare-fun f29 () S13)
(declare-fun f30 () S3)
(declare-fun f31 () S4)
(declare-fun f32 () S4)
(declare-fun f33 (S11 S11) S1)
(declare-fun f34 () S11)
(declare-fun f35 (S14 S11) S11)
(declare-fun f36 (S15 S11) S14)
(declare-fun f37 () S15)
(declare-fun f38 () S15)
(declare-fun f39 (S16 S11) S2)
(declare-fun f40 (S17 S2) S16)
(declare-fun f41 () S17)
(declare-fun f42 (S18 S18) S1)
(declare-fun f43 () S18)
(declare-fun f44 (S19 S18) S18)
(declare-fun f45 (S20 S18) S19)
(declare-fun f46 () S20)
(declare-fun f47 (S21 S11) S18)
(declare-fun f48 (S22 S18) S21)
(declare-fun f49 () S22)
(declare-fun f50 () S3)
(declare-fun f51 () S2)
(declare-fun f52 () S18)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f12 f13 (f7 f8 f14)))) (let ((?v_1 (f5 f6 (f7 f8 (f9 (f10 f11 ?v_0) f14))))) (not (= (f3 (f4 ?v_1 (f7 f8 (f9 (f10 f15 f16) (f9 (f10 f17 f14) (f9 (f10 f11 (f18 (f19 f20 f21) f22)) ?v_0))))) (f4 ?v_1 f23)) f1)))))
(assert (not (= f22 f24)))
(assert (not (= f14 f25)))
(assert (= (f7 f8 (f9 (f10 f11 (f12 f13 (f7 f8 f14))) f14)) f23))
(assert (= (f3 (f7 f8 (f9 (f10 f15 (f9 (f10 f11 (f12 f13 (f7 f8 f14))) f14)) (f18 (f19 f20 f21) f22))) f23) f1))
(assert (not (= (f26 f22) f1)))
(assert (exists ((?v0 S6)) (= (f3 (f7 f8 (f9 (f10 f15 (f9 (f10 f11 (f12 f13 (f7 f8 f14))) f14)) (f18 (f19 f20 ?v0) f22))) f23) f1)))
(assert (=> (forall ((?v0 S6)) (=> (= (f3 (f7 f8 (f9 (f10 f15 (f9 (f10 f11 (f12 f13 (f7 f8 f14))) f14)) (f18 (f19 f20 ?v0) f22))) f23) f1) false)) false))
(assert (not (= f27 f24)))
(assert (let ((?v_0 (f7 f8 f14))) (= (f18 (f19 f20 (f9 (f10 f11 f21) (f12 f13 (f4 (f28 f29 f22) ?v_0)))) f22) (f9 (f10 f11 (f18 (f19 f20 f21) f22)) (f12 f13 ?v_0)))))
(assert (=> (= (f26 f22) f1) (exists ((?v0 S6)) (= (f3 (f7 f8 (f9 (f10 f15 f16) (f9 (f10 f17 f14) (f18 (f19 f20 ?v0) f22)))) f23) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f3 (f4 f30 ?v0) ?v1) f1) (=> (= (f3 (f4 f30 ?v2) ?v3) f1) (= (f3 (f4 f30 (f4 (f5 f6 ?v0) ?v2)) (f4 (f5 f6 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6) (?v3 S2)) (=> (= (f3 (f7 f8 ?v0) ?v1) f1) (=> (= (f3 (f7 f8 ?v2) ?v3) f1) (= (f3 (f7 f8 (f9 (f10 f17 ?v0) ?v2)) (f4 (f5 f6 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 ?v1) f1) (= (f3 ?v0 (f4 (f5 f31 (f4 (f5 f32 ?v0) ?v1)) (f4 (f5 f32 f23) f23))) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 ?v1) f1) (= (f3 (f4 (f5 f31 (f4 (f5 f32 ?v0) ?v1)) (f4 (f5 f32 f23) f23)) ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f33 f34 ?v0) f1) (= (f33 f34 (f35 (f36 f37 ?v0) (f35 (f36 f38 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S2) (?v1 S11)) (=> (= (f3 f23 ?v0) f1) (= (f3 f23 (f4 (f5 f6 ?v0) (f39 (f40 f41 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S18) (?v1 S11)) (=> (= (f42 f43 ?v0) f1) (= (f42 f43 (f44 (f45 f46 ?v0) (f47 (f48 f49 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (let ((?v_0 (f35 (f36 f38 ?v0) ?v1))) (=> (= (f33 f34 ?v0) f1) (= (f33 ?v_0 (f35 (f36 f37 ?v0) ?v_0)) f1)))))
(assert (forall ((?v0 S2) (?v1 S11)) (let ((?v_0 (f39 (f40 f41 ?v0) ?v1))) (=> (= (f3 f23 ?v0) f1) (= (f3 ?v_0 (f4 (f5 f6 ?v0) ?v_0)) f1)))))
(assert (forall ((?v0 S18) (?v1 S11)) (let ((?v_0 (f47 (f48 f49 ?v0) ?v1))) (=> (= (f42 f43 ?v0) f1) (= (f42 ?v_0 (f44 (f45 f46 ?v0) ?v_0)) f1)))))
(assert (forall ((?v0 S11)) (=> (= (f33 ?v0 f22) f1) (=> (not (= ?v0 f24)) (exists ((?v1 S6)) (= (f3 (f7 f8 (f9 (f10 f15 f16) (f9 (f10 f17 f14) (f18 (f19 f20 ?v1) ?v0)))) f23) f1))))))
(assert (= (f4 f50 f23) f23))
(assert (= (f12 f13 f23) f16))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 f50 (f4 (f5 f6 ?v0) ?v1)) (f4 (f5 f6 (f4 f50 ?v0)) (f4 f50 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f12 f13 (f4 (f5 f6 ?v0) ?v1)) (f9 (f10 f17 (f12 f13 ?v0)) (f12 f13 ?v1)))))
(assert (= (f7 f8 f16) f23))
(assert (= (f4 f30 f23) f23))
(assert (let ((?v_0 (f7 f8 f14))) (= (f39 (f40 f41 (f4 (f28 f29 f22) ?v_0)) f22) ?v_0)))
(assert (= (f4 f50 f51) f51))
(assert (= (f12 f13 f51) f25))
(assert (= (f4 f50 f51) f51))
(assert (= (f12 f13 f51) f25))
(assert (= (f7 f8 f25) f51))
(assert (= (f4 f30 f51) f51))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f33 f24 (f35 (f36 f38 ?v0) ?v1)) f1) (or (= (f33 f24 ?v0) f1) (= ?v1 f24)))))
(assert (forall ((?v0 S2)) (= (= (f4 f50 ?v0) f51) (= ?v0 f51))))
(assert (forall ((?v0 S2)) (= (= (f12 f13 ?v0) f25) (= ?v0 f51))))
(assert (forall ((?v0 S6)) (= (= (f7 f8 ?v0) f51) (= ?v0 f25))))
(assert (forall ((?v0 S2)) (= (= (f4 f30 ?v0) f51) (= ?v0 f51))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f35 (f36 f38 ?v0) ?v1) f24) (and (= ?v0 f24) (not (= ?v1 f24))))))
(assert (forall ((?v0 S6) (?v1 S11)) (= (= (f18 (f19 f20 ?v0) ?v1) f25) (and (= ?v0 f25) (not (= ?v1 f24))))))
(assert (forall ((?v0 S18) (?v1 S11)) (= (= (f47 (f48 f49 ?v0) ?v1) f52) (and (= ?v0 f52) (not (= ?v1 f24))))))
(assert (forall ((?v0 S2) (?v1 S11)) (= (= (f39 (f40 f41 ?v0) ?v1) f51) (and (= ?v0 f51) (not (= ?v1 f24))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f36 f38 ?v0))) (=> (= (f33 f24 ?v0) f1) (=> (= (f33 (f35 ?v_0 ?v1) (f35 ?v_0 ?v2)) f1) (= (f33 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S18) (?v1 S11) (?v2 S11)) (let ((?v_0 (f48 f49 ?v0))) (= (f47 ?v_0 (f35 (f36 f37 ?v1) ?v2)) (f47 (f48 f49 (f47 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S11) (?v2 S11)) (let ((?v_0 (f19 f20 ?v0))) (= (f18 ?v_0 (f35 (f36 f37 ?v1) ?v2)) (f18 (f19 f20 (f18 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S11) (?v2 S11)) (let ((?v_0 (f40 f41 ?v0))) (= (f39 ?v_0 (f35 (f36 f37 ?v1) ?v2)) (f39 (f40 f41 (f39 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f36 f38 ?v0))) (= (f35 ?v_0 (f35 (f36 f37 ?v1) ?v2)) (f35 (f36 f38 (f35 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6)) (= (f9 (f10 f17 ?v0) f25) f25)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f51) f51)))
(assert (forall ((?v0 S6)) (= (f9 (f10 f17 ?v0) f25) f25)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f51) f51)))
(assert (forall ((?v0 S6)) (= (f9 (f10 f17 f25) ?v0) f25)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f51) ?v0) f51)))
(check-sat)
(exit)
