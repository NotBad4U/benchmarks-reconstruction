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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S2)
(declare-fun f4 () S3)
(declare-fun f5 (S4 S5) S2)
(declare-fun f6 (S6 S2) S4)
(declare-fun f7 (S7 S2) S6)
(declare-fun f8 () S7)
(declare-fun f9 () S2)
(declare-fun f10 () S5)
(declare-fun f11 () S3)
(declare-fun f12 () S6)
(declare-fun f13 () S5)
(declare-fun f14 (S8 S5) S3)
(declare-fun f15 () S8)
(declare-fun f16 (S9 S2) S8)
(declare-fun f17 () S9)
(declare-fun f18 (S10 S2) S1)
(declare-fun f19 (S11 S10) S10)
(declare-fun f20 (S10) S11)
(declare-fun f21 () S3)
(declare-fun f22 (S12 S13 S14) S1)
(declare-fun f23 (S15 S16) S12)
(declare-fun f24 (S17 S5) S15)
(declare-fun f25 (S18 S12) S17)
(declare-fun f26 () S18)
(declare-fun f27 () S12)
(declare-fun f28 (S19 S16) S16)
(declare-fun f29 (S20 S14) S19)
(declare-fun f30 (S21 S22) S20)
(declare-fun f31 () S21)
(declare-fun f32 () S22)
(declare-fun f33 () S14)
(declare-fun f34 () S16)
(declare-fun f35 (S23 S13) S13)
(declare-fun f36 (S24 S3) S23)
(declare-fun f37 () S24)
(declare-fun f38 () S13)
(declare-fun f39 () S5)
(declare-fun f40 () S10)
(declare-fun f41 () S2)
(declare-fun f42 () S16)
(declare-fun f43 (S12 S2 S16) S1)
(declare-fun f44 (S22 S16) S19)
(declare-fun f45 () S16)
(declare-fun f46 (S10 S13) S1)
(declare-fun f47 () S4)
(declare-fun f48 () S2)
(declare-fun f49 (S12 S5) S16)
(declare-fun f50 () S12)
(declare-fun f51 () S2)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 (f6 (f7 f8 ?v0) f9) f10))))
(assert (forall ((?v0 S2)) (= (f3 f11 ?v0) (f5 (f6 f12 ?v0) f13))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (f3 (f14 f15 ?v0) ?v1) (f5 (f6 f12 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2)) (= (f3 (f14 (f16 f17 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 ?v2) ?v0) ?v1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S2)) (= (= (f18 (f19 (f20 ?v0) ?v1) ?v2) f1) (and (= (f18 ?v0 ?v2) f1) (= (f18 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (f3 f21 ?v0) ?v0)))
(assert (not (= (f22 (f23 (f24 (f25 f26 f27) f13) (f28 (f29 (f30 f31 f32) f33) f34)) (f35 (f36 f37 f11) (f35 (f36 f37 f4) f38)) f33) f1)))
(assert (= (f22 f27 (f35 (f36 f37 f4) f38) f33) f1))
(assert (= f39 f10))
(assert (= (f18 f40 f41) f1))
(assert (= (f18 f40 f9) f1))
(assert (= (f22 f27 (f35 (f36 f37 f4) f38) f33) f1))
(assert (= (f22 (f23 (f24 (f25 f26 f27) f10) f42) f38 f33) f1))
(assert (forall ((?v0 S12) (?v1 S13) (?v2 S14) (?v3 S5) (?v4 S16)) (=> (= (f22 ?v0 ?v1 ?v2) f1) (= (f22 (f23 (f24 (f25 f26 ?v0) ?v3) ?v4) (f35 (f36 f37 (f14 f15 ?v3)) ?v1) ?v2) f1))))
(assert (= (f43 f27 f9 (f28 (f44 f32 f45) (f28 (f29 (f30 f31 f32) f33) f34))) f1))
(assert (= (f46 f40 (f35 (f36 f37 f11) (f35 (f36 f37 f4) f38))) f1))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2)) (= (f5 (f6 (f7 f8 (f5 (f6 f12 ?v0) ?v1)) ?v2) ?v1) ?v0)))
(assert (let ((?v_0 (f28 (f29 (f30 f31 f32) f33) f34))) (= (f43 (f23 (f24 (f25 f26 f27) f13) ?v_0) (f5 f47 f13) ?v_0) f1)))
(assert (= f42 (f28 (f44 f32 f45) (f28 (f29 (f30 f31 f32) f33) f34))))
(assert (forall ((?v0 S13)) (= (f35 (f36 f37 f21) ?v0) ?v0)))
(assert (= (f18 f40 f48) f1))
(assert (= (f43 f27 f9 f42) f1))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S12) (?v3 S16)) (=> (= ?v0 ?v1) (= (f49 (f23 (f24 (f25 f26 ?v2) ?v0) ?v3) ?v1) ?v3))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S16) (?v3 S16)) (= (= (f28 (f44 f32 ?v0) ?v1) (f28 (f44 f32 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S12) (?v1 S2) (?v2 S16) (?v3 S5) (?v4 S13) (?v5 S14)) (=> (= (f43 ?v0 ?v1 ?v2) f1) (=> (= (f22 (f23 (f24 (f25 f26 ?v0) ?v3) ?v2) ?v4 ?v5) f1) (= (f22 ?v0 (f35 (f36 f37 (f14 (f16 f17 ?v1) ?v3)) ?v4) ?v5) f1)))))
(assert (= (f43 f50 f48 f42) f1))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S2) (?v3 S12) (?v4 S5) (?v5 S16) (?v6 S2)) (=> (= f42 (f28 (f44 f32 ?v0) ?v1)) (=> (= (f18 f40 ?v2) f1) (=> (= (f43 (f23 (f24 (f25 f26 ?v3) ?v4) ?v1) ?v2 ?v5) f1) (=> (= (f18 f40 ?v6) f1) (=> (= (f43 ?v3 ?v6 ?v1) f1) (= (f18 f40 (f5 (f6 (f7 f8 ?v2) ?v6) ?v4)) f1))))))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S2) (?v3 S12) (?v4 S5) (?v5 S16) (?v6 S2)) (=> (= f42 (f28 (f44 f32 ?v0) ?v1)) (=> (= (f18 f40 ?v2) f1) (=> (= (f43 (f23 (f24 (f25 f26 ?v3) ?v4) ?v0) ?v2 ?v5) f1) (=> (= (f18 f40 ?v6) f1) (=> (= (f43 ?v3 ?v6 ?v0) f1) (= (f18 f40 (f5 (f6 (f7 f8 ?v2) ?v6) ?v4)) f1))))))))
(assert (forall ((?v0 S12) (?v1 S5) (?v2 S16)) (=> (= (f49 ?v0 ?v1) ?v2) (= (f43 ?v0 (f5 f47 ?v1) ?v2) f1))))
(assert (forall ((?v0 S12) (?v1 S5) (?v2 S16)) (=> (= (f43 ?v0 (f5 f47 ?v1) ?v2) f1) (=> (=> (= (f49 ?v0 ?v1) ?v2) false) false))))
(assert (forall ((?v0 S2) (?v1 S5)) (=> (= (f18 f40 ?v0) f1) (= (f18 f40 (f5 (f6 f12 ?v0) ?v1)) f1))))
(assert (= (f43 (f23 (f24 (f25 f26 f27) f10) f42) (f5 f47 f39) (f28 (f44 f32 f45) (f28 (f29 (f30 f31 f32) f33) f34))) f1))
(assert (forall ((?v0 S12) (?v1 S2) (?v2 S16) (?v3 S5) (?v4 S16)) (=> (= (f43 ?v0 ?v1 ?v2) f1) (= (f43 (f23 (f24 (f25 f26 ?v0) ?v3) ?v4) (f5 (f6 f12 ?v1) ?v3) ?v2) f1))))
(assert (= (f43 (f23 (f24 (f25 f26 f27) f10) f42) f51 f45) f1))
(assert (forall ((?v0 S5)) (= (f18 f40 (f5 f47 ?v0)) f1)))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S13)) (= (= (f46 (f19 (f20 ?v0) ?v1) ?v2) f1) (and (= (f46 ?v0 ?v2) f1) (= (f46 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f5 f47 ?v0) (f5 f47 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S5)) (=> (= (f18 f40 ?v0) f1) (= (f18 f40 (f5 (f6 (f7 f8 ?v0) (f5 f47 ?v1)) ?v2)) f1))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (f5 (f6 (f7 f8 (f5 f47 ?v0)) ?v1) ?v0) ?v1)))
(assert (forall ((?v0 S12) (?v1 S2) (?v2 S16) (?v3 S12) (?v4 S2) (?v5 S16) (?v6 S5)) (=> (= (f43 ?v0 ?v1 ?v2) f1) (=> (= (f43 ?v3 ?v4 ?v5) f1) (=> (= ?v0 (f23 (f24 (f25 f26 ?v3) ?v6) ?v5)) (= (f43 ?v3 (f5 (f6 (f7 f8 ?v1) ?v4) ?v6) ?v2) f1))))))
(check-sat)
(exit)
