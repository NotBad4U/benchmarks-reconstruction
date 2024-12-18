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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S2 S3) S1)
(declare-fun f6 (S4) S3)
(declare-fun f7 () S4)
(declare-fun f8 (S5 S6 S6) S3)
(declare-fun f9 () S5)
(declare-fun f10 () S6)
(declare-fun f11 (S9 S8) S1)
(declare-fun f12 (S5 S7) S9)
(declare-fun f13 (S6 S7) S5)
(declare-fun f14 (S10 S11 S8) S1)
(declare-fun f15 () S10)
(declare-fun f16 (S12 S4) S11)
(declare-fun f17 () S12)
(declare-fun f18 () S8)
(declare-fun f19 (S4) S13)
(declare-fun f20 () S13)
(declare-fun f21 (S7 S7) S1)
(declare-fun f22 () S7)
(declare-fun f23 (S7 S7) S1)
(declare-fun f24 (S14 S8) S7)
(declare-fun f25 () S14)
(declare-fun f26 (S15 S4) S8)
(declare-fun f27 (S16 S17) S15)
(declare-fun f28 () S16)
(declare-fun f29 () S17)
(declare-fun f30 (S3 S4) S4)
(declare-fun f31 (S3) S3)
(declare-fun f32 (S10 S2) S9)
(declare-fun f33 (S18 S8) S8)
(declare-fun f34 (S19 S7) S18)
(declare-fun f35 () S19)
(declare-fun f36 (S17 S2) S7)
(declare-fun f37 () S7)
(declare-fun f38 (S20 S2) S11)
(declare-fun f39 () S20)
(declare-fun f40 (S22 S21) S11)
(declare-fun f41 () S22)
(declare-fun f42 (S11 S23) S1)
(declare-fun f43 (S21) S23)
(declare-fun f44 (S24 S11) S11)
(declare-fun f45 (S25 S11) S24)
(declare-fun f46 () S25)
(declare-fun f47 () S25)
(declare-fun f48 () S25)
(declare-fun f49 () S25)
(declare-fun f50 () S24)
(declare-fun f51 () S24)
(declare-fun f52 () S22)
(declare-fun f53 (S26 S20) S24)
(declare-fun f54 () S26)
(declare-fun f55 () S20)
(declare-fun f56 () S11)
(declare-fun f57 () S11)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (and (= (f5 ?v0 (f6 f7)) f1) (= (f3 (f8 f9 f10 f10) ?v0) f1)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S8)) (= (= (f11 (f12 (f13 f10 ?v0) ?v1) ?v2) f1) true)))
(assert (forall ((?v0 S7) (?v1 S8)) (= (= (f11 (f12 f9 ?v0) ?v1) f1) false)))
(assert (not (= (f14 f15 (f16 f17 f7) f18) f1)))
(assert (= (f19 f7) f20))
(assert (exists ((?v0 S7)) (and (= (f21 f22 ?v0) f1) (and (= (f23 ?v0 (f24 f25 (f26 (f27 f28 f29) (f30 (f8 f9 f10 f10) f7)))) f1) (forall ((?v1 S2)) (=> (= (f5 ?v1 (f31 f4)) f1) (= (f11 (f32 f15 ?v1) (f33 (f34 f35 ?v0) f18)) f1)))))))
(assert (= (f19 f7) f20))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 (f6 f7)) f1) (not (= (f36 f29 ?v0) f22)))))
(assert (forall ((?v0 S2)) (=> (= (f5 ?v0 (f6 f7)) f1) (= (f11 (f32 f15 ?v0) (f33 (f34 f35 f37) f18)) f1))))
(assert (exists ((?v0 S7)) (forall ((?v1 S2)) (=> (= (f5 ?v1 (f6 f7)) f1) (= (f11 (f32 f15 ?v1) (f33 (f34 f35 ?v0) f18)) f1)))))
(assert (=> (forall ((?v0 S7)) (=> (forall ((?v1 S2)) (=> (= (f5 ?v1 (f6 f7)) f1) (= (f11 (f32 f15 ?v1) (f33 (f34 f35 ?v0) f18)) f1))) false)) false))
(assert (forall ((?v0 S2) (?v1 S8)) (= (= (f14 f15 (f38 f39 ?v0) ?v1) f1) (not (= (f11 (f32 f15 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S21) (?v1 S8)) (= (= (f14 f15 (f40 f41 ?v0) ?v1) f1) (forall ((?v2 S11)) (=> (= (f42 ?v2 (f43 ?v0)) f1) (= (f14 f15 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S8)) (= (= (f14 f15 (f44 (f45 f46 ?v0) ?v1) ?v2) f1) (= (f14 f15 (f44 (f45 f47 ?v0) ?v1) ?v2) f1))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S8)) (= (= (f14 f15 (f44 (f45 f48 ?v0) ?v1) ?v2) f1) (= (f14 f15 (f44 (f45 f49 ?v0) ?v1) ?v2) f1))))
(assert (forall ((?v0 S11) (?v1 S8)) (= (= (f14 f15 (f44 f50 ?v0) ?v1) f1) (= (f14 f15 (f44 f51 ?v0) ?v1) f1))))
(assert (forall ((?v0 S21) (?v1 S8)) (= (= (f14 f15 (f40 f52 ?v0) ?v1) f1) (exists ((?v2 S11)) (and (= (f42 ?v2 (f43 ?v0)) f1) (= (f14 f15 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S11) (?v1 S8)) (= (= (f14 f15 (f44 (f53 f54 f39) ?v0) ?v1) f1) (= (f14 f15 ?v0 ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S2) (?v2 S8)) (= (= (f14 ?v0 (f38 f55 ?v1) ?v2) f1) (= (f11 (f32 ?v0 ?v1) ?v2) f1))))
(assert (forall ((?v0 S10) (?v1 S8)) (= (= (f14 ?v0 f56 ?v1) f1) true)))
(assert (forall ((?v0 S10) (?v1 S8)) (= (= (f14 ?v0 f57 ?v1) f1) false)))
(assert (forall ((?v0 S10) (?v1 S11) (?v2 S11) (?v3 S8)) (= (= (f14 ?v0 (f44 (f45 f47 ?v1) ?v2) ?v3) f1) (and (= (f14 ?v0 ?v1 ?v3) f1) (= (f14 ?v0 ?v2 ?v3) f1)))))
(assert (not (= f56 f57)))
(assert (not (= f57 f56)))
(assert (forall ((?v0 S11)) (not (= f56 (f44 f51 ?v0)))))
(assert (forall ((?v0 S2)) (not (= f56 (f38 f55 ?v0)))))
(assert (forall ((?v0 S11)) (not (= f57 (f44 f51 ?v0)))))
(assert (forall ((?v0 S2)) (not (= f57 (f38 f55 ?v0)))))
(assert (forall ((?v0 S11) (?v1 S11)) (not (= f56 (f44 (f45 f49 ?v0) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (not (= f56 (f44 (f45 f47 ?v0) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (not (= f57 (f44 (f45 f49 ?v0) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (not (= f57 (f44 (f45 f47 ?v0) ?v1)))))
(assert (forall ((?v0 S11)) (not (= (f44 f51 ?v0) f56))))
(assert (forall ((?v0 S11)) (not (= (f44 f51 ?v0) f57))))
(assert (forall ((?v0 S2)) (not (= (f38 f55 ?v0) f56))))
(assert (forall ((?v0 S2)) (not (= (f38 f55 ?v0) f57))))
(assert (forall ((?v0 S11) (?v1 S2)) (not (= (f44 f51 ?v0) (f38 f55 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S11)) (not (= (f38 f55 ?v0) (f44 f51 ?v1)))))
(check-sat)
(exit)
