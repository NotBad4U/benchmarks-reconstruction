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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 (S3 S2) S2)
(declare-fun f5 (S4 S2) S3)
(declare-fun f6 () S4)
(declare-fun f7 () S2)
(declare-fun f8 (S5 S6) S2)
(declare-fun f9 (S7 S2) S5)
(declare-fun f10 () S7)
(declare-fun f11 (S8 S9) S2)
(declare-fun f12 () S8)
(declare-fun f13 () S9)
(declare-fun f14 (S10 S6) S6)
(declare-fun f15 (S11 S6) S10)
(declare-fun f16 () S11)
(declare-fun f17 () S6)
(declare-fun f18 () S6)
(declare-fun f19 () S2)
(declare-fun f20 () S2)
(declare-fun f21 () S2)
(declare-fun f22 () S3)
(declare-fun f23 () S6)
(declare-fun f24 (S2 S2) S1)
(declare-fun f25 (S12 S9) S9)
(declare-fun f26 (S13 S9) S12)
(declare-fun f27 () S13)
(declare-fun f28 () S3)
(declare-fun f29 (S6 S6) S1)
(declare-fun f30 () S11)
(declare-fun f31 () S11)
(declare-fun f32 (S14 S14) S1)
(declare-fun f33 () S14)
(declare-fun f34 (S15 S14) S14)
(declare-fun f35 (S16 S14) S15)
(declare-fun f36 () S16)
(declare-fun f37 (S17 S6) S14)
(declare-fun f38 (S18 S14) S17)
(declare-fun f39 () S18)
(declare-fun f40 (S19 S6) S9)
(declare-fun f41 (S20 S9) S19)
(declare-fun f42 () S20)
(declare-fun f43 () S9)
(declare-fun f44 () S4)
(declare-fun f45 () S13)
(declare-fun f46 (S6 S6) S1)
(declare-fun f47 (S14 S14) S1)
(declare-fun f48 () S14)
(declare-fun f49 () S9)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 (f5 f6 f7) (f4 (f5 f6 (f8 (f9 f10 (f11 f12 f13)) (f14 (f15 f16 f17) f18))) f19)) f20) f1)))
(assert (= (f3 f21 f7) f1))
(assert (= (f3 f7 f20) f1))
(assert (= (f3 f7 (f4 f22 (f4 (f5 f6 (f8 (f9 f10 (f11 f12 f13)) (f14 (f15 f16 f17) f18))) f19))) f1))
(assert (= (f3 f21 (f4 f22 (f4 (f5 f6 (f8 (f9 f10 (f11 f12 f13)) (f14 (f15 f16 f17) f18))) f19))) f1))
(assert (= (f3 f21 f7) f1))
(assert (= (f3 f7 f20) f1))
(assert (= (f3 f21 f19) f1))
(assert (not (= f17 f23)))
(assert (= (f3 f7 (f4 f22 (f4 (f5 f6 (f8 (f9 f10 (f11 f12 f13)) (f14 (f15 f16 f17) f18))) f19))) f1))
(assert (= (f3 f21 (f4 f22 (f4 (f5 f6 (f8 (f9 f10 (f11 f12 f13)) (f14 (f15 f16 f17) f18))) f19))) f1))
(assert (forall ((?v0 S2)) (=> (= (f3 f21 ?v0) f1) (exists ((?v1 S2)) (and (= (f3 f21 ?v1) f1) (and (= (f3 ?v1 f20) f1) (= (f3 ?v1 ?v0) f1)))))))
(assert (=> (forall ((?v0 S2)) (=> (= (f3 f21 ?v0) f1) (=> (= (f3 ?v0 f20) f1) (=> (= (f3 ?v0 (f4 f22 (f4 (f5 f6 (f8 (f9 f10 (f11 f12 f13)) (f14 (f15 f16 f17) f18))) f19))) f1) false)))) false))
(assert (let ((?v_0 (f11 f12 f13))) (= (f24 (f4 (f5 f6 f7) ?v_0) (f4 (f5 f6 f20) ?v_0)) f1)))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S9) (?v3 S2)) (=> (= (f3 (f11 f12 ?v0) ?v1) f1) (=> (= (f3 (f11 f12 ?v2) ?v3) f1) (= (f3 (f11 f12 (f25 (f26 f27 ?v0) ?v2)) (f4 (f5 f6 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f3 (f4 f28 ?v0) ?v1) f1) (=> (= (f3 (f4 f28 ?v2) ?v3) f1) (= (f3 (f4 f28 (f4 (f5 f6 ?v0) ?v2)) (f4 (f5 f6 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f29 f18 ?v0) f1) (= (f29 f18 (f14 (f15 f30 ?v0) (f14 (f15 f31 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S2) (?v1 S6)) (=> (= (f3 f20 ?v0) f1) (= (f3 f20 (f4 (f5 f6 ?v0) (f8 (f9 f10 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S14) (?v1 S6)) (=> (= (f32 f33 ?v0) f1) (= (f32 f33 (f34 (f35 f36 ?v0) (f37 (f38 f39 ?v0) ?v1))) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f14 (f15 f31 ?v0) ?v1))) (=> (= (f29 f18 ?v0) f1) (= (f29 ?v_0 (f14 (f15 f30 ?v0) ?v_0)) f1)))))
(assert (forall ((?v0 S2) (?v1 S6)) (let ((?v_0 (f8 (f9 f10 ?v0) ?v1))) (=> (= (f3 f20 ?v0) f1) (= (f3 ?v_0 (f4 (f5 f6 ?v0) ?v_0)) f1)))))
(assert (forall ((?v0 S14) (?v1 S6)) (let ((?v_0 (f37 (f38 f39 ?v0) ?v1))) (=> (= (f32 f33 ?v0) f1) (= (f32 ?v_0 (f34 (f35 f36 ?v0) ?v_0)) f1)))))
(assert (forall ((?v0 S9) (?v1 S6)) (= (f11 f12 (f40 (f41 f42 ?v0) ?v1)) (f8 (f9 f10 (f11 f12 ?v0)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S6)) (= (f4 f28 (f8 (f9 f10 ?v0) ?v1)) (f8 (f9 f10 (f4 f28 ?v0)) ?v1))))
(assert (= (f11 f12 f43) f20))
(assert (= (f4 f28 f20) f20))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f11 f12 (f25 (f26 f27 ?v0) ?v1)) (f4 (f5 f6 (f11 f12 ?v0)) (f11 f12 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 f28 (f4 (f5 f6 ?v0) ?v1)) (f4 (f5 f6 (f4 f28 ?v0)) (f4 f28 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f3 (f4 f28 ?v0) ?v1) f1) (=> (= (f3 (f4 f28 ?v2) ?v3) f1) (= (f3 (f4 f28 (f4 (f5 f44 ?v0) ?v2)) (f4 (f5 f44 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S9) (?v3 S2)) (=> (= (f3 (f11 f12 ?v0) ?v1) f1) (=> (= (f3 (f11 f12 ?v2) ?v3) f1) (= (f3 (f11 f12 (f25 (f26 f45 ?v0) ?v2)) (f4 (f5 f44 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S14) (?v1 S6) (?v2 S6)) (let ((?v_0 (f38 f39 ?v0))) (= (f37 ?v_0 (f14 (f15 f16 ?v1) ?v2)) (f34 (f35 f36 (f37 ?v_0 ?v1)) (f37 ?v_0 ?v2))))))
(assert (forall ((?v0 S9) (?v1 S6) (?v2 S6)) (let ((?v_0 (f41 f42 ?v0))) (= (f40 ?v_0 (f14 (f15 f16 ?v1) ?v2)) (f25 (f26 f27 (f40 ?v_0 ?v1)) (f40 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6)) (let ((?v_0 (f9 f10 ?v0))) (= (f8 ?v_0 (f14 (f15 f16 ?v1) ?v2)) (f4 (f5 f6 (f8 ?v_0 ?v1)) (f8 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f31 ?v0))) (= (f14 ?v_0 (f14 (f15 f16 ?v1) ?v2)) (f14 (f15 f30 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S6) (?v2 S6)) (let ((?v_0 (f38 f39 ?v0))) (= (f34 (f35 f36 (f37 ?v_0 ?v1)) (f37 ?v_0 ?v2)) (f37 ?v_0 (f14 (f15 f16 ?v1) ?v2))))))
(assert (forall ((?v0 S9) (?v1 S6) (?v2 S6)) (let ((?v_0 (f41 f42 ?v0))) (= (f25 (f26 f27 (f40 ?v_0 ?v1)) (f40 ?v_0 ?v2)) (f40 ?v_0 (f14 (f15 f16 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6)) (let ((?v_0 (f9 f10 ?v0))) (= (f4 (f5 f6 (f8 ?v_0 ?v1)) (f8 ?v_0 ?v2)) (f8 ?v_0 (f14 (f15 f16 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f31 ?v0))) (= (f14 (f15 f30 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v2)) (f14 ?v_0 (f14 (f15 f16 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f31 ?v0))) (=> (= (f29 f18 ?v0) f1) (= (= (f14 ?v_0 ?v1) (f14 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6)) (let ((?v_0 (f9 f10 ?v0))) (=> (= (f3 f20 ?v0) f1) (= (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S14) (?v1 S6) (?v2 S6)) (let ((?v_0 (f38 f39 ?v0))) (=> (= (f32 f33 ?v0) f1) (= (= (f37 ?v_0 ?v1) (f37 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f24 (f11 f12 ?v0) (f4 (f5 f44 (f11 f12 (f25 (f26 f45 ?v0) ?v1))) (f11 f12 ?v1))) f1)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f29 f23 (f14 (f15 f31 ?v0) ?v1)) f1) (or (= (f29 f23 ?v0) f1) (= ?v1 f23)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f31 ?v0))) (=> (= (f29 f23 ?v0) f1) (=> (= (f29 (f14 ?v_0 ?v1) (f14 ?v_0 ?v2)) f1) (= (f29 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S2)) (=> (= (f8 (f9 f10 ?v0) ?v1) (f8 (f9 f10 ?v2) ?v1)) (=> (= (f24 f21 ?v0) f1) (=> (= (f24 f21 ?v2) f1) (=> (= (f29 f23 ?v1) f1) (= ?v0 ?v2)))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f14 (f15 f31 ?v0) ?v1) (f14 (f15 f31 ?v2) ?v1)) (=> (= (f46 f23 ?v0) f1) (=> (= (f46 f23 ?v2) f1) (=> (= (f29 f23 ?v1) f1) (= ?v0 ?v2)))))))
(assert (forall ((?v0 S14) (?v1 S6) (?v2 S14)) (=> (= (f37 (f38 f39 ?v0) ?v1) (f37 (f38 f39 ?v2) ?v1)) (=> (= (f47 f48 ?v0) f1) (=> (= (f47 f48 ?v2) f1) (=> (= (f29 f23 ?v1) f1) (= ?v0 ?v2)))))))
(assert (forall ((?v0 S9)) (= (= (f24 (f11 f12 ?v0) f21) f1) (= ?v0 f49))))
(assert (forall ((?v0 S2)) (= (= (f24 (f4 f28 ?v0) f21) f1) (= ?v0 f21))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (=> (= (f24 ?v0 ?v1) f1) (=> (= (f24 f21 ?v0) f1) (= (f24 (f8 (f9 f10 ?v0) ?v2) (f8 (f9 f10 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f46 ?v0 ?v1) f1) (=> (= (f46 f23 ?v0) f1) (= (f46 (f14 (f15 f31 ?v0) ?v2) (f14 (f15 f31 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S6)) (=> (= (f47 ?v0 ?v1) f1) (=> (= (f47 f48 ?v0) f1) (= (f47 (f37 (f38 f39 ?v0) ?v2) (f37 (f38 f39 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S6)) (=> (= (f24 f21 ?v0) f1) (= (f24 f21 (f8 (f9 f10 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f46 f23 ?v0) f1) (= (f46 f23 (f14 (f15 f31 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S14) (?v1 S6)) (=> (= (f47 f48 ?v0) f1) (= (f47 f48 (f37 (f38 f39 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S2)) (= (f24 f21 (f4 f28 ?v0)) f1)))
(assert (forall ((?v0 S9)) (= (f24 f21 (f11 f12 ?v0)) f1)))
(assert (forall ((?v0 S9) (?v1 S6)) (= (= (f40 (f41 f42 ?v0) ?v1) f49) (and (= ?v0 f49) (not (= ?v1 f23))))))
(assert (forall ((?v0 S2) (?v1 S6)) (= (= (f8 (f9 f10 ?v0) ?v1) f21) (and (= ?v0 f21) (not (= ?v1 f23))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 (f15 f31 ?v0) ?v1) f23) (and (= ?v0 f23) (not (= ?v1 f23))))))
(assert (forall ((?v0 S14) (?v1 S6)) (= (= (f37 (f38 f39 ?v0) ?v1) f48) (and (= ?v0 f48) (not (= ?v1 f23))))))
(assert (forall ((?v0 S14) (?v1 S6) (?v2 S6)) (let ((?v_0 (f38 f39 ?v0))) (= (f37 (f38 f39 (f37 ?v_0 ?v1)) ?v2) (f37 ?v_0 (f14 (f15 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S9) (?v1 S6) (?v2 S6)) (let ((?v_0 (f41 f42 ?v0))) (= (f40 (f41 f42 (f40 ?v_0 ?v1)) ?v2) (f40 ?v_0 (f14 (f15 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6)) (let ((?v_0 (f9 f10 ?v0))) (= (f8 (f9 f10 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f14 (f15 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f31 ?v0))) (= (f14 (f15 f31 (f14 ?v_0 ?v1)) ?v2) (f14 ?v_0 (f14 (f15 f30 ?v1) ?v2))))))
(assert (forall ((?v0 S14) (?v1 S6) (?v2 S6)) (let ((?v_0 (f38 f39 ?v0))) (= (f37 ?v_0 (f14 (f15 f30 ?v1) ?v2)) (f37 (f38 f39 (f37 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S6) (?v2 S6)) (let ((?v_0 (f41 f42 ?v0))) (= (f40 ?v_0 (f14 (f15 f30 ?v1) ?v2)) (f40 (f41 f42 (f40 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6)) (let ((?v_0 (f9 f10 ?v0))) (= (f8 ?v_0 (f14 (f15 f30 ?v1) ?v2)) (f8 (f9 f10 (f8 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f31 ?v0))) (= (f14 ?v_0 (f14 (f15 f30 ?v1) ?v2)) (f14 (f15 f31 (f14 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f31 ?v2))) (=> (= (f46 ?v0 ?v1) f1) (=> (= (f46 f23 ?v2) f1) (=> (= (f46 ?v2 f18) f1) (= (f46 (f14 ?v_0 ?v1) (f14 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S2)) (let ((?v_0 (f9 f10 ?v2))) (=> (= (f46 ?v0 ?v1) f1) (=> (= (f24 f21 ?v2) f1) (=> (= (f24 ?v2 f20) f1) (= (f24 (f8 ?v_0 ?v1) (f8 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S14)) (let ((?v_0 (f38 f39 ?v2))) (=> (= (f46 ?v0 ?v1) f1) (=> (= (f47 f48 ?v2) f1) (=> (= (f47 ?v2 f33) f1) (= (f47 (f37 ?v_0 ?v1) (f37 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f24 f21 ?v0) f1) (=> (= (f29 f23 ?v2) f1) (= (f3 (f8 (f9 f10 ?v0) ?v2) (f8 (f9 f10 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f29 ?v0 ?v1) f1) (=> (= (f46 f23 ?v0) f1) (=> (= (f29 f23 ?v2) f1) (= (f29 (f14 (f15 f31 ?v0) ?v2) (f14 (f15 f31 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S6)) (=> (= (f32 ?v0 ?v1) f1) (=> (= (f47 f48 ?v0) f1) (=> (= (f29 f23 ?v2) f1) (= (f32 (f37 (f38 f39 ?v0) ?v2) (f37 (f38 f39 ?v1) ?v2)) f1))))))
(check-sat)
(exit)