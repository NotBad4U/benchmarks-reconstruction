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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 (S3 S2) S2)
(declare-fun f5 (S4 S2) S3)
(declare-fun f6 () S4)
(declare-fun f7 (S5 S6) S2)
(declare-fun f8 () S5)
(declare-fun f9 (S7 S6) S6)
(declare-fun f10 () S7)
(declare-fun f11 () S7)
(declare-fun f12 () S6)
(declare-fun f13 () S3)
(declare-fun f14 () S4)
(declare-fun f15 (S8 S9) S2)
(declare-fun f16 () S8)
(declare-fun f17 (S10 S9) S9)
(declare-fun f18 (S11 S12) S10)
(declare-fun f19 () S11)
(declare-fun f20 () S12)
(declare-fun f21 () S9)
(declare-fun f22 () S3)
(declare-fun f23 () S2)
(declare-fun f24 (S13 S14) S2)
(declare-fun f25 () S13)
(declare-fun f26 (S15 S14) S14)
(declare-fun f27 () S15)
(declare-fun f28 (S16 S14) S15)
(declare-fun f29 () S16)
(declare-fun f30 () S14)
(declare-fun f31 () S14)
(declare-fun f32 () S2)
(declare-fun f33 (S17 S9) S10)
(declare-fun f34 () S17)
(declare-fun f35 () S2)
(declare-fun f36 (S18 S6) S9)
(declare-fun f37 () S18)
(declare-fun f38 () S3)
(declare-fun f39 () S17)
(declare-fun f40 () S4)
(declare-fun f41 (S6 S6) S1)
(declare-fun f42 () S7)
(declare-fun f43 (S19 S6) S7)
(declare-fun f44 () S19)
(declare-fun f45 () S19)
(declare-fun f46 () S17)
(declare-fun f47 () S7)
(declare-fun f48 () S7)
(declare-fun f49 () S9)
(declare-fun f50 () S6)
(declare-fun f51 (S14 S14) S1)
(declare-fun f52 () S14)
(declare-fun f53 (S20 S6) S14)
(declare-fun f54 () S20)
(declare-fun f55 () S10)
(declare-fun f56 (S21 S14) S9)
(declare-fun f57 () S21)
(declare-fun f58 () S15)
(declare-fun f59 () S2)
(declare-fun f60 (S15) S1)
(declare-fun f61 (S14 S14) S1)
(declare-fun f62 () S9)
(declare-fun f63 () S6)
(declare-fun f64 () S14)
(declare-fun f65 () S16)
(declare-fun f66 (S2 S2) S1)
(declare-fun f67 () S2)
(declare-fun f68 (S6 S6) S1)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 (f5 f6 (f7 f8 (f9 f10 (f9 f11 f12)))) (f4 f13 (f4 (f5 f14 (f15 f16 (f17 (f18 f19 f20) f21))) (f4 f22 f23)))) (f24 f25 (f26 f27 (f26 (f28 f29 f30) f31)))) f1)))
(assert (= (f3 (f4 (f5 f6 (f7 f8 (f9 f10 (f9 f11 f12)))) (f4 f13 (f4 (f5 f14 (f15 f16 (f17 (f18 f19 f20) f21))) (f4 f22 f23)))) (f24 f25 f31)) f1))
(assert (= (f3 (f4 (f5 f6 (f7 f8 (f9 f10 (f9 f11 f12)))) (f4 f13 (f4 (f5 f14 (f15 f16 (f17 (f18 f19 f20) f21))) (f4 f22 f23)))) (f24 f25 f31)) f1))
(assert (= (f3 f32 (f4 f13 (f4 (f5 f14 (f15 f16 (f17 (f18 f19 f20) f21))) (f4 f22 f23)))) f1))
(assert (exists ((?v0 S14)) (= (f3 (f4 (f5 f6 (f7 f8 (f9 f10 (f9 f11 f12)))) (f4 f13 (f4 (f5 f14 (f15 f16 (f17 (f18 f19 f20) f21))) (f4 f22 f23)))) (f24 f25 ?v0)) f1)))
(assert (=> (forall ((?v0 S14)) (=> (= (f3 (f4 (f5 f6 (f7 f8 (f9 f10 (f9 f11 f12)))) (f4 f13 (f4 (f5 f14 (f15 f16 (f17 (f18 f19 f20) f21))) (f4 f22 f23)))) (f24 f25 ?v0)) f1) false)) false))
(assert (= (f3 f32 (f4 (f5 f6 (f4 f13 (f4 (f5 f14 (f15 f16 (f17 (f18 f19 f20) f21))) (f4 f22 f23)))) (f7 f8 (f9 f10 (f9 f11 f12))))) f1))
(assert (= (f3 f32 (f24 f25 (f26 f27 (f26 (f28 f29 f30) f31)))) f1))
(assert (forall ((?v0 S9)) (let ((?v_0 (f18 f19 f20))) (let ((?v_1 (f17 ?v_0 f21))) (=> (= (f3 (f15 f16 (f17 (f33 f34 ?v0) f21)) f35) f1) (= (f3 (f15 f16 (f17 (f33 f34 (f17 ?v_0 ?v0)) ?v_1)) (f4 (f5 f6 (f4 f13 (f4 (f5 f14 (f15 f16 ?v_1)) (f4 f22 f23)))) (f7 f8 (f9 f10 (f9 f11 f12))))) f1))))))
(assert (forall ((?v0 S6)) (= (f15 f16 (f36 f37 ?v0)) (f4 f13 (f7 f8 ?v0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f7 f8 ?v0))) (= (f4 f38 ?v_0) (f4 f13 ?v_0)))))
(assert (forall ((?v0 S9)) (= (f17 (f33 f39 ?v0) (f36 f37 (f9 f11 f12))) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f7 f8 (f9 f11 f12))) ?v0)))
(assert (forall ((?v0 S9)) (= (f17 (f33 f39 ?v0) (f36 f37 (f9 f11 f12))) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f7 f8 (f9 f11 f12))) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f3 (f4 f13 (f4 (f5 f14 ?v0) ?v1)) ?v2) f1) (and (= (f3 (f4 (f5 f14 ?v1) ?v2) ?v0) f1) (= (f3 ?v0 (f4 (f5 f40 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f41 (f9 f42 (f9 (f43 f44 ?v0) ?v1)) ?v2) f1) (and (= (f41 (f9 (f43 f44 ?v1) ?v2) ?v0) f1) (= (f41 ?v0 (f9 (f43 f45 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S9)) (let ((?v_1 (f18 f19 f20))) (let ((?v_2 (f17 ?v_1 f21)) (?v_0 (f15 f16 (f17 (f33 f34 ?v0) f21)))) (=> (and (= (f3 f32 ?v_0) f1) (= (f3 ?v_0 f35) f1)) (= (f3 (f15 f16 (f17 (f33 f34 (f17 ?v_1 ?v0)) ?v_2)) (f4 (f5 f6 (f4 f13 (f4 (f5 f14 (f15 f16 ?v_2)) (f4 f22 f23)))) (f7 f8 (f9 f10 (f9 f11 f12))))) f1))))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f15 f16 (f17 (f33 f39 ?v0) ?v1)) (f4 (f5 f6 (f15 f16 ?v0)) (f15 f16 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 f38 (f4 (f5 f6 ?v0) ?v1)) (f4 (f5 f6 (f4 f38 ?v0)) (f4 f38 ?v1)))))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S9) (?v3 S2)) (=> (= (f3 (f15 f16 ?v0) ?v1) f1) (=> (= (f3 (f15 f16 ?v2) ?v3) f1) (= (f3 (f15 f16 (f17 (f33 f46 ?v0) ?v2)) (f4 (f5 f40 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f3 (f4 f38 ?v0) ?v1) f1) (=> (= (f3 (f4 f38 ?v2) ?v3) f1) (= (f3 (f4 f38 (f4 (f5 f40 ?v0) ?v2)) (f4 (f5 f40 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 f13 ?v0) ?v1) f1) (and (= (f3 ?v0 ?v1) f1) (= (f3 (f4 f22 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f41 (f9 f42 ?v0) ?v1) f1) (and (= (f41 ?v0 ?v1) f1) (= (f41 (f9 f47 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S9)) (= (f17 (f33 f46 ?v0) (f36 f37 f12)) ?v0)))
(assert (forall ((?v0 S6)) (= (f9 (f43 f45 ?v0) (f9 f48 f12)) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f40 ?v0) (f7 f8 f12)) ?v0)))
(assert (= (f3 f32 f35) f1))
(assert (exists ((?v0 S2)) (and (= (f3 f32 ?v0) f1) (forall ((?v1 S9)) (let ((?v_1 (f18 f19 f20))) (let ((?v_2 (f17 ?v_1 f21)) (?v_0 (f15 f16 (f17 (f33 f34 ?v1) f21)))) (=> (and (= (f3 f32 ?v_0) f1) (= (f3 ?v_0 ?v0) f1)) (= (f3 (f15 f16 (f17 (f33 f34 (f17 ?v_1 ?v1)) ?v_2)) (f4 (f5 f6 (f4 f13 (f4 (f5 f14 (f15 f16 ?v_2)) (f4 f22 f23)))) (f7 f8 (f9 f10 (f9 f11 f12))))) f1))))))))
(assert (=> (forall ((?v0 S2)) (=> (= (f3 f32 ?v0) f1) (=> (forall ((?v1 S9)) (let ((?v_1 (f18 f19 f20))) (let ((?v_2 (f17 ?v_1 f21)) (?v_0 (f15 f16 (f17 (f33 f34 ?v1) f21)))) (=> (and (= (f3 f32 ?v_0) f1) (= (f3 ?v_0 ?v0) f1)) (= (f3 (f15 f16 (f17 (f33 f34 (f17 ?v_1 ?v1)) ?v_2)) (f4 (f5 f6 (f4 f13 (f4 (f5 f14 (f15 f16 ?v_2)) (f4 f22 f23)))) (f7 f8 (f9 f10 (f9 f11 f12))))) f1))))) false))) false))
(assert (= (f15 f16 f49) f32))
(assert (= (f4 f38 f32) f32))
(assert (forall ((?v0 S9)) (= (= (f15 f16 ?v0) f32) (= ?v0 f49))))
(assert (forall ((?v0 S2)) (= (= (f4 f38 ?v0) f32) (= ?v0 f32))))
(assert (forall ((?v0 S6)) (= (f9 (f43 f44 ?v0) f12) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f44 (f9 f10 ?v0)) (f9 f10 ?v1)) (f9 f10 (f9 (f43 f44 ?v0) ?v1)))))
(assert (= (f9 f47 f12) f12))
(assert (forall ((?v0 S6)) (= (f9 f47 (f9 f10 ?v0)) (f9 f10 (f9 f47 ?v0)))))
(assert (forall ((?v0 S6)) (= (f9 (f43 f45 ?v0) f12) ?v0)))
(assert (forall ((?v0 S6)) (= (f9 (f43 f45 f12) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f45 (f9 f10 ?v0)) (f9 f10 ?v1)) (f9 f10 (f9 (f43 f45 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (f9 f10 ?v0) (f9 (f43 f45 ?v0) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f41 (f9 f11 ?v0) (f9 f11 ?v1)) f1) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f41 (f9 f11 ?v0) (f9 f11 ?v1)) f1) (= (f41 ?v0 ?v1) f1))))
(assert (= (= (f41 f12 f12) f1) false))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f41 (f9 f10 ?v0) (f9 f10 ?v1)) f1) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f41 (f9 f10 ?v0) (f9 f10 ?v1)) f1) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6)) (= (= (f9 (f43 f45 ?v0) ?v0) f50) (= ?v0 f50))))
(assert (forall ((?v0 S2)) (= (= (f4 (f5 f40 ?v0) ?v0) f32) (= ?v0 f32))))
(assert (forall ((?v0 S2)) (= (f4 f38 ?v0) (f4 f13 ?v0))))
(assert (forall ((?v0 S9)) (= (f17 (f33 f39 ?v0) f49) f49)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f32) f32)))
(assert (forall ((?v0 S9)) (= (f17 (f33 f39 f49) ?v0) f49)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f32) ?v0) f32)))
(assert (forall ((?v0 S9)) (= (f17 (f33 f39 f49) ?v0) f49)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 f32) ?v0) f32)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f4 (f5 f14 (f7 f8 ?v0)) (f7 f8 ?v1)) (f7 f8 (f9 (f43 f45 ?v0) (f9 f47 ?v1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f17 (f33 f34 (f36 f37 ?v0)) (f36 f37 ?v1)) (f36 f37 (f9 (f43 f45 ?v0) (f9 f47 ?v1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f44 (f9 f48 ?v0)) (f9 f48 ?v1)) (f9 f48 (f9 (f43 f45 ?v0) (f9 f47 ?v1))))))
(assert (forall ((?v0 S9)) (= (= (f3 f32 (f15 f16 ?v0)) f1) (not (= ?v0 f49)))))
(assert (forall ((?v0 S2)) (= (= (f3 f32 (f4 f38 ?v0)) f1) (not (= ?v0 f32)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f44 (f9 f11 ?v0)) (f9 f11 ?v1)) (f9 f10 (f9 (f43 f44 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f44 (f9 f11 ?v0)) (f9 f10 ?v1)) (f9 f11 (f9 (f43 f44 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f43 f44 f12))) (= (f9 ?v_0 (f9 f10 ?v0)) (f9 f10 (f9 ?v_0 ?v0))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f45 (f9 f11 ?v0)) (f9 f10 ?v1)) (f9 f11 (f9 (f43 f45 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f45 (f9 f10 ?v0)) (f9 f11 ?v1)) (f9 f11 (f9 (f43 f45 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (= (f41 (f9 f11 ?v0) f12) f1) (= (f41 ?v0 f12) f1))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (=> (= (f51 f52 ?v0) f1) (=> (= (f51 ?v1 ?v2) f1) (= (f51 ?v1 (f26 (f28 f29 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f41 f50 ?v0) f1) (=> (= (f41 ?v1 ?v2) f1) (= (f41 ?v1 (f9 (f43 f45 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 f32 ?v0) f1) (=> (= (f3 ?v1 ?v2) f1) (= (f3 ?v1 (f4 (f5 f40 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S6)) (= (= (f41 (f9 (f43 f45 ?v0) ?v0) f50) f1) (= (f41 ?v0 f50) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 (f4 (f5 f40 ?v0) ?v0) f32) f1) (= (f3 ?v0 f32) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f41 (f9 f11 ?v0) (f9 f10 ?v1)) f1) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f41 (f9 f11 ?v0) (f9 f10 ?v1)) f1) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6)) (= (= (f41 (f9 f10 ?v0) f12) f1) (= (f41 ?v0 f12) f1))))
(assert (forall ((?v0 S6)) (= (= (f41 f12 (f9 f10 ?v0)) f1) (= (f41 f12 ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 ?v0 (f4 f22 ?v0)) f1) (= (f3 ?v0 f32) f1))))
(assert (forall ((?v0 S6)) (= (= (f41 ?v0 (f9 f47 ?v0)) f1) (= (f41 ?v0 f50) f1))))
(assert (= (f36 f37 f12) f49))
(assert (= (f7 f8 f12) f32))
(assert (= (f9 f48 f12) f50))
(assert (= (f53 f54 f12) f52))
(assert (= (f36 f37 f12) f49))
(assert (= (f7 f8 f12) f32))
(assert (= (f9 f48 f12) f50))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (not (= ?v0 f49)) (= (f17 (f33 f39 (f17 f55 ?v1)) (f17 f55 ?v0)) (f17 (f33 f39 ?v1) ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 f32)) (= (f4 (f5 f6 (f4 f22 ?v1)) (f4 f22 ?v0)) (f4 (f5 f6 ?v1) ?v0)))))
(assert (forall ((?v0 S9) (?v1 S9)) (let ((?v_0 (f33 f39 ?v1))) (=> (not (= ?v0 f49)) (= (f17 f55 (f17 ?v_0 ?v0)) (f17 ?v_0 (f17 f55 ?v0)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f5 f6 ?v1))) (=> (not (= ?v0 f32)) (= (f4 f22 (f4 ?v_0 ?v0)) (f4 ?v_0 (f4 f22 ?v0)))))))
(assert (forall ((?v0 S9)) (not (= (f3 (f15 f16 ?v0) f32) f1))))
(assert (forall ((?v0 S2)) (not (= (f3 (f4 f38 ?v0) f32) f1))))
(assert (forall ((?v0 S6) (?v1 S9) (?v2 S6)) (= (f17 (f33 f46 (f36 f37 ?v0)) (f17 (f33 f34 ?v1) (f36 f37 ?v2))) (f17 (f33 f46 (f36 f37 (f9 (f43 f45 ?v0) (f9 f47 ?v2)))) ?v1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f9 (f43 f45 (f9 f48 ?v0)) (f9 (f43 f44 ?v1) (f9 f48 ?v2))) (f9 (f43 f45 (f9 f48 (f9 (f43 f45 ?v0) (f9 f47 ?v2)))) ?v1))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6)) (= (f4 (f5 f40 (f7 f8 ?v0)) (f4 (f5 f14 ?v1) (f7 f8 ?v2))) (f4 (f5 f40 (f7 f8 (f9 (f43 f45 ?v0) (f9 f47 ?v2)))) ?v1))))
(assert (forall ((?v0 S6)) (= (= (f3 (f7 f8 ?v0) f32) f1) (= (f41 ?v0 f12) f1))))
(assert (forall ((?v0 S6)) (= (= (f41 (f9 f48 ?v0) f50) f1) (= (f41 ?v0 f12) f1))))
(assert (forall ((?v0 S6)) (= (= (f3 f32 (f7 f8 ?v0)) f1) (= (f41 f12 ?v0) f1))))
(assert (forall ((?v0 S6)) (= (= (f41 f50 (f9 f48 ?v0)) f1) (= (f41 f12 ?v0) f1))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f36 f37 ?v0))) (= (f36 f37 (f9 f10 ?v0)) (f17 (f33 f46 (f17 (f33 f46 f49) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f9 f48 ?v0))) (= (f9 f48 (f9 f10 ?v0)) (f9 (f43 f45 (f9 (f43 f45 f50) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f7 f8 ?v0))) (= (f7 f8 (f9 f10 ?v0)) (f4 (f5 f40 (f4 (f5 f40 f32) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S9)) (= (f17 (f33 f39 ?v0) (f36 f37 f12)) f49)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) (f7 f8 f12)) f32)))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (not (= ?v0 f49)) (= (f15 f16 (f17 (f33 f39 ?v1) ?v0)) (f4 (f5 f6 (f15 f16 ?v1)) (f15 f16 ?v0))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 f32)) (= (f4 f38 (f4 (f5 f6 ?v1) ?v0)) (f4 (f5 f6 (f4 f38 ?v1)) (f4 f38 ?v0))))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f7 f8 ?v0))) (= (f4 f13 ?v_0) (ite (= (f3 ?v_0 f32) f1) (f4 f22 ?v_0) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f9 f48 ?v0))) (= (f9 f42 ?v_0) (ite (= (f41 ?v_0 f50) f1) (f9 f47 ?v_0) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 ?v0 ?v1) f1) false) (=> (=> (= (f3 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f41 ?v0 ?v1) f1) false) (=> (=> (= (f41 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f36 f37 ?v0) (f36 f37 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f7 f8 ?v0) (f7 f8 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f9 f48 ?v0) (f9 f48 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S9)) (let ((?v_0 (f36 f37 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S2)) (let ((?v_0 (f7 f8 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f9 f48 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S14)) (let ((?v_0 (f53 f54 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f9 f11 ?v0) (f9 f11 ?v1)) (= ?v0 ?v1))))
(assert (= (= f12 f12) true))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f9 f10 ?v0) (f9 f10 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f4 (f5 f6 ?v0) (f7 f8 (f9 f10 (f9 f11 f12)))))) (= (f4 (f5 f40 ?v_0) ?v_0) ?v0))))
(assert (forall ((?v0 S2)) (=> (= (f3 f32 ?v0) f1) (= (f3 f32 (f4 (f5 f6 ?v0) (f7 f8 (f9 f10 (f9 f11 f12))))) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f32 (f4 (f5 f6 ?v0) (f7 f8 (f9 f10 (f9 f11 f12))))) f1) (= (f3 f32 ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f3 (f7 f8 ?v0) (f7 f8 ?v1)) f1) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f41 (f9 f48 ?v0) (f9 f48 ?v1)) f1) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S9)) (= (f17 (f33 f46 (f36 f37 ?v0)) (f17 (f33 f46 (f36 f37 ?v1)) ?v2)) (f17 (f33 f46 (f36 f37 (f9 (f43 f45 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f9 (f43 f45 (f9 f48 ?v0)) (f9 (f43 f45 (f9 f48 ?v1)) ?v2)) (f9 (f43 f45 (f9 f48 (f9 (f43 f45 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S2)) (= (f4 (f5 f40 (f7 f8 ?v0)) (f4 (f5 f40 (f7 f8 ?v1)) ?v2)) (f4 (f5 f40 (f7 f8 (f9 (f43 f45 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f17 (f33 f46 (f36 f37 ?v0)) (f36 f37 ?v1)) (f36 f37 (f9 (f43 f45 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f45 (f9 f48 ?v0)) (f9 f48 ?v1)) (f9 f48 (f9 (f43 f45 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f4 (f5 f40 (f7 f8 ?v0)) (f7 f8 ?v1)) (f7 f8 (f9 (f43 f45 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f36 f37 (f9 (f43 f45 ?v0) ?v1)) (f17 (f33 f46 (f36 f37 ?v0)) (f36 f37 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 f48 (f9 (f43 f45 ?v0) ?v1)) (f9 (f43 f45 (f9 f48 ?v0)) (f9 f48 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f7 f8 (f9 (f43 f45 ?v0) ?v1)) (f4 (f5 f40 (f7 f8 ?v0)) (f7 f8 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f7 f8 (f9 (f43 f44 ?v0) ?v1)) (f4 (f5 f14 (f7 f8 ?v0)) (f7 f8 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f36 f37 (f9 (f43 f44 ?v0) ?v1)) (f17 (f33 f34 (f36 f37 ?v0)) (f36 f37 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 f48 (f9 (f43 f44 ?v0) ?v1)) (f9 (f43 f44 (f9 f48 ?v0)) (f9 f48 ?v1)))))
(assert (forall ((?v0 S6)) (= (f36 f37 (f9 f47 ?v0)) (f17 f55 (f36 f37 ?v0)))))
(assert (forall ((?v0 S6)) (= (f7 f8 (f9 f47 ?v0)) (f4 f22 (f7 f8 ?v0)))))
(assert (forall ((?v0 S6)) (= (f9 f48 (f9 f47 ?v0)) (f9 f47 (f9 f48 ?v0)))))
(assert (forall ((?v0 S6)) (= (f17 f55 (f36 f37 ?v0)) (f36 f37 (f9 f47 ?v0)))))
(assert (forall ((?v0 S6)) (= (f4 f22 (f7 f8 ?v0)) (f7 f8 (f9 f47 ?v0)))))
(assert (forall ((?v0 S6)) (= (f9 f47 (f9 f48 ?v0)) (f9 f48 (f9 f47 ?v0)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (= (f17 (f33 f39 (f17 (f33 f46 ?v0) ?v1)) ?v2) (f17 (f33 f46 (f17 (f33 f39 ?v0) ?v2)) (f17 (f33 f39 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f6 (f4 (f5 f40 ?v0) ?v1)) ?v2) (f4 (f5 f40 (f4 (f5 f6 ?v0) ?v2)) (f4 (f5 f6 ?v1) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (= (f17 (f33 f39 (f17 (f33 f46 ?v0) ?v1)) ?v2) (f17 (f33 f46 (f17 (f33 f39 ?v0) ?v2)) (f17 (f33 f39 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f6 (f4 (f5 f40 ?v0) ?v1)) ?v2) (f4 (f5 f40 (f4 (f5 f6 ?v0) ?v2)) (f4 (f5 f6 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f6 (f4 (f5 f14 ?v0) ?v1)) ?v2) (f4 (f5 f14 (f4 (f5 f6 ?v0) ?v2)) (f4 (f5 f6 ?v1) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (= (f17 (f33 f39 (f17 (f33 f34 ?v0) ?v1)) ?v2) (f17 (f33 f34 (f17 (f33 f39 ?v0) ?v2)) (f17 (f33 f39 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f4 (f5 f6 (f4 (f5 f14 ?v0) ?v1)) ?v2) (f4 (f5 f14 (f4 (f5 f6 ?v0) ?v2)) (f4 (f5 f6 ?v1) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (= (f17 (f33 f39 (f17 (f33 f34 ?v0) ?v1)) ?v2) (f17 (f33 f34 (f17 (f33 f39 ?v0) ?v2)) (f17 (f33 f39 ?v1) ?v2)))))
(assert (forall ((?v0 S6)) (= (= (f9 f11 ?v0) f12) false)))
(assert (forall ((?v0 S6)) (= (= f12 (f9 f11 ?v0)) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f9 f11 ?v0) (f9 f10 ?v1)) false)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f9 f10 ?v0) (f9 f11 ?v1)) false)))
(assert (forall ((?v0 S6)) (= (= (f9 f10 ?v0) f12) (= ?v0 f12))))
(assert (forall ((?v0 S6)) (= (= f12 (f9 f10 ?v0)) (= f12 ?v0))))
(assert (= (f9 f10 f12) f12))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 f38 (f4 (f5 f14 ?v0) ?v1)) (f4 f38 (f4 (f5 f14 ?v1) ?v0)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f15 f16 (f17 (f33 f34 ?v0) ?v1)) (f15 f16 (f17 (f33 f34 ?v1) ?v0)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f17 (f33 f39 (f17 f55 ?v0)) ?v1) (f17 f55 (f17 (f33 f39 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f6 (f4 f22 ?v0)) ?v1) (f4 f22 (f4 (f5 f6 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (f17 f55 (f17 (f33 f39 ?v0) ?v1)) (f17 (f33 f39 (f17 f55 ?v0)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 f22 (f4 (f5 f6 ?v0) ?v1)) (f4 (f5 f6 (f4 f22 ?v0)) ?v1))))
(assert (forall ((?v0 S9)) (= (f15 f16 (f17 f55 ?v0)) (f15 f16 ?v0))))
(assert (forall ((?v0 S2)) (= (f4 f38 (f4 f22 ?v0)) (f4 f38 ?v0))))
(assert (forall ((?v0 S9)) (let ((?v_0 (f15 f16 ?v0))) (= (f4 f13 ?v_0) ?v_0))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f4 f38 ?v0))) (= (f4 f13 ?v_0) ?v_0))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S9)) (= (f17 (f33 f46 (f36 f37 ?v0)) (f17 (f33 f34 (f36 f37 ?v1)) ?v2)) (f17 (f33 f34 (f36 f37 (f9 (f43 f45 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f9 (f43 f45 (f9 f48 ?v0)) (f9 (f43 f44 (f9 f48 ?v1)) ?v2)) (f9 (f43 f44 (f9 f48 (f9 (f43 f45 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S2)) (= (f4 (f5 f40 (f7 f8 ?v0)) (f4 (f5 f14 (f7 f8 ?v1)) ?v2)) (f4 (f5 f14 (f7 f8 (f9 (f43 f45 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S9)) (= (f17 (f33 f46 (f36 f37 f12)) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f9 (f43 f45 (f9 f48 f12)) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f40 (f7 f8 f12)) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f7 f8 (f9 f10 (f9 f11 f12))))) (= (f4 (f5 f14 (f4 (f5 f6 (f4 (f5 f40 ?v0) ?v1)) ?v_0)) ?v1) (f4 (f5 f6 (f4 (f5 f14 ?v0) ?v1)) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f7 f8 (f9 f10 (f9 f11 f12))))) (= (f4 (f5 f14 (f4 (f5 f6 (f4 (f5 f40 ?v0) ?v1)) ?v_0)) ?v0) (f4 (f5 f6 (f4 (f5 f14 ?v1) ?v0)) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 ?v1) f1) (= (f3 (f4 (f5 f6 (f4 (f5 f40 ?v0) ?v1)) (f7 f8 (f9 f10 (f9 f11 f12)))) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 ?v1) f1) (= (f3 ?v0 (f4 (f5 f6 (f4 (f5 f40 ?v0) ?v1)) (f7 f8 (f9 f10 (f9 f11 f12))))) f1))))
(assert (forall ((?v0 S2) (?v1 S9) (?v2 S12)) (=> (= (f3 f32 ?v0) f1) (exists ((?v3 S2)) (and (= (f3 f32 ?v3) f1) (forall ((?v4 S9)) (let ((?v_0 (f15 f16 (f17 (f33 f34 ?v4) ?v1))) (?v_1 (f18 f19 ?v2))) (=> (and (= (f3 f32 ?v_0) f1) (= (f3 ?v_0 ?v3) f1)) (= (f3 (f15 f16 (f17 (f33 f34 (f17 ?v_1 ?v4)) (f17 ?v_1 ?v1))) ?v0) f1)))))))))
(assert (let ((?v_0 (f18 f19 f20))) (let ((?v_1 (f17 ?v_0 f21))) (= (f3 (f15 f16 (f17 (f33 f34 (f17 ?v_0 (f56 f57 (f26 f58 (f26 (f28 f29 f30) f31))))) ?v_1)) (f4 (f5 f6 (f4 f13 (f4 (f5 f14 (f15 f16 ?v_1)) (f4 f22 f23)))) (f7 f8 (f9 f10 (f9 f11 f12))))) f1))))
(assert (forall ((?v0 S14)) (= (f26 (f28 f29 (f53 f54 (f9 f10 (f9 f11 f12)))) ?v0) (f26 f27 (f26 f27 ?v0)))))
(assert (forall ((?v0 S14)) (= (f26 (f28 f29 ?v0) (f53 f54 (f9 f10 (f9 f11 f12)))) (f26 f27 (f26 f27 ?v0)))))
(assert (forall ((?v0 S14)) (= (f3 (f15 f16 (f17 (f18 f19 f20) (f56 f57 ?v0))) (f4 (f5 f40 (f4 f22 f23)) (f4 (f5 f6 f59) (f24 f25 (f26 f27 ?v0))))) f1)))
(assert (forall ((?v0 S2)) (= (f4 f13 ?v0) (ite (= (f3 ?v0 f32) f1) (f4 f22 ?v0) ?v0))))
(assert (= (f60 f58) f1))
(assert (let ((?v_0 (f26 f58 (f26 (f28 f29 f30) f31)))) (= (f3 (f15 f16 (f17 (f18 f19 f20) (f56 f57 ?v_0))) (f4 (f5 f40 (f4 f22 f23)) (f4 (f5 f6 f59) (f24 f25 (f26 f27 ?v_0))))) f1)))
(assert (let ((?v_0 (f26 (f28 f29 f30) f31))) (= (f3 (f15 f16 (f17 (f18 f19 f20) (f56 f57 (f26 f58 ?v_0)))) (f4 (f5 f40 (f4 f22 f23)) (f4 (f5 f6 f59) (f24 f25 (f26 f27 ?v_0))))) f1)))
(assert (forall ((?v0 S14)) (=> (= (f61 f30 ?v0) f1) (= (f3 (f15 f16 (f17 (f33 f34 (f56 f57 (f26 f58 ?v0))) f21)) f35) f1))))
(assert (= (f9 f47 f50) f50))
(assert (forall ((?v0 S6)) (= (f9 f42 ?v0) (ite (= (f41 ?v0 f50) f1) (f9 f47 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f9 f47 (f9 f47 ?v0)) ?v0)))
(assert (forall ((?v0 S6)) (= (f9 f47 (f9 f48 ?v0)) (f9 f48 (f9 f47 ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 f47 (f9 (f43 f45 ?v0) ?v1)) (f9 (f43 f45 (f9 f47 ?v0)) (f9 f47 ?v1)))))
(assert (forall ((?v0 S6)) (= (f9 (f43 f45 f50) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f9 (f43 f45 ?v0) f50) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f45 ?v0) ?v1) (f9 (f43 f45 ?v1) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f44 ?v0) ?v1) (f9 (f43 f45 ?v0) (f9 f47 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f41 ?v0 ?v1) f1) (= (f41 (f9 (f43 f44 ?v0) ?v1) f50) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (or (= (f41 ?v0 ?v1) f1) (or (= ?v0 ?v1) (= (f41 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f45 ?v0) (f9 f47 ?v1)) (f9 (f43 f44 ?v0) ?v1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_1 (f43 f45 ?v0)) (?v_0 (f43 f45 ?v1))) (= (f9 ?v_1 (f9 ?v_0 ?v2)) (f9 ?v_0 (f9 ?v_1 ?v2))))))
(assert (forall ((?v0 S6)) (= (f9 (f43 f45 (f9 f47 ?v0)) ?v0) f50)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f45 (f9 f48 ?v0)) (f9 f48 ?v1)) (f9 f48 (f9 (f43 f45 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f9 (f43 f44 (f9 f48 ?v0)) (f9 f48 ?v1)) (f9 f48 (f9 (f43 f45 ?v0) (f9 f47 ?v1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f41 (f9 f48 ?v0) (f9 f48 ?v1)) f1) (= (f41 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f43 f45 ?v0))) (= (f9 (f43 f45 (f9 ?v_0 ?v1)) ?v2) (f9 ?v_0 (f9 (f43 f45 ?v1) ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f41 ?v0 ?v1) f1) (= (f41 (f9 (f43 f45 ?v0) ?v2) (f9 (f43 f45 ?v1) ?v2)) f1))))
(assert (= (f15 f16 f62) f59))
(assert (= (f4 f38 f59) f59))
(assert (not (= f32 f59)))
(assert (forall ((?v0 S6)) (= (= (f51 f52 (f53 f54 ?v0)) f1) (= (f41 f12 ?v0) f1))))
(assert (= (f53 f54 f12) f52))
(assert (= f52 (f53 f54 f12)))
(assert (= (f24 f25 (f26 f27 f52)) f59))
(assert (not (= f49 f62)))
(assert (not (= f50 f63)))
(assert (not (= f32 f59)))
(assert (not (= f52 f64)))
(assert (not (= f62 f49)))
(assert (not (= f63 f50)))
(assert (not (= f59 f32)))
(assert (not (= f64 f52)))
(assert (forall ((?v0 S9)) (= (f17 (f33 f39 ?v0) f62) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) f59) ?v0)))
(assert (= (f4 f13 f59) f59))
(assert (= (f9 f42 f63) f63))
(assert (forall ((?v0 S6)) (= (= (f41 (f9 f11 ?v0) f50) f1) (= (f41 ?v0 f50) f1))))
(assert (= f12 f50))
(assert (= (= (f41 f12 f50) f1) false))
(assert (= f50 (f9 f48 f12)))
(assert (forall ((?v0 S6)) (= (= (f41 (f9 f10 ?v0) f50) f1) (= (f41 ?v0 f50) f1))))
(assert (forall ((?v0 S14)) (= (= (f24 f25 ?v0) f32) (= ?v0 f52))))
(assert (= (f24 f25 f52) f32))
(assert (= (f41 f50 f63) f1))
(assert (= (f3 f32 f59) f1))
(assert (= (f51 f52 f64) f1))
(assert (not (= (f41 f63 f50) f1)))
(assert (not (= (f3 f59 f32) f1)))
(assert (not (= (f51 f64 f52) f1)))
(assert (forall ((?v0 S6)) (= (f41 ?v0 (f9 (f43 f45 ?v0) f63)) f1)))
(assert (forall ((?v0 S2)) (= (f3 ?v0 (f4 (f5 f40 ?v0) f59)) f1)))
(assert (forall ((?v0 S14)) (= (f51 ?v0 (f26 (f28 f29 ?v0) f64)) f1)))
(assert (= f62 (f36 f37 (f9 f11 f12))))
(assert (= f63 (f9 f48 (f9 f11 f12))))
(assert (= f59 (f7 f8 (f9 f11 f12))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (not (= ?v0 f49)) (= (= (f17 (f33 f39 ?v1) ?v0) f62) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 f32)) (= (= (f4 (f5 f6 ?v1) ?v0) f59) (= ?v1 ?v0)))))
(assert (forall ((?v0 S9)) (=> (not (= ?v0 f49)) (= (f17 (f33 f39 ?v0) ?v0) f62))))
(assert (forall ((?v0 S2)) (=> (not (= ?v0 f32)) (= (f4 (f5 f6 ?v0) ?v0) f59))))
(assert (forall ((?v0 S9)) (= (f17 (f33 f39 ?v0) ?v0) (ite (= ?v0 f49) f49 f62))))
(assert (forall ((?v0 S2)) (= (f4 (f5 f6 ?v0) ?v0) (ite (= ?v0 f32) f32 f59))))
(assert (= (f53 f54 (f9 f11 f12)) (f26 f27 f52)))
(assert (= (f53 f54 (f9 f11 (f9 f11 f12))) (f26 f27 (f26 f27 (f26 f27 f52)))))
(assert (forall ((?v0 S14)) (= (f24 f25 (f26 f27 ?v0)) (f4 (f5 f40 (f24 f25 ?v0)) f59))))
(assert (forall ((?v0 S2)) (not (= (f3 (f4 (f5 f40 (f4 f13 ?v0)) f59) ?v0) f1))))
(assert (forall ((?v0 S14)) (= (= (f3 f32 (f24 f25 ?v0)) f1) (= (f51 f52 ?v0) f1))))
(assert (= (f41 f50 (f9 (f43 f45 f63) f63)) f1))
(assert (= (f3 f32 (f4 (f5 f40 f59) f59)) f1))
(assert (= (f51 f52 (f26 (f28 f29 f64) f64)) f1))
(assert (= (f26 f27 (f26 f27 f52)) (f53 f54 (f9 f10 (f9 f11 f12)))))
(assert (= (f53 f54 (f9 f10 (f9 f11 f12))) (f26 f27 (f26 f27 f52))))
(assert (forall ((?v0 S14)) (=> (= (f51 ?v0 (f53 f54 (f9 f10 (f9 f11 f12)))) f1) (or (= ?v0 f52) (= ?v0 (f26 f27 f52))))))
(assert (forall ((?v0 S2)) (= (f3 f32 (f4 (f5 f40 f59) (f4 f13 ?v0))) f1)))
(assert (forall ((?v0 S6)) (let ((?v_0 (f36 f37 ?v0))) (= (f36 f37 (f9 f11 ?v0)) (f17 (f33 f46 (f17 (f33 f46 f62) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f9 f48 ?v0))) (= (f9 f48 (f9 f11 ?v0)) (f9 (f43 f45 (f9 (f43 f45 f63) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f7 f8 ?v0))) (= (f7 f8 (f9 f11 ?v0)) (f4 (f5 f40 (f4 (f5 f40 f59) ?v_0)) ?v_0)))))
(assert (= (f36 f37 (f9 f11 f12)) f62))
(assert (= (f9 f48 (f9 f11 f12)) f63))
(assert (= (f7 f8 (f9 f11 f12)) f59))
(assert (= (f36 f37 (f9 f11 f12)) f62))
(assert (= (f9 f48 (f9 f11 f12)) f63))
(assert (= (f7 f8 (f9 f11 f12)) f59))
(assert (= (f53 f54 (f9 f11 f12)) f64))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f51 (f53 f54 ?v0) (f53 f54 ?v1)) f1) (ite (= (f41 ?v0 ?v1) f1) (= (f41 f12 ?v1) f1) false))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f24 f25 ?v0) (f24 f25 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6)) (= (= (f41 f63 (f9 f48 ?v0)) f1) (= (f41 (f9 f11 f12) ?v0) f1))))
(assert (forall ((?v0 S6)) (= (= (f3 f59 (f7 f8 ?v0)) f1) (= (f41 (f9 f11 f12) ?v0) f1))))
(assert (forall ((?v0 S6)) (= (= (f41 (f9 f48 ?v0) f63) f1) (= (f41 ?v0 (f9 f11 f12)) f1))))
(assert (forall ((?v0 S6)) (= (= (f3 (f7 f8 ?v0) f59) f1) (= (f41 ?v0 (f9 f11 f12)) f1))))
(assert (forall ((?v0 S6)) (= (f17 (f33 f46 f62) (f36 f37 ?v0)) (f36 f37 (f9 (f43 f45 (f9 f11 f12)) ?v0)))))
(assert (forall ((?v0 S6)) (= (f9 (f43 f45 f63) (f9 f48 ?v0)) (f9 f48 (f9 (f43 f45 (f9 f11 f12)) ?v0)))))
(assert (forall ((?v0 S6)) (= (f4 (f5 f40 f59) (f7 f8 ?v0)) (f7 f8 (f9 (f43 f45 (f9 f11 f12)) ?v0)))))
(assert (forall ((?v0 S6)) (= (f17 (f33 f46 (f36 f37 ?v0)) f62) (f36 f37 (f9 (f43 f45 ?v0) (f9 f11 f12))))))
(assert (forall ((?v0 S6)) (= (f9 (f43 f45 (f9 f48 ?v0)) f63) (f9 f48 (f9 (f43 f45 ?v0) (f9 f11 f12))))))
(assert (forall ((?v0 S6)) (= (f4 (f5 f40 (f7 f8 ?v0)) f59) (f7 f8 (f9 (f43 f45 ?v0) (f9 f11 f12))))))
(assert (forall ((?v0 S6)) (= (f17 (f33 f34 f62) (f36 f37 ?v0)) (f36 f37 (f9 (f43 f45 (f9 f11 f12)) (f9 f47 ?v0))))))
(assert (forall ((?v0 S6)) (= (f9 (f43 f44 f63) (f9 f48 ?v0)) (f9 f48 (f9 (f43 f45 (f9 f11 f12)) (f9 f47 ?v0))))))
(assert (forall ((?v0 S6)) (= (f4 (f5 f14 f59) (f7 f8 ?v0)) (f7 f8 (f9 (f43 f45 (f9 f11 f12)) (f9 f47 ?v0))))))
(assert (forall ((?v0 S6)) (= (f17 (f33 f34 (f36 f37 ?v0)) f62) (f36 f37 (f9 (f43 f45 ?v0) (f9 f47 (f9 f11 f12)))))))
(assert (forall ((?v0 S6)) (= (f9 (f43 f44 (f9 f48 ?v0)) f63) (f9 f48 (f9 (f43 f45 ?v0) (f9 f47 (f9 f11 f12)))))))
(assert (forall ((?v0 S6)) (= (f4 (f5 f14 (f7 f8 ?v0)) f59) (f7 f8 (f9 (f43 f45 ?v0) (f9 f47 (f9 f11 f12)))))))
(assert (= (f17 (f33 f46 f62) f62) (f36 f37 (f9 f10 (f9 f11 f12)))))
(assert (= (f9 (f43 f45 f63) f63) (f9 f48 (f9 f10 (f9 f11 f12)))))
(assert (= (f4 (f5 f40 f59) f59) (f7 f8 (f9 f10 (f9 f11 f12)))))
(assert (= (f17 (f33 f46 f62) f62) (f36 f37 (f9 f10 (f9 f11 f12)))))
(assert (= (f9 (f43 f45 f63) f63) (f9 f48 (f9 f10 (f9 f11 f12)))))
(assert (= (f4 (f5 f40 f59) f59) (f7 f8 (f9 f10 (f9 f11 f12)))))
(assert (= (f26 (f28 f29 f64) f64) (f53 f54 (f9 f10 (f9 f11 f12)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9) (?v3 S9)) (= (f17 (f33 f34 (f17 (f33 f46 ?v0) ?v1)) (f17 (f33 f46 ?v2) ?v3)) (f17 (f33 f46 (f17 (f33 f34 ?v0) ?v2)) (f17 (f33 f34 ?v1) ?v3)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (f9 (f43 f44 (f9 (f43 f45 ?v0) ?v1)) (f9 (f43 f45 ?v2) ?v3)) (f9 (f43 f45 (f9 (f43 f44 ?v0) ?v2)) (f9 (f43 f44 ?v1) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (f4 (f5 f14 (f4 (f5 f40 ?v0) ?v1)) (f4 (f5 f40 ?v2) ?v3)) (f4 (f5 f40 (f4 (f5 f14 ?v0) ?v2)) (f4 (f5 f14 ?v1) ?v3)))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_1 (f53 f54 ?v0)) (?v_0 (f53 f54 ?v1))) (= (f26 (f28 f29 ?v_1) ?v_0) (ite (= (f41 ?v0 f12) f1) ?v_0 (ite (= (f41 ?v1 f12) f1) ?v_1 (f53 f54 (f9 (f43 f45 ?v0) ?v1))))))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f3 (f24 f25 ?v0) (f24 f25 ?v1)) f1) (= (f51 ?v0 ?v1) f1))))
(assert (forall ((?v0 S14)) (let ((?v_0 (f24 f25 ?v0))) (= (f4 f13 ?v_0) ?v_0))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f17 (f33 f46 ?v0) ?v1) f49) (= ?v1 (f17 f55 ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f9 (f43 f45 ?v0) ?v1) f50) (= ?v1 (f9 f47 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f40 ?v0) ?v1) f32) (= ?v1 (f4 f22 ?v0)))))
(assert (= f49 (f36 f37 f12)))
(assert (= f32 (f7 f8 f12)))
(assert (= f50 (f9 f48 f12)))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f51 (f53 f54 f12) ?v0) f1) (= (f26 (f28 f65 (f26 f27 ?v1)) ?v0) (f26 (f28 f65 ?v1) (f26 (f28 f65 ?v0) (f53 f54 (f9 f11 f12))))))))
(assert (forall ((?v0 S14)) (not (= (f3 (f24 f25 ?v0) f32) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f40 ?v0) (f4 f22 ?v1)) f32) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f4 (f5 f40 ?v0) ?v1) f32) (= ?v1 (f4 f22 ?v0)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f24 f25 (f26 (f28 f29 ?v0) ?v1)) (f4 (f5 f40 (f24 f25 ?v0)) (f24 f25 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f14 ?v0) ?v1) (f4 (f5 f40 ?v0) (f4 f22 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 (f5 f14 ?v0) ?v1) (f4 (f5 f40 ?v0) (f4 f22 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f4 f13 (f4 (f5 f40 ?v0) (f4 f22 ?v1))) (f4 f13 (f4 (f5 f40 ?v1) (f4 f22 ?v0))))))
(assert (forall ((?v0 S14)) (= (f26 f27 (f26 f27 (f26 f27 ?v0))) (f26 (f28 f29 (f53 f54 (f9 f11 (f9 f11 f12)))) ?v0))))
(assert (forall ((?v0 S14)) (= (f3 f32 (f24 f25 (f26 f27 ?v0))) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 f32 (f4 (f5 f40 ?v0) ?v1)) f1) (= (f3 (f4 f22 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f4 (f5 f40 ?v0) ?v1) f32) f1) (= (f3 ?v1 (f4 f22 ?v0)) f1))))
(assert (forall ((?v0 S2)) (= (f4 f13 ?v0) (ite (= (f3 ?v0 f32) f1) (f4 f22 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (=> (= (f3 f32 ?v0) f1) (exists ((?v1 S14)) (forall ((?v2 S14)) (=> (= (f61 ?v1 ?v2) f1) (= (f3 (f15 f16 (f17 (f33 f34 (f56 f57 (f26 f58 ?v2))) f21)) ?v0) f1)))))))
(assert (= (f66 (f4 f22 f23) (f15 f16 (f17 (f18 f19 f20) (f56 f57 (f26 f58 (f26 (f28 f29 f30) f31)))))) f1))
(assert (let ((?v_2 (f26 (f28 f29 f30) f31)) (?v_0 (f5 f40 (f4 f22 f23))) (?v_1 (f5 f6 f59))) (= (f66 (f4 ?v_0 (f4 ?v_1 (f24 f25 (f26 f27 (f26 f58 ?v_2))))) (f4 ?v_0 (f4 ?v_1 (f24 f25 (f26 f27 ?v_2))))) f1)))
(assert (let ((?v_1 (f26 (f28 f29 f30) f31)) (?v_0 (f5 f6 f59))) (= (f66 (f4 ?v_0 (f24 f25 (f26 f27 (f26 f58 ?v_1)))) (f4 ?v_0 (f24 f25 (f26 f27 ?v_1)))) f1)))
(assert (= (f66 f59 f59) f1))
(assert (= (f66 f32 f59) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f66 ?v0 ?v1) f1) (=> (= (f3 ?v1 (f4 (f5 f40 ?v0) ?v2)) f1) (= (f3 (f4 f13 (f4 (f5 f14 ?v1) ?v0)) ?v2) f1)))))
(assert (let ((?v_0 (f26 (f28 f29 f30) f31))) (= (f61 ?v_0 (f26 f58 ?v_0)) f1)))
(assert (forall ((?v0 S14)) (= (f66 (f4 f22 f23) (f15 f16 (f17 (f18 f19 f20) (f56 f57 ?v0)))) f1)))
(assert (= (f66 f32 f67) f1))
(assert (forall ((?v0 S14)) (= (f66 f32 (f24 f25 ?v0)) f1)))
(assert (forall ((?v0 S14)) (= (f66 (f15 f16 (f56 f57 ?v0)) f67) f1)))
(assert (exists ((?v0 S14)) (forall ((?v1 S14)) (=> (= (f61 ?v0 ?v1) f1) (= (f3 (f15 f16 (f17 (f33 f34 (f56 f57 (f26 f58 ?v1))) f21)) f35) f1)))))
(assert (=> (forall ((?v0 S14)) (=> (forall ((?v1 S14)) (=> (= (f61 ?v0 ?v1) f1) (= (f3 (f15 f16 (f17 (f33 f34 (f56 f57 (f26 f58 ?v1))) f21)) f35) f1))) false)) false))
(assert (not (= f50 f63)))
(assert (forall ((?v0 S6)) (not (= (f9 (f43 f45 (f9 (f43 f45 f63) ?v0)) ?v0) f50))))
(assert (= (f41 f50 f63) f1))
(assert (forall ((?v0 S6)) (= (f9 f48 ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (= (f41 (f9 f42 ?v0) f63) f1) (= ?v0 f50))))
(assert (forall ((?v0 S14)) (=> (= (f51 f52 ?v0) f1) (= ?v0 (f26 f27 (f26 (f28 f65 ?v0) f64))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f66 ?v0 ?v1) f1) (=> (= (f66 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f66 ?v0 ?v1) f1) (=> (= (f66 ?v1 ?v2) f1) (= (f66 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (= (f66 (f24 f25 ?v0) (f24 f25 ?v1)) f1) (= (f61 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f66 ?v0 ?v1) f1) (= (f66 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2)) (= (f66 ?v0 ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f66 (f7 f8 ?v0) (f7 f8 ?v1)) f1) (= (f68 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f68 (f9 f48 ?v0) (f9 f48 ?v1)) f1) (= (f68 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 ?v0 ?v1) f1) (and (= (f66 ?v0 ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f66 ?v0 ?v1) f1) (or (= (f3 ?v0 ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (let ((?v_0 (f28 f65 ?v0))) (= (f26 ?v_0 (f26 f27 ?v1)) (f26 (f28 f65 (f26 ?v_0 f64)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f5 f40 ?v2))) (=> (= (f66 ?v0 ?v1) f1) (= (f66 (f4 ?v_0 ?v0) (f4 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S6)) (= (= (f66 (f7 f8 ?v0) f32) f1) (= (f68 ?v0 f12) f1))))
(assert (forall ((?v0 S6)) (= (= (f68 (f9 f48 ?v0) f50) f1) (= (f68 ?v0 f12) f1))))
(assert (forall ((?v0 S6)) (= (= (f66 f32 (f7 f8 ?v0)) f1) (= (f68 f12 ?v0) f1))))
(assert (forall ((?v0 S6)) (= (= (f68 f50 (f9 f48 ?v0)) f1) (= (f68 f12 ?v0) f1))))
(assert (forall ((?v0 S6)) (= (= (f68 (f9 f48 ?v0) f63) f1) (= (f68 ?v0 (f9 f11 f12)) f1))))
(assert (forall ((?v0 S6)) (= (= (f66 (f7 f8 ?v0) f59) f1) (= (f68 ?v0 (f9 f11 f12)) f1))))
(assert (forall ((?v0 S6)) (= (= (f68 f63 (f9 f48 ?v0)) f1) (= (f68 (f9 f11 f12) ?v0) f1))))
(assert (forall ((?v0 S6)) (= (= (f66 f59 (f7 f8 ?v0)) f1) (= (f68 (f9 f11 f12) ?v0) f1))))
(assert (= (f68 f50 f63) f1))
(assert (= (f66 f32 f59) f1))
(assert (= (f61 f52 f64) f1))
(assert (not (= (f68 f63 f50) f1)))
(assert (not (= (f66 f59 f32) f1)))
(assert (not (= (f61 f64 f52) f1)))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_1 (f7 f8 ?v0)) (?v_0 (f7 f8 ?v1))) (= (= (f66 ?v_1 ?v_0) f1) (not (= (f3 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_1 (f9 f48 ?v0)) (?v_0 (f9 f48 ?v1))) (= (= (f68 ?v_1 ?v_0) f1) (not (= (f41 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_1 (f53 f54 ?v0)) (?v_0 (f53 f54 ?v1))) (= (= (f61 ?v_1 ?v_0) f1) (not (= (f51 ?v_0 ?v_1) f1))))))
(assert (forall ((?v0 S9)) (= (f66 f32 (f15 f16 ?v0)) f1)))
(assert (forall ((?v0 S2)) (= (f66 f32 (f4 f38 ?v0)) f1)))
(assert (= f63 (f9 f48 (f9 f11 f12))))
(assert (forall ((?v0 S14)) (= (f26 f27 ?v0) (f26 (f28 f29 ?v0) f64))))
(assert (forall ((?v0 S14)) (= (f26 f27 ?v0) (f26 (f28 f29 f64) ?v0))))
(assert (forall ((?v0 S14) (?v1 S14)) (= (f26 (f28 f29 ?v0) ?v1) (ite (= ?v0 f52) ?v1 (f26 f27 (f26 (f28 f29 (f26 (f28 f65 ?v0) f64)) ?v1))))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f53 f54 ?v0))) (=> (= (f51 f52 ?v_0) f1) (= ?v_0 (f26 f27 (f26 (f28 f65 ?v_0) f64)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f66 f32 (f4 (f5 f6 ?v0) ?v1)) f1) (and (or (= (f66 ?v0 f32) f1) (= (f66 f32 ?v1) f1)) (or (= (f66 f32 ?v0) f1) (= (f66 ?v1 f32) f1))))))
(assert (forall ((?v0 S14)) (= (= (f66 (f24 f25 ?v0) f32) f1) (= ?v0 f52))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f66 ?v0 ?v1) f1) (= (f66 (f4 (f5 f14 ?v0) ?v1) f32) f1))))
(assert (forall ((?v0 S6)) (= (f9 f11 ?v0) (f9 (f43 f45 (f9 (f43 f45 f63) ?v0)) ?v0))))
(assert (forall ((?v0 S6)) (= (= (f41 (f9 (f43 f45 (f9 (f43 f45 f63) ?v0)) ?v0) f50) f1) (= (f41 ?v0 f50) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f41 ?v0 (f9 (f43 f45 ?v1) f63)) f1) (or (= (f41 ?v0 ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S14) (?v1 S14)) (=> (= (f61 ?v0 ?v1) f1) (= (f24 f25 (f26 (f28 f65 ?v1) ?v0)) (f4 (f5 f14 (f24 f25 ?v1)) (f24 f25 ?v0))))))
(assert (= (f24 f25 f64) f59))
(check-sat)
(exit)