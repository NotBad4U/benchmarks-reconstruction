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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S3) S1)
(declare-fun f4 (S5 S2) S4)
(declare-fun f5 (S6 S2) S5)
(declare-fun f6 () S6)
(declare-fun f7 () S5)
(declare-fun f8 (S7 S2) S2)
(declare-fun f9 () S7)
(declare-fun f10 (S8 S3) S1)
(declare-fun f11 () S8)
(declare-fun f12 (S9 S3) S3)
(declare-fun f13 (S10 S2) S9)
(declare-fun f14 () S10)
(declare-fun f15 () S2)
(declare-fun f16 () S3)
(declare-fun f17 () S2)
(declare-fun f18 (S11 S2) S7)
(declare-fun f19 () S11)
(declare-fun f20 () S11)
(declare-fun f21 () S2)
(declare-fun f22 (S12 S3) S2)
(declare-fun f23 (S13 S3) S12)
(declare-fun f24 () S13)
(declare-fun f25 () S3)
(declare-fun f26 () S2)
(declare-fun f27 (S14 S3) S8)
(declare-fun f28 (S15 S2) S14)
(declare-fun f29 (S16 S2) S15)
(declare-fun f30 () S16)
(declare-fun f31 () S3)
(declare-fun f32 (S17 S8) S2)
(declare-fun f33 () S17)
(declare-fun f34 () S2)
(declare-fun f35 () S17)
(declare-fun f36 (S20 S18) S18)
(declare-fun f37 (S21 S19) S20)
(declare-fun f38 () S21)
(declare-fun f39 (S23 S19) S19)
(declare-fun f40 (S24 S22) S23)
(declare-fun f41 () S24)
(declare-fun f42 (S5 S6 S6 S8) S1)
(declare-fun f43 (S25 S8) S8)
(declare-fun f44 (S26 S3) S25)
(declare-fun f45 (S27 S2) S26)
(declare-fun f46 () S27)
(declare-fun f47 (S3) S1)
(declare-fun f48 (S18) S1)
(declare-fun f49 (S19) S1)
(declare-fun f50 (S28 S3) S9)
(declare-fun f51 () S28)
(declare-fun f52 (S29 S2) S1)
(declare-fun f53 (S2) S29)
(declare-fun f54 () S16)
(declare-fun f55 (S30 S11) S28)
(declare-fun f56 () S30)
(declare-fun f57 () S7)
(declare-fun f58 () S11)
(declare-fun f59 (S31 S7) S9)
(declare-fun f60 () S31)
(declare-fun f61 () S11)
(declare-fun f62 () S15)
(declare-fun f63 () S11)
(declare-fun f64 () S28)
(declare-fun f65 (S2) S29)
(declare-fun f66 () S2)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f5 f6 ?v0) ?v1) ?v2) f1) true)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f3 (f4 f7 ?v0) ?v1) f1) false)))
(assert (forall ((?v0 S2)) (= (f8 f9 ?v0) ?v0)))
(assert (not (= (= (f10 f11 (f12 (f13 f14 f15) f16)) f1) (= (f10 f11 (f12 (f13 f14 f17) f16)) f1))))
(assert (let ((?v_0 (f18 f20 f21)) (?v_1 (f22 (f23 f24 f25) f16))) (= (f8 (f18 f19 (f8 ?v_0 (f8 (f18 f20 f15) ?v_1))) f26) (f8 (f18 f19 (f8 ?v_0 (f8 (f18 f20 f17) ?v_1))) f26))))
(assert (= f11 (f27 (f28 (f29 f30 f26) f21) f31)))
(assert (= f11 (f27 (f28 (f29 f30 f26) f21) f31)))
(assert (let ((?v_0 (f18 f20 f21)) (?v_1 (f22 (f23 f24 f25) f16))) (= (f8 (f18 f19 (f8 ?v_0 (f8 (f18 f20 f15) ?v_1))) f26) (f8 (f18 f19 (f8 ?v_0 (f8 (f18 f20 f17) ?v_1))) f26))))
(assert (let ((?v_0 (f32 f33 f11))) (= (f8 (f18 f19 f15) ?v_0) (f8 (f18 f19 f17) ?v_0))))
(assert (= f31 (f12 (f13 f14 f34) f25)))
(assert (= (f32 f35 f11) f34))
(assert (forall ((?v0 S3) (?v1 S2)) (not (= ?v0 (f12 (f13 f14 ?v1) ?v0)))))
(assert (forall ((?v0 S18) (?v1 S19)) (not (= ?v0 (f36 (f37 f38 ?v1) ?v0)))))
(assert (forall ((?v0 S19) (?v1 S22)) (not (= ?v0 (f39 (f40 f41 ?v1) ?v0)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f12 (f13 f14 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S19) (?v1 S18)) (not (= (f36 (f37 f38 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S22) (?v1 S19)) (not (= (f39 (f40 f41 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S3)) (= (= (f12 (f13 f14 ?v0) ?v1) (f12 (f13 f14 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S19) (?v1 S18) (?v2 S19) (?v3 S18)) (= (= (f36 (f37 f38 ?v0) ?v1) (f36 (f37 f38 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S22) (?v1 S19) (?v2 S22) (?v3 S19)) (= (= (f39 (f40 f41 ?v0) ?v1) (f39 (f40 f41 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (=> (forall ((?v0 S3)) (=> (= f31 (f12 (f13 f14 f34) ?v0)) false)) false))
(assert (= (f42 f7 f6 f6 f11) f1))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S8) (?v3 S3)) (= (= (f10 (f43 (f44 (f45 f46 ?v0) ?v1) ?v2) ?v3) f1) (= (f10 ?v2 (f12 (f13 f14 (f8 (f18 f20 ?v0) (f22 (f23 f24 ?v1) ?v3))) ?v3)) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f47 (f12 (f13 f14 ?v0) ?v1)) f1) false)))
(assert (forall ((?v0 S19) (?v1 S18)) (= (= (f48 (f36 (f37 f38 ?v0) ?v1)) f1) false)))
(assert (forall ((?v0 S22) (?v1 S19)) (= (= (f49 (f39 (f40 f41 ?v0) ?v1)) f1) false)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (f32 f33 (f27 (f28 (f29 f30 ?v0) ?v1) ?v2)) ?v0)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S8)) (= (f32 f33 (f43 (f44 (f45 f46 ?v0) ?v1) ?v2)) (f32 f33 ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S2) (?v4 S2) (?v5 S3)) (= (= (f27 (f28 (f29 f30 ?v0) ?v1) ?v2) (f27 (f28 (f29 f30 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S6) (?v3 S2) (?v4 S2) (?v5 S3)) (= (= (f42 ?v0 ?v1 ?v2 (f27 (f28 (f29 f30 ?v3) ?v4) ?v5)) f1) (= (f3 (f4 (f5 ?v1 ?v3) ?v4) ?v5) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f22 (f23 f24 (f12 (f50 f51 ?v0) ?v1)) ?v2) (f8 (f18 f20 (f22 (f23 f24 ?v0) ?v2)) (f22 (f23 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f19 (f8 (f18 f20 ?v0) ?v1)) ?v1) (f8 (f18 f19 ?v0) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f19 (f8 (f18 f20 ?v0) ?v1)) ?v0) (f8 (f18 f19 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v0))) (= (f8 (f18 f19 (f8 ?v_0 ?v1)) ?v2) (f8 (f18 f19 (f8 ?v_0 (f8 (f18 f19 ?v1) ?v2))) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f19 (f8 (f18 f20 ?v0) ?v1)) ?v2) (f8 (f18 f19 (f8 (f18 f20 (f8 (f18 f19 ?v0) ?v2)) ?v1)) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f19 (f8 (f18 f20 ?v0) ?v1)) ?v2) (f8 (f18 f19 (f8 (f18 f20 (f8 (f18 f19 ?v0) ?v2)) (f8 (f18 f19 ?v1) ?v2))) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v0))) (= (f8 (f18 f19 (f8 ?v_0 (f8 (f18 f19 ?v1) ?v2))) ?v2) (f8 (f18 f19 (f8 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f19 (f8 (f18 f20 (f8 (f18 f19 ?v0) ?v1)) ?v2)) ?v1) (f8 (f18 f19 (f8 (f18 f20 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (=> (= (f8 (f18 f19 ?v0) ?v1) (f8 (f18 f19 ?v2) ?v1)) (=> (= (f8 (f18 f19 ?v3) ?v1) (f8 (f18 f19 ?v4) ?v1)) (= (f8 (f18 f19 (f8 (f18 f20 ?v0) ?v3)) ?v1) (f8 (f18 f19 (f8 (f18 f20 ?v2) ?v4)) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S3)) (= (f12 (f50 f51 (f12 (f13 f14 ?v0) ?v1)) (f12 (f13 f14 ?v2) ?v3)) (f12 (f13 f14 (f8 (f18 f20 ?v0) ?v2)) (f12 (f50 f51 ?v1) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S3)) (= (= (f10 (f27 (f28 (f29 f30 ?v0) ?v1) ?v2) ?v3) f1) (= (f52 (f53 ?v0) (f8 (f18 f20 ?v1) (f22 (f23 f24 ?v2) ?v3))) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f50 f51 ?v0))) (= (f12 (f50 f51 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f12 (f50 f51 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 (f8 (f18 f19 ?v1) ?v2)) f1) (=> (= (f52 ?v_0 ?v2) f1) (= (f52 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (=> (= (f52 ?v_0 ?v2) f1) (= (f52 ?v_0 (f8 (f18 f19 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f19 ?v2))) (=> (= (f52 (f53 ?v0) ?v1) f1) (= (f8 (f18 f19 (f8 ?v_0 ?v1)) ?v0) (f8 ?v_0 ?v0))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (= (= (f52 ?v_0 (f8 (f18 f19 ?v2) ?v1)) f1) (= (f52 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 (f8 (f18 f19 ?v1) ?v2)) f1) (=> (= (f52 ?v_0 ?v2) f1) (= (f52 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (=> (= (f52 ?v_0 ?v2) f1) (= (f52 ?v_0 (f8 (f18 f19 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f8 (f18 f19 ?v0) ?v1))) (= (f8 (f18 f19 ?v_0) ?v1) ?v_0))))
(assert (forall ((?v0 S2)) (= (f52 (f53 f34) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (=> (= (f52 ?v_0 ?v2) f1) (= (f52 ?v_0 (f8 (f18 f20 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S3)) (= (= (f10 (f27 (f28 (f29 f54 ?v0) ?v1) ?v2) ?v3) f1) (not (= (f52 (f53 ?v0) (f8 (f18 f20 ?v1) (f22 (f23 f24 ?v2) ?v3))) f1)))))
(assert (= f51 (f55 f56 f20)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v0))) (= (f8 (f18 f20 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f18 f20 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f18 f20 ?v0)) (?v_0 (f18 f20 ?v1))) (= (f8 ?v_1 (f8 ?v_0 ?v2)) (f8 ?v_0 (f8 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f20 ?v0) ?v1) (f8 (f18 f20 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (=> (= (f52 (f53 ?v1) ?v2) f1) (= (f52 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S2) (?v4 S2) (?v5 S3)) (= (= (f27 (f28 (f29 f54 ?v0) ?v1) ?v2) (f27 (f28 (f29 f54 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (f32 f33 (f27 (f28 (f29 f54 ?v0) ?v1) ?v2)) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S2) (?v4 S2) (?v5 S3)) (not (= (f27 (f28 (f29 f30 ?v0) ?v1) ?v2) (f27 (f28 (f29 f54 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S2) (?v4 S2) (?v5 S3)) (not (= (f27 (f28 (f29 f54 ?v0) ?v1) ?v2) (f27 (f28 (f29 f30 ?v3) ?v4) ?v5)))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S3) (?v3 S2) (?v4 S3)) (let ((?v_0 (f55 f56 ?v0))) (= (f12 (f50 ?v_0 (f12 (f13 f14 ?v1) ?v2)) (f12 (f13 f14 ?v3) ?v4)) (f12 (f13 f14 (f8 (f18 ?v0 ?v1) ?v3)) (f12 (f50 ?v_0 ?v2) ?v4))))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S6) (?v3 S2) (?v4 S2) (?v5 S3)) (= (= (f42 ?v0 ?v1 ?v2 (f27 (f28 (f29 f54 ?v3) ?v4) ?v5)) f1) (= (f3 (f4 (f5 ?v2 ?v3) ?v4) ?v5) f1))))
(assert (forall ((?v0 S2)) (= (f52 (f53 ?v0) ?v0) f1)))
(assert (forall ((?v0 S2)) (= (f8 f57 ?v0) (f8 (f18 f20 ?v0) f34))))
(assert (forall ((?v0 S2)) (= (= f34 ?v0) (= ?v0 f34))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S3)) (= (f22 (f23 f24 (f12 (f13 f14 ?v0) ?v1)) (f12 (f13 f14 ?v2) ?v3)) (f8 (f18 f20 (f8 (f18 f58 ?v0) ?v2)) (f22 (f23 f24 ?v1) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f20 ?v0) ?v1) (f8 (f18 f20 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f18 f20 ?v0)) (?v_0 (f18 f20 ?v1))) (= (f8 ?v_1 (f8 ?v_0 ?v2)) (f8 ?v_0 (f8 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v0))) (= (f8 ?v_0 (f8 (f18 f20 ?v1) ?v2)) (f8 (f18 f20 (f8 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v0))) (= (f8 (f18 f20 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f18 f20 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v0))) (= (f8 (f18 f20 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f18 f20 ?v1) ?v2))))))
(assert (forall ((?v0 S2)) (= (f8 (f18 f58 f34) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f8 (f18 f58 f34) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f8 (f18 f58 f34) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f8 (f18 f58 ?v0) f34) ?v0)))
(assert (forall ((?v0 S2)) (= (f8 (f18 f58 ?v0) f34) ?v0)))
(assert (forall ((?v0 S2)) (= (f8 (f18 f58 ?v0) f34) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 (f18 f58 (f8 ?v_0 ?v1)) (f8 (f18 f58 ?v2) ?v3)) (f8 (f18 f58 (f8 ?v_0 ?v2)) (f8 (f18 f58 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_1 (f18 f58 (f8 (f18 f58 ?v0) ?v1))) (?v_0 (f18 f58 ?v2))) (= (f8 ?v_1 (f8 ?v_0 ?v3)) (f8 ?v_0 (f8 ?v_1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f18 f58 ?v0)) (?v_1 (f8 (f18 f58 ?v2) ?v3))) (= (f8 (f18 f58 (f8 ?v_0 ?v1)) ?v_1) (f8 ?v_0 (f8 (f18 f58 ?v1) ?v_1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 (f18 f58 (f8 ?v_0 ?v1)) ?v2) (f8 (f18 f58 (f8 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 (f18 f58 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f18 f58 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 (f18 f58 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f18 f58 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 ?v_0 (f8 (f18 f58 ?v1) ?v2)) (f8 (f18 f58 (f8 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f18 f58 ?v0)) (?v_0 (f18 f58 ?v1))) (= (f8 ?v_1 (f8 ?v_0 ?v2)) (f8 ?v_0 (f8 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f58 ?v0) ?v1) (f8 (f18 f58 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 ?v_0 (f8 (f18 f20 ?v1) ?v2)) (f8 (f18 f20 (f8 ?v_0 ?v1)) (f8 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f18 f58 ?v0)) (?v_1 (f18 f58 ?v1))) (= (and (not (= ?v0 ?v1)) (not (= ?v2 ?v3))) (not (= (f8 (f18 f20 (f8 ?v_0 ?v2)) (f8 ?v_1 ?v3)) (f8 (f18 f20 (f8 ?v_0 ?v3)) (f8 ?v_1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f58 (f8 (f18 f20 ?v0) ?v1)) ?v2) (f8 (f18 f20 (f8 (f18 f58 ?v0) ?v2)) (f8 (f18 f58 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f20 (f8 (f18 f58 ?v0) ?v1)) (f8 (f18 f58 ?v2) ?v1)) (f8 (f18 f58 (f8 (f18 f20 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f18 f58 ?v0)) (?v_1 (f18 f58 ?v2))) (= (= (f8 (f18 f20 (f8 ?v_0 ?v1)) (f8 ?v_1 ?v3)) (f8 (f18 f20 (f8 ?v_0 ?v3)) (f8 ?v_1 ?v1))) (or (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f58 (f8 (f18 f20 ?v0) ?v1)) ?v2) (f8 (f18 f20 (f8 (f18 f58 ?v0) ?v2)) (f8 (f18 f58 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (f8 (f18 f20 (f8 (f18 f58 ?v0) ?v1)) (f8 (f18 f20 (f8 (f18 f58 ?v2) ?v1)) ?v3)) (f8 (f18 f20 (f8 (f18 f58 (f8 (f18 f20 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f52 (f53 (f8 (f18 f58 ?v0) ?v1)) ?v2) f1) (= (f52 (f53 ?v1) ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f52 (f53 (f8 (f18 f58 ?v0) ?v1)) ?v2) f1) (= (f52 (f53 ?v0) ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 (f8 (f18 f58 ?v1) ?v2)) (= (f52 (f53 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f52 (f53 ?v0) ?v1) f1) (=> (= (f52 (f53 ?v2) ?v3) f1) (= (f52 (f53 (f8 (f18 f58 ?v0) ?v2)) (f8 (f18 f58 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (= (f52 ?v_0 (f8 (f18 f58 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (= (f52 ?v_0 (f8 (f18 f58 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f52 (f53 ?v0) (f8 (f18 f58 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f52 (f53 ?v0) (f8 (f18 f58 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (=> (= (f8 (f18 f19 ?v0) ?v1) (f8 (f18 f19 ?v2) ?v1)) (=> (= (f8 (f18 f19 ?v3) ?v1) (f8 (f18 f19 ?v4) ?v1)) (= (f8 (f18 f19 (f8 (f18 f58 ?v0) ?v3)) ?v1) (f8 (f18 f19 (f8 (f18 f58 ?v2) ?v4)) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f19 (f8 (f18 f58 (f8 (f18 f19 ?v0) ?v1)) ?v2)) ?v1) (f8 (f18 f19 (f8 (f18 f58 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f19 (f8 (f18 f58 ?v0) ?v1)) (f8 (f18 f58 ?v2) ?v1)) (f8 (f18 f58 (f8 (f18 f19 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 (f18 f19 (f8 ?v_0 ?v1)) (f8 ?v_0 ?v2)) (f8 ?v_0 (f8 (f18 f19 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f19 (f8 (f18 f58 ?v0) ?v1)) ?v2) (f8 (f18 f19 (f8 (f18 f58 (f8 (f18 f19 ?v0) ?v2)) (f8 (f18 f19 ?v1) ?v2))) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f19 (f8 (f18 f58 ?v0) ?v1)) ?v2) (f8 (f18 f19 (f8 (f18 f58 (f8 (f18 f19 ?v0) ?v2)) ?v1)) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 (f18 f19 (f8 ?v_0 ?v1)) ?v2) (f8 (f18 f19 (f8 ?v_0 (f8 (f18 f19 ?v1) ?v2))) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f58 (f8 (f18 f20 ?v0) ?v1)) ?v2) (f8 (f18 f20 (f8 (f18 f58 ?v0) ?v2)) (f8 (f18 f58 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 ?v_0 (f8 (f18 f20 ?v1) ?v2)) (f8 (f18 f20 (f8 ?v_0 ?v1)) (f8 ?v_0 ?v2))))))
(assert (forall ((?v0 S2)) (= (f8 (f18 f58 ?v0) f34) ?v0)))
(assert (forall ((?v0 S2)) (= (f8 (f18 f58 f34) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 (f18 f19 (f8 ?v_0 (f8 (f18 f19 ?v1) ?v2))) ?v2) (f8 (f18 f19 (f8 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 (f18 f19 (f8 ?v_0 ?v1)) ?v2) (f8 (f18 f19 (f8 ?v_0 (f8 (f18 f19 ?v1) ?v2))) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f20 (f8 (f18 f58 ?v0) ?v1)) ?v1) (f8 (f18 f58 (f8 (f18 f20 ?v0) f34)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f20 ?v0) (f8 (f18 f58 ?v1) ?v0)) (f8 (f18 f58 (f8 (f18 f20 ?v1) f34)) ?v0))))
(assert (forall ((?v0 S2)) (= (f8 (f18 f20 ?v0) ?v0) (f8 (f18 f58 (f8 (f18 f20 f34) f34)) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f19 (f8 (f18 f20 ?v0) (f8 (f18 f58 ?v1) ?v2))) ?v2) (f8 (f18 f19 ?v0) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f19 (f8 (f18 f20 ?v0) (f8 (f18 f58 ?v1) ?v2))) ?v1) (f8 (f18 f19 ?v0) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (= (= (f52 ?v_0 (f8 (f18 f20 ?v1) (f8 (f18 f58 ?v0) ?v2))) f1) (= (f52 ?v_0 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (let ((?v_0 (f53 ?v0)) (?v_1 (f18 f20 ?v2))) (=> (= (f52 ?v_0 ?v1) f1) (= (= (f52 ?v_0 (f8 ?v_1 ?v3)) f1) (= (f52 ?v_0 (f8 (f18 f20 (f8 ?v_1 (f8 (f18 f58 ?v4) ?v1))) ?v3)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f8 (f18 f20 ?v0) ?v1) (f8 (f18 f20 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v0))) (=> (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v0))) (=> (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f18 f20 ?v0))) (= (f8 (f18 f20 (f8 ?v_0 ?v1)) (f8 (f18 f20 ?v2) ?v3)) (f8 (f18 f20 (f8 ?v_0 ?v2)) (f8 (f18 f20 ?v1) ?v3))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f8 (f18 f20 ?v0) ?v1) (f8 (f18 f20 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v0))) (= (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v0))) (= (f8 (f18 f20 (f8 ?v_0 ?v1)) ?v2) (f8 (f18 f20 (f8 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f52 (f53 ?v0) ?v1) f1) (=> (forall ((?v2 S2)) (=> (= ?v1 (f8 (f18 f58 ?v0) ?v2)) false)) false))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2) (?v4 S2) (?v5 S3)) (let ((?v_0 (f29 f54 ?v2)) (?v_1 (f18 f58 ?v4))) (= (f43 (f44 (f45 f46 ?v0) ?v1) (f27 (f28 ?v_0 ?v3) (f12 (f13 f14 ?v4) ?v5))) (f27 (f28 ?v_0 (f8 (f18 f20 ?v3) (f8 ?v_1 ?v0))) (f12 (f50 f51 (f12 (f59 f60 ?v_1) ?v1)) ?v5))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2) (?v4 S2) (?v5 S3)) (let ((?v_0 (f29 f30 ?v2)) (?v_1 (f18 f58 ?v4))) (= (f43 (f44 (f45 f46 ?v0) ?v1) (f27 (f28 ?v_0 ?v3) (f12 (f13 f14 ?v4) ?v5))) (f27 (f28 ?v_0 (f8 (f18 f20 ?v3) (f8 ?v_1 ?v0))) (f12 (f50 f51 (f12 (f59 f60 ?v_1) ?v1)) ?v5))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f20 (f8 (f18 f20 (f8 (f18 f58 (f8 (f18 f61 ?v0) ?v1)) ?v1)) (f8 (f18 f19 ?v0) ?v1))) ?v2) (f8 (f18 f20 ?v0) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f20 (f8 (f18 f20 (f8 (f18 f58 ?v0) (f8 (f18 f61 ?v1) ?v0))) (f8 (f18 f19 ?v1) ?v0))) ?v2) (f8 (f18 f20 ?v1) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f20 (f8 (f18 f58 (f8 (f18 f61 ?v0) ?v1)) ?v1)) (f8 (f18 f19 ?v0) ?v1)) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f20 (f8 (f18 f58 ?v0) (f8 (f18 f61 ?v1) ?v0))) (f8 (f18 f19 ?v1) ?v0)) ?v1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f58 ?v0) ?v1) (f8 (f18 f58 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 (f18 f58 (f8 ?v_0 ?v1)) ?v2) (f8 ?v_0 (f8 (f18 f58 ?v1) ?v2))))))
(assert (forall ((?v0 S3)) (= (f12 (f59 f60 f9) ?v0) ?v0)))
(assert (forall ((?v0 S7) (?v1 S2) (?v2 S3)) (let ((?v_0 (f59 f60 ?v0))) (= (f12 ?v_0 (f12 (f13 f14 ?v1) ?v2)) (f12 (f13 f14 (f8 ?v0 ?v1)) (f12 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f52 (f53 ?v0) ?v1) f1) (= (f8 (f18 f58 ?v0) (f8 (f18 f61 ?v1) ?v0)) ?v1))))
(assert (forall ((?v0 S2)) (= (f8 (f18 f61 ?v0) f34) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (=> (= (f52 ?v_0 ?v2) f1) (= (= (f52 (f53 (f8 (f18 f61 ?v1) ?v0)) (f8 (f18 f61 ?v2) ?v0)) f1) (= (f52 (f53 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S3)) (= (f12 (f59 f60 (f18 f58 f34)) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f18 f58 ?v0))) (= (f22 (f23 f24 (f12 (f59 f60 ?v_0) ?v1)) ?v2) (f8 ?v_0 (f22 (f23 f24 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f61 (f8 (f18 f20 ?v0) ?v1)) ?v2) (f8 (f18 f20 (f8 (f18 f20 (f8 (f18 f61 ?v0) ?v2)) (f8 (f18 f61 ?v1) ?v2))) (f8 (f18 f61 (f8 (f18 f20 (f8 (f18 f19 ?v0) ?v2)) (f8 (f18 f19 ?v1) ?v2))) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= ?v0 (f8 (f18 f20 (f8 (f18 f58 ?v1) (f8 (f18 f61 ?v0) ?v1))) (f8 (f18 f19 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 (f18 f61 (f8 ?v_0 ?v1)) ?v2) (f8 (f18 f20 (f8 ?v_0 (f8 (f18 f61 ?v1) ?v2))) (f8 (f18 f61 (f8 ?v_0 (f8 (f18 f19 ?v1) ?v2))) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f20 (f8 (f18 f20 (f8 (f18 f58 ?v0) (f8 (f18 f61 ?v1) ?v0))) (f8 (f18 f19 ?v1) ?v0))) ?v2) (f8 (f18 f20 ?v1) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f20 (f8 (f18 f20 (f8 (f18 f58 (f8 (f18 f61 ?v0) ?v1)) ?v1)) (f8 (f18 f19 ?v0) ?v1))) ?v2) (f8 (f18 f20 ?v0) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (=> (= (f52 ?v_0 ?v2) f1) (= (f8 (f18 f61 (f8 (f18 f20 ?v1) ?v2)) ?v0) (f8 (f18 f20 (f8 (f18 f61 ?v1) ?v0)) (f8 (f18 f61 ?v2) ?v0))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f52 (f53 ?v0) ?v1) f1) (= (f8 (f18 f58 ?v0) (f8 (f18 f61 ?v1) ?v0)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v2))) (=> (= (f52 (f53 ?v0) ?v1) f1) (= (f8 ?v_0 (f8 (f18 f61 ?v1) ?v0)) (f8 (f18 f61 (f8 ?v_0 ?v1)) ?v0))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f52 (f53 ?v0) ?v1) f1) (= (f8 (f18 f58 (f8 (f18 f61 ?v1) ?v0)) ?v0) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f52 (f53 ?v0) ?v1) f1) (= (f8 (f18 f58 (f8 (f18 f61 ?v1) ?v0)) ?v2) (f8 (f18 f61 (f8 (f18 f58 ?v1) ?v2)) ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f52 (f53 ?v0) ?v1) f1) (=> (= (f52 (f53 ?v2) ?v3) f1) (= (f8 (f18 f58 (f8 (f18 f61 ?v1) ?v0)) (f8 (f18 f61 ?v3) ?v2)) (f8 (f18 f61 (f8 (f18 f58 ?v1) ?v3)) (f8 (f18 f58 ?v0) ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f20 (f8 (f18 f19 ?v0) ?v1)) (f8 (f18 f58 (f8 (f18 f61 ?v0) ?v1)) ?v1)) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (forall ((?v2 S2) (?v3 S2)) (=> (= ?v2 (f8 (f18 f61 ?v0) ?v1)) (=> (= ?v3 (f8 (f18 f19 ?v0) ?v1)) (=> (= ?v0 (f8 (f18 f20 (f8 (f18 f58 ?v2) ?v1)) ?v3)) false)))) false)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S7) (?v3 S3)) (= (= (f12 (f13 f14 ?v0) ?v1) (f12 (f59 f60 ?v2) ?v3)) (exists ((?v4 S2) (?v5 S3)) (and (= ?v3 (f12 (f13 f14 ?v4) ?v5)) (and (= ?v0 (f8 ?v2 ?v4)) (= ?v1 (f12 (f59 f60 ?v2) ?v5))))))))
(assert (forall ((?v0 S7) (?v1 S3) (?v2 S2) (?v3 S3)) (= (= (f12 (f59 f60 ?v0) ?v1) (f12 (f13 f14 ?v2) ?v3)) (exists ((?v4 S2) (?v5 S3)) (and (= ?v1 (f12 (f13 f14 ?v4) ?v5)) (and (= (f8 ?v0 ?v4) ?v2) (= (f12 (f59 f60 ?v0) ?v5) ?v3)))))))
(assert (forall ((?v0 S7) (?v1 S3) (?v2 S2) (?v3 S3)) (=> (= (f12 (f59 f60 ?v0) ?v1) (f12 (f13 f14 ?v2) ?v3)) (exists ((?v4 S2) (?v5 S3)) (and (= ?v1 (f12 (f13 f14 ?v4) ?v5)) (and (= (f8 ?v0 ?v4) ?v2) (= (f12 (f59 f60 ?v0) ?v5) ?v3)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S7) (?v3 S3)) (=> (= (f12 (f13 f14 ?v0) ?v1) (f12 (f59 f60 ?v2) ?v3)) (exists ((?v4 S2) (?v5 S3)) (and (= ?v3 (f12 (f13 f14 ?v4) ?v5)) (and (= ?v0 (f8 ?v2 ?v4)) (= ?v1 (f12 (f59 f60 ?v2) ?v5))))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2) (?v4 S3)) (let ((?v_0 (f18 f58 ?v3))) (= (f43 (f44 (f45 f46 ?v0) ?v1) (f27 (f28 f62 ?v2) (f12 (f13 f14 ?v3) ?v4))) (f27 (f28 f62 (f8 (f18 f63 ?v2) (f8 ?v_0 ?v0))) (f12 (f50 f51 (f12 (f59 f60 ?v_0) ?v1)) ?v4))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S2) (?v4 S3)) (not (= (f27 (f28 (f29 f30 ?v0) ?v1) ?v2) (f27 (f28 f62 ?v3) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2) (?v4 S3)) (not (= (f27 (f28 f62 ?v0) ?v1) (f27 (f28 (f29 f30 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2) (?v4 S3)) (not (= (f27 (f28 f62 ?v0) ?v1) (f27 (f28 (f29 f54 ?v2) ?v3) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S2) (?v4 S3)) (not (= (f27 (f28 (f29 f54 ?v0) ?v1) ?v2) (f27 (f28 f62 ?v3) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f8 (f18 f63 ?v0) ?v1) (f8 (f18 f63 ?v2) ?v3)) (= (= ?v0 ?v1) (= ?v2 ?v3)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f22 (f23 f24 (f12 (f50 f64 ?v0) ?v1)) ?v2) (f8 (f18 f63 (f22 (f23 f24 ?v0) ?v2)) (f22 (f23 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S3)) (= (f12 (f50 f64 (f12 (f13 f14 ?v0) ?v1)) (f12 (f13 f14 ?v2) ?v3)) (f12 (f13 f14 (f8 (f18 f63 ?v0) ?v2)) (f12 (f50 f64 ?v1) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S3)) (= (= (f27 (f28 f62 ?v0) ?v1) (f27 (f28 f62 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (= f64 (f55 f56 f63)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 (f8 (f18 f63 ?v1) ?v2)) f1) (=> (= (f52 ?v_0 ?v2) f1) (= (f52 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f19 (f8 (f18 f63 (f8 (f18 f19 ?v0) ?v1)) ?v2)) ?v1) (f8 (f18 f19 (f8 (f18 f63 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f63 ?v0))) (= (f8 (f18 f19 (f8 ?v_0 (f8 (f18 f19 ?v1) ?v2))) ?v2) (f8 (f18 f19 (f8 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (=> (= (f8 (f18 f19 ?v0) ?v1) (f8 (f18 f19 ?v2) ?v1)) (=> (= (f8 (f18 f19 ?v3) ?v1) (f8 (f18 f19 ?v4) ?v1)) (= (f8 (f18 f19 (f8 (f18 f63 ?v0) ?v3)) ?v1) (f8 (f18 f19 (f8 (f18 f63 ?v2) ?v4)) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f19 (f8 (f18 f63 ?v0) ?v1)) ?v2) (f8 (f18 f19 (f8 (f18 f63 (f8 (f18 f19 ?v0) ?v2)) (f8 (f18 f19 ?v1) ?v2))) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f19 (f8 (f18 f63 ?v0) ?v1)) ?v2) (f8 (f18 f19 (f8 (f18 f63 (f8 (f18 f19 ?v0) ?v2)) ?v1)) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f63 ?v0))) (= (f8 (f18 f19 (f8 ?v_0 ?v1)) ?v2) (f8 (f18 f19 (f8 ?v_0 (f8 (f18 f19 ?v1) ?v2))) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f53 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (=> (= (f52 ?v_0 ?v2) f1) (= (f52 ?v_0 (f8 (f18 f63 ?v1) ?v2)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f20 (f8 (f18 f63 ?v0) ?v1)) ?v1) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f63 (f8 (f18 f20 ?v0) ?v1)) ?v1) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f8 (f18 f58 (f8 (f18 f63 ?v0) ?v1)) ?v2) (f8 (f18 f63 (f8 (f18 f58 ?v0) ?v2)) (f8 (f18 f58 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (= (f8 ?v_0 (f8 (f18 f63 ?v1) ?v2)) (f8 (f18 f63 (f8 ?v_0 ?v1)) (f8 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (= (= (f8 (f18 f20 (f8 (f18 f58 ?v0) ?v1)) ?v2) (f8 (f18 f20 (f8 (f18 f58 ?v3) ?v1)) ?v4)) (= (f8 (f18 f20 (f8 (f18 f58 (f8 (f18 f63 ?v0) ?v3)) ?v1)) ?v2) ?v4))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (= (= (f8 (f18 f20 (f8 (f18 f58 ?v0) ?v1)) ?v2) (f8 (f18 f20 (f8 (f18 f58 ?v3) ?v1)) ?v4)) (= ?v2 (f8 (f18 f20 (f8 (f18 f58 (f8 (f18 f63 ?v3) ?v0)) ?v1)) ?v4)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f8 (f18 f19 ?v0) ?v1) (f8 (f18 f19 ?v2) ?v1)) (= (f52 (f53 ?v1) (f8 (f18 f63 ?v0) ?v2)) f1))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S6) (?v3 S2) (?v4 S3)) (= (= (f42 ?v0 ?v1 ?v2 (f27 (f28 f62 ?v3) ?v4)) f1) (= (f3 (f4 ?v0 ?v3) ?v4) f1))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f32 f33 (f27 (f28 f62 ?v0) ?v1)) f34)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f58 ?v0) (f8 (f18 f61 ?v1) ?v0)) (f8 (f18 f63 ?v1) (f8 (f18 f19 ?v1) ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f8 (f18 f19 ?v0) ?v1) (f8 (f18 f63 ?v0) (f8 (f18 f58 (f8 (f18 f61 ?v0) ?v1)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f52 (f53 ?v0) ?v1) f1) (forall ((?v3 S2) (?v4 S2)) (let ((?v_0 (f53 ?v0))) (= (not (= (f52 ?v_0 (f8 (f18 f20 ?v3) ?v2)) f1)) (not (= (f52 ?v_0 (f8 (f18 f20 (f8 (f18 f63 ?v3) (f8 (f18 f58 ?v4) ?v1))) ?v2)) f1))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f52 (f53 ?v0) ?v1) f1) (forall ((?v3 S2) (?v4 S2)) (let ((?v_0 (f53 ?v0))) (= (= (f52 ?v_0 (f8 (f18 f20 ?v3) ?v2)) f1) (= (f52 ?v_0 (f8 (f18 f20 (f8 (f18 f63 ?v3) (f8 (f18 f58 ?v4) ?v1))) ?v2)) f1)))))))
(assert (forall ((?v0 S8)) (=> (forall ((?v1 S2) (?v2 S3)) (=> (= ?v0 (f27 (f28 f62 ?v1) ?v2)) false)) (=> (forall ((?v1 S2) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f27 (f28 (f29 f30 ?v1) ?v2) ?v3)) false)) (=> (forall ((?v1 S2) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f27 (f28 (f29 f54 ?v1) ?v2) ?v3)) false)) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (= (= (f10 (f27 (f28 f62 ?v0) ?v1) ?v2) f1) (= (f52 (f65 ?v0) (f22 (f23 f24 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S29) (?v1 S2) (?v2 S29)) (=> (forall ((?v3 S2) (?v4 S2)) (= (= (f52 ?v0 ?v3) f1) (= (f52 ?v0 (f8 (f18 f63 ?v3) (f8 (f18 f58 ?v4) ?v1))) f1))) (=> (forall ((?v3 S2) (?v4 S2)) (= (= (f52 ?v2 ?v3) f1) (= (f52 ?v2 (f8 (f18 f63 ?v3) (f8 (f18 f58 ?v4) ?v1))) f1))) (forall ((?v3 S2) (?v4 S2)) (let ((?v_0 (f8 (f18 f63 ?v3) (f8 (f18 f58 ?v4) ?v1)))) (= (or (= (f52 ?v0 ?v3) f1) (= (f52 ?v2 ?v3) f1)) (or (= (f52 ?v0 ?v_0) f1) (= (f52 ?v2 ?v_0) f1)))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f8 (f18 f63 ?v0) ?v1) (f8 (f18 f63 ?v2) ?v3)) (= (= (f52 (f65 ?v0) ?v1) f1) (= (f52 (f65 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f52 (f65 ?v0) ?v1) f1) (=> (= (f52 (f65 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f65 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (=> (= (f52 (f65 ?v1) ?v2) f1) (= (f52 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f52 (f65 ?v0) ?v1) f1) (= (f52 (f65 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2)) (= (f52 (f65 ?v0) ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v2))) (=> (= (f52 (f65 ?v0) ?v1) f1) (= (f52 (f65 (f8 ?v_0 ?v0)) (f8 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f52 (f65 (f8 (f18 f20 ?v0) ?v1)) (f8 (f18 f20 ?v2) ?v1)) f1) (= (f52 (f65 ?v0) ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v0))) (= (= (f52 (f65 (f8 ?v_0 ?v1)) (f8 ?v_0 ?v2)) f1) (= (f52 (f65 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f52 (f65 ?v0) ?v1) f1) (= (f52 (f65 (f8 (f18 f20 ?v0) ?v2)) (f8 (f18 f20 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v2))) (=> (= (f52 (f65 ?v0) ?v1) f1) (= (f52 (f65 (f8 ?v_0 ?v0)) (f8 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f52 (f65 ?v0) ?v1) f1) (=> (= (f52 (f65 ?v2) ?v3) f1) (= (f52 (f65 (f8 (f18 f20 ?v0) ?v2)) (f8 (f18 f20 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f52 (f65 (f8 (f18 f20 ?v0) ?v1)) (f8 (f18 f20 ?v2) ?v1)) f1) (= (f52 (f65 ?v0) ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f20 ?v0))) (=> (= (f52 (f65 (f8 ?v_0 ?v1)) (f8 ?v_0 ?v2)) f1) (= (f52 (f65 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (= (= (f52 (f65 (f8 (f18 f20 (f8 (f18 f58 ?v0) ?v1)) ?v2)) (f8 (f18 f20 (f8 (f18 f58 ?v3) ?v1)) ?v4)) f1) (= (f52 (f65 ?v2) (f8 (f18 f20 (f8 (f18 f58 (f8 (f18 f63 ?v3) ?v0)) ?v1)) ?v4)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (= (= (f52 (f65 (f8 (f18 f20 (f8 (f18 f58 ?v0) ?v1)) ?v2)) (f8 (f18 f20 (f8 (f18 f58 ?v3) ?v1)) ?v4)) f1) (= (f52 (f65 (f8 (f18 f20 (f8 (f18 f58 (f8 (f18 f63 ?v0) ?v3)) ?v1)) ?v2)) ?v4) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S29)) (=> (= (f52 (f65 ?v0) ?v1) f1) (=> (= (f52 ?v2 ?v1) f1) (=> (forall ((?v3 S2)) (=> (= (f52 (f65 ?v3) ?v1) f1) (=> (= (f52 ?v2 ?v3) f1) (= (f52 ?v2 (f8 (f18 f63 ?v3) f34)) f1)))) (= (f52 ?v2 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S29)) (=> (= (f52 (f65 ?v0) ?v1) f1) (=> (= (f52 ?v2 ?v0) f1) (=> (forall ((?v3 S2)) (=> (= (f52 (f65 ?v0) ?v3) f1) (=> (= (f52 ?v2 ?v3) f1) (= (f52 ?v2 (f8 (f18 f20 ?v3) f34)) f1)))) (= (f52 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (f52 (f65 ?v0) ?v0) f1)))
(assert (forall ((?v0 S29) (?v1 S2) (?v2 S2)) (=> (= (f52 ?v0 ?v1) f1) (=> (forall ((?v3 S2)) (=> (= (f52 (f65 ?v1) ?v3) f1) (=> (= (f52 ?v0 ?v3) f1) (= (f52 ?v0 (f8 (f18 f20 ?v3) f34)) f1)))) (=> (forall ((?v3 S2)) (=> (= (f52 (f65 ?v3) ?v1) f1) (=> (= (f52 ?v0 ?v3) f1) (= (f52 ?v0 (f8 (f18 f63 ?v3) f34)) f1)))) (= (f52 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f52 (f65 ?v0) ?v1) f1) (= (f52 (f65 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 ?v1) (and (= (f52 (f65 ?v0) ?v1) f1) (= (f52 (f65 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= ?v0 ?v1) (= (f52 (f65 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f52 (f65 ?v0) ?v1) f1) (= (= (f52 (f65 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f52 (f65 ?v1) ?v2) f1) (= (f52 (f65 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f65 ?v2))) (=> (= ?v0 ?v1) (=> (= (f52 ?v_0 ?v1) f1) (= (f52 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f65 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f52 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f52 (f65 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f52 (f65 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f52 (f65 ?v0) ?v1) f1) (=> (= (f52 (f65 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f65 ?v0))) (=> (= (f52 ?v_0 ?v1) f1) (=> (= (f52 (f65 ?v1) ?v2) f1) (= (f52 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f52 (f65 ?v0) ?v1) f1) (=> (= (f52 (f65 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f65 ?v2))) (=> (= (f52 (f65 ?v0) ?v1) f1) (=> (= (f52 ?v_0 ?v0) f1) (= (f52 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f52 (f65 ?v0) ?v1) f1) false) (=> (=> (= (f52 (f65 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S7) (?v2 S2) (?v3 S2)) (=> (= ?v0 (f8 ?v1 ?v2)) (=> (= (f52 (f65 ?v3) ?v2) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f52 (f65 ?v5) ?v4) f1) (= (f52 (f65 (f8 ?v1 ?v5)) (f8 ?v1 ?v4)) f1))) (= (f52 (f65 (f8 ?v1 ?v3)) ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S7) (?v3 S2)) (=> (= (f52 (f65 ?v0) ?v1) f1) (=> (= (f8 ?v2 ?v0) ?v3) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f52 (f65 ?v5) ?v4) f1) (= (f52 (f65 (f8 ?v2 ?v5)) (f8 ?v2 ?v4)) f1))) (= (f52 (f65 ?v3) (f8 ?v2 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (let ((?v_0 (f65 f66))) (=> (= (f52 (f65 ?v0) ?v1) f1) (=> (= (f52 (f65 ?v2) ?v1) f1) (=> (= (f52 ?v_0 ?v3) f1) (=> (= (f52 ?v_0 ?v4) f1) (=> (= (f8 (f18 f20 ?v3) ?v4) f34) (= (f52 (f65 (f8 (f18 f20 (f8 (f18 f58 ?v3) ?v0)) (f8 (f18 f58 ?v4) ?v2))) ?v1) f1)))))))))
(assert (forall ((?v0 S2)) (= (f52 (f53 ?v0) f66) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (not (= ?v0 f66)) (= (f8 (f18 f61 (f8 (f18 f20 ?v1) (f8 (f18 f58 ?v0) ?v2))) ?v0) (f8 (f18 f20 ?v2) (f8 (f18 f61 ?v1) ?v0))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (not (= ?v0 f66)) (= (f8 (f18 f61 (f8 (f18 f20 ?v1) (f8 (f18 f58 ?v2) ?v0))) ?v0) (f8 (f18 f20 ?v2) (f8 (f18 f61 ?v1) ?v0))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 f66)) (= (f8 (f18 f61 (f8 (f18 f20 ?v1) ?v0)) ?v0) (f8 (f18 f20 (f8 (f18 f61 ?v1) ?v0)) f34)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 f66)) (= (f8 (f18 f61 (f8 (f18 f20 ?v0) ?v1)) ?v0) (f8 (f18 f20 (f8 (f18 f61 ?v1) ?v0)) f34)))))
(assert (forall ((?v0 S2)) (=> (not (= ?v0 f66)) (= (f8 (f18 f61 ?v0) ?v0) f34))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f8 (f18 f19 ?v0) ?v1) f66) (exists ((?v2 S2)) (= ?v0 (f8 (f18 f58 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (=> (= (f52 (f53 (f8 ?v_0 ?v1)) (f8 ?v_0 ?v2)) f1) (=> (not (= ?v0 f66)) (= (f52 (f53 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 f58 ?v0))) (=> (not (= ?v0 f66)) (= (= (f52 (f53 ?v1) ?v2) f1) (= (f52 (f53 (f8 ?v_0 ?v1)) (f8 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S2)) (= (= (f8 (f18 f20 ?v0) ?v0) f66) (= ?v0 f66))))
(assert (forall ((?v0 S2)) (= (f8 (f18 f58 f66) ?v0) f66)))
(assert (forall ((?v0 S2)) (= (f8 (f18 f58 ?v0) f66) f66)))
(check-sat)
(exit)
