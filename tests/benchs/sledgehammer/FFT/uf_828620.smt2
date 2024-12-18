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
(declare-sort S27 0)
(declare-sort S28 0)
(declare-sort S29 0)
(declare-sort S30 0)
(declare-sort S31 0)
(declare-sort S32 0)
(declare-sort S33 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S4) S4)
(declare-fun f6 (S6 S4) S5)
(declare-fun f7 () S6)
(declare-fun f8 (S7 S8) S4)
(declare-fun f9 (S9 S3) S7)
(declare-fun f10 () S9)
(declare-fun f11 (S10 S2) S3)
(declare-fun f12 () S10)
(declare-fun f13 (S11 S2) S8)
(declare-fun f14 (S2) S11)
(declare-fun f15 () S2)
(declare-fun f16 () S2)
(declare-fun f17 (S12 S4) S3)
(declare-fun f18 () S12)
(declare-fun f19 () S3)
(declare-fun f20 (S13 S2) S2)
(declare-fun f21 (S14 S2) S13)
(declare-fun f22 () S14)
(declare-fun f23 () S2)
(declare-fun f24 () S6)
(declare-fun f25 () S3)
(declare-fun f26 (S15 S13) S3)
(declare-fun f27 () S15)
(declare-fun f28 () S3)
(declare-fun f29 (S16 S13) S13)
(declare-fun f30 () S16)
(declare-fun f31 () S13)
(declare-fun f32 (S17 S2) S18)
(declare-fun f33 (S19 S13) S17)
(declare-fun f34 () S19)
(declare-fun f35 () S17)
(declare-fun f36 (S20 S3) S12)
(declare-fun f37 () S20)
(declare-fun f38 () S20)
(declare-fun f39 (S21 S13) S14)
(declare-fun f40 () S21)
(declare-fun f41 (S22 S18) S17)
(declare-fun f42 (S23 S17) S22)
(declare-fun f43 () S23)
(declare-fun f44 (S24 S18) S18)
(declare-fun f45 (S25 S18) S24)
(declare-fun f46 () S25)
(declare-fun f47 (S26 S3) S10)
(declare-fun f48 (S27 S2) S26)
(declare-fun f49 () S27)
(declare-fun f50 () S27)
(declare-fun f51 (S8 S2) S1)
(declare-fun f52 (S2) S8)
(declare-fun f53 () S4)
(declare-fun f54 (S28 S3) S3)
(declare-fun f55 (S29 S2) S28)
(declare-fun f56 () S29)
(declare-fun f57 () S29)
(declare-fun f58 () S18)
(declare-fun f59 () S22)
(declare-fun f60 () S14)
(declare-fun f61 (S18 S18) S1)
(declare-fun f62 (S2 S8) S1)
(declare-fun f63 () S4)
(declare-fun f64 (S30 S8) S2)
(declare-fun f65 (S31 S13) S30)
(declare-fun f66 () S31)
(declare-fun f67 (S32 S8) S18)
(declare-fun f68 (S33 S17) S32)
(declare-fun f69 () S33)
(declare-fun f70 () S2)
(declare-fun f71 () S18)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 (f6 f7 (f8 (f9 f10 (f11 f12 ?v0)) (f13 (f14 f15) f16))) (f3 (f17 f18 (f3 f19 f16)) (f20 (f21 f22 f23) ?v0))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f3 (f11 f12 ?v0) ?v1) (f5 (f6 f24 (f3 (f17 f18 (f3 f19 f16)) (f20 (f21 f22 ?v0) ?v1))) (f3 f25 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S2)) (= (f3 (f26 f27 ?v0) ?v1) (f3 f28 (f20 ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S2)) (= (f20 (f29 f30 ?v0) ?v1) (f20 f31 (f20 ?v0 ?v1)))))
(assert (forall ((?v0 S13) (?v1 S2)) (= (f32 (f33 f34 ?v0) ?v1) (f32 f35 (f20 ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S2)) (= (f3 (f17 (f36 f37 ?v0) ?v1) ?v2) (f5 (f6 f7 (f3 ?v0 ?v2)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S2)) (= (f3 (f17 (f36 f38 ?v0) ?v1) ?v2) (f5 (f6 f24 (f3 ?v0 ?v2)) ?v1))))
(assert (forall ((?v0 S13) (?v1 S2) (?v2 S2)) (= (f20 (f21 (f39 f40 ?v0) ?v1) ?v2) (f20 (f21 f22 (f20 ?v0 ?v2)) ?v1))))
(assert (forall ((?v0 S17) (?v1 S18) (?v2 S2)) (= (f32 (f41 (f42 f43 ?v0) ?v1) ?v2) (f44 (f45 f46 (f32 ?v0 ?v2)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2)) (= (f3 (f11 (f47 (f48 f49 ?v0) ?v1) ?v2) ?v3) (f5 (f6 f24 (f3 (f17 f18 (f3 f19 ?v0)) (f20 (f21 f22 ?v2) ?v3))) (f3 ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S2)) (= (f3 (f11 (f47 (f48 f50 ?v0) ?v1) ?v2) ?v3) (f5 (f6 f7 (f3 ?v1 ?v3)) (f3 (f17 f18 (f3 f19 ?v0)) (f20 (f21 f22 ?v2) ?v3))))))
(assert (not (= (f8 (f9 f10 f4) (f13 (f14 f15) f16)) (f5 (f6 f24 (f3 f28 f16)) (f3 f25 f23)))))
(assert (= (f51 (f52 f23) f16) f1))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f17 f18 ?v0))) (=> (not (= ?v0 f53)) (= (f5 (f6 f7 (f3 ?v_0 (f20 (f21 f22 ?v1) ?v2))) (f3 ?v_0 (f20 (f21 f22 ?v3) ?v1))) (f3 (f17 f18 (f5 (f6 f7 (f3 ?v_0 ?v2)) (f3 ?v_0 ?v3))) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (f3 (f54 (f55 f56 ?v0) ?v1) ?v2) (f8 (f9 f10 (f11 (f47 (f48 f50 ?v0) ?v1) ?v2)) (f13 (f14 f15) ?v0)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (f3 (f54 (f55 f57 ?v0) ?v1) ?v2) (f8 (f9 f10 (f11 (f47 (f48 f49 ?v0) ?v1) ?v2)) (f13 (f14 f15) ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f20 f31 (f20 (f21 f22 ?v0) ?v1)) (f20 (f21 f22 (f20 f31 ?v0)) (f20 f31 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f3 f28 (f20 (f21 f22 ?v0) ?v1)) (f5 (f6 f24 (f3 f28 ?v0)) (f3 f28 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f32 f35 (f20 (f21 f22 ?v0) ?v1)) (f44 (f45 f46 (f32 f35 ?v0)) (f32 f35 ?v1)))))
(assert (= (f3 f28 f15) f53))
(assert (= (f32 f35 f15) f58))
(assert (= (f20 f31 f15) f15))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2)) (=> (not (= ?v0 f53)) (= (f3 (f17 f18 (f5 (f6 f7 ?v1) ?v0)) ?v2) (f5 (f6 f7 (f3 (f17 f18 ?v1) ?v2)) (f3 (f17 f18 ?v0) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S2)) (= (= (f3 (f17 f18 ?v0) ?v1) f53) (and (= ?v0 f53) (not (= ?v1 f15))))))
(assert (forall ((?v0 S18) (?v1 S2)) (= (= (f32 (f41 f59 ?v0) ?v1) f58) (and (= ?v0 f58) (not (= ?v1 f15))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f20 (f21 f60 ?v0) ?v1) f15) (and (= ?v0 f15) (not (= ?v1 f15))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (= ?v0 (f5 (f6 f7 ?v1) ?v2)) (ite (not (= ?v2 f53)) (= (f5 (f6 f24 ?v0) ?v2) ?v1) (= ?v0 f53)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (= (= (f5 (f6 f7 ?v0) ?v1) ?v2) (ite (not (= ?v1 f53)) (= ?v0 (f5 (f6 f24 ?v2) ?v1)) (= ?v2 f53)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (=> (not (= ?v0 f53)) (= (= ?v1 (f5 (f6 f7 ?v2) ?v0)) (= (f5 (f6 f24 ?v1) ?v0) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (=> (not (= ?v0 f53)) (= (= (f5 (f6 f7 ?v1) ?v0) ?v2) (= ?v1 (f5 (f6 f24 ?v2) ?v0))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (=> (not (= ?v0 f53)) (= (f5 (f6 f7 (f5 (f6 f24 ?v1) ?v0)) (f5 (f6 f24 ?v2) ?v0)) (f5 (f6 f7 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f24 ?v0))) (=> (not (= ?v0 f53)) (= (f5 (f6 f7 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2)) (f5 (f6 f7 ?v1) ?v2))))))
(assert (forall ((?v0 S2)) (=> (= (f51 (f52 ?v0) f15) f1) false)))
(assert (forall ((?v0 S2)) (not (= (f51 (f52 ?v0) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= ?v0 ?v1)) (or (= (f51 (f52 ?v0) ?v1) f1) (= (f51 (f52 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f52 f15))) (= (= (f51 ?v_0 (f20 (f21 f60 ?v0) ?v1)) f1) (or (= (f51 ?v_0 ?v0) f1) (= ?v1 f15))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f61 (f32 f35 ?v0) (f32 f35 ?v1)) f1) (= (f51 (f52 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f51 (f52 (f20 f31 ?v0)) (f20 f31 ?v1)) f1) (= (f51 (f52 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f51 (f52 ?v0) ?v1) f1) false) (=> (=> (= (f51 (f52 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f61 ?v0 ?v1) f1) false) (=> (=> (= (f61 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f21 f60 ?v0))) (=> (= (f51 (f52 f15) ?v0) f1) (=> (= (f51 (f52 (f20 ?v_0 ?v1)) (f20 ?v_0 ?v2)) f1) (= (f51 (f52 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S2)) (=> (= (f51 (f52 ?v0) ?v0) f1) false)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f51 (f52 ?v0) ?v1) f1) (not (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f51 (f52 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f51 (f52 ?v0) ?v1) f1) (= (f61 (f32 f35 ?v0) (f32 f35 ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f51 (f52 ?v0) ?v1) f1) (= (f51 (f52 (f20 f31 ?v0)) (f20 f31 ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f61 (f32 f35 ?v0) (f32 f35 ?v1)) f1) (= (f51 (f52 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f51 (f52 (f20 f31 ?v0)) (f20 f31 ?v1)) f1) (= (f51 (f52 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S11)) (let ((?v_0 (= (f51 (f13 ?v2 ?v1) ?v0) f1))) (=> (=> (= (f51 (f52 ?v0) ?v1) f1) ?v_0) (=> (=> (= ?v0 ?v1) ?v_0) (=> (=> (= (f51 (f52 ?v1) ?v0) f1) ?v_0) ?v_0))))))
(assert (forall ((?v0 S2)) (=> (=> (= ?v0 f15) false) (= (f51 (f52 f15) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f51 (f52 ?v0) ?v1) f1) (not (= ?v1 f15)))))
(assert (forall ((?v0 S2)) (= (= (f51 (f52 ?v0) f15) f1) false)))
(assert (forall ((?v0 S2)) (= (not (= ?v0 f15)) (= (f51 (f52 f15) ?v0) f1))))
(assert (forall ((?v0 S2)) (not (= (f51 (f52 ?v0) f15) f1))))
(assert (forall ((?v0 S2)) (= (= (f61 f58 (f32 f35 ?v0)) f1) (= (f51 (f52 f15) ?v0) f1))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f52 f15))) (= (= (f51 ?v_0 (f20 f31 ?v0)) f1) (= (f51 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f45 f46 ?v2))) (=> (= (f61 ?v0 ?v1) f1) (=> (= (f61 ?v2 f58) f1) (= (f61 (f44 ?v_0 ?v1) (f44 ?v_0 ?v0)) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f61 ?v0 ?v1) f1) (=> (= (f61 ?v2 f58) f1) (= (f61 (f44 (f45 f46 ?v1) ?v2) (f44 (f45 f46 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f45 f46 ?v2))) (=> (= (f61 ?v0 ?v1) f1) (=> (= (f61 f58 ?v2) f1) (= (f61 (f44 ?v_0 ?v0) (f44 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f21 f22 ?v2))) (=> (= (f51 (f52 ?v0) ?v1) f1) (=> (= (f51 (f52 f15) ?v2) f1) (= (f51 (f52 (f20 ?v_0 ?v0)) (f20 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f45 f46 ?v2))) (=> (= (f61 ?v0 ?v1) f1) (=> (= (f61 f58 ?v2) f1) (= (f61 (f44 ?v_0 ?v0) (f44 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f21 f22 ?v2))) (=> (= (f51 (f52 ?v0) ?v1) f1) (=> (= (f51 (f52 f15) ?v2) f1) (= (f51 (f52 (f20 ?v_0 ?v0)) (f20 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (=> (= (f61 ?v0 ?v1) f1) (=> (= (f61 f58 ?v2) f1) (= (f61 (f44 (f45 f46 ?v0) ?v2) (f44 (f45 f46 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f51 (f52 ?v0) ?v1) f1) (=> (= (f51 (f52 f15) ?v2) f1) (= (f51 (f52 (f20 (f21 f22 ?v0) ?v2)) (f20 (f21 f22 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f61 ?v0 f58) f1) (=> (= (f61 ?v1 f58) f1) (= (f61 f58 (f44 (f45 f46 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f61 ?v0 f58) f1) (=> (= (f61 f58 ?v1) f1) (= (f61 (f44 (f45 f46 ?v0) ?v1) f58) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f51 (f52 ?v0) f15) f1) (=> (= (f51 (f52 f15) ?v1) f1) (= (f51 (f52 (f20 (f21 f22 ?v0) ?v1)) f15) f1)))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f45 f46 ?v0))) (=> (= (f61 ?v0 f58) f1) (= (= (f61 (f44 ?v_0 ?v1) (f44 ?v_0 ?v2)) f1) (= (f61 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f61 f58 (f44 (f45 f46 ?v0) ?v1)) f1) (=> (= (f61 f58 ?v1) f1) (= (f61 f58 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f52 f15))) (=> (= (f51 ?v_0 (f20 (f21 f22 ?v0) ?v1)) f1) (=> (= (f51 ?v_0 ?v1) f1) (= (f51 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f61 f58 (f44 (f45 f46 ?v0) ?v1)) f1) (=> (= (f61 f58 ?v0) f1) (= (f61 f58 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f52 f15))) (=> (= (f51 ?v_0 (f20 (f21 f22 ?v0) ?v1)) f1) (=> (= (f51 ?v_0 ?v0) f1) (= (f51 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f61 f58 ?v0) f1) (=> (= (f61 ?v1 f58) f1) (= (f61 (f44 (f45 f46 ?v1) ?v0) f58) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f51 (f52 f15) ?v0) f1) (=> (= (f51 (f52 ?v1) f15) f1) (= (f51 (f52 (f20 (f21 f22 ?v1) ?v0)) f15) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f61 f58 ?v0) f1) (=> (= (f61 ?v1 f58) f1) (= (f61 (f44 (f45 f46 ?v0) ?v1) f58) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f51 (f52 f15) ?v0) f1) (=> (= (f51 (f52 ?v1) f15) f1) (= (f51 (f52 (f20 (f21 f22 ?v0) ?v1)) f15) f1)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f61 f58 ?v0) f1) (=> (= (f61 f58 ?v1) f1) (= (f61 f58 (f44 (f45 f46 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f52 f15))) (=> (= (f51 ?v_0 ?v0) f1) (=> (= (f51 ?v_0 ?v1) f1) (= (f51 ?v_0 (f20 (f21 f22 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f45 f46 ?v0))) (=> (= (f61 f58 ?v0) f1) (= (= (f61 (f44 ?v_0 ?v1) (f44 ?v_0 ?v2)) f1) (= (f61 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (let ((?v_0 (f45 f46 ?v0))) (= (= (f61 (f44 ?v_0 ?v1) (f44 ?v_0 ?v2)) f1) (or (and (= (f61 f58 ?v0) f1) (= (f61 ?v1 ?v2) f1)) (and (= (f61 ?v0 f58) f1) (= (f61 ?v2 ?v1) f1)))))))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S18)) (= (= (f61 (f44 (f45 f46 ?v0) ?v1) (f44 (f45 f46 ?v2) ?v1)) f1) (or (and (= (f61 f58 ?v1) f1) (= (f61 ?v0 ?v2) f1)) (and (= (f61 ?v1 f58) f1) (= (f61 ?v2 ?v0) f1))))))
(assert (forall ((?v0 S18)) (not (= (f61 (f44 (f45 f46 ?v0) ?v0) f58) f1))))
(assert (forall ((?v0 S18) (?v1 S2)) (=> (= (f61 f58 ?v0) f1) (= (f61 f58 (f32 (f41 f59 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f52 f15))) (=> (= (f51 ?v_0 ?v0) f1) (= (f51 ?v_0 (f20 (f21 f60 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2)) (not (= (f61 (f32 f35 ?v0) f58) f1))))
(assert (forall ((?v0 S2)) (not (= (f51 (f52 (f20 f31 ?v0)) f15) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f21 f22 ?v2))) (=> (= (f51 (f52 ?v0) ?v1) f1) (=> (= (f51 (f52 f15) ?v2) f1) (= (f51 (f52 (f20 ?v_0 ?v0)) (f20 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f51 (f52 ?v0) ?v1) f1) (=> (= (f51 (f52 f15) ?v2) f1) (= (f51 (f52 (f20 (f21 f22 ?v0) ?v2)) (f20 (f21 f22 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f51 (f52 (f20 (f21 f22 ?v0) ?v1)) (f20 (f21 f22 ?v2) ?v1)) f1) (and (= (f51 (f52 f15) ?v1) f1) (= (f51 (f52 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f21 f22 ?v0))) (= (= (f51 (f52 (f20 ?v_0 ?v1)) (f20 ?v_0 ?v2)) f1) (and (= (f51 (f52 f15) ?v0) f1) (= (f51 (f52 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f52 f15))) (= (= (f51 ?v_0 (f20 (f21 f22 ?v0) ?v1)) f1) (and (= (f51 ?v_0 ?v0) f1) (= (f51 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (not (= (f3 f19 ?v0) f53))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f51 (f52 f15) ?v0) f1) (=> (= (f51 (f52 ?v0) ?v1) f1) (= (f8 (f9 f10 (f17 f18 (f3 (f17 f18 (f3 f19 ?v1)) ?v0))) (f13 (f14 f15) ?v1)) f53)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f21 f22 ?v0))) (= (f20 (f21 f22 (f20 ?v_0 ?v1)) ?v2) (f20 ?v_0 (f20 (f21 f22 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f20 (f21 f22 ?v0) ?v1) (f20 (f21 f22 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f32 f35 ?v0) (f32 f35 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 f28 ?v0) (f3 f28 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f20 f31 ?v0) (f20 f31 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f21 f22 ?v0))) (=> (= (f51 (f52 f15) ?v0) f1) (= (f3 (f17 f18 (f3 f19 (f20 ?v_0 ?v1))) (f20 ?v_0 ?v2)) (f3 (f17 f18 (f3 f19 ?v1)) ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (= (f5 (f6 f24 ?v0) ?v1) f53) (or (= ?v0 f53) (= ?v1 f53)))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (= (f44 (f45 f46 ?v0) ?v1) f58) (or (= ?v0 f58) (= ?v1 f58)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f20 (f21 f22 ?v0) ?v1) f15) (or (= ?v0 f15) (= ?v1 f15)))))
(assert (forall ((?v0 S4) (?v1 S4)) (=> (not (= ?v0 f53)) (=> (not (= ?v1 f53)) (not (= (f5 (f6 f24 ?v0) ?v1) f53))))))
(assert (forall ((?v0 S18) (?v1 S18)) (=> (not (= ?v0 f58)) (=> (not (= ?v1 f58)) (not (= (f44 (f45 f46 ?v0) ?v1) f58))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 f15)) (=> (not (= ?v1 f15)) (not (= (f20 (f21 f22 ?v0) ?v1) f15))))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (= (f5 (f6 f24 ?v0) ?v1) f53) (or (= ?v0 f53) (= ?v1 f53)))))
(assert (forall ((?v0 S18) (?v1 S18)) (= (= (f44 (f45 f46 ?v0) ?v1) f58) (or (= ?v0 f58) (= ?v1 f58)))))
(assert (forall ((?v0 S4)) (= (f5 (f6 f24 ?v0) f53) f53)))
(assert (forall ((?v0 S18)) (= (f44 (f45 f46 ?v0) f58) f58)))
(assert (forall ((?v0 S2)) (= (f20 (f21 f22 ?v0) f15) f15)))
(assert (forall ((?v0 S4)) (= (f5 (f6 f24 f53) ?v0) f53)))
(assert (forall ((?v0 S18)) (= (f44 (f45 f46 f58) ?v0) f58)))
(assert (forall ((?v0 S2)) (= (f20 (f21 f22 f15) ?v0) f15)))
(assert (forall ((?v0 S4) (?v1 S2)) (=> (not (= ?v0 f53)) (not (= (f3 (f17 f18 ?v0) ?v1) f53)))))
(assert (forall ((?v0 S18) (?v1 S2)) (=> (not (= ?v0 f58)) (not (= (f32 (f41 f59 ?v0) ?v1) f58)))))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 ?v0) f53) f53)))
(assert (forall ((?v0 S4)) (= (f5 (f6 f7 f53) ?v0) f53)))
(assert (forall ((?v0 S18) (?v1 S18) (?v2 S2)) (= (f32 (f41 f59 (f44 (f45 f46 ?v0) ?v1)) ?v2) (f44 (f45 f46 (f32 (f41 f59 ?v0) ?v2)) (f32 (f41 f59 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f20 (f21 f60 (f20 (f21 f22 ?v0) ?v1)) ?v2) (f20 (f21 f22 (f20 (f21 f60 ?v0) ?v2)) (f20 (f21 f60 ?v1) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2)) (= (f3 (f17 f18 (f5 (f6 f24 ?v0) ?v1)) ?v2) (f5 (f6 f24 (f3 (f17 f18 ?v0) ?v2)) (f3 (f17 f18 ?v1) ?v2)))))
(assert (forall ((?v0 S18) (?v1 S2)) (let ((?v_0 (f32 (f41 f59 ?v0) ?v1))) (= (f44 (f45 f46 ?v_0) ?v0) (f44 (f45 f46 ?v0) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f20 (f21 f60 ?v0) ?v1))) (= (f20 (f21 f22 ?v_0) ?v0) (f20 (f21 f22 ?v0) ?v_0)))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f3 (f17 f18 ?v0) ?v1))) (= (f5 (f6 f24 ?v_0) ?v0) (f5 (f6 f24 ?v0) ?v_0)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (= (f5 (f6 f24 (f5 (f6 f7 ?v0) ?v1)) (f5 (f6 f7 ?v2) ?v3)) (f5 (f6 f7 (f5 (f6 f24 ?v0) ?v2)) (f5 (f6 f24 ?v1) ?v3)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (let ((?v_0 (f6 f24 ?v0))) (= (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f5 (f6 f7 (f5 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2)) (= (f3 (f17 f18 (f5 (f6 f7 ?v0) ?v1)) ?v2) (f5 (f6 f7 (f3 (f17 f18 ?v0) ?v2)) (f3 (f17 f18 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f20 (f21 f22 ?v0) ?v1) (f20 (f21 f22 ?v2) ?v1)) (or (= ?v0 ?v2) (= ?v1 f15)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f21 f22 ?v0))) (= (= (f20 ?v_0 ?v1) (f20 ?v_0 ?v2)) (or (= ?v1 ?v2) (= ?v0 f15))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f20 (f21 f22 ?v0) ?v1) f15) (or (= ?v0 f15) (= ?v1 f15)))))
(assert (forall ((?v0 S2)) (= (f20 (f21 f22 ?v0) f15) f15)))
(assert (forall ((?v0 S2)) (= (f20 (f21 f22 f15) ?v0) f15)))
(assert (forall ((?v0 S18) (?v1 S2) (?v2 S2)) (let ((?v_0 (f41 f59 ?v0))) (= (f32 ?v_0 (f20 (f21 f22 ?v1) ?v2)) (f32 (f41 f59 (f32 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f21 f60 ?v0))) (= (f20 ?v_0 (f20 (f21 f22 ?v1) ?v2)) (f20 (f21 f60 (f20 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f17 f18 ?v0))) (= (f3 ?v_0 (f20 (f21 f22 ?v1) ?v2)) (f3 (f17 f18 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f32 f35 (f20 (f21 f60 ?v0) ?v1)) (f32 (f41 f59 (f32 f35 ?v0)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f20 f31 (f20 (f21 f60 ?v0) ?v1)) (f20 (f21 f60 (f20 f31 ?v0)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f3 f28 (f20 (f21 f60 ?v0) ?v1)) (f3 (f17 f18 (f3 f28 ?v0)) ?v1))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (=> (not (= ?v0 f53)) (=> (= (f5 (f6 f24 ?v1) ?v0) ?v2) (= ?v1 (f5 (f6 f7 ?v2) ?v0))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4)) (=> (not (= ?v0 f53)) (=> (= ?v1 (f5 (f6 f24 ?v2) ?v0)) (= (f5 (f6 f7 ?v1) ?v0) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4)) (=> (not (= ?v0 f53)) (=> (not (= ?v1 f53)) (= (= (f5 (f6 f7 ?v2) ?v0) (f5 (f6 f7 ?v3) ?v1)) (= (f5 (f6 f24 ?v2) ?v1) (f5 (f6 f24 ?v3) ?v0)))))))
(assert (forall ((?v0 S2) (?v1 S8)) (= (forall ((?v2 S2)) (=> (= (f51 (f52 ?v2) ?v0) f1) (= (f51 ?v1 ?v2) f1))) (forall ((?v2 S2)) (=> (= (f62 ?v2 (f13 (f14 f15) ?v0)) f1) (= (f51 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S8)) (= (exists ((?v2 S2)) (and (= (f51 (f52 ?v2) ?v0) f1) (= (f51 ?v1 ?v2) f1))) (exists ((?v2 S2)) (and (= (f62 ?v2 (f13 (f14 f15) ?v0)) f1) (= (f51 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f21 f22 ?v0))) (=> (= (f51 (f52 f15) ?v0) f1) (= (= (f51 (f52 (f20 ?v_0 ?v1)) (f20 ?v_0 ?v2)) f1) (= (f51 (f52 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f21 f22 ?v0))) (=> (= (f51 (f52 f15) ?v0) f1) (= (= (f20 ?v_0 ?v1) (f20 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f51 (f52 f15) ?v0) f1) (=> (= (f51 (f52 ?v0) ?v1) f1) (= (f8 (f9 f10 (f17 f18 (f3 (f17 f18 (f5 (f6 f7 f63) (f3 f19 ?v1))) ?v0))) (f13 (f14 f15) ?v1)) f53)))))
(assert (forall ((?v0 S13) (?v1 S8)) (= (f32 f35 (f64 (f65 f66 ?v0) ?v1)) (f67 (f68 f69 (f33 f34 ?v0)) ?v1))))
(assert (forall ((?v0 S13) (?v1 S8)) (= (f3 f28 (f64 (f65 f66 ?v0) ?v1)) (f8 (f9 f10 (f26 f27 ?v0)) ?v1))))
(assert (forall ((?v0 S13) (?v1 S8)) (= (f20 f31 (f64 (f65 f66 ?v0) ?v1)) (f64 (f65 f66 (f29 f30 ?v0)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S4)) (= (f5 (f6 f7 (f8 (f9 f10 ?v0) ?v1)) ?v2) (f8 (f9 f10 (f17 (f36 f37 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S4)) (= (f5 (f6 f7 (f8 (f9 f10 ?v0) ?v1)) ?v2) (f8 (f9 f10 (f17 (f36 f37 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S4)) (= (f5 (f6 f24 (f8 (f9 f10 ?v0) ?v1)) ?v2) (f8 (f9 f10 (f17 (f36 f38 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S13) (?v1 S8) (?v2 S2)) (= (f20 (f21 f22 (f64 (f65 f66 ?v0) ?v1)) ?v2) (f64 (f65 f66 (f21 (f39 f40 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S4)) (= (f5 (f6 f24 (f8 (f9 f10 ?v0) ?v1)) ?v2) (f8 (f9 f10 (f17 (f36 f38 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S17) (?v1 S8) (?v2 S18)) (= (f44 (f45 f46 (f67 (f68 f69 ?v0) ?v1)) ?v2) (f67 (f68 f69 (f41 (f42 f43 ?v0) ?v2)) ?v1))))
(assert (forall ((?v0 S13) (?v1 S8)) (= (f32 f35 (f64 (f65 f66 ?v0) ?v1)) (f67 (f68 f69 (f33 f34 ?v0)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f32 f35 (f20 (f21 f60 ?v0) ?v1)) (f32 (f41 f59 (f32 f35 ?v0)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f32 (f41 f59 (f32 f35 ?v0)) ?v1) (f32 f35 (f20 (f21 f60 ?v0) ?v1)))))
(assert (= (f20 f31 f70) f70))
(assert (= (f3 f28 f70) f63))
(assert (= (f32 f35 f70) f71))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f61 (f32 f35 ?v0) (f32 f35 ?v1)) f1) (= (f51 (f52 ?v0) ?v1) f1))))
(assert (not (= f70 f15)))
(assert (not (= f63 f53)))
(assert (not (= f71 f58)))
(assert (not (= f15 f70)))
(assert (not (= f53 f63)))
(assert (not (= f58 f71)))
(check-sat)
(exit)
