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
(declare-sort S34 0)
(declare-sort S35 0)
(declare-sort S36 0)
(declare-sort S37 0)
(declare-sort S38 0)
(declare-sort S39 0)
(declare-sort S40 0)
(declare-sort S41 0)
(declare-sort S42 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S4 S3) S1)
(declare-fun f4 (S5 S2) S4)
(declare-fun f5 () S5)
(declare-fun f6 () S5)
(declare-fun f7 (S6 S7) S3)
(declare-fun f8 (S8 S9) S6)
(declare-fun f9 (S10 S3) S8)
(declare-fun f10 () S10)
(declare-fun f11 (S11) S9)
(declare-fun f12 () S11)
(declare-fun f13 (S12 S3) S7)
(declare-fun f14 () S12)
(declare-fun f15 (S14 S13) S1)
(declare-fun f16 (S15 S13) S14)
(declare-fun f17 () S15)
(declare-fun f18 () S15)
(declare-fun f19 (S16 S14) S14)
(declare-fun f20 (S17 S13) S16)
(declare-fun f21 () S17)
(declare-fun f22 (S18 S3) S5)
(declare-fun f23 () S18)
(declare-fun f24 (S19 S2) S5)
(declare-fun f25 (S20 S5) S19)
(declare-fun f26 () S20)
(declare-fun f27 (S21 S5) S5)
(declare-fun f28 (S22 S5) S21)
(declare-fun f29 () S22)
(declare-fun f30 (S23 S1) S21)
(declare-fun f31 () S23)
(declare-fun f32 (S24 S5) S18)
(declare-fun f33 () S24)
(declare-fun f34 (S25 S11) S18)
(declare-fun f35 (S26 S5) S25)
(declare-fun f36 () S26)
(declare-fun f37 (S27 S11) S7)
(declare-fun f38 (S28 S3) S27)
(declare-fun f39 () S28)
(declare-fun f40 (S29 S12) S5)
(declare-fun f41 (S30 S3) S29)
(declare-fun f42 (S31 S11) S30)
(declare-fun f43 (S32 S5) S31)
(declare-fun f44 () S32)
(declare-fun f45 () S5)
(declare-fun f46 () S5)
(declare-fun f47 () S14)
(declare-fun f48 (S33 S14) S1)
(declare-fun f49 (S34 S14) S33)
(declare-fun f50 () S34)
(declare-fun f51 () S14)
(declare-fun f52 () S17)
(declare-fun f53 (S35 S5) S13)
(declare-fun f54 (S36 S37) S35)
(declare-fun f55 (S38 S5) S36)
(declare-fun f56 () S38)
(declare-fun f57 (S39 S37) S37)
(declare-fun f58 (S40 S12) S39)
(declare-fun f59 (S41 S11) S40)
(declare-fun f60 () S41)
(declare-fun f61 () S37)
(declare-fun f62 () S5)
(declare-fun f63 () S14)
(declare-fun f64 (S42 S13) S33)
(declare-fun f65 () S42)
(declare-fun f66 () S16)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (= (f3 (f4 f6 ?v0) (f7 (f8 (f9 f10 ?v1) (f11 f12)) (f13 f14 ?v1))) f1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f15 (f16 f17 ?v0) ?v1) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S13) (?v1 S13)) (= (= (f15 (f16 f18 ?v0) ?v1) f1) (= ?v1 ?v0))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S13)) (= (= (f15 (f19 (f20 f21 ?v0) ?v1) ?v2) f1) (and (= ?v0 ?v2) (= (f15 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (= (= (f3 (f4 (f22 f23 ?v0) ?v1) ?v2) f1) (= ?v2 ?v0))))
(assert (forall ((?v0 S5) (?v1 S2) (?v2 S2)) (= (f4 (f24 (f25 f26 ?v0) ?v1) ?v2) (f4 ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S2) (?v3 S3)) (= (= (f3 (f4 (f27 (f28 f29 ?v0) ?v1) ?v2) ?v3) f1) (or (= (f3 (f4 ?v0 ?v2) ?v3) f1) (= (f3 (f4 ?v1 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S1) (?v1 S5) (?v2 S2) (?v3 S3)) (= (= (f3 (f4 (f27 (f30 f31 ?v0) ?v1) ?v2) ?v3) f1) (and (= (f3 (f4 ?v1 ?v2) ?v3) f1) (= ?v0 f1)))))
(assert (forall ((?v0 S5) (?v1 S3) (?v2 S2) (?v3 S3)) (= (= (f3 (f4 (f22 (f32 f33 ?v0) ?v1) ?v2) ?v3) f1) (and (= ?v1 ?v3) (= (f3 (f4 ?v0 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S5) (?v1 S11) (?v2 S3) (?v3 S2) (?v4 S3)) (= (= (f3 (f4 (f22 (f34 (f35 f36 ?v0) ?v1) ?v2) ?v3) ?v4) f1) (= (f3 (f4 ?v0 ?v3) (f7 (f8 (f9 f10 ?v4) (f11 ?v1)) (f37 (f38 f39 ?v2) ?v1))) f1))))
(assert (forall ((?v0 S5) (?v1 S11) (?v2 S3) (?v3 S12) (?v4 S2) (?v5 S3)) (= (= (f3 (f4 (f40 (f41 (f42 (f43 f44 ?v0) ?v1) ?v2) ?v3) ?v4) ?v5) f1) (and (= ?v2 ?v5) (= (f3 (f4 ?v0 ?v4) (f7 (f8 (f9 f10 ?v5) (f11 ?v1)) (f13 ?v3 ?v5))) f1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f3 (f4 f45 ?v0) ?v1) f1) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f3 (f4 f46 ?v0) ?v1) f1) true)))
(assert (forall ((?v0 S13)) (= (= (f15 f47 ?v0) f1) false)))
(assert (not (= (f48 (f49 f50 f51) (f19 (f20 f52 (f53 (f54 (f55 f56 f5) (f57 (f58 (f59 f60 f12) f14) f61)) f62)) f63)) f1)))
(assert (= (f48 (f49 f50 f51) (f19 (f20 f52 (f53 (f54 (f55 f56 f6) f61) f62)) f63)) f1))
(assert (forall ((?v0 S7) (?v1 S2) (?v2 S3)) (let ((?v_0 (f4 f62 ?v1))) (=> (= (f3 ?v_0 ?v2) f1) (= (f3 ?v_0 (f7 (f8 (f9 f10 ?v2) (f11 f12)) ?v0)) f1)))))
(assert (forall ((?v0 S14)) (= (f48 (f49 f50 ?v0) f63) f1)))
(assert (forall ((?v0 S14) (?v1 S5) (?v2 S37)) (= (f48 (f49 f50 ?v0) (f19 (f20 f52 (f53 (f54 (f55 f56 ?v1) ?v2) f46)) f63)) f1)))
(assert (forall ((?v0 S14) (?v1 S37) (?v2 S5)) (= (f48 (f49 f50 ?v0) (f19 (f20 f52 (f53 (f54 (f55 f56 f45) ?v1) ?v2)) f63)) f1)))
(assert (forall ((?v0 S13)) (let ((?v_0 (f19 (f20 f52 ?v0) f63))) (= (f48 (f49 f50 ?v_0) ?v_0) f1))))
(assert (forall ((?v0 S5) (?v1 S37) (?v2 S5) (?v3 S5) (?v4 S37) (?v5 S5)) (= (= (f53 (f54 (f55 f56 ?v0) ?v1) ?v2) (f53 (f54 (f55 f56 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S14) (?v1 S14) (?v2 S14)) (let ((?v_0 (f49 f50 ?v2))) (=> (= (f48 (f49 f50 ?v0) ?v1) f1) (=> (= (f48 ?v_0 ?v0) f1) (= (f48 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S14) (?v1 S13) (?v2 S14)) (let ((?v_0 (f49 f50 ?v0)) (?v_1 (f20 f52 ?v1))) (=> (= (f48 ?v_0 (f19 ?v_1 f63)) f1) (=> (= (f48 ?v_0 ?v2) f1) (= (f48 ?v_0 (f19 ?v_1 ?v2)) f1))))))
(assert (forall ((?v0 S14) (?v1 S13) (?v2 S14)) (let ((?v_0 (f49 f50 ?v0)) (?v_1 (f20 f52 ?v1))) (=> (= (f48 ?v_0 (f19 ?v_1 ?v2)) f1) (and (= (f48 ?v_0 (f19 ?v_1 f63)) f1) (= (f48 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S14) (?v1 S5) (?v2 S37) (?v3 S5) (?v4 S5) (?v5 S5)) (let ((?v_0 (f49 f50 ?v0))) (=> (= (f48 ?v_0 (f19 (f20 f52 (f53 (f54 (f55 f56 ?v1) ?v2) ?v3)) f63)) f1) (=> (= (f48 ?v_0 (f19 (f20 f52 (f53 (f54 (f55 f56 ?v4) ?v2) ?v5)) f63)) f1) (= (f48 ?v_0 (f19 (f20 f52 (f53 (f54 (f55 f56 (f27 (f28 f29 ?v1) ?v4)) ?v2) (f27 (f28 f29 ?v3) ?v5))) f63)) f1))))))
(assert (forall ((?v0 S1) (?v1 S14) (?v2 S5) (?v3 S37) (?v4 S5)) (let ((?v_0 (f49 f50 ?v1))) (=> (=> (= ?v0 f1) (= (f48 ?v_0 (f19 (f20 f52 (f53 (f54 (f55 f56 ?v2) ?v3) ?v4)) f63)) f1)) (= (f48 ?v_0 (f19 (f20 f52 (f53 (f54 (f55 f56 (f27 (f30 f31 ?v0) ?v2)) ?v3) ?v4)) f63)) f1)))))
(assert (forall ((?v0 S14) (?v1 S5) (?v2 S37) (?v3 S5)) (=> (forall ((?v4 S3)) (= (f48 (f49 f50 ?v0) (f19 (f20 f52 (f53 (f54 (f55 f56 (f22 (f32 f33 ?v1) ?v4)) ?v2) ?v3)) f63)) f1)) (= (f48 (f49 f50 ?v0) (f19 (f20 f52 (f53 (f54 (f55 f56 ?v1) ?v2) ?v3)) f63)) f1))))
(assert (forall ((?v0 S5) (?v1 S14) (?v2 S37) (?v3 S5)) (=> (forall ((?v4 S2) (?v5 S3)) (=> (= (f3 (f4 ?v0 ?v4) ?v5) f1) (= (f48 (f49 f50 ?v1) (f19 (f20 f52 (f53 (f54 (f55 f56 (f22 f23 ?v5)) ?v2) (f24 (f25 f26 ?v3) ?v4))) f63)) f1))) (= (f48 (f49 f50 ?v1) (f19 (f20 f52 (f53 (f54 (f55 f56 ?v0) ?v2) ?v3)) f63)) f1))))
(assert (forall ((?v0 S14) (?v1 S5) (?v2 S37) (?v3 S5) (?v4 S5)) (let ((?v_0 (f49 f50 ?v0)) (?v_1 (f54 (f55 f56 ?v1) ?v2))) (=> (= (f48 ?v_0 (f19 (f20 f52 (f53 ?v_1 ?v3)) f63)) f1) (=> (forall ((?v5 S2) (?v6 S3)) (=> (= (f3 (f4 ?v3 ?v5) ?v6) f1) (= (f3 (f4 ?v4 ?v5) ?v6) f1))) (= (f48 ?v_0 (f19 (f20 f52 (f53 ?v_1 ?v4)) f63)) f1))))))
(assert (forall ((?v0 S14) (?v1 S5) (?v2 S37) (?v3 S5) (?v4 S5)) (let ((?v_0 (f49 f50 ?v0))) (=> (= (f48 ?v_0 (f19 (f20 f52 (f53 (f54 (f55 f56 ?v1) ?v2) ?v3)) f63)) f1) (=> (forall ((?v5 S2) (?v6 S3)) (=> (= (f3 (f4 ?v4 ?v5) ?v6) f1) (= (f3 (f4 ?v1 ?v5) ?v6) f1))) (= (f48 ?v_0 (f19 (f20 f52 (f53 (f54 (f55 f56 ?v4) ?v2) ?v3)) f63)) f1))))))
(assert (forall ((?v0 S14) (?v1 S5) (?v2 S37) (?v3 S5) (?v4 S11) (?v5 S3) (?v6 S12)) (let ((?v_0 (f49 f50 ?v0))) (=> (= (f48 ?v_0 (f19 (f20 f52 (f53 (f54 (f55 f56 ?v1) ?v2) (f22 (f34 (f35 f36 ?v3) ?v4) ?v5))) f63)) f1) (= (f48 ?v_0 (f19 (f20 f52 (f53 (f54 (f55 f56 (f40 (f41 (f42 (f43 f44 ?v1) ?v4) ?v5) ?v6)) (f57 (f58 (f59 f60 ?v4) ?v6) ?v2)) ?v3)) f63)) f1)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S14)) (let ((?v_0 (f64 f65 ?v0))) (=> (= (f48 ?v_0 (f19 (f20 f52 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f48 ?v_0 ?v2) f1) false) false))))))
(assert (forall ((?v0 S13) (?v1 S14) (?v2 S13)) (let ((?v_0 (f64 f65 ?v0))) (=> (=> (not (= (f48 ?v_0 ?v1) f1)) (= ?v0 ?v2)) (= (f48 ?v_0 (f19 (f20 f52 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S13)) (=> (= (f48 (f64 f65 ?v0) f63) f1) false)))
(assert (forall ((?v0 S14) (?v1 S5) (?v2 S37) (?v3 S5) (?v4 S5) (?v5 S5)) (let ((?v_0 (f49 f50 ?v0))) (=> (= (f48 ?v_0 (f19 (f20 f52 (f53 (f54 (f55 f56 ?v1) ?v2) ?v3)) f63)) f1) (=> (forall ((?v6 S2) (?v7 S3)) (=> (= (f3 (f4 ?v4 ?v6) ?v7) f1) (forall ((?v8 S3)) (=> (forall ((?v9 S2)) (=> (= (f3 (f4 ?v1 ?v9) ?v7) f1) (= (f3 (f4 ?v3 ?v9) ?v8) f1))) (= (f3 (f4 ?v5 ?v6) ?v8) f1))))) (= (f48 ?v_0 (f19 (f20 f52 (f53 (f54 (f55 f56 ?v4) ?v2) ?v5)) f63)) f1))))))
(assert (forall ((?v0 S13)) (= (f19 f66 (f16 f17 ?v0)) (f19 (f20 f52 ?v0) f63))))
(assert (forall ((?v0 S13)) (= (f19 f66 (f16 f18 ?v0)) (f19 (f20 f52 ?v0) f63))))
(assert (forall ((?v0 S13) (?v1 S14)) (= (f19 f66 (f19 (f20 f21 ?v0) ?v1)) (ite (= (f15 ?v1 ?v0) f1) (f19 (f20 f52 ?v0) f63) f63))))
(assert (forall ((?v0 S14) (?v1 S13)) (=> (= ?v0 f63) (not (= (f48 (f64 f65 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S14)) (= (= (f19 f66 ?v0) f63) (forall ((?v1 S13)) (not (= (f15 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S13)) (= (= (f48 (f64 f65 ?v0) f63) f1) false)))
(assert (forall ((?v0 S14)) (= (= f63 (f19 f66 ?v0)) (forall ((?v1 S13)) (not (= (f15 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S14)) (= (forall ((?v1 S13)) (=> (= (f48 (f64 f65 ?v1) f63) f1) (= (f15 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S14)) (= (exists ((?v1 S13)) (and (= (f48 (f64 f65 ?v1) f63) f1) (= (f15 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S14)) (= (exists ((?v1 S13)) (= (f48 (f64 f65 ?v1) ?v0) f1)) (not (= ?v0 f63)))))
(assert (forall ((?v0 S14)) (= (forall ((?v1 S13)) (not (= (f48 (f64 f65 ?v1) ?v0) f1))) (= ?v0 f63))))
(assert (= f63 (f19 f66 f47)))
(assert (forall ((?v0 S13) (?v1 S14)) (=> (= (f48 (f64 f65 ?v0) ?v1) f1) (= (f19 (f20 f52 ?v0) ?v1) ?v1))))
(check-sat)
(exit)