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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S6) S4)
(declare-fun f6 (S7 S8) S5)
(declare-fun f7 (S9 S6) S7)
(declare-fun f8 () S9)
(declare-fun f9 () S6)
(declare-fun f10 (S10 S11) S8)
(declare-fun f11 () S10)
(declare-fun f12 (S2) S11)
(declare-fun f13 () S6)
(declare-fun f14 () S3)
(declare-fun f15 (S12 S2) S8)
(declare-fun f16 () S12)
(declare-fun f17 (S14 S13) S3)
(declare-fun f18 (S15 S13) S14)
(declare-fun f19 () S15)
(declare-fun f20 (S13 S2) S6)
(declare-fun f21 () S15)
(declare-fun f22 (S16 S4) S4)
(declare-fun f23 (S17 S4) S16)
(declare-fun f24 () S17)
(declare-fun f25 (S18 S4) S3)
(declare-fun f26 () S18)
(declare-fun f27 (S19 S4) S2)
(declare-fun f28 (S20 S2) S19)
(declare-fun f29 () S20)
(declare-fun f30 (S21 S2) S2)
(declare-fun f31 (S22 S2) S21)
(declare-fun f32 () S22)
(declare-fun f33 (S23 S4) S1)
(declare-fun f34 () S23)
(declare-fun f35 (S24 S2) S1)
(declare-fun f36 () S24)
(declare-fun f37 (S23 S23) S1)
(declare-fun f38 (S25 S23) S23)
(declare-fun f39 (S23) S25)
(declare-fun f40 () S23)
(declare-fun f41 (S26 S24) S23)
(declare-fun f42 (S3) S26)
(declare-fun f43 () S24)
(declare-fun f44 (S4) S25)
(declare-fun f45 () S2)
(declare-fun f46 () S23)
(declare-fun f47 (S2 S24) S1)
(declare-fun f48 (S29 S28) S1)
(declare-fun f49 (S6 S27) S29)
(declare-fun f50 () S24)
(declare-fun f51 (S30 S23) S24)
(declare-fun f52 (S19) S30)
(declare-fun f53 (S31 S24) S24)
(declare-fun f54 (S2) S31)
(declare-fun f55 (S21) S31)
(declare-fun f56 (S16) S25)
(declare-fun f57 (S4 S23) S1)
(declare-fun f58 (S24) S31)
(declare-fun f59 (S23) S23)
(declare-fun f60 (S24) S24)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 (f6 (f7 f8 f9) (f10 f11 (f12 ?v0))) f13))))
(assert (forall ((?v0 S2)) (= (f3 f14 ?v0) (f5 (f6 (f7 f8 f9) (f15 f16 ?v0)) f13))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S2)) (= (f3 (f17 (f18 f19 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f20 ?v0 ?v2)) (f10 f11 (f12 ?v2))) (f20 ?v1 ?v2)))))
(assert (forall ((?v0 S13) (?v1 S13) (?v2 S2)) (= (f3 (f17 (f18 f21 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 (f20 ?v0 ?v2)) (f15 f16 ?v2)) (f20 ?v1 ?v2)))))
(assert (forall ((?v0 S4) (?v1 S4)) (= (f22 (f23 f24 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S4) (?v1 S2)) (= (f3 (f25 f26 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S2) (?v1 S4)) (= (f27 (f28 f29 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f30 (f31 f32 ?v0) ?v1) ?v0)))
(assert (forall ((?v0 S4)) (= (= (f33 f34 ?v0) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f35 f36 ?v0) f1) false)))
(assert (not (= (f37 (f38 (f39 f40) (f41 (f42 f14) f43)) (f41 (f42 f4) f43)) f1)))
(assert (let ((?v_0 (f7 f8 f9))) (= (f37 (f38 (f44 (f5 (f6 ?v_0 (f15 f16 f45)) f13)) f40) (f38 (f44 (f5 (f6 ?v_0 (f10 f11 (f12 f45))) f13)) f46)) f1)))
(assert (forall ((?v0 S23)) (= (f37 ?v0 f46) f1)))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6) (?v3 S6) (?v4 S8) (?v5 S6)) (= (= (f5 (f6 (f7 f8 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S23)) (=> (= (f37 ?v0 ?v1) f1) (=> (= (f37 ?v2 ?v0) f1) (= (f37 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S23) (?v1 S4) (?v2 S23)) (let ((?v_0 (f44 ?v1))) (=> (= (f37 ?v0 (f38 ?v_0 f46)) f1) (=> (= (f37 ?v0 ?v2) f1) (= (f37 ?v0 (f38 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S23) (?v1 S13) (?v2 S13) (?v3 S24)) (let ((?v_0 (f41 (f42 (f17 (f18 f21 ?v1) ?v2)) ?v3))) (=> (= (f37 (f38 (f39 ?v0) ?v_0) (f41 (f42 (f17 (f18 f19 ?v1) ?v2)) ?v3)) f1) (= (f37 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S23) (?v1 S13) (?v2 S13) (?v3 S24) (?v4 S2)) (=> (= (f37 (f38 (f39 ?v0) (f41 (f42 (f17 (f18 f21 ?v1) ?v2)) ?v3)) (f41 (f42 (f17 (f18 f19 ?v1) ?v2)) ?v3)) f1) (=> (= (f47 ?v4 ?v3) f1) (= (f37 ?v0 (f38 (f44 (f5 (f6 (f7 f8 (f20 ?v1 ?v4)) (f15 f16 ?v4)) (f20 ?v2 ?v4))) f46)) f1)))))
(assert (forall ((?v0 S23) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6)) (let ((?v_0 (f6 (f7 f8 ?v1) ?v2))) (=> (= (f37 ?v0 (f38 (f44 (f5 ?v_0 ?v3)) f46)) f1) (=> (forall ((?v5 S27) (?v6 S28)) (=> (= (f48 (f49 ?v3 ?v5) ?v6) f1) (= (f48 (f49 ?v4 ?v5) ?v6) f1))) (= (f37 ?v0 (f38 (f44 (f5 ?v_0 ?v4)) f46)) f1))))))
(assert (forall ((?v0 S23) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6)) (=> (= (f37 ?v0 (f38 (f44 (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) f46)) f1) (=> (forall ((?v5 S27) (?v6 S28)) (=> (= (f48 (f49 ?v4 ?v5) ?v6) f1) (= (f48 (f49 ?v1 ?v5) ?v6) f1))) (= (f37 ?v0 (f38 (f44 (f5 (f6 (f7 f8 ?v4) ?v2) ?v3)) f46)) f1)))))
(assert (forall ((?v0 S4) (?v1 S24)) (= (f41 (f42 (f25 f26 ?v0)) ?v1) (ite (= ?v1 f50) f46 (f38 (f44 ?v0) f46)))))
(assert (forall ((?v0 S2) (?v1 S23)) (= (f51 (f52 (f28 f29 ?v0)) ?v1) (ite (= ?v1 f46) f50 (f53 (f54 ?v0) f50)))))
(assert (forall ((?v0 S2) (?v1 S24)) (= (f53 (f55 (f31 f32 ?v0)) ?v1) (ite (= ?v1 f50) f50 (f53 (f54 ?v0) f50)))))
(assert (forall ((?v0 S4) (?v1 S23)) (= (f38 (f56 (f23 f24 ?v0)) ?v1) (ite (= ?v1 f46) f46 (f38 (f44 ?v0) f46)))))
(assert (forall ((?v0 S2) (?v1 S24) (?v2 S4)) (=> (= (f47 ?v0 ?v1) f1) (= (f41 (f42 (f25 f26 ?v2)) ?v1) (f38 (f44 ?v2) f46)))))
(assert (forall ((?v0 S4) (?v1 S23) (?v2 S4)) (=> (= (f57 ?v0 ?v1) f1) (= (f38 (f56 (f23 f24 ?v2)) ?v1) (f38 (f44 ?v2) f46)))))
(assert (forall ((?v0 S2) (?v1 S24) (?v2 S2)) (=> (= (f47 ?v0 ?v1) f1) (= (f53 (f55 (f31 f32 ?v2)) ?v1) (f53 (f54 ?v2) f50)))))
(assert (forall ((?v0 S4) (?v1 S23) (?v2 S2)) (=> (= (f57 ?v0 ?v1) f1) (= (f51 (f52 (f28 f29 ?v2)) ?v1) (f53 (f54 ?v2) f50)))))
(assert (forall ((?v0 S4) (?v1 S23)) (let ((?v_0 (f44 ?v0))) (= (f38 ?v_0 ?v1) (f38 (f39 (f38 ?v_0 f46)) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S24)) (let ((?v_0 (f54 ?v0))) (= (f53 ?v_0 ?v1) (f53 (f58 (f53 ?v_0 f50)) ?v1)))))
(assert (forall ((?v0 S23) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6) (?v5 S6)) (=> (= (f37 ?v0 (f38 (f44 (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)) f46)) f1) (=> (forall ((?v6 S27) (?v7 S28)) (=> (= (f48 (f49 ?v4 ?v6) ?v7) f1) (forall ((?v8 S28)) (=> (forall ((?v9 S27)) (=> (= (f48 (f49 ?v1 ?v9) ?v7) f1) (= (f48 (f49 ?v3 ?v9) ?v8) f1))) (= (f48 (f49 ?v5 ?v6) ?v8) f1))))) (= (f37 ?v0 (f38 (f44 (f5 (f6 (f7 f8 ?v4) ?v2) ?v5)) f46)) f1)))))
(assert (forall ((?v0 S2) (?v1 S24) (?v2 S24)) (=> (= (f47 ?v0 (f53 (f58 ?v1) ?v2)) f1) (=> (=> (= (f47 ?v0 ?v1) f1) false) (=> (=> (= (f47 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S4) (?v1 S23) (?v2 S23)) (=> (= (f57 ?v0 (f38 (f39 ?v1) ?v2)) f1) (=> (=> (= (f57 ?v0 ?v1) f1) false) (=> (=> (= (f57 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S23) (?v1 S23) (?v2 S4)) (=> (= (f33 (f38 (f39 ?v0) ?v1) ?v2) f1) (=> (=> (= (f33 ?v0 ?v2) f1) false) (=> (=> (= (f33 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S24) (?v1 S24) (?v2 S2)) (=> (= (f35 (f53 (f58 ?v0) ?v1) ?v2) f1) (=> (=> (= (f35 ?v0 ?v2) f1) false) (=> (=> (= (f35 ?v1 ?v2) f1) false) false)))))
(assert (forall ((?v0 S23) (?v1 S4) (?v2 S23)) (=> (=> (not (= (f33 ?v0 ?v1) f1)) (= (f33 ?v2 ?v1) f1)) (= (f33 (f38 (f39 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S24) (?v1 S2) (?v2 S24)) (=> (=> (not (= (f35 ?v0 ?v1) f1)) (= (f35 ?v2 ?v1) f1)) (= (f35 (f53 (f58 ?v2) ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S24) (?v2 S24)) (=> (=> (not (= (f47 ?v0 ?v1) f1)) (= (f47 ?v0 ?v2) f1)) (= (f47 ?v0 (f53 (f58 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S23) (?v2 S23)) (=> (=> (not (= (f57 ?v0 ?v1) f1)) (= (f57 ?v0 ?v2) f1)) (= (f57 ?v0 (f38 (f39 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S4) (?v1 S3) (?v2 S2) (?v3 S24)) (=> (= ?v0 (f3 ?v1 ?v2)) (=> (= (f47 ?v2 ?v3) f1) (= (f57 ?v0 (f41 (f42 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S19) (?v2 S4) (?v3 S23)) (=> (= ?v0 (f27 ?v1 ?v2)) (=> (= (f57 ?v2 ?v3) f1) (= (f47 ?v0 (f51 (f52 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S21) (?v2 S2) (?v3 S24)) (=> (= ?v0 (f30 ?v1 ?v2)) (=> (= (f47 ?v2 ?v3) f1) (= (f47 ?v0 (f53 (f55 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S4) (?v1 S16) (?v2 S4) (?v3 S23)) (=> (= ?v0 (f22 ?v1 ?v2)) (=> (= (f57 ?v2 ?v3) f1) (= (f57 ?v0 (f38 (f56 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S23)) (=> (= (f57 ?v0 (f38 (f44 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f57 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S24)) (=> (= (f47 ?v0 (f53 (f54 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f47 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2)) (=> (= (f47 ?v0 f50) f1) false)))
(assert (forall ((?v0 S4)) (=> (= (f57 ?v0 f46) f1) false)))
(assert (forall ((?v0 S4) (?v1 S23) (?v2 S4)) (=> (=> (not (= (f57 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f57 ?v0 (f38 (f44 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S24) (?v2 S2)) (=> (=> (not (= (f47 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f47 ?v0 (f53 (f54 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S24) (?v1 S2)) (=> (= ?v0 f50) (not (= (f47 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S23) (?v1 S4)) (=> (= ?v0 f46) (not (= (f57 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S23)) (= (= (f59 ?v0) f46) (forall ((?v1 S4)) (not (= (f33 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S24)) (= (= (f60 ?v0) f50) (forall ((?v1 S2)) (not (= (f35 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f47 ?v0 f50) f1) false)))
(assert (forall ((?v0 S4)) (= (= (f57 ?v0 f46) f1) false)))
(assert (forall ((?v0 S23)) (= (= f46 (f59 ?v0)) (forall ((?v1 S4)) (not (= (f33 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S24)) (= (= f50 (f60 ?v0)) (forall ((?v1 S2)) (not (= (f35 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S24)) (= (forall ((?v1 S2)) (=> (= (f47 ?v1 f50) f1) (= (f35 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S23)) (= (forall ((?v1 S4)) (=> (= (f57 ?v1 f46) f1) (= (f33 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S24)) (= (exists ((?v1 S2)) (and (= (f47 ?v1 f50) f1) (= (f35 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S23)) (= (exists ((?v1 S4)) (and (= (f57 ?v1 f46) f1) (= (f33 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S24)) (= (exists ((?v1 S2)) (= (f47 ?v1 ?v0) f1)) (not (= ?v0 f50)))))
(assert (forall ((?v0 S23)) (= (exists ((?v1 S4)) (= (f57 ?v1 ?v0) f1)) (not (= ?v0 f46)))))
(assert (forall ((?v0 S24)) (= (forall ((?v1 S2)) (not (= (f47 ?v1 ?v0) f1))) (= ?v0 f50))))
(assert (forall ((?v0 S23)) (= (forall ((?v1 S4)) (not (= (f57 ?v1 ?v0) f1))) (= ?v0 f46))))
(assert (= f46 (f59 f34)))
(assert (= f50 (f60 f36)))
(assert (forall ((?v0 S2)) (= (= (f35 f50 ?v0) f1) (= (f47 ?v0 f50) f1))))
(assert (forall ((?v0 S4)) (= (= (f33 f46 ?v0) f1) (= (f57 ?v0 f46) f1))))
(assert (forall ((?v0 S4) (?v1 S23)) (=> (= (f57 ?v0 ?v1) f1) (= (f38 (f44 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S24)) (=> (= (f47 ?v0 ?v1) f1) (= (f53 (f54 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S4) (?v1 S23) (?v2 S4)) (=> (= (f57 ?v0 ?v1) f1) (= (f57 ?v0 (f38 (f44 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S24) (?v2 S2)) (=> (= (f47 ?v0 ?v1) f1) (= (f47 ?v0 (f53 (f54 ?v2) ?v1)) f1))))
(check-sat)
(exit)
