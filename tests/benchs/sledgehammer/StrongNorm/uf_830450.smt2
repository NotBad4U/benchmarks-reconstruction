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
(declare-fun f22 () S10)
(declare-fun f23 (S12 S13) S2)
(declare-fun f24 (S14 S2) S12)
(declare-fun f25 (S15 S16) S14)
(declare-fun f26 () S15)
(declare-fun f27 () S16)
(declare-fun f28 (S16 S2) S3)
(declare-fun f29 () S3)
(declare-fun f30 () S2)
(declare-fun f31 () S2)
(declare-fun f32 () S13)
(declare-fun f33 (S17 S5) S5)
(declare-fun f34 () S17)
(declare-fun f35 (S18 S13) S13)
(declare-fun f36 (S19 S3) S18)
(declare-fun f37 () S19)
(declare-fun f38 () S2)
(declare-fun f39 () S2)
(declare-fun f40 (S20 S2 S21) S1)
(declare-fun f41 (S22 S21) S20)
(declare-fun f42 (S23 S5) S22)
(declare-fun f43 (S24 S20) S23)
(declare-fun f44 () S24)
(declare-fun f45 () S20)
(declare-fun f46 () S21)
(declare-fun f47 () S21)
(declare-fun f48 () S20)
(declare-fun f49 () S5)
(declare-fun f50 () S21)
(declare-fun f51 (S25 S21) S21)
(declare-fun f52 (S26 S21) S25)
(declare-fun f53 () S26)
(declare-fun f54 (S20 S5) S21)
(declare-fun f55 (S27 S5) S1)
(declare-fun f56 (S20 S13 S28) S1)
(declare-fun f57 (S10 S13) S1)
(declare-fun f58 (S29 S28) S25)
(declare-fun f59 (S30 S26) S29)
(declare-fun f60 () S30)
(declare-fun f61 () S4)
(declare-fun f62 (S2) S10)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 (f6 (f7 f8 ?v0) f9) f10))))
(assert (forall ((?v0 S2)) (= (f3 f11 ?v0) (f5 (f6 f12 ?v0) f13))))
(assert (forall ((?v0 S5) (?v1 S2)) (= (f3 (f14 f15 ?v0) ?v1) (f5 (f6 f12 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2)) (= (f3 (f14 (f16 f17 ?v0) ?v1) ?v2) (f5 (f6 (f7 f8 ?v2) ?v0) ?v1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S2)) (= (= (f18 (f19 (f20 ?v0) ?v1) ?v2) f1) (and (= (f18 ?v0 ?v2) f1) (= (f18 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (f3 f21 ?v0) ?v0)))
(assert (not (= (f18 f22 (f5 (f6 (f7 f8 (f23 (f24 (f25 f26 f27) (f3 (f28 f27 (f3 f29 f30)) f31)) f32)) f9) f10)) f1)))
(assert (= (f18 f22 (f23 (f24 (f25 f26 f27) (f3 (f28 f27 (f3 f29 (f5 (f6 (f7 f8 f30) (f5 (f6 f12 f9) f13)) (f33 f34 f10)))) (f5 (f6 (f7 f8 f31) f9) f10))) (f35 (f36 f37 f4) f32))) f1))
(assert (= (f18 f22 f38) f1))
(assert (= (f18 f22 f39) f1))
(assert (= (f18 f22 f31) f1))
(assert (= (f18 f22 f9) f1))
(assert (= (f18 f22 (f23 (f24 (f25 f26 f27) (f5 (f6 (f7 f8 f30) f31) f13)) f32)) f1))
(assert (forall ((?v0 S2) (?v1 S5)) (=> (= (f18 f22 ?v0) f1) (= (f18 f22 (f5 (f6 f12 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S2)) (=> (= (f18 f22 ?v0) f1) (= (f18 f22 (f3 f29 ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S13)) (let ((?v_0 (f25 f26 f27))) (=> (= (f18 f22 (f23 (f24 ?v_0 (f5 (f6 (f7 f8 ?v0) ?v1) f13)) ?v2)) f1) (=> (= (f18 f22 ?v1) f1) (= (f18 f22 (f23 (f24 ?v_0 (f3 (f28 f27 (f3 f29 ?v0)) ?v1)) ?v2)) f1))))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S2) (?v3 S13)) (let ((?v_0 (f25 f26 f27))) (= (= (f23 (f24 ?v_0 (f3 f29 ?v0)) ?v1) (f23 (f24 ?v_0 (f3 f29 ?v2)) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (= (f18 f22 (f23 (f24 (f25 f26 f27) (f3 (f28 f27 (f3 f29 (f5 (f6 (f7 f8 f30) (f5 (f6 f12 f9) f13)) (f33 f34 f10)))) (f5 (f6 (f7 f8 f31) f9) f10))) (f35 (f36 f37 f4) f32))) f1))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S5)) (= (f5 (f6 (f7 f8 (f3 (f28 f27 ?v0) ?v1)) ?v2) ?v3) (f3 (f28 f27 (f5 (f6 (f7 f8 ?v0) ?v2) ?v3)) (f5 (f6 (f7 f8 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (not (= (f3 f29 ?v0) (f3 (f28 f27 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (not (= (f3 (f28 f27 ?v0) ?v1) (f3 f29 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S2)) (let ((?v_0 (f25 f26 f27))) (= (= (f23 (f24 ?v_0 ?v0) ?v1) (f23 (f24 ?v_0 ?v2) ?v1)) (= ?v0 ?v2)))))
(assert (= (f40 (f41 (f42 (f43 f44 f45) f10) f46) (f23 (f24 (f25 f26 f27) (f3 (f28 f27 (f3 f29 f30)) f31)) f32) f47) f1))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 f29 ?v0) (f3 f29 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f3 (f28 f27 ?v0) ?v1) (f3 (f28 f27 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (= (f40 f45 f9 f46) f1))
(assert (= (f40 f48 f39 f46) f1))
(assert (forall ((?v0 S20) (?v1 S5) (?v2 S21) (?v3 S2)) (=> (= (f40 (f41 (f42 (f43 f44 ?v0) ?v1) f46) f31 ?v2) f1) (=> (= (f18 f22 ?v3) f1) (=> (= (f40 ?v0 ?v3 f46) f1) (= (f18 f22 (f5 (f6 (f7 f8 f31) ?v3) ?v1)) f1))))))
(assert (forall ((?v0 S20) (?v1 S5) (?v2 S21) (?v3 S2)) (let ((?v_0 (f23 (f24 (f25 f26 f27) (f5 (f6 (f7 f8 f30) f31) f13)) f32))) (=> (= (f40 (f41 (f42 (f43 f44 ?v0) ?v1) f46) ?v_0 ?v2) f1) (=> (= (f18 f22 ?v3) f1) (=> (= (f40 ?v0 ?v3 f46) f1) (= (f18 f22 (f5 (f6 (f7 f8 ?v_0) ?v3) ?v1)) f1)))))))
(assert (= (f40 (f41 (f42 (f43 f44 f48) f49) f46) (f23 (f24 (f25 f26 f27) (f3 (f28 f27 (f3 f29 f30)) f31)) f32) f50) f1))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S5)) (let ((?v_0 (f25 f26 f27))) (= (f5 (f6 f12 (f23 (f24 ?v_0 ?v0) ?v1)) ?v2) (f23 (f24 ?v_0 (f5 (f6 f12 ?v0) ?v2)) (f35 (f36 f37 (f14 f15 ?v2)) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S2) (?v3 S5)) (let ((?v_0 (f25 f26 f27))) (= (f5 (f6 (f7 f8 (f23 (f24 ?v_0 ?v0) ?v1)) ?v2) ?v3) (f23 (f24 ?v_0 (f5 (f6 (f7 f8 ?v0) ?v2) ?v3)) (f35 (f36 f37 (f14 (f16 f17 ?v2) ?v3)) ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S5)) (= (f5 (f6 f12 (f3 (f28 f27 ?v0) ?v1)) ?v2) (f3 (f28 f27 (f5 (f6 f12 ?v0) ?v2)) (f5 (f6 f12 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S5) (?v2 S2)) (= (f5 (f6 (f7 f8 (f5 (f6 f12 ?v0) ?v1)) ?v2) ?v1) ?v0)))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S2) (?v3 S20) (?v4 S5) (?v5 S21) (?v6 S2)) (=> (= f46 (f51 (f52 f53 ?v0) ?v1)) (=> (= (f18 f22 ?v2) f1) (=> (= (f40 (f41 (f42 (f43 f44 ?v3) ?v4) ?v1) ?v2 ?v5) f1) (=> (= (f18 f22 ?v6) f1) (=> (= (f40 ?v3 ?v6 ?v1) f1) (= (f18 f22 (f5 (f6 (f7 f8 ?v2) ?v6) ?v4)) f1))))))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S2) (?v3 S20) (?v4 S5) (?v5 S21) (?v6 S2)) (=> (= f46 (f51 (f52 f53 ?v0) ?v1)) (=> (= (f18 f22 ?v2) f1) (=> (= (f40 (f41 (f42 (f43 f44 ?v3) ?v4) ?v0) ?v2 ?v5) f1) (=> (= (f18 f22 ?v6) f1) (=> (= (f40 ?v3 ?v6 ?v0) f1) (= (f18 f22 (f5 (f6 (f7 f8 ?v2) ?v6) ?v4)) f1))))))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S21) (?v3 S5) (?v4 S21)) (=> (= (f40 ?v0 ?v1 ?v2) f1) (= (f40 (f41 (f42 (f43 f44 ?v0) ?v3) ?v4) (f5 (f6 f12 ?v1) ?v3) ?v2) f1))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S21) (?v3 S20) (?v4 S2) (?v5 S21) (?v6 S5)) (=> (= (f40 ?v0 ?v1 ?v2) f1) (=> (= (f40 ?v3 ?v4 ?v5) f1) (=> (= ?v0 (f41 (f42 (f43 f44 ?v3) ?v6) ?v5)) (= (f40 ?v3 (f5 (f6 (f7 f8 ?v1) ?v4) ?v6) ?v2) f1))))))
(assert (forall ((?v0 S20) (?v1 S5) (?v2 S21) (?v3 S21)) (let ((?v_0 (f43 f44 ?v0))) (= (f41 (f42 (f43 f44 (f41 (f42 ?v_0 ?v1) ?v2)) f13) ?v3) (f41 (f42 (f43 f44 (f41 (f42 ?v_0 f13) ?v3)) (f33 f34 ?v1)) ?v2)))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S21)) (=> (= (f40 ?v0 (f3 f29 ?v1) ?v2) f1) (=> (forall ((?v3 S21) (?v4 S21)) (=> (= (f40 (f41 (f42 (f43 f44 ?v0) f13) ?v3) ?v1 ?v4) f1) false)) false))))
(assert (forall ((?v0 S5)) (not (= f13 (f33 f34 ?v0)))))
(assert (forall ((?v0 S5)) (not (= f13 (f33 f34 ?v0)))))
(assert (forall ((?v0 S5)) (not (= (f33 f34 ?v0) f13))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S21) (?v3 S21) (?v4 S2)) (=> (= (f40 ?v0 ?v1 (f51 (f52 f53 ?v2) ?v3)) f1) (=> (= (f40 ?v0 ?v4 ?v2) f1) (= (f40 ?v0 (f3 (f28 f27 ?v1) ?v4) ?v3) f1)))))
(assert (forall ((?v0 S20) (?v1 S21) (?v2 S2) (?v3 S21)) (=> (= (f40 (f41 (f42 (f43 f44 ?v0) f13) ?v1) ?v2 ?v3) f1) (= (f40 ?v0 (f3 f29 ?v2) (f51 (f52 f53 ?v1) ?v3)) f1))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S21) (?v3 S21)) (= (= (f51 (f52 f53 ?v0) ?v1) (f51 (f52 f53 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f33 f34 ?v0) (f33 f34 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f33 f34 ?v0) (f33 f34 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5)) (not (= (f33 f34 ?v0) ?v0))))
(assert (forall ((?v0 S5)) (not (= ?v0 (f33 f34 ?v0)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S20) (?v3 S21)) (=> (= ?v0 ?v1) (= (f54 (f41 (f42 (f43 f44 ?v2) ?v0) ?v3) ?v1) ?v3))))
(assert (forall ((?v0 S13)) (= (f35 (f36 f37 f21) ?v0) ?v0)))
(assert (forall ((?v0 S5)) (=> (= (f33 f34 ?v0) f13) false)))
(assert (forall ((?v0 S5)) (=> (= f13 (f33 f34 ?v0)) false)))
(assert (forall ((?v0 S5)) (not (= (f33 f34 ?v0) f13))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S21)) (=> (= (f40 ?v0 (f3 f29 ?v1) ?v2) f1) (=> (forall ((?v3 S21) (?v4 S21)) (=> (= ?v2 (f51 (f52 f53 ?v3) ?v4)) (=> (= (f40 (f41 (f42 (f43 f44 ?v0) f13) ?v3) ?v1 ?v4) f1) false))) false))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S2) (?v3 S21)) (=> (= (f40 ?v0 (f3 (f28 f27 ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S21)) (=> (= (f40 ?v0 ?v1 (f51 (f52 f53 ?v4) ?v3)) f1) (=> (= (f40 ?v0 ?v2 ?v4) f1) false))) false))))
(assert (forall ((?v0 S5)) (=> (=> (= ?v0 f13) false) (=> (forall ((?v1 S5)) (=> (= ?v0 (f33 f34 ?v1)) false)) false))))
(assert (forall ((?v0 S27) (?v1 S5)) (=> (= (f55 ?v0 ?v1) f1) (=> (forall ((?v2 S5)) (=> (= (f55 ?v0 (f33 f34 ?v2)) f1) (= (f55 ?v0 ?v2) f1))) (= (f55 ?v0 f13) f1)))))
(assert (forall ((?v0 S27) (?v1 S5)) (=> (= (f55 ?v0 f13) f1) (=> (forall ((?v2 S5)) (=> (= (f55 ?v0 ?v2) f1) (= (f55 ?v0 (f33 f34 ?v2)) f1))) (= (f55 ?v0 ?v1) f1)))))
(assert (forall ((?v0 S5)) (=> (not (= ?v0 f13)) (exists ((?v1 S5)) (= ?v0 (f33 f34 ?v1))))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S21) (?v3 S5) (?v4 S13) (?v5 S28)) (=> (= (f40 ?v0 ?v1 ?v2) f1) (=> (= (f56 (f41 (f42 (f43 f44 ?v0) ?v3) ?v2) ?v4 ?v5) f1) (= (f56 ?v0 (f35 (f36 f37 (f14 (f16 f17 ?v1) ?v3)) ?v4) ?v5) f1)))))
(assert (forall ((?v0 S13)) (=> (= (f57 f22 ?v0) f1) (= (f57 f22 (f35 (f36 f37 f11) ?v0)) f1))))
(assert (forall ((?v0 S20) (?v1 S13) (?v2 S28) (?v3 S5) (?v4 S21)) (=> (= (f56 ?v0 ?v1 ?v2) f1) (= (f56 (f41 (f42 (f43 f44 ?v0) ?v3) ?v4) (f35 (f36 f37 (f14 f15 ?v3)) ?v1) ?v2) f1))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S13)) (= (= (f57 (f19 (f20 ?v0) ?v1) ?v2) f1) (and (= (f57 ?v0 ?v2) f1) (= (f57 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S28) (?v3 S21) (?v4 S13)) (=> (= (f40 ?v0 ?v1 (f51 (f58 (f59 f60 f53) ?v2) ?v3)) f1) (=> (= (f56 ?v0 ?v4 ?v2) f1) (= (f40 ?v0 (f23 (f24 (f25 f26 f27) ?v1) ?v4) ?v3) f1)))))
(assert (forall ((?v0 S13) (?v1 S5)) (=> (= (f57 f22 ?v0) f1) (= (f18 f22 (f23 (f24 (f25 f26 f27) (f5 f61 ?v1)) ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f18 (f62 (f3 (f28 f27 (f3 f29 ?v0)) ?v1)) (f5 (f6 (f7 f8 ?v0) ?v1) f13)) f1)))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S13) (?v3 S21)) (=> (= (f40 ?v0 (f23 (f24 (f25 f26 f27) ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S28)) (=> (= (f40 ?v0 ?v1 (f51 (f58 (f59 f60 f53) ?v4) ?v3)) f1) (=> (= (f56 ?v0 ?v2 ?v4) f1) false))) false))))
(assert (forall ((?v0 S20) (?v1 S2) (?v2 S13) (?v3 S21)) (=> (= (f40 ?v0 (f23 (f24 (f25 f26 f27) ?v1) ?v2) ?v3) f1) (exists ((?v4 S28)) (and (= (f40 ?v0 ?v1 (f51 (f58 (f59 f60 f53) ?v4) ?v3)) f1) (= (f56 ?v0 ?v2 ?v4) f1))))))
(check-sat)
(exit)