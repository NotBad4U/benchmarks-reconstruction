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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S6) S4)
(declare-fun f6 () S5)
(declare-fun f7 (S7 S8) S6)
(declare-fun f8 () S7)
(declare-fun f9 (S9 S2) S8)
(declare-fun f10 () S9)
(declare-fun f11 () S3)
(declare-fun f12 (S10 S2) S6)
(declare-fun f13 () S10)
(declare-fun f14 (S11 S4) S1)
(declare-fun f15 (S12 S11) S11)
(declare-fun f16 (S4) S12)
(declare-fun f17 (S4 S11) S1)
(declare-fun f18 (S13 S2) S1)
(declare-fun f19 (S14 S13) S13)
(declare-fun f20 (S2) S14)
(declare-fun f21 (S2 S13) S1)
(declare-fun f22 (S4) S12)
(declare-fun f23 (S2) S14)
(declare-fun f24 () S11)
(declare-fun f25 () S13)
(declare-fun f26 (S16 S4) S15)
(declare-fun f27 (S15 S17) S1)
(declare-fun f28 (S18 S11) S17)
(declare-fun f29 (S16) S18)
(declare-fun f30 (S19 S2) S15)
(declare-fun f31 (S20 S13) S17)
(declare-fun f32 (S19) S20)
(declare-fun f33 (S21 S15) S4)
(declare-fun f34 (S22 S17) S11)
(declare-fun f35 (S21) S22)
(declare-fun f36 (S23 S15) S2)
(declare-fun f37 (S24 S17) S13)
(declare-fun f38 (S23) S24)
(declare-fun f39 (S25 S13) S11)
(declare-fun f40 (S3) S25)
(declare-fun f41 () S11)
(declare-fun f42 () S13)
(declare-fun f43 (S2) S14)
(declare-fun f44 (S13) S13)
(declare-fun f45 (S4) S12)
(declare-fun f46 (S11) S11)
(declare-fun f47 (S11 S11) S1)
(declare-fun f48 (S11 S11) S1)
(declare-fun f49 (S13 S13) S1)
(declare-fun f50 (S26 S15) S8)
(declare-fun f51 (S6) S8)
(declare-fun f52 (S27 S17) S17)
(declare-fun f53 (S15) S27)
(declare-fun f54 (S26) S17)
(declare-fun f55 (S28 S4) S29)
(declare-fun f56 (S15) S29)
(declare-fun f57 (S28) S11)
(declare-fun f58 (S9) S13)
(declare-fun f59 () S1)
(declare-fun f60 (S11) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 f6 (f7 f8 (f9 f10 ?v0))))))
(assert (forall ((?v0 S2)) (= (f3 f11 ?v0) (f5 f6 (f12 f13 ?v0)))))
(assert (forall ((?v0 S4) (?v1 S11) (?v2 S4)) (= (= (f14 (f15 (f16 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f17 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S2)) (= (= (f18 (f19 (f20 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f21 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S4) (?v1 S11) (?v2 S4)) (= (= (f14 (f15 (f22 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f14 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S2)) (= (= (f18 (f19 (f23 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f18 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S4)) (= (= (f14 f24 ?v0) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f18 f25 ?v0) f1) false)))
(assert (forall ((?v0 S4) (?v1 S11) (?v2 S15) (?v3 S16)) (=> (= (f17 ?v0 ?v1) f1) (=> (= ?v2 (f26 ?v3 ?v0)) (= (f27 ?v2 (f28 (f29 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S15) (?v3 S19)) (=> (= (f21 ?v0 ?v1) f1) (=> (= ?v2 (f30 ?v3 ?v0)) (= (f27 ?v2 (f31 (f32 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S15) (?v1 S17) (?v2 S4) (?v3 S21)) (=> (= (f27 ?v0 ?v1) f1) (=> (= ?v2 (f33 ?v3 ?v0)) (= (f17 ?v2 (f34 (f35 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S15) (?v1 S17) (?v2 S2) (?v3 S23)) (=> (= (f27 ?v0 ?v1) f1) (=> (= ?v2 (f36 ?v3 ?v0)) (= (f21 ?v2 (f37 (f38 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S4) (?v3 S3)) (=> (= (f21 ?v0 ?v1) f1) (=> (= ?v2 (f3 ?v3 ?v0)) (= (f17 ?v2 (f39 (f40 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S11)) (= (exists ((?v1 S4)) (and (= (f17 ?v1 f41) f1) (= (f14 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S13)) (= (exists ((?v1 S2)) (and (= (f21 ?v1 f42) f1) (= (f18 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S2) (?v1 S13)) (= (f19 (f43 ?v0) ?v1) (f44 (f19 (f20 ?v0) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S11)) (= (f15 (f45 ?v0) ?v1) (f46 (f15 (f16 ?v0) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f47 ?v0 ?v1) f1) (= (f48 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S13)) (= (= (f49 (f19 (f43 ?v0) ?v1) ?v2) f1) (and (= (f21 ?v0 ?v2) f1) (= (f49 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S4) (?v1 S11) (?v2 S11)) (= (= (f47 (f15 (f45 ?v0) ?v1) ?v2) f1) (and (= (f17 ?v0 ?v2) f1) (= (f47 ?v1 ?v2) f1)))))
(assert (= f42 (f44 f25)))
(assert (= f41 (f46 f24)))
(assert (forall ((?v0 S13)) (= (f49 f42 ?v0) f1)))
(assert (forall ((?v0 S11)) (= (f47 f41 ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S13)) (not (= (f19 (f43 ?v0) ?v1) f42))))
(assert (forall ((?v0 S4) (?v1 S11)) (not (= (f15 (f45 ?v0) ?v1) f41))))
(assert (forall ((?v0 S2) (?v1 S13)) (= (f19 (f43 ?v0) (f44 ?v1)) (f44 (f19 (f23 ?v0) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S11)) (= (f15 (f45 ?v0) (f46 ?v1)) (f46 (f15 (f22 ?v0) ?v1)))))
(assert (forall ((?v0 S13)) (= (= (f44 ?v0) f42) (forall ((?v1 S2)) (not (= (f18 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S11)) (= (= (f46 ?v0) f41) (forall ((?v1 S4)) (not (= (f14 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S4)) (= (= (f17 ?v0 f41) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f21 ?v0 f42) f1) false)))
(assert (forall ((?v0 S26) (?v1 S15) (?v2 S6)) (let ((?v_0 (f54 ?v0))) (=> (= (f50 ?v0 ?v1) (f51 ?v2)) (= (f52 (f53 ?v1) ?v_0) ?v_0)))))
(assert (forall ((?v0 S28) (?v1 S4) (?v2 S15)) (let ((?v_0 (f57 ?v0))) (=> (= (f55 ?v0 ?v1) (f56 ?v2)) (= (f15 (f45 ?v1) ?v_0) ?v_0)))))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S6)) (let ((?v_0 (f58 ?v0))) (=> (= (f9 ?v0 ?v1) (f51 ?v2)) (= (f19 (f43 ?v1) ?v_0) ?v_0)))))
(assert (not (forall ((?v0 S11) (?v1 S2) (?v2 S6)) (let ((?v_0 (f58 f10))) (=> (= f59 f1) (=> (= (f60 ?v0) f1) (=> (not (= (f17 (f5 f6 ?v2) ?v0) f1)) (=> (= (f47 ?v0 (f39 (f40 f4) ?v_0)) f1) (=> (= (f9 f10 ?v1) (f51 ?v2)) (=> (= (f48 (f39 (f40 f11) ?v_0) ?v0) f1) (forall ((?v3 S2)) (=> (= (f21 ?v3 ?v_0) f1) (= (f48 (f39 (f40 f11) ?v_0) (f15 (f45 (f5 f6 (f12 f13 ?v3))) f41)) f1)))))))))))))
(check-sat)
(exit)