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
(declare-fun f17 (S13 S2) S1)
(declare-fun f18 (S14 S13) S13)
(declare-fun f19 (S2) S14)
(declare-fun f20 () S11)
(declare-fun f21 () S13)
(declare-fun f22 (S2 S13) S1)
(declare-fun f23 (S4 S11) S1)
(declare-fun f24 (S15 S13) S11)
(declare-fun f25 (S3) S15)
(declare-fun f26 (S16 S17) S1)
(declare-fun f27 (S18 S16) S4)
(declare-fun f28 (S19 S17) S11)
(declare-fun f29 (S18) S19)
(declare-fun f30 (S20 S4) S2)
(declare-fun f31 (S21 S11) S13)
(declare-fun f32 (S20) S21)
(declare-fun f33 (S11 S11) S1)
(declare-fun f34 (S4) S12)
(declare-fun f35 (S13 S13) S1)
(declare-fun f36 (S2) S14)
(declare-fun f37 () S11)
(declare-fun f38 () S13)
(declare-fun f39 (S11) S11)
(declare-fun f40 (S13) S13)
(declare-fun f41 (S6) S8)
(declare-fun f42 (S9) S13)
(declare-fun f43 (S22 S4) S23)
(declare-fun f44 (S16) S23)
(declare-fun f45 (S22) S11)
(declare-fun f46 (S24 S16) S8)
(declare-fun f47 (S24) S17)
(declare-fun f48 (S25 S17) S17)
(declare-fun f49 (S16) S25)
(declare-fun f50 () S1)
(declare-fun f51 (S11) S1)
(declare-fun f52 (S11 S11) S1)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (f3 f4 ?v0) (f5 f6 (f7 f8 (f9 f10 ?v0))))))
(assert (forall ((?v0 S2)) (= (f3 f11 ?v0) (f5 f6 (f12 f13 ?v0)))))
(assert (forall ((?v0 S4) (?v1 S11) (?v2 S4)) (= (= (f14 (f15 (f16 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f14 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S2)) (= (= (f17 (f18 (f19 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f17 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S4)) (= (= (f14 f20 ?v0) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f17 f21 ?v0) f1) false)))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S4) (?v3 S3)) (=> (= (f22 ?v0 ?v1) f1) (=> (= ?v2 (f3 ?v3 ?v0)) (= (f23 ?v2 (f24 (f25 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S16) (?v1 S17) (?v2 S4) (?v3 S18)) (=> (= (f26 ?v0 ?v1) f1) (=> (= ?v2 (f27 ?v3 ?v0)) (= (f23 ?v2 (f28 (f29 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S11) (?v2 S2) (?v3 S20)) (=> (= (f23 ?v0 ?v1) f1) (=> (= ?v2 (f30 ?v3 ?v0)) (= (f22 ?v2 (f31 (f32 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S4) (?v1 S11) (?v2 S11)) (= (= (f33 (f15 (f34 ?v0) ?v1) ?v2) f1) (and (= (f23 ?v0 ?v2) f1) (= (f33 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S13) (?v2 S13)) (= (= (f35 (f18 (f36 ?v0) ?v1) ?v2) f1) (and (= (f22 ?v0 ?v2) f1) (= (f35 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S11)) (= (f33 f37 ?v0) f1)))
(assert (forall ((?v0 S13)) (= (f35 f38 ?v0) f1)))
(assert (forall ((?v0 S4) (?v1 S11)) (not (= (f15 (f34 ?v0) ?v1) f37))))
(assert (forall ((?v0 S2) (?v1 S13)) (not (= (f18 (f36 ?v0) ?v1) f38))))
(assert (forall ((?v0 S4) (?v1 S11)) (= (f15 (f34 ?v0) (f39 ?v1)) (f39 (f15 (f16 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S13)) (= (f18 (f36 ?v0) (f40 ?v1)) (f40 (f18 (f19 ?v0) ?v1)))))
(assert (= f37 (f39 f20)))
(assert (= f38 (f40 f21)))
(assert (forall ((?v0 S11)) (= (= (f39 ?v0) f37) (forall ((?v1 S4)) (not (= (f14 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S13)) (= (= (f40 ?v0) f38) (forall ((?v1 S2)) (not (= (f17 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S4)) (= (= (f23 ?v0 f37) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f22 ?v0 f38) f1) false)))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S6)) (=> (= (f9 ?v0 ?v1) (f41 ?v2)) (= (f22 ?v1 (f42 ?v0)) f1))))
(assert (forall ((?v0 S22) (?v1 S4) (?v2 S16)) (=> (= (f43 ?v0 ?v1) (f44 ?v2)) (= (f23 ?v1 (f45 ?v0)) f1))))
(assert (forall ((?v0 S24) (?v1 S16) (?v2 S6)) (=> (= (f46 ?v0 ?v1) (f41 ?v2)) (= (f26 ?v1 (f47 ?v0)) f1))))
(assert (forall ((?v0 S9) (?v1 S2) (?v2 S6)) (let ((?v_0 (f42 ?v0))) (=> (= (f9 ?v0 ?v1) (f41 ?v2)) (= (f18 (f36 ?v1) ?v_0) ?v_0)))))
(assert (forall ((?v0 S22) (?v1 S4) (?v2 S16)) (let ((?v_0 (f45 ?v0))) (=> (= (f43 ?v0 ?v1) (f44 ?v2)) (= (f15 (f34 ?v1) ?v_0) ?v_0)))))
(assert (forall ((?v0 S24) (?v1 S16) (?v2 S6)) (let ((?v_0 (f47 ?v0))) (=> (= (f46 ?v0 ?v1) (f41 ?v2)) (= (f48 (f49 ?v1) ?v_0) ?v_0)))))
(assert (not (forall ((?v0 S11) (?v1 S2) (?v2 S6) (?v3 S2) (?v4 S6)) (let ((?v_0 (f42 f10))) (let ((?v_1 (f24 (f25 f11) ?v_0))) (=> (= f50 f1) (=> (= (f51 ?v0) f1) (=> (not (= (f23 (f5 f6 ?v2) ?v0) f1)) (=> (= (f33 ?v0 (f24 (f25 f4) ?v_0)) f1) (=> (= (f9 f10 ?v1) (f41 ?v2)) (=> (= (f52 ?v_1 ?v0) f1) (=> (= (f9 f10 ?v3) (f41 ?v4)) (= (f33 (f15 (f34 (f5 f6 (f12 f13 ?v3))) f37) ?v_1) f1)))))))))))))
(check-sat)
(exit)