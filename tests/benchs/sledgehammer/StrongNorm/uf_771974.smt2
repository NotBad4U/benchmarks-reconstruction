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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 () S3)
(declare-fun f6 (S4 S2 S5) S1)
(declare-fun f7 (S7 S5) S4)
(declare-fun f8 (S8 S6) S7)
(declare-fun f9 (S9 S4) S8)
(declare-fun f10 () S9)
(declare-fun f11 () S5)
(declare-fun f12 (S10 S6) S2)
(declare-fun f13 (S11 S2) S10)
(declare-fun f14 (S12 S2) S11)
(declare-fun f15 () S12)
(declare-fun f16 () S3)
(declare-fun f17 (S13 S3) S3)
(declare-fun f18 (S3) S13)
(declare-fun f19 (S3 S14) S1)
(declare-fun f20 () S14)
(declare-fun f21 () S4)
(declare-fun f22 () S6)
(declare-fun f23 (S15 S14) S2)
(declare-fun f24 (S16 S2) S15)
(declare-fun f25 (S17 S18) S16)
(declare-fun f26 () S17)
(declare-fun f27 () S18)
(declare-fun f28 () S10)
(declare-fun f29 () S6)
(declare-fun f30 () S5)
(declare-fun f31 () S2)
(declare-fun f32 () S2)
(declare-fun f33 () S2)
(declare-fun f34 () S4)
(declare-fun f35 (S19 S5) S5)
(declare-fun f36 (S20 S5) S19)
(declare-fun f37 () S20)
(declare-fun f38 () S6)
(declare-fun f39 () S5)
(declare-fun f40 (S4 S6) S5)
(declare-fun f41 (S21 S2) S2)
(declare-fun f42 (S18 S2) S21)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (and (= (f3 f5 ?v0) f1) (forall ((?v1 S4) (?v2 S5) (?v3 S2) (?v4 S6)) (=> (= (f6 (f7 (f8 (f9 f10 ?v1) ?v4) f11) ?v0 ?v2) f1) (=> (= (f3 f5 ?v3) f1) (=> (= (f6 ?v1 ?v3 f11) f1) (= (f3 f5 (f12 (f13 (f14 f15 ?v0) ?v3) ?v4)) f1)))))))))
(assert (forall ((?v0 S2)) (= (= (f3 f16 ?v0) f1) (forall ((?v1 S4) (?v2 S5) (?v3 S2) (?v4 S6)) (=> (= (f6 (f7 (f8 (f9 f10 ?v1) ?v4) f11) ?v0 ?v2) f1) (=> (= (f3 f5 ?v3) f1) (=> (= (f6 ?v1 ?v3 f11) f1) (= (f3 f5 (f12 (f13 (f14 f15 ?v0) ?v3) ?v4)) f1))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (= (= (f3 (f17 (f18 ?v0) ?v1) ?v2) f1) (and (= (f3 ?v0 ?v2) f1) (= (f3 ?v1 ?v2) f1)))))
(assert (not (= (f19 f16 f20) f1)))
(assert (= (f19 f4 f20) f1))
(assert (= (f6 (f7 (f8 (f9 f10 f21) f22) f11) (f23 (f24 (f25 f26 f27) (f12 f28 f29)) f20) f30) f1))
(assert (= (f3 f5 f31) f1))
(assert (= (f6 f21 f31 f11) f1))
(assert (= (f3 f5 f31) f1))
(assert (= (f3 f5 f32) f1))
(assert (= (f3 f5 f33) f1))
(assert (= (f6 f21 f31 f11) f1))
(assert (= (f6 f34 f33 f11) f1))
(assert (= (f19 f4 f20) f1))
(assert (= (f6 (f7 (f8 (f9 f10 f21) f22) f11) (f23 (f24 (f25 f26 f27) (f12 f28 f29)) f20) f30) f1))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S2) (?v3 S4) (?v4 S6) (?v5 S5) (?v6 S2)) (=> (= f11 (f35 (f36 f37 ?v0) ?v1)) (=> (= (f3 f5 ?v2) f1) (=> (= (f6 (f7 (f8 (f9 f10 ?v3) ?v4) ?v0) ?v2 ?v5) f1) (=> (= (f3 f5 ?v6) f1) (=> (= (f6 ?v3 ?v6 ?v0) f1) (= (f3 f5 (f12 (f13 (f14 f15 ?v2) ?v6) ?v4)) f1))))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S2) (?v3 S4) (?v4 S6) (?v5 S5) (?v6 S2)) (=> (= f11 (f35 (f36 f37 ?v0) ?v1)) (=> (= (f3 f5 ?v2) f1) (=> (= (f6 (f7 (f8 (f9 f10 ?v3) ?v4) ?v1) ?v2 ?v5) f1) (=> (= (f3 f5 ?v6) f1) (=> (= (f6 ?v3 ?v6 ?v1) f1) (= (f3 f5 (f12 (f13 (f14 f15 ?v2) ?v6) ?v4)) f1))))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S5) (?v3 S4) (?v4 S2) (?v5 S5) (?v6 S6)) (=> (= (f6 ?v0 ?v1 ?v2) f1) (=> (= (f6 ?v3 ?v4 ?v5) f1) (=> (= ?v0 (f7 (f8 (f9 f10 ?v3) ?v6) ?v5)) (= (f6 ?v3 (f12 (f13 (f14 f15 ?v1) ?v4) ?v6) ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S6) (?v2 S6)) (=> (= (f3 f5 ?v0) f1) (= (f3 f5 (f12 (f13 (f14 f15 ?v0) (f12 f28 ?v1)) ?v2)) f1))))
(assert (= (f6 (f7 (f8 (f9 f10 f34) f38) f11) (f23 (f24 (f25 f26 f27) (f12 f28 f29)) f20) f39) f1))
(assert (forall ((?v0 S6)) (= (f3 f5 (f12 f28 ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S14)) (= (= (f19 (f17 (f18 ?v0) ?v1) ?v2) f1) (and (= (f19 ?v0 ?v2) f1) (= (f19 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S4) (?v3 S5)) (=> (= ?v0 ?v1) (= (f40 (f7 (f8 (f9 f10 ?v2) ?v0) ?v3) ?v1) ?v3))))
(assert (forall ((?v0 S4) (?v1 S6) (?v2 S5)) (=> (= (f40 ?v0 ?v1) ?v2) (= (f6 ?v0 (f12 f28 ?v1) ?v2) f1))))
(assert (forall ((?v0 S4) (?v1 S6) (?v2 S5)) (=> (= (f6 ?v0 (f12 f28 ?v1) ?v2) f1) (=> (=> (= (f40 ?v0 ?v1) ?v2) false) false))))
(assert (forall ((?v0 S2) (?v1 S6)) (=> (= (f3 f5 ?v0) f1) (= (f3 f5 (f41 (f42 f27 ?v0) (f12 f28 ?v1))) f1))))
(assert (not (= f29 f38)))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S5) (?v3 S5) (?v4 S2)) (=> (= (f6 ?v0 ?v1 (f35 (f36 f37 ?v2) ?v3)) f1) (=> (= (f6 ?v0 ?v4 ?v2) f1) (= (f6 ?v0 (f41 (f42 f27 ?v1) ?v4) ?v3) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (= (= (f35 (f36 f37 ?v0) ?v1) (f35 (f36 f37 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S4) (?v1 S6) (?v2 S14) (?v3 S5) (?v4 S5)) (let ((?v_0 (f23 (f24 (f25 f26 f27) (f12 f28 ?v1)) ?v2))) (=> (= (f6 ?v0 ?v_0 ?v3) f1) (=> (= (f6 ?v0 ?v_0 ?v4) f1) (= ?v3 ?v4))))))
(assert (forall ((?v0 S14) (?v1 S6)) (=> (= (f19 f5 ?v0) f1) (= (f3 f5 (f23 (f24 (f25 f26 f27) (f12 f28 ?v1)) ?v0)) f1))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2) (?v3 S5)) (=> (= (f6 ?v0 (f41 (f42 f27 ?v1) ?v2) ?v3) f1) (=> (forall ((?v4 S5)) (=> (= (f6 ?v0 ?v1 (f35 (f36 f37 ?v4) ?v3)) f1) (=> (= (f6 ?v0 ?v2 ?v4) f1) false))) false))))
(assert (forall ((?v0 S6) (?v1 S14) (?v2 S6) (?v3 S14)) (let ((?v_0 (f25 f26 f27))) (= (= (f23 (f24 ?v_0 (f12 f28 ?v0)) ?v1) (f23 (f24 ?v_0 (f12 f28 ?v2)) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3))))))
(assert (forall ((?v0 S6) (?v1 S2)) (= (f12 (f13 (f14 f15 (f12 f28 ?v0)) ?v1) ?v0) ?v1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S6)) (= (f12 (f13 (f14 f15 (f41 (f42 f27 ?v0) ?v1)) ?v2) ?v3) (f41 (f42 f27 (f12 (f13 (f14 f15 ?v0) ?v2) ?v3)) (f12 (f13 (f14 f15 ?v1) ?v2) ?v3)))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S2)) (not (= (f12 f28 ?v0) (f41 (f42 f27 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S6)) (not (= (f41 (f42 f27 ?v0) ?v1) (f12 f28 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S14) (?v2 S2)) (let ((?v_0 (f25 f26 f27))) (= (= (f23 (f24 ?v_0 ?v0) ?v1) (f23 (f24 ?v_0 ?v2) ?v1)) (= ?v0 ?v2)))))
(check-sat)
(exit)
