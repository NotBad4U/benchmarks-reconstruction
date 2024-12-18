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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S3) S3)
(declare-fun f5 (S2) S4)
(declare-fun f6 (S2 S3) S1)
(declare-fun f7 (S6 S5) S1)
(declare-fun f8 (S7 S6) S6)
(declare-fun f9 (S5) S7)
(declare-fun f10 (S5 S6) S1)
(declare-fun f11 () S3)
(declare-fun f12 () S6)
(declare-fun f13 (S5) S7)
(declare-fun f14 (S2) S4)
(declare-fun f15 (S9 S3) S6)
(declare-fun f16 (S8) S9)
(declare-fun f17 (S8 S2) S5)
(declare-fun f18 (S13 S12) S6)
(declare-fun f19 (S10) S13)
(declare-fun f20 (S14 S12) S12)
(declare-fun f21 (S11) S14)
(declare-fun f22 (S10 S11) S5)
(declare-fun f23 (S16 S6) S3)
(declare-fun f24 (S15) S16)
(declare-fun f25 (S15 S5) S2)
(declare-fun f26 (S17) S4)
(declare-fun f27 (S17 S2) S2)
(declare-fun f28 (S18) S7)
(declare-fun f29 (S18 S5) S5)
(declare-fun f30 () S3)
(declare-fun f31 () S6)
(declare-fun f32 (S3 S3) S1)
(declare-fun f33 (S6 S6) S1)
(declare-fun f34 (S6 S6) S1)
(declare-fun f35 (S19 S6) S5)
(declare-fun f36 () S19)
(declare-fun f37 (S20 S3) S2)
(declare-fun f38 () S20)
(declare-fun f39 (S21) S1)
(declare-fun f40 () S3)
(declare-fun f41 () S8)
(declare-fun f42 (S22 S21) S5)
(declare-fun f43 () S22)
(declare-fun f44 (S6) S1)
(declare-fun f45 (S3) S1)
(declare-fun f46 (S6) S6)
(declare-fun f47 (S3) S3)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f6 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f7 (f8 (f9 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f10 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f11 ?v0) f1) false)))
(assert (forall ((?v0 S5)) (= (= (f7 f12 ?v0) f1) false)))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (=> (=> (not (= (f10 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f10 ?v0 (f8 (f13 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (=> (not (= (f6 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f6 ?v0 (f4 (f14 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S3)) (let ((?v_0 (f16 ?v0))) (= (f15 ?v_0 (f4 (f14 ?v1) ?v2)) (f8 (f13 (f17 ?v0 ?v1)) (f15 ?v_0 ?v2))))))
(assert (forall ((?v0 S10) (?v1 S11) (?v2 S12)) (let ((?v_0 (f19 ?v0))) (= (f18 ?v_0 (f20 (f21 ?v1) ?v2)) (f8 (f13 (f22 ?v0 ?v1)) (f18 ?v_0 ?v2))))))
(assert (forall ((?v0 S15) (?v1 S5) (?v2 S6)) (let ((?v_0 (f24 ?v0))) (= (f23 ?v_0 (f8 (f13 ?v1) ?v2)) (f4 (f14 (f25 ?v0 ?v1)) (f23 ?v_0 ?v2))))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S3)) (let ((?v_0 (f26 ?v0))) (= (f4 ?v_0 (f4 (f14 ?v1) ?v2)) (f4 (f14 (f27 ?v0 ?v1)) (f4 ?v_0 ?v2))))))
(assert (forall ((?v0 S18) (?v1 S5) (?v2 S6)) (let ((?v_0 (f28 ?v0))) (= (f8 ?v_0 (f8 (f13 ?v1) ?v2)) (f8 (f13 (f29 ?v0 ?v1)) (f8 ?v_0 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S6)) (=> (= (f10 ?v0 (f8 (f13 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f10 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f6 ?v0 (f4 (f14 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f6 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2)) (=> (= (f6 ?v0 f30) f1) false)))
(assert (forall ((?v0 S5)) (=> (= (f10 ?v0 f31) f1) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S2)) (=> (= (f6 ?v2 ?v0) f1) (= (f6 ?v2 ?v1) f1))) (= (f32 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (forall ((?v2 S5)) (=> (= (f10 ?v2 ?v0) f1) (= (f10 ?v2 ?v1) f1))) (= (f33 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f33 ?v0 ?v1) f1) (= (f34 ?v1 ?v0) f1))))
(assert (forall ((?v0 S5)) (= (f35 f36 (f8 (f13 ?v0) f31)) ?v0)))
(assert (forall ((?v0 S2)) (= (f37 f38 (f4 (f14 ?v0) f30)) ?v0)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S8)) (let ((?v_0 (f15 (f16 ?v2) ?v1))) (=> (= (f6 ?v0 ?v1) f1) (= (f8 (f13 (f17 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S18)) (let ((?v_0 (f8 (f28 ?v2) ?v1))) (=> (= (f10 ?v0 ?v1) f1) (= (f8 (f13 (f29 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S17)) (let ((?v_0 (f4 (f26 ?v2) ?v1))) (=> (= (f6 ?v0 ?v1) f1) (= (f4 (f14 (f27 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S15)) (let ((?v_0 (f23 (f24 ?v2) ?v1))) (=> (= (f10 ?v0 ?v1) f1) (= (f4 (f14 (f25 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f30) (not (= (f6 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S6) (?v1 S5)) (=> (= ?v0 f31) (not (= (f10 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S21) (?v1 S6)) (=> (= (f39 ?v0) f1) (=> (forall ((?v2 S2)) (=> (= (f6 ?v2 f40) f1) (= (f34 ?v1 (f8 (f13 (f17 f41 ?v2)) f31)) f1))) (= (f34 ?v1 (f8 (f13 (f42 f43 ?v0)) f31)) f1)))))
(assert (forall ((?v0 S6)) (= (= (f44 ?v0) f1) (or (= ?v0 f31) (exists ((?v1 S6) (?v2 S5)) (and (= ?v0 (f8 (f13 ?v2) ?v1)) (= (f44 ?v1) f1)))))))
(assert (forall ((?v0 S3)) (= (= (f45 ?v0) f1) (or (= ?v0 f30) (exists ((?v1 S3) (?v2 S2)) (and (= ?v0 (f4 (f14 ?v2) ?v1)) (= (f45 ?v1) f1)))))))
(assert (= f31 (f46 f12)))
(assert (= f30 (f47 f11)))
(assert (forall ((?v0 S5) (?v1 S6)) (= (f8 (f13 ?v0) ?v1) (f46 (f8 (f9 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f14 ?v0) ?v1) (f47 (f4 (f5 ?v0) ?v1)))))
(assert (not (forall ((?v0 S6) (?v1 S21)) (let ((?v_0 (f15 (f16 f41) f40))) (=> (= (f45 f40) f1) (=> (= (f39 ?v1) f1) (=> (= ?v0 ?v_0) (= (f34 ?v_0 (f8 (f13 (f42 f43 ?v1)) f31)) f1))))))))
(check-sat)
(exit)
