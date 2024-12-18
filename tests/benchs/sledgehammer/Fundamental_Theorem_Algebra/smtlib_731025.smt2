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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 () S3)
(declare-fun f6 (S4 S2) S3)
(declare-fun f7 () S4)
(declare-fun f8 () S2)
(declare-fun f9 () S2)
(declare-fun f10 (S5 S3) S1)
(declare-fun f11 (S6 S2) S5)
(declare-fun f12 () S6)
(declare-fun f13 (S7 S3) S3)
(declare-fun f14 () S7)
(declare-fun f15 () S2)
(declare-fun f16 () S4)
(declare-fun f17 (S8 S1) S1)
(declare-fun f18 (S9 S1) S8)
(declare-fun f19 () S9)
(declare-fun f20 (S10 S3) S5)
(declare-fun f21 () S10)
(declare-fun f22 (S11 S2) S2)
(declare-fun f23 (S12 S2) S11)
(declare-fun f24 () S12)
(declare-fun f25 () S12)
(declare-fun f26 () S9)
(declare-fun f27 () S10)
(declare-fun f28 (S13 S5) S1)
(declare-fun f29 (S14 S3) S13)
(declare-fun f30 () S14)
(declare-fun f31 (S15 S3) S7)
(declare-fun f32 () S15)
(declare-fun f33 () S3)
(declare-fun f34 (S16 S1) S2)
(declare-fun f35 (S17 S3) S2)
(declare-fun f36 () S1)
(declare-fun f37 () S5)
(declare-fun f38 () S15)
(declare-fun f39 (S18 S8) S8)
(declare-fun f40 (S19 S8) S18)
(declare-fun f41 () S19)
(declare-fun f42 () S19)
(declare-fun f43 (S20 S5) S5)
(declare-fun f44 (S21 S5) S20)
(declare-fun f45 () S21)
(declare-fun f46 () S21)
(declare-fun f47 (S22 S8) S1)
(declare-fun f48 (S23 S1) S22)
(declare-fun f49 () S23)
(declare-fun f50 (S24 S5) S13)
(declare-fun f51 () S24)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) true)))
(assert (not (exists ((?v0 S2)) (forall ((?v1 S2)) (= (exists ((?v2 S2)) (and (= (f3 f5 ?v2) f1) (= (f3 (f6 f7 ?v1) ?v2) f1))) (= (f3 (f6 f7 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S2)) (= (exists ((?v1 S2)) (and (= (f3 f5 ?v1) f1) (= (f3 (f6 f7 ?v0) ?v1) f1))) (= (f3 (f6 f7 ?v0) f8) f1))))
(assert (forall ((?v0 S2)) (= (exists ((?v1 S2)) (and (= (f3 f5 ?v1) f1) (= (f3 (f6 f7 ?v0) ?v1) f1))) (= (f3 (f6 f7 ?v0) f8) f1))))
(assert (exists ((?v0 S2)) (= (f3 f5 ?v0) f1)))
(assert (= (f3 f5 f9) f1))
(assert (exists ((?v0 S2)) (forall ((?v1 S2)) (=> (= (f3 f5 ?v1) f1) (= (f3 (f6 f7 ?v1) ?v0) f1)))))
(assert (exists ((?v0 S2)) (= (f10 (f11 f12 ?v0) (f13 f14 f5)) f1)))
(assert (forall ((?v0 S2)) (=> (= (f3 f5 ?v0) f1) (= (f3 (f6 f7 ?v0) f15) f1))))
(assert (=> (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f5 ?v0) f1) (=> (forall ((?v2 S2)) (=> (= (f3 f5 ?v2) f1) (= (f3 (f6 f7 ?v2) ?v1) f1))) false))) false))
(assert (forall ((?v0 S2)) (=> (= (f3 f5 ?v0) f1) (= (f3 (f6 f16 ?v0) f8) f1))))
(assert (= (f3 (f6 f7 f9) f15) f1))
(assert (forall ((?v0 S2)) (not (= (f3 (f6 f7 ?v0) ?v0) f1))))
(assert (forall ((?v0 S1)) (not (= (f17 (f18 f19 ?v0) ?v0) f1))))
(assert (forall ((?v0 S3)) (not (= (f10 (f20 f21 ?v0) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= ?v0 ?v1)) (or (= (f3 (f6 f7 ?v0) ?v1) f1) (= (f3 (f6 f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f6 f7 ?v0) ?v1) f1)) (or (= (f3 (f6 f7 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f6 f7 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f6 f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v0))) (= (= (f3 ?v_0 (f22 (f23 f24 ?v1) ?v2)) f1) (or (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v0))) (= (= (f3 ?v_0 (f22 (f23 f25 ?v1) ?v2)) f1) (and (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f3 (f6 f7 (f22 (f23 f24 ?v0) ?v1)) ?v2) f1) (and (= (f3 (f6 f7 ?v0) ?v2) f1) (= (f3 (f6 f7 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f3 (f6 f7 (f22 (f23 f25 ?v0) ?v1)) ?v2) f1) (or (= (f3 (f6 f7 ?v0) ?v2) f1) (= (f3 (f6 f7 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f6 f7 ?v0) ?v1) f1)) (= (not (= (f3 (f6 f7 ?v1) ?v0) f1)) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 (f6 f7 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f6 f7 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2)) (= (f3 (f6 f16 ?v0) ?v0) f1)))
(assert (forall ((?v0 S1)) (= (f17 (f18 f26 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3)) (= (f10 (f20 f27 ?v0) ?v0) f1)))
(assert (forall ((?v0 S2)) (=> (= (f3 f5 ?v0) f1) (= (f3 (f6 f16 ?v0) f15) f1))))
(assert (= (f3 (f6 f16 f8) f15) f1))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f10 (f20 f27 ?v0) ?v1) f1) (forall ((?v2 S2)) (= (f17 (f18 f26 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f6 f16 ?v0) ?v1) f1) (= (f3 (f6 f16 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 ?v1) (and (= (f3 (f6 f16 ?v0) ?v1) f1) (= (f3 (f6 f16 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (= ?v0 f1) (= ?v1 f1)) (and (= (f17 (f18 f26 ?v0) ?v1) f1) (= (f17 (f18 f26 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (and (= (f10 (f20 f27 ?v0) ?v1) f1) (= (f10 (f20 f27 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f16 ?v0))) (= (= (f3 ?v_0 (f22 (f23 f24 ?v1) ?v2)) f1) (or (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f3 (f6 f16 (f22 (f23 f25 ?v0) ?v1)) ?v2) f1) (or (= (f3 (f6 f16 ?v0) ?v2) f1) (= (f3 (f6 f16 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= ?v0 ?v1) (= (f3 (f6 f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (= ?v0 f1) (= ?v1 f1)) (= (f17 (f18 f26 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f10 (f20 f27 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (= (f17 (f18 f26 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (= (= (f3 (f6 f16 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (= (= (f17 (f18 f26 ?v1) ?v0) f1) (= (= ?v1 f1) (= ?v0 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (= (= (f10 (f20 f27 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f3 (f6 f16 ?v1) ?v2) f1) (= (f3 (f6 f16 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f17 (f18 f26 ?v1) ?v2) f1) (= (f17 (f18 f26 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= ?v0 ?v1) (=> (= (f10 (f20 f27 ?v1) ?v2) f1) (= (f10 (f20 f27 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f16 ?v2))) (=> (= ?v0 ?v1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f18 f26 ?v2))) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f17 ?v_0 ?v1) f1) (= (f17 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f20 f27 ?v2))) (=> (= ?v0 ?v1) (=> (= (f10 ?v_0 ?v1) f1) (= (f10 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f16 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f18 f26 ?v0))) (=> (= (f17 ?v_0 ?v1) f1) (=> (= (= ?v1 f1) (= ?v2 f1)) (= (f17 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f20 f27 ?v0))) (=> (= (f10 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f10 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f3 (f6 f16 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (=> (= (= ?v0 f1) (= ?v2 f1)) (= (f17 (f18 f26 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f10 (f20 f27 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (=> (= (f3 (f6 f16 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (=> (= (f17 (f18 f26 ?v1) ?v0) f1) (= (= ?v0 f1) (= ?v1 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (= (f10 (f20 f27 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f16 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f6 f16 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f18 f26 ?v0))) (=> (= (f17 ?v_0 ?v1) f1) (=> (= (f17 (f18 f26 ?v1) ?v2) f1) (= (f17 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f20 f27 ?v0))) (=> (= (f10 ?v_0 ?v1) f1) (=> (= (f10 (f20 f27 ?v1) ?v2) f1) (= (f10 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (=> (= (f3 (f6 f16 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (=> (= (f17 (f18 f26 ?v1) ?v0) f1) (= (= ?v1 f1) (= ?v0 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (= (f10 (f20 f27 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f16 ?v2))) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f18 f26 ?v2))) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (=> (= (f17 ?v_0 ?v0) f1) (= (f17 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f20 f27 ?v2))) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (= (f10 ?v_0 ?v0) f1) (= (f10 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (=> (= (f17 (f18 f26 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f3 (f6 f16 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f6 f16 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v2))) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f18 f19 ?v2))) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (=> (= (f17 ?v_0 ?v0) f1) (= (f17 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f20 f21 ?v2))) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (= (f10 ?v_0 ?v0) f1) (= (f10 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (=> (= (f3 (f6 f7 ?v1) ?v2) f1) (= (f3 (f6 f7 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (=> (= (f17 (f18 f19 ?v1) ?v2) f1) (= (f17 (f18 f19 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (= (f10 (f20 f21 ?v1) ?v2) f1) (= (f10 (f20 f21 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (=> (= (f3 (f6 f16 ?v2) ?v0) f1) (= (f3 (f6 f7 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (=> (= (f17 (f18 f26 ?v2) ?v0) f1) (= (f17 (f18 f19 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (=> (= (f10 (f20 f27 ?v2) ?v0) f1) (= (f10 (f20 f21 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f6 f16 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f18 f19 ?v0))) (=> (= (f17 ?v_0 ?v1) f1) (=> (= (f17 (f18 f26 ?v1) ?v2) f1) (= (f17 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f20 f21 ?v0))) (=> (= (f10 ?v_0 ?v1) f1) (=> (= (f10 (f20 f27 ?v1) ?v2) f1) (= (f10 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (=> (not (= ?v1 ?v0)) (= (f3 (f6 f7 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (=> (not (= (= ?v1 f1) (= ?v0 f1))) (= (f17 (f18 f19 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (not (= ?v1 ?v0)) (= (f10 (f20 f21 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f3 (f6 f7 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (=> (not (= (= ?v0 f1) (= ?v1 f1))) (= (f17 (f18 f19 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f10 (f20 f21 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (or (= (f3 (f6 f7 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (or (= (f17 (f18 f19 ?v0) ?v1) f1) (= (= ?v0 f1) (= ?v1 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (or (= (f10 (f20 f21 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (= (not (= (f3 (f6 f7 ?v0) ?v1) f1)) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (= (f3 (f6 f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (= (f17 (f18 f26 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (= (f10 (f20 f27 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (not (= (f3 (f6 f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (= (f3 (f6 f16 ?v1) ?v0) f1) (= (f3 (f6 f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (not (= (= ?v0 f1) (= ?v1 f1))) (=> (= (f17 (f18 f26 ?v1) ?v0) f1) (= (f17 (f18 f19 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 ?v1)) (=> (= (f10 (f20 f27 ?v1) ?v0) f1) (= (f10 (f20 f21 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (= (f3 (f6 f7 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (not (= (= ?v0 f1) (= ?v1 f1))) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (= (f17 (f18 f19 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 ?v1)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (= (f10 (f20 f21 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f6 f7 ?v0) ?v1) f1)) (= (= (f3 (f6 f16 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f6 f16 ?v0) ?v1) f1)) (= (f3 (f6 f7 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f3 (f6 f7 ?v0) ?v1) f1)) (= (f3 (f6 f16 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f6 f16 ?v0) ?v1) f1) (or (= (f3 (f6 f7 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f17 (f18 f26 ?v0) ?v1) f1) (or (= (f17 (f18 f19 ?v0) ?v1) f1) (= (= ?v0 f1) (= ?v1 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f10 (f20 f27 ?v0) ?v1) f1) (or (= (f10 (f20 f21 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f6 f7 ?v0) ?v1) f1) (and (= (f3 (f6 f16 ?v0) ?v1) f1) (not (= (f3 (f6 f16 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f17 (f18 f19 ?v0) ?v1) f1) (and (= (f17 (f18 f26 ?v0) ?v1) f1) (not (= (f17 (f18 f26 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f10 (f20 f21 ?v0) ?v1) f1) (and (= (f10 (f20 f27 ?v0) ?v1) f1) (not (= (f10 (f20 f27 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 (f6 f7 ?v0) ?v1) f1) (and (= (f3 (f6 f16 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S1) (?v1 S1)) (= (= (f17 (f18 f19 ?v0) ?v1) f1) (and (= (f17 (f18 f26 ?v0) ?v1) f1) (not (= (= ?v0 f1) (= ?v1 f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f10 (f20 f21 ?v0) ?v1) f1) (and (= (f10 (f20 f27 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 (f6 f16 ?v0) ?v1) f1) (= (f3 (f6 f7 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f6 f16 ?v0) ?v1) f1)) (= (f3 (f6 f7 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= (f3 (f6 f7 ?v0) ?v1) f1)) (= (f3 (f6 f16 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f3 (f6 f7 ?v0) ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f3 (f6 f7 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (=> (=> (not false) (= (f3 (f6 f7 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (=> (=> (not false) (= (f17 (f18 f19 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (=> (=> (not false) (= (f10 (f20 f21 ?v1) ?v0) f1)) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v2))) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f18 f19 ?v2))) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (=> (= (f17 ?v_0 ?v0) f1) (= (f17 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f20 f21 ?v2))) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (=> (= (f10 ?v_0 ?v0) f1) (= (f10 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f6 f7 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f18 f19 ?v0))) (=> (= (f17 ?v_0 ?v1) f1) (=> (= (f17 (f18 f19 ?v1) ?v2) f1) (= (f17 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f20 f21 ?v0))) (=> (= (f10 ?v_0 ?v1) f1) (=> (= (f10 (f20 f21 ?v1) ?v2) f1) (= (f10 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f3 (f6 f7 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (=> (= (= ?v0 f1) (= ?v2 f1)) (= (f17 (f18 f19 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f10 (f20 f21 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f18 f19 ?v0))) (=> (= (f17 ?v_0 ?v1) f1) (=> (= (= ?v1 f1) (= ?v2 f1)) (= (f17 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f20 f21 ?v0))) (=> (= (f10 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f10 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v2))) (=> (= ?v0 ?v1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (let ((?v_0 (f18 f19 ?v2))) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f17 ?v_0 ?v1) f1) (= (f17 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f20 f21 ?v2))) (=> (= ?v0 ?v1) (=> (= (f10 ?v_0 ?v1) f1) (= (f10 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f3 (f6 f7 ?v1) ?v2) f1) (= (f3 (f6 f7 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (= ?v0 f1) (= ?v1 f1)) (=> (= (f17 (f18 f19 ?v1) ?v2) f1) (= (f17 (f18 f19 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= ?v0 ?v1) (=> (= (f10 (f20 f21 ?v1) ?v2) f1) (= (f10 (f20 f21 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (=> (= (f3 (f6 f7 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (=> (= (f17 (f18 f19 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (=> (= (f10 (f20 f21 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (=> (= (f3 (f6 f7 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (=> (= (f17 (f18 f19 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (=> (= (f10 (f20 f21 ?v1) ?v0) f1) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S1)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (= (=> (= (f3 (f6 f7 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S1)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (= (=> (= (f17 (f18 f19 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S1)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (= (=> (= (f10 (f20 f21 ?v1) ?v0) f1) (= ?v2 f1)) true))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (= (= (= ?v1 f1) (= ?v0 f1)) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (= (= ?v1 ?v0) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (= (= (= ?v0 f1) (= ?v1 f1)) false))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (= (= ?v0 ?v1) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (= (not (= (f3 (f6 f7 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (= (not (= (f17 (f18 f19 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (= (not (= (f10 (f20 f21 ?v1) ?v0) f1)) true))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (= (f10 (f11 f12 ?v0) ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S5)) (= (= (f28 (f29 f30 ?v0) ?v1) f1) (= (f10 ?v1 ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f13 f14 ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (not (= (f3 (f6 f7 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (not (= (f17 (f18 f19 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (not (= (f10 (f20 f21 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S1) (?v1 S1)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (not (= (= ?v0 f1) (= ?v1 f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (= (f3 (f13 (f31 f32 f33) (f13 f14 f5)) f8) f1))
(assert (forall ((?v0 S16) (?v1 S1) (?v2 S2) (?v3 S1)) (=> (= (f3 (f6 f16 (f34 ?v0 ?v1)) ?v2) f1) (=> (= (f17 (f18 f19 ?v3) ?v1) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f17 (f18 f19 ?v5) ?v4) f1) (= (f3 (f6 f7 (f34 ?v0 ?v5)) (f34 ?v0 ?v4)) f1))) (= (f3 (f6 f7 (f34 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S17) (?v1 S3) (?v2 S2) (?v3 S3)) (=> (= (f3 (f6 f16 (f35 ?v0 ?v1)) ?v2) f1) (=> (= (f10 (f20 f21 ?v3) ?v1) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f10 (f20 f21 ?v5) ?v4) f1) (= (f3 (f6 f7 (f35 ?v0 ?v5)) (f35 ?v0 ?v4)) f1))) (= (f3 (f6 f7 (f35 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S1) (?v3 S2)) (=> (= (f17 (f18 f26 (f3 ?v0 ?v1)) ?v2) f1) (=> (= (f3 (f6 f7 ?v3) ?v1) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f7 ?v5) ?v4) f1) (= (f17 (f18 f19 (f3 ?v0 ?v5)) (f3 ?v0 ?v4)) f1))) (= (f17 (f18 f19 (f3 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S3) (?v3 S2)) (=> (= (f10 (f20 f27 (f6 ?v0 ?v1)) ?v2) f1) (=> (= (f3 (f6 f7 ?v3) ?v1) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f7 ?v5) ?v4) f1) (= (f10 (f20 f21 (f6 ?v0 ?v5)) (f6 ?v0 ?v4)) f1))) (= (f10 (f20 f21 (f6 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S16) (?v1 S1) (?v2 S2) (?v3 S1)) (=> (= (f3 (f6 f7 (f34 ?v0 ?v1)) ?v2) f1) (=> (= (f17 (f18 f26 ?v3) ?v1) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f17 (f18 f26 ?v5) ?v4) f1) (= (f3 (f6 f16 (f34 ?v0 ?v5)) (f34 ?v0 ?v4)) f1))) (= (f3 (f6 f7 (f34 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S17) (?v1 S3) (?v2 S2) (?v3 S3)) (=> (= (f3 (f6 f7 (f35 ?v0 ?v1)) ?v2) f1) (=> (= (f10 (f20 f27 ?v3) ?v1) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f10 (f20 f27 ?v5) ?v4) f1) (= (f3 (f6 f16 (f35 ?v0 ?v5)) (f35 ?v0 ?v4)) f1))) (= (f3 (f6 f7 (f35 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S1) (?v3 S2)) (=> (= (f17 (f18 f19 (f3 ?v0 ?v1)) ?v2) f1) (=> (= (f3 (f6 f16 ?v3) ?v1) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f16 ?v5) ?v4) f1) (= (f17 (f18 f26 (f3 ?v0 ?v5)) (f3 ?v0 ?v4)) f1))) (= (f17 (f18 f19 (f3 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S3) (?v3 S2)) (=> (= (f10 (f20 f21 (f6 ?v0 ?v1)) ?v2) f1) (=> (= (f3 (f6 f16 ?v3) ?v1) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f16 ?v5) ?v4) f1) (= (f10 (f20 f27 (f6 ?v0 ?v5)) (f6 ?v0 ?v4)) f1))) (= (f10 (f20 f21 (f6 ?v0 ?v3)) ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S16) (?v2 S1) (?v3 S1)) (=> (= (f3 (f6 f16 ?v0) (f34 ?v1 ?v2)) f1) (=> (= (f17 (f18 f19 ?v2) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f17 (f18 f19 ?v4) ?v5) f1) (= (f3 (f6 f7 (f34 ?v1 ?v4)) (f34 ?v1 ?v5)) f1))) (= (f3 (f6 f7 ?v0) (f34 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S2) (?v1 S17) (?v2 S3) (?v3 S3)) (=> (= (f3 (f6 f16 ?v0) (f35 ?v1 ?v2)) f1) (=> (= (f10 (f20 f21 ?v2) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f10 (f20 f21 ?v4) ?v5) f1) (= (f3 (f6 f7 (f35 ?v1 ?v4)) (f35 ?v1 ?v5)) f1))) (= (f3 (f6 f7 ?v0) (f35 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S1) (?v1 S3) (?v2 S2) (?v3 S2)) (=> (= (f17 (f18 f26 ?v0) (f3 ?v1 ?v2)) f1) (=> (= (f3 (f6 f7 ?v2) ?v3) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f7 ?v4) ?v5) f1) (= (f17 (f18 f19 (f3 ?v1 ?v4)) (f3 ?v1 ?v5)) f1))) (= (f17 (f18 f19 ?v0) (f3 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S2) (?v3 S2)) (=> (= (f10 (f20 f27 ?v0) (f6 ?v1 ?v2)) f1) (=> (= (f3 (f6 f7 ?v2) ?v3) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f7 ?v4) ?v5) f1) (= (f10 (f20 f21 (f6 ?v1 ?v4)) (f6 ?v1 ?v5)) f1))) (= (f10 (f20 f21 ?v0) (f6 ?v1 ?v3)) f1))))))
(assert (forall ((?v0 S2) (?v1 S16) (?v2 S1) (?v3 S1)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f3 ?v_0 (f34 ?v1 ?v2)) f1) (=> (= (f17 (f18 f26 ?v2) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f17 (f18 f26 ?v4) ?v5) f1) (= (f3 (f6 f16 (f34 ?v1 ?v4)) (f34 ?v1 ?v5)) f1))) (= (f3 ?v_0 (f34 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S17) (?v2 S3) (?v3 S3)) (let ((?v_0 (f6 f7 ?v0))) (=> (= (f3 ?v_0 (f35 ?v1 ?v2)) f1) (=> (= (f10 (f20 f27 ?v2) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f10 (f20 f27 ?v4) ?v5) f1) (= (f3 (f6 f16 (f35 ?v1 ?v4)) (f35 ?v1 ?v5)) f1))) (= (f3 ?v_0 (f35 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S1) (?v1 S3) (?v2 S2) (?v3 S2)) (let ((?v_0 (f18 f19 ?v0))) (=> (= (f17 ?v_0 (f3 ?v1 ?v2)) f1) (=> (= (f3 (f6 f16 ?v2) ?v3) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f16 ?v4) ?v5) f1) (= (f17 (f18 f26 (f3 ?v1 ?v4)) (f3 ?v1 ?v5)) f1))) (= (f17 ?v_0 (f3 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S4) (?v2 S2) (?v3 S2)) (let ((?v_0 (f20 f21 ?v0))) (=> (= (f10 ?v_0 (f6 ?v1 ?v2)) f1) (=> (= (f3 (f6 f16 ?v2) ?v3) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f16 ?v4) ?v5) f1) (= (f10 (f20 f27 (f6 ?v1 ?v4)) (f6 ?v1 ?v5)) f1))) (= (f10 ?v_0 (f6 ?v1 ?v3)) f1)))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S16) (?v3 S2)) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (=> (= (f3 (f6 f7 (f34 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f17 (f18 f26 ?v4) ?v5) f1) (= (f3 (f6 f16 (f34 ?v2 ?v4)) (f34 ?v2 ?v5)) f1))) (= (f3 (f6 f7 (f34 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S17) (?v3 S2)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (= (f3 (f6 f7 (f35 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f10 (f20 f27 ?v4) ?v5) f1) (= (f3 (f6 f16 (f35 ?v2 ?v4)) (f35 ?v2 ?v5)) f1))) (= (f3 (f6 f7 (f35 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S1)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (=> (= (f17 (f18 f19 (f3 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f16 ?v4) ?v5) f1) (= (f17 (f18 f26 (f3 ?v2 ?v4)) (f3 ?v2 ?v5)) f1))) (= (f17 (f18 f19 (f3 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S4) (?v3 S3)) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (=> (= (f10 (f20 f21 (f6 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f16 ?v4) ?v5) f1) (= (f10 (f20 f27 (f6 ?v2 ?v4)) (f6 ?v2 ?v5)) f1))) (= (f10 (f20 f21 (f6 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S16) (?v3 S2)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (=> (= (f3 (f6 f16 (f34 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f17 (f18 f19 ?v4) ?v5) f1) (= (f3 (f6 f7 (f34 ?v2 ?v4)) (f34 ?v2 ?v5)) f1))) (= (f3 (f6 f7 (f34 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S17) (?v3 S2)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (=> (= (f3 (f6 f16 (f35 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f10 (f20 f21 ?v4) ?v5) f1) (= (f3 (f6 f7 (f35 ?v2 ?v4)) (f35 ?v2 ?v5)) f1))) (= (f3 (f6 f7 (f35 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S1)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (=> (= (f17 (f18 f26 (f3 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f7 ?v4) ?v5) f1) (= (f17 (f18 f19 (f3 ?v2 ?v4)) (f3 ?v2 ?v5)) f1))) (= (f17 (f18 f19 (f3 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S4) (?v3 S3)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (=> (= (f10 (f20 f27 (f6 ?v2 ?v1)) ?v3) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f7 ?v4) ?v5) f1) (= (f10 (f20 f21 (f6 ?v2 ?v4)) (f6 ?v2 ?v5)) f1))) (= (f10 (f20 f21 (f6 ?v2 ?v0)) ?v3) f1))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S2) (?v3 S16)) (let ((?v_0 (f6 f7 ?v2))) (=> (= (f17 (f18 f26 ?v0) ?v1) f1) (=> (= (f3 ?v_0 (f34 ?v3 ?v0)) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f17 (f18 f26 ?v5) ?v4) f1) (= (f3 (f6 f16 (f34 ?v3 ?v5)) (f34 ?v3 ?v4)) f1))) (= (f3 ?v_0 (f34 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2) (?v3 S17)) (let ((?v_0 (f6 f7 ?v2))) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (= (f3 ?v_0 (f35 ?v3 ?v0)) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f10 (f20 f27 ?v5) ?v4) f1) (= (f3 (f6 f16 (f35 ?v3 ?v5)) (f35 ?v3 ?v4)) f1))) (= (f3 ?v_0 (f35 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S1) (?v3 S3)) (let ((?v_0 (f18 f19 ?v2))) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (=> (= (f17 ?v_0 (f3 ?v3 ?v0)) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f16 ?v5) ?v4) f1) (= (f17 (f18 f26 (f3 ?v3 ?v5)) (f3 ?v3 ?v4)) f1))) (= (f17 ?v_0 (f3 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S4)) (let ((?v_0 (f20 f21 ?v2))) (=> (= (f3 (f6 f16 ?v0) ?v1) f1) (=> (= (f10 ?v_0 (f6 ?v3 ?v0)) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f16 ?v5) ?v4) f1) (= (f10 (f20 f27 (f6 ?v3 ?v5)) (f6 ?v3 ?v4)) f1))) (= (f10 ?v_0 (f6 ?v3 ?v1)) f1)))))))
(assert (forall ((?v0 S1) (?v1 S1) (?v2 S2) (?v3 S16)) (=> (= (f17 (f18 f19 ?v0) ?v1) f1) (=> (= (f3 (f6 f16 ?v2) (f34 ?v3 ?v0)) f1) (=> (forall ((?v4 S1) (?v5 S1)) (=> (= (f17 (f18 f19 ?v5) ?v4) f1) (= (f3 (f6 f7 (f34 ?v3 ?v5)) (f34 ?v3 ?v4)) f1))) (= (f3 (f6 f7 ?v2) (f34 ?v3 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2) (?v3 S17)) (=> (= (f10 (f20 f21 ?v0) ?v1) f1) (=> (= (f3 (f6 f16 ?v2) (f35 ?v3 ?v0)) f1) (=> (forall ((?v4 S3) (?v5 S3)) (=> (= (f10 (f20 f21 ?v5) ?v4) f1) (= (f3 (f6 f7 (f35 ?v3 ?v5)) (f35 ?v3 ?v4)) f1))) (= (f3 (f6 f7 ?v2) (f35 ?v3 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S1) (?v3 S3)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (=> (= (f17 (f18 f26 ?v2) (f3 ?v3 ?v0)) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f7 ?v5) ?v4) f1) (= (f17 (f18 f19 (f3 ?v3 ?v5)) (f3 ?v3 ?v4)) f1))) (= (f17 (f18 f19 ?v2) (f3 ?v3 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3) (?v3 S4)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (=> (= (f10 (f20 f27 ?v2) (f6 ?v3 ?v0)) f1) (=> (forall ((?v4 S2) (?v5 S2)) (=> (= (f3 (f6 f7 ?v5) ?v4) f1) (= (f10 (f20 f21 (f6 ?v3 ?v5)) (f6 ?v3 ?v4)) f1))) (= (f10 (f20 f21 ?v2) (f6 ?v3 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f6 f7 ?v0) ?v1) f1) (=> (forall ((?v3 S2)) (=> (= (f3 (f6 f7 ?v0) ?v3) f1) (=> (= (f3 (f6 f7 ?v3) ?v1) f1) (= (f3 (f6 f16 ?v3) ?v2) f1)))) (= (f3 (f6 f16 ?v1) ?v2) f1)))))
(assert (exists ((?v0 S2)) (= (f3 (f13 (f31 f32 f33) (f13 f14 f5)) ?v0) f1)))
(assert (=> (forall ((?v0 S2)) (=> (= (f3 (f13 (f31 f32 f33) (f13 f14 f5)) ?v0) f1) false)) false))
(assert (forall ((?v0 S2)) (= (= (f3 f33 ?v0) f1) (= f36 f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f10 (f20 f21 ?v0) ?v1) f1) (and (= (f10 (f20 f27 ?v0) ?v1) f1) (not (= (f10 (f20 f27 ?v1) ?v0) f1))))))
(assert (forall ((?v0 S3)) (=> (= (f10 (f20 f27 f33) ?v0) f1) (= ?v0 f33))))
(assert (forall ((?v0 S1)) (=> (= (f17 (f18 f26 f36) ?v0) f1) (= (= ?v0 f1) (= f36 f1)))))
(assert (forall ((?v0 S3)) (= (= (f10 (f20 f27 f33) ?v0) f1) (= ?v0 f33))))
(assert (forall ((?v0 S1)) (= (= (f17 (f18 f26 f36) ?v0) f1) (= (= ?v0 f1) (= f36 f1)))))
(assert (forall ((?v0 S3)) (= (f10 (f20 f27 ?v0) f33) f1)))
(assert (forall ((?v0 S1)) (= (f17 (f18 f26 ?v0) f36) f1)))
(assert (forall ((?v0 S3)) (not (= (f10 (f20 f21 f33) ?v0) f1))))
(assert (forall ((?v0 S1)) (not (= (f17 (f18 f19 f36) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (not (= ?v0 f33)) (= (f10 (f20 f21 ?v0) f33) f1))))
(assert (forall ((?v0 S1)) (= (not (= (= ?v0 f1) (= f36 f1))) (= (f17 (f18 f19 ?v0) f36) f1))))
(assert (forall ((?v0 S2)) (= (= (f10 (f11 f12 ?v0) f33) f1) true)))
(assert (forall ((?v0 S3)) (= (= (f28 (f29 f30 ?v0) f37) f1) true)))
(assert (forall ((?v0 S2)) (= (f10 (f11 f12 ?v0) f33) f1)))
(assert (forall ((?v0 S3)) (= (f28 (f29 f30 ?v0) f37) f1)))
(assert (forall ((?v0 S2)) (= (f3 f33 ?v0) f1)))
(assert (exists ((?v0 S2)) (= (f3 (f13 (f31 f38 f33) (f13 f14 f5)) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (forall ((?v2 S2)) (= (f17 (f18 f26 (f3 ?v0 ?v2)) (f3 ?v1 ?v2)) f1)) (= (f10 (f20 f27 ?v0) ?v1) f1))))
(assert (= f33 (f13 f14 f4)))
(assert (forall ((?v0 S3)) (= (f10 (f20 f27 ?v0) f33) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2) (?v3 S2)) (=> (= (f3 (f13 (f31 f32 ?v0) ?v1) ?v2) f1) (=> (= (f3 (f13 (f31 f38 ?v0) ?v1) ?v3) f1) (= (f3 (f6 f16 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S1) (?v3 S1)) (=> (= (f17 (f39 (f40 f41 ?v0) ?v1) ?v2) f1) (=> (= (f17 (f39 (f40 f42 ?v0) ?v1) ?v3) f1) (= (f17 (f18 f26 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3) (?v3 S3)) (=> (= (f10 (f43 (f44 f45 ?v0) ?v1) ?v2) f1) (=> (= (f10 (f43 (f44 f46 ?v0) ?v1) ?v3) f1) (= (f10 (f20 f27 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (=> (= (f3 (f13 (f31 f32 ?v0) ?v1) ?v2) f1) (= (f3 (f13 (f31 f38 ?v0) ?v1) ?v2) f1))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3)) (=> (= (f10 (f43 (f44 f45 ?v0) ?v1) ?v2) f1) (= (f10 (f43 (f44 f46 ?v0) ?v1) ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (forall ((?v2 S2)) (=> (= (f3 (f6 f7 ?v2) ?v0) f1) (= (f3 (f6 f16 ?v2) ?v1) f1))) (= (f3 (f6 f16 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2) (?v3 S2)) (=> (= (f3 (f13 (f31 f38 ?v0) ?v1) ?v2) f1) (=> (= (f10 (f11 f12 ?v3) ?v1) f1) (= (f3 (f6 f16 ?v3) ?v2) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S1) (?v3 S1)) (=> (= (f17 (f39 (f40 f42 ?v0) ?v1) ?v2) f1) (=> (= (f47 (f48 f49 ?v3) ?v1) f1) (= (f17 (f18 f26 ?v3) ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3) (?v3 S3)) (=> (= (f10 (f43 (f44 f46 ?v0) ?v1) ?v2) f1) (=> (= (f28 (f29 f30 ?v3) ?v1) f1) (= (f10 (f20 f27 ?v3) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2) (?v3 S2)) (=> (= (f3 (f13 (f31 f32 ?v0) ?v1) ?v2) f1) (=> (= (f10 (f11 f12 ?v3) ?v1) f1) (= (f3 (f6 f16 ?v3) ?v2) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S1) (?v3 S1)) (=> (= (f17 (f39 (f40 f41 ?v0) ?v1) ?v2) f1) (=> (= (f47 (f48 f49 ?v3) ?v1) f1) (= (f17 (f18 f26 ?v3) ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3) (?v3 S3)) (=> (= (f10 (f43 (f44 f45 ?v0) ?v1) ?v2) f1) (=> (= (f28 (f29 f30 ?v3) ?v1) f1) (= (f10 (f20 f27 ?v3) ?v2) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S2)) (let ((?v_0 (f11 f12 ?v2))) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (= (f10 ?v_0 ?v0) f1) (= (f10 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3)) (let ((?v_0 (f29 f30 ?v2))) (=> (= (f28 (f50 f51 ?v0) ?v1) f1) (=> (= (f28 ?v_0 ?v0) f1) (= (f28 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f10 (f20 f27 ?v0) ?v1) f1) (=> (= (f10 (f20 f27 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3)) (= (f10 (f20 f27 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f10 (f20 f21 ?v0) ?v1) f1) (and (= (f10 (f20 f27 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= ?v0 ?v1) (and (= (f10 (f20 f27 ?v0) ?v1) f1) (= (f10 (f20 f27 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f10 (f20 f27 ?v0) ?v1) f1) (or (= (f10 (f20 f21 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f10 (f20 f27 ?v0) ?v2) f1) (= (f3 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= ?v0 ?v1) (= (f10 (f20 f27 ?v0) ?v1) f1))))
(check-sat)
(exit)
