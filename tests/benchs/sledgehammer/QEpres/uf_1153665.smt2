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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S4 S2) S5)
(declare-fun f6 () S4)
(declare-fun f7 () S5)
(declare-fun f8 (S6 S7 S8) S1)
(declare-fun f9 () S6)
(declare-fun f10 (S9 S7) S7)
(declare-fun f11 () S9)
(declare-fun f12 () S7)
(declare-fun f13 () S8)
(declare-fun f14 (S3 S7) S1)
(declare-fun f15 (S10 S7) S9)
(declare-fun f16 () S10)
(declare-fun f17 () S10)
(declare-fun f18 () S9)
(declare-fun f19 () S7)
(declare-fun f20 () S7)
(declare-fun f21 () S10)
(declare-fun f22 () S10)
(declare-fun f23 (S11 S2) S7)
(declare-fun f24 () S11)
(declare-fun f25 () S9)
(declare-fun f26 (S12 S2) S2)
(declare-fun f27 (S13 S12) S9)
(declare-fun f28 () S13)
(declare-fun f29 () S11)
(declare-fun f30 (S14 S8) S1)
(declare-fun f31 (S6 S2) S14)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (not (= (f5 f6 ?v0) f7)))))
(assert (not (= (= (f8 f9 (f10 f11 f12) f13) f1) (= (f8 f9 f12 f13) f1))))
(assert (= (f14 f4 f12) f1))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f14 f4 ?v0) f1) (=> (= (f14 f4 ?v1) f1) (= (f14 f4 (f10 (f15 f16 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (=> (= (f14 f4 ?v0) f1) (=> (= (f14 f4 ?v1) f1) (= (f14 f4 (f10 (f15 f17 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S5)) (= (= f7 ?v0) (= ?v0 f7))))
(assert (forall ((?v0 S7)) (= (= (f14 f4 (f10 f18 ?v0)) f1) (= (f14 f4 ?v0) f1))))
(assert (= (f14 f4 f19) f1))
(assert (= (f14 f4 f20) f1))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f14 f4 (f10 (f15 f21 ?v0) ?v1)) f1) (and (= (f14 f4 ?v0) f1) (= (f14 f4 ?v1) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f14 f4 (f10 (f15 f22 ?v0) ?v1)) f1) (and (= (f14 f4 ?v0) f1) (= (f14 f4 ?v1) f1)))))
(assert (forall ((?v0 S2)) (= (= (f14 f4 (f23 f24 ?v0)) f1) (not (= (f5 f6 ?v0) f7)))))
(assert (forall ((?v0 S7)) (= (= (f14 f4 (f10 f25 ?v0)) f1) (= (f14 f4 ?v0) f1))))
(assert (forall ((?v0 S12) (?v1 S7)) (=> (forall ((?v2 S2)) (= (not (= (f5 f6 (f26 ?v0 ?v2)) f7)) (not (= (f5 f6 ?v2) f7)))) (= (= (f14 f4 (f10 (f27 f28 ?v0) ?v1)) f1) (= (f14 f4 ?v1) f1)))))
(assert (forall ((?v0 S2)) (=> (not (= (f5 f6 ?v0) f7)) (= (f14 f4 (f23 f29 ?v0)) f1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S8)) (= (= (f8 f9 (f10 (f15 f16 ?v0) ?v1) ?v2) f1) (= (f8 f9 (f10 (f15 f22 ?v0) ?v1) ?v2) f1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S8)) (= (= (f8 f9 (f10 (f15 f17 ?v0) ?v1) ?v2) f1) (= (f8 f9 (f10 (f15 f21 ?v0) ?v1) ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S8)) (= (= (f8 f9 (f23 f29 ?v0) ?v1) f1) (not (= (f30 (f31 f9 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f10 (f15 f17 ?v0) ?v1) (ite (= ?v0 f19) ?v1 (ite (= ?v1 f19) ?v0 (ite (or (= ?v0 f20) (= ?v1 f20)) f20 (f10 (f15 f21 ?v0) ?v1)))))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f10 (f15 f16 ?v0) ?v1) (ite (= ?v0 f20) ?v1 (ite (= ?v1 f20) ?v0 (ite (or (= ?v0 f19) (= ?v1 f19)) f19 (f10 (f15 f22 ?v0) ?v1)))))))
(assert (forall ((?v0 S12) (?v1 S7)) (let ((?v_0 (f27 f28 ?v0))) (= (f10 ?v_0 (f10 f18 ?v1)) (f10 f18 (f10 ?v_0 ?v1))))))
(assert (forall ((?v0 S12) (?v1 S7) (?v2 S7)) (let ((?v_0 (f27 f28 ?v0))) (= (f10 ?v_0 (f10 (f15 f21 ?v1) ?v2)) (f10 (f15 f21 (f10 ?v_0 ?v1)) (f10 ?v_0 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S7) (?v2 S7)) (let ((?v_0 (f27 f28 ?v0))) (= (f10 ?v_0 (f10 (f15 f22 ?v1) ?v2)) (f10 (f15 f22 (f10 ?v_0 ?v1)) (f10 ?v_0 ?v2))))))
(assert (forall ((?v0 S12) (?v1 S2)) (= (f10 (f27 f28 ?v0) (f23 f24 ?v1)) (f23 f24 (f26 ?v0 ?v1)))))
(assert (forall ((?v0 S12)) (= (f10 (f27 f28 ?v0) f19) f19)))
(assert (forall ((?v0 S12)) (= (f10 (f27 f28 ?v0) f20) f20)))
(assert (forall ((?v0 S12) (?v1 S7)) (let ((?v_0 (f27 f28 ?v0))) (= (f10 ?v_0 (f10 f25 ?v1)) (f10 f25 (f10 ?v_0 ?v1))))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (not (= (f10 f18 ?v0) (f10 (f15 f21 ?v1) ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (not (= (f10 (f15 f21 ?v0) ?v1) (f10 f18 ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f10 f25 ?v0) (f10 f25 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f23 f24 ?v0) (f23 f24 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (= (= (f10 (f15 f22 ?v0) ?v1) (f10 (f15 f22 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7) (?v3 S7)) (= (= (f10 (f15 f21 ?v0) ?v1) (f10 (f15 f21 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f10 f18 ?v0) (f10 f18 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S8)) (= (= (f8 ?v0 (f10 f25 ?v1) ?v2) f1) (not (= (f8 ?v0 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S8)) (= (= (f8 ?v0 f19 ?v1) f1) true)))
(assert (forall ((?v0 S6) (?v1 S8)) (= (= (f8 ?v0 f20 ?v1) f1) false)))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S8)) (= (= (f8 ?v0 (f23 f24 ?v1) ?v2) f1) (= (f30 (f31 ?v0 ?v1) ?v2) f1))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S7) (?v3 S8)) (= (= (f8 ?v0 (f10 (f15 f22 ?v1) ?v2) ?v3) f1) (or (= (f8 ?v0 ?v1 ?v3) f1) (= (f8 ?v0 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S6) (?v1 S7) (?v2 S7) (?v3 S8)) (= (= (f8 ?v0 (f10 (f15 f21 ?v1) ?v2) ?v3) f1) (and (= (f8 ?v0 ?v1 ?v3) f1) (= (f8 ?v0 ?v2 ?v3) f1)))))
(assert (forall ((?v0 S7)) (not (= (f10 f25 ?v0) f20))))
(assert (forall ((?v0 S7)) (not (= (f10 f25 ?v0) f19))))
(assert (forall ((?v0 S7)) (not (= f20 (f10 f25 ?v0)))))
(assert (forall ((?v0 S7)) (not (= f19 (f10 f25 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S7)) (not (= (f23 f24 ?v0) (f10 f25 ?v1)))))
(assert (forall ((?v0 S7) (?v1 S2)) (not (= (f10 f25 ?v0) (f23 f24 ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (not (= (f10 (f15 f22 ?v0) ?v1) (f10 f25 ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (not (= (f10 f25 ?v0) (f10 (f15 f22 ?v1) ?v2)))))
(assert (not (= f20 f19)))
(assert (not (= f19 f20)))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (not (= (f10 (f15 f21 ?v0) ?v1) (f10 f25 ?v2)))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (not (= (f10 f25 ?v0) (f10 (f15 f21 ?v1) ?v2)))))
(assert (forall ((?v0 S2)) (not (= (f23 f24 ?v0) f20))))
(assert (forall ((?v0 S2)) (not (= (f23 f24 ?v0) f19))))
(assert (forall ((?v0 S2)) (not (= f20 (f23 f24 ?v0)))))
(assert (forall ((?v0 S2)) (not (= f19 (f23 f24 ?v0)))))
(assert (forall ((?v0 S7) (?v1 S7)) (not (= (f10 (f15 f22 ?v0) ?v1) f20))))
(assert (forall ((?v0 S7) (?v1 S7)) (not (= (f10 (f15 f22 ?v0) ?v1) f19))))
(assert (forall ((?v0 S7) (?v1 S7)) (not (= f20 (f10 (f15 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (not (= f19 (f10 (f15 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (not (= (f10 (f15 f21 ?v0) ?v1) f20))))
(assert (forall ((?v0 S7) (?v1 S7)) (not (= (f10 (f15 f21 ?v0) ?v1) f19))))
(assert (forall ((?v0 S7) (?v1 S7)) (not (= f20 (f10 (f15 f21 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (not (= f19 (f10 (f15 f21 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (not (= (f10 f25 ?v0) (f10 f18 ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (not (= (f10 f18 ?v0) (f10 f25 ?v1)))))
(check-sat)
(exit)