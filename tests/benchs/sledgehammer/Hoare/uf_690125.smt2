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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S3 S3) S1)
(declare-fun f6 (S4 S3) S3)
(declare-fun f7 (S2) S4)
(declare-fun f8 (S5 S6) S2)
(declare-fun f9 (S7 S8) S5)
(declare-fun f10 (S9 S6) S7)
(declare-fun f11 () S9)
(declare-fun f12 () S6)
(declare-fun f13 (S10 S11) S8)
(declare-fun f14 () S10)
(declare-fun f15 () S11)
(declare-fun f16 () S6)
(declare-fun f17 () S3)
(declare-fun f18 (S12 S13) S8)
(declare-fun f19 () S12)
(declare-fun f20 (S11) S13)
(declare-fun f21 () S3)
(declare-fun f22 (S16 S15) S1)
(declare-fun f23 (S6 S14) S16)
(declare-fun f24 (S2 S3) S1)
(declare-fun f25 (S3) S3)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) false)))
(assert (let ((?v_0 (f10 f11 f12))) (not (= (f5 (f6 (f7 (f8 (f9 ?v_0 (f13 f14 f15)) f16)) f17) (f6 (f7 (f8 (f9 ?v_0 (f18 f19 (f20 f15))) f16)) f21)) f1))))
(assert (= (f5 f17 (f6 (f7 (f8 (f9 (f10 f11 f12) (f18 f19 (f20 f15))) f16)) f21)) f1))
(assert (forall ((?v0 S3)) (= (f5 ?v0 f21) f1)))
(assert (forall ((?v0 S6) (?v1 S8) (?v2 S6) (?v3 S6) (?v4 S8) (?v5 S6)) (= (= (f8 (f9 (f10 f11 ?v0) ?v1) ?v2) (f8 (f9 (f10 f11 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f5 ?v0 ?v1) f1) (=> (= (f5 ?v2 ?v0) f1) (= (f5 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f7 ?v1))) (=> (= (f5 ?v0 (f6 ?v_0 f21)) f1) (=> (= (f5 ?v0 ?v2) f1) (= (f5 ?v0 (f6 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S6) (?v1 S11) (?v2 S6) (?v3 S3)) (let ((?v_0 (f10 f11 ?v0))) (let ((?v_1 (f7 (f8 (f9 ?v_0 (f13 f14 ?v1)) ?v2)))) (=> (= (f5 (f6 ?v_1 ?v3) (f6 (f7 (f8 (f9 ?v_0 (f18 f19 (f20 ?v1))) ?v2)) f21)) f1) (= (f5 ?v3 (f6 ?v_1 f21)) f1))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6)) (let ((?v_0 (f9 (f10 f11 ?v1) ?v2))) (=> (= (f5 ?v0 (f6 (f7 (f8 ?v_0 ?v3)) f21)) f1) (=> (forall ((?v5 S14) (?v6 S15)) (=> (= (f22 (f23 ?v3 ?v5) ?v6) f1) (= (f22 (f23 ?v4 ?v5) ?v6) f1))) (= (f5 ?v0 (f6 (f7 (f8 ?v_0 ?v4)) f21)) f1))))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6)) (=> (= (f5 ?v0 (f6 (f7 (f8 (f9 (f10 f11 ?v1) ?v2) ?v3)) f21)) f1) (=> (forall ((?v5 S14) (?v6 S15)) (=> (= (f22 (f23 ?v4 ?v5) ?v6) f1) (= (f22 (f23 ?v1 ?v5) ?v6) f1))) (= (f5 ?v0 (f6 (f7 (f8 (f9 (f10 f11 ?v4) ?v2) ?v3)) f21)) f1)))))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S8) (?v3 S6) (?v4 S6) (?v5 S6)) (=> (= (f5 ?v0 (f6 (f7 (f8 (f9 (f10 f11 ?v1) ?v2) ?v3)) f21)) f1) (=> (forall ((?v6 S14) (?v7 S15)) (=> (= (f22 (f23 ?v4 ?v6) ?v7) f1) (forall ((?v8 S15)) (=> (forall ((?v9 S14)) (=> (= (f22 (f23 ?v1 ?v9) ?v7) f1) (= (f22 (f23 ?v3 ?v9) ?v8) f1))) (= (f22 (f23 ?v5 ?v6) ?v8) f1))))) (= (f5 ?v0 (f6 (f7 (f8 (f9 (f10 f11 ?v4) ?v2) ?v5)) f21)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f24 ?v0 (f6 (f7 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f24 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (=> (not (= (f24 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f24 ?v0 (f6 (f7 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2)) (=> (= (f24 ?v0 f21) f1) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f21 (f6 (f7 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f6 (f7 ?v0) ?v1) f21))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f24 ?v0 (f6 (f7 ?v1) f21)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f6 (f7 ?v0) (f6 (f7 ?v1) f21)) (f6 (f7 ?v2) (f6 (f7 ?v3) f21))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f21) (not (= (f24 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f25 ?v0) f21) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f24 ?v0 f21) f1) false)))
(assert (forall ((?v0 S3)) (= (= f21 (f25 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f24 ?v1 f21) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f24 ?v1 f21) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f24 ?v1 ?v0) f1)) (not (= ?v0 f21)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f24 ?v1 ?v0) f1))) (= ?v0 f21))))
(assert (= f21 (f25 f4)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f24 ?v0 ?v1) f1) (= (f6 (f7 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (= (f24 ?v0 ?v1) f1) (= (f24 ?v0 (f6 (f7 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 ?v0))) (=> (not (= (f24 ?v0 ?v1) f1)) (=> (not (= (f24 ?v0 ?v2) f1)) (= (= (f6 ?v_0 ?v1) (f6 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f6 (f7 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (= (f24 ?v0 (f6 (f7 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f24 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f7 ?v0)) (?v_0 (f7 ?v1))) (= (f6 ?v_1 (f6 ?v_0 ?v2)) (f6 ?v_0 (f6 ?v_1 ?v2))))))
(check-sat)
(exit)