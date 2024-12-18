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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S4 S5) S1)
(declare-fun f6 (S6 S5 S7 S5) S1)
(declare-fun f7 () S6)
(declare-fun f8 () S7)
(declare-fun f9 (S4 S5) S1)
(declare-fun f10 (S3 S3) S1)
(declare-fun f11 () S3)
(declare-fun f12 (S9 S3) S3)
(declare-fun f13 (S2) S9)
(declare-fun f14 (S10 S8) S2)
(declare-fun f15 (S11 S6) S10)
(declare-fun f16 (S12 S8) S11)
(declare-fun f17 () S12)
(declare-fun f18 () S3)
(declare-fun f19 (S2 S3) S1)
(declare-fun f20 (S7) S3)
(declare-fun f21 (S13 S5) S1)
(declare-fun f22 (S8 S4) S13)
(declare-fun f23 (S3) S3)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) false)))
(assert (not (forall ((?v0 S4) (?v1 S5)) (=> (= (f5 ?v0 ?v1) f1) (forall ((?v2 S5)) (=> (= (f6 f7 ?v1 f8 ?v2) f1) (= (f9 ?v0 ?v2) f1)))))))
(assert (forall ((?v0 S4) (?v1 S5)) (=> (= (f5 ?v0 ?v1) f1) (exists ((?v2 S8) (?v3 S8)) (and (= (f10 f11 (f12 (f13 (f14 (f15 (f16 f17 ?v2) f7) ?v3)) f18)) f1) (and (forall ((?v4 S7)) (=> (forall ((?v5 S2)) (=> (= (f19 ?v5 f11) f1) (= (f3 (f20 ?v4) ?v5) f1))) (forall ((?v5 S4) (?v6 S5)) (=> (= (f21 (f22 ?v2 ?v5) ?v6) f1) (forall ((?v7 S5)) (=> (= (f6 f7 ?v6 ?v4 ?v7) f1) (= (f21 (f22 ?v3 ?v5) ?v7) f1))))))) (forall ((?v4 S5)) (=> (forall ((?v5 S4)) (=> (= (f21 (f22 ?v2 ?v5) ?v1) f1) (= (f21 (f22 ?v3 ?v5) ?v4) f1))) (= (f9 ?v0 ?v4) f1)))))))))
(assert (forall ((?v0 S2)) (=> (= (f19 ?v0 f11) f1) (= (f3 (f20 f8) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f10 ?v0 f18) f1)))
(assert (forall ((?v0 S7) (?v1 S8) (?v2 S6) (?v3 S8)) (= (= (f3 (f20 ?v0) (f14 (f15 (f16 f17 ?v1) ?v2) ?v3)) f1) (forall ((?v4 S4) (?v5 S5)) (=> (= (f21 (f22 ?v1 ?v4) ?v5) f1) (forall ((?v6 S5)) (=> (= (f6 ?v2 ?v5 ?v0 ?v6) f1) (= (f21 (f22 ?v3 ?v4) ?v6) f1))))))))
(assert (forall ((?v0 S8) (?v1 S6) (?v2 S8) (?v3 S8) (?v4 S6) (?v5 S8)) (= (= (f14 (f15 (f16 f17 ?v0) ?v1) ?v2) (f14 (f15 (f16 f17 ?v3) ?v4) ?v5)) (and (= ?v0 ?v3) (and (= ?v1 ?v4) (= ?v2 ?v5))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f10 ?v0 ?v1) f1) (=> (= (f10 ?v2 ?v0) f1) (= (f10 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f13 ?v1))) (=> (= (f10 ?v0 (f12 ?v_0 f18)) f1) (=> (= (f10 ?v0 ?v2) f1) (= (f10 ?v0 (f12 ?v_0 ?v2)) f1))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S3)) (let ((?v_0 (f13 ?v1))) (=> (= (f10 ?v0 (f12 ?v_0 ?v2)) f1) (and (= (f10 ?v0 (f12 ?v_0 f18)) f1) (= (f10 ?v0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S6) (?v3 S8) (?v4 S8)) (let ((?v_0 (f15 (f16 f17 ?v1) ?v2))) (=> (= (f10 ?v0 (f12 (f13 (f14 ?v_0 ?v3)) f18)) f1) (=> (forall ((?v5 S4) (?v6 S5)) (=> (= (f21 (f22 ?v3 ?v5) ?v6) f1) (= (f21 (f22 ?v4 ?v5) ?v6) f1))) (= (f10 ?v0 (f12 (f13 (f14 ?v_0 ?v4)) f18)) f1))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S6) (?v3 S8) (?v4 S8)) (=> (= (f10 ?v0 (f12 (f13 (f14 (f15 (f16 f17 ?v1) ?v2) ?v3)) f18)) f1) (=> (forall ((?v5 S4) (?v6 S5)) (=> (= (f21 (f22 ?v4 ?v5) ?v6) f1) (= (f21 (f22 ?v1 ?v5) ?v6) f1))) (= (f10 ?v0 (f12 (f13 (f14 (f15 (f16 f17 ?v4) ?v2) ?v3)) f18)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f19 ?v0 (f12 (f13 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f19 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (=> (not (= (f19 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f19 ?v0 (f12 (f13 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S6) (?v3 S8) (?v4 S8) (?v5 S8)) (=> (= (f10 ?v0 (f12 (f13 (f14 (f15 (f16 f17 ?v1) ?v2) ?v3)) f18)) f1) (=> (forall ((?v6 S4) (?v7 S5)) (=> (= (f21 (f22 ?v4 ?v6) ?v7) f1) (forall ((?v8 S5)) (=> (forall ((?v9 S4)) (=> (= (f21 (f22 ?v1 ?v9) ?v7) f1) (= (f21 (f22 ?v3 ?v9) ?v8) f1))) (= (f21 (f22 ?v5 ?v6) ?v8) f1))))) (= (f10 ?v0 (f12 (f13 (f14 (f15 (f16 f17 ?v4) ?v2) ?v5)) f18)) f1)))))
(assert (forall ((?v0 S2)) (=> (= (f19 ?v0 f18) f1) false)))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f18 (f12 (f13 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f12 (f13 ?v0) ?v1) f18))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f19 ?v0 (f12 (f13 ?v1) f18)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f12 (f13 ?v0) (f12 (f13 ?v1) f18)) (f12 (f13 ?v2) (f12 (f13 ?v3) f18))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f18) (not (= (f19 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f23 ?v0) f18) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f19 ?v0 f18) f1) false)))
(assert (forall ((?v0 S3)) (= (= f18 (f23 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f19 ?v1 f18) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f19 ?v1 f18) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f19 ?v1 ?v0) f1)) (not (= ?v0 f18)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f19 ?v1 ?v0) f1))) (= ?v0 f18))))
(assert (= f18 (f23 f4)))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f19 ?v0 ?v1) f1) (= (f12 (f13 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (= (f19 ?v0 ?v1) f1) (= (f19 ?v0 (f12 (f13 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f13 ?v0))) (=> (not (= (f19 ?v0 ?v1) f1)) (=> (not (= (f19 ?v0 ?v2) f1)) (= (= (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f12 (f13 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (= (f19 ?v0 (f12 (f13 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f19 ?v0 ?v2) f1)))))
(check-sat)
(exit)
