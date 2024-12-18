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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 (S5 S4) S2)
(declare-fun f5 () S5)
(declare-fun f6 (S6 S4) S4)
(declare-fun f7 (S7 S4) S6)
(declare-fun f8 () S7)
(declare-fun f9 () S4)
(declare-fun f10 () S2)
(declare-fun f11 () S3)
(declare-fun f12 () S3)
(declare-fun f13 (S3 S3) S1)
(declare-fun f14 (S8 S3) S9)
(declare-fun f15 (S10 S9) S8)
(declare-fun f16 () S10)
(declare-fun f17 () S9)
(declare-fun f18 (S11 S3) S3)
(declare-fun f19 (S12 S3) S11)
(declare-fun f20 () S12)
(declare-fun f21 () S3)
(declare-fun f22 () S3)
(declare-fun f23 () S4)
(declare-fun f24 (S9 S9) S1)
(declare-fun f25 () S9)
(assert (not (= f1 f2)))
(assert (not (not (= (f3 (f4 f5 (f6 (f7 f8 f9) (f3 f10 f11))) f12) f9))))
(assert (= (f13 f12 f11) f1))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 (f3 f10 ?v0)) ?v0) f9)))
(assert (forall ((?v0 S4) (?v1 S3)) (let ((?v_0 (f7 f8 f9))) (= (f6 ?v_0 (f3 (f4 f5 ?v0) ?v1)) (f3 (f4 f5 (f6 ?v_0 ?v0)) ?v1)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (= (f3 (f4 f5 (f6 (f7 f8 ?v0) ?v1)) ?v2) (f6 (f7 f8 (f3 (f4 f5 ?v0) ?v2)) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S4)) (= (f6 (f7 f8 ?v0) f9) ?v0)))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f9) ?v0) f9)))
(assert (forall ((?v0 S3)) (= (f14 (f15 f16 f17) ?v0) f17)))
(assert (forall ((?v0 S3)) (= (f18 (f19 f20 f21) ?v0) f21)))
(assert (= (f13 f22 f12) f1))
(assert (forall ((?v0 S4)) (= (= f9 ?v0) (= ?v0 f9))))
(assert (forall ((?v0 S9)) (= (= f17 ?v0) (= ?v0 f17))))
(assert (forall ((?v0 S3)) (= (= f21 ?v0) (= ?v0 f21))))
(assert (forall ((?v0 S3)) (not (= (f3 f10 ?v0) f23))))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) f22) f9)))
(assert (forall ((?v0 S9)) (= (f14 (f15 f16 ?v0) f22) f17)))
(assert (forall ((?v0 S3)) (= (f18 (f19 f20 ?v0) f22) f21)))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) f22) f9)))
(assert (forall ((?v0 S9)) (= (f14 (f15 f16 ?v0) f22) f17)))
(assert (forall ((?v0 S3)) (= (f18 (f19 f20 ?v0) f22) f21)))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S3)) (=> (not (= ?v0 f23)) (= (f3 (f4 f5 (f6 (f7 f8 ?v1) ?v0)) ?v2) (f6 (f7 f8 (f3 (f4 f5 ?v1) ?v2)) (f3 (f4 f5 ?v0) ?v2))))))
(assert (forall ((?v0 S4)) (= (f6 (f7 f8 ?v0) ?v0) (ite (= ?v0 f23) f23 f9))))
(assert (forall ((?v0 S4)) (=> (not (= ?v0 f23)) (= (f6 (f7 f8 ?v0) ?v0) f9))))
(assert (not (= (f24 f17 f25) f1)))
(assert (not (= (f13 f21 f22) f1)))
(assert (= (f24 f25 f17) f1))
(assert (= (f13 f22 f21) f1))
(assert (forall ((?v0 S9)) (= (= f25 ?v0) (= ?v0 f25))))
(assert (forall ((?v0 S3)) (= (= f22 ?v0) (= ?v0 f22))))
(assert (forall ((?v0 S4)) (= (= f23 ?v0) (= ?v0 f23))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f13 f22 (f18 (f19 f20 ?v0) ?v1)) f1) (or (= (f13 f22 ?v0) f1) (= ?v1 f22)))))
(assert (forall ((?v0 S9) (?v1 S3)) (= (= (f14 (f15 f16 ?v0) ?v1) f25) (and (= ?v0 f25) (not (= ?v1 f22))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f18 (f19 f20 ?v0) ?v1) f22) (and (= ?v0 f22) (not (= ?v1 f22))))))
(assert (forall ((?v0 S4) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f23) (and (= ?v0 f23) (not (= ?v1 f22))))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f24 ?v0 ?v1) f1) false) (=> (=> (= (f24 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S9) (?v1 S3)) (=> (= (f24 f25 ?v0) f1) (= (f24 f25 (f14 (f15 f16 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f13 f22 ?v0) f1) (= (f13 f22 (f18 (f19 f20 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f19 f20 ?v0))) (=> (= (f13 f22 ?v0) f1) (=> (= (f13 (f18 ?v_0 ?v1) (f18 ?v_0 ?v2)) f1) (= (f13 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S9)) (let ((?v_0 (f15 f16 ?v2))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f24 f25 ?v2) f1) (=> (= (f24 ?v2 f17) f1) (= (f24 (f14 ?v_0 ?v1) (f14 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f19 f20 ?v2))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 f22 ?v2) f1) (=> (= (f13 ?v2 f21) f1) (= (f13 (f18 ?v_0 ?v1) (f18 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S9) (?v1 S3)) (=> (= (f24 f17 ?v0) f1) (=> (= (f13 f22 ?v1) f1) (= (f24 f17 (f14 (f15 f16 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f13 f21 ?v0) f1) (=> (= (f13 f22 ?v1) f1) (= (f13 f21 (f18 (f19 f20 ?v0) ?v1)) f1)))))
(assert (not (= f23 f9)))
(assert (not (= f25 f17)))
(assert (not (= f22 f21)))
(assert (not (= f9 f23)))
(assert (not (= f17 f25)))
(assert (not (= f21 f22)))
(assert (forall ((?v0 S9)) (= (f14 (f15 f16 ?v0) f21) ?v0)))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) f21) ?v0)))
(assert (forall ((?v0 S3)) (= (f18 (f19 f20 ?v0) f21) ?v0)))
(assert (forall ((?v0 S9)) (= (f14 (f15 f16 ?v0) f21) ?v0)))
(assert (forall ((?v0 S4)) (= (f3 (f4 f5 ?v0) f21) ?v0)))
(assert (forall ((?v0 S3)) (= (f18 (f19 f20 ?v0) f21) ?v0)))
(assert (forall ((?v0 S9) (?v1 S3)) (=> (not (= ?v0 f25)) (not (= (f14 (f15 f16 ?v0) ?v1) f25)))))
(assert (forall ((?v0 S4) (?v1 S3)) (=> (not (= ?v0 f23)) (not (= (f3 (f4 f5 ?v0) ?v1) f23)))))
(assert (forall ((?v0 S4)) (= (f6 (f7 f8 ?v0) f23) f23)))
(assert (forall ((?v0 S4)) (= (f6 (f7 f8 f23) ?v0) f23)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S9)) (let ((?v_0 (f15 f16 ?v2))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f24 f17 ?v2) f1) (= (f24 (f14 ?v_0 ?v0) (f14 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f19 f20 ?v2))) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 f21 ?v2) f1) (= (f13 (f18 ?v_0 ?v0) (f18 ?v_0 ?v1)) f1))))))
(check-sat)
(exit)
