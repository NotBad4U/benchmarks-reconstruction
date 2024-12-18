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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 (S3 S2) S2)
(declare-fun f5 () S3)
(declare-fun f6 (S4 S2) S3)
(declare-fun f7 () S4)
(declare-fun f8 (S5 S6) S2)
(declare-fun f9 () S5)
(declare-fun f10 (S7 S6) S6)
(declare-fun f11 () S7)
(declare-fun f12 () S7)
(declare-fun f13 () S6)
(declare-fun f14 () S2)
(declare-fun f15 () S2)
(declare-fun f16 () S6)
(declare-fun f17 () S2)
(declare-fun f18 (S6 S6) S1)
(declare-fun f19 () S6)
(declare-fun f20 () S7)
(declare-fun f21 (S8 S6) S9)
(declare-fun f22 () S8)
(declare-fun f23 () S9)
(declare-fun f24 (S10 S6) S7)
(declare-fun f25 () S10)
(declare-fun f26 (S9 S9) S1)
(declare-fun f27 () S7)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 f5 (f4 (f6 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f14)) f15) f1)))
(assert (= (f3 (f4 (f6 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f14) f15) f1))
(assert (= (f3 (f8 f9 f16) (f4 (f6 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f14)) f1))
(assert (= (f3 (f4 (f6 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f17) f15) f1))
(assert (= (f3 (f8 f9 f16) (f4 (f6 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f17)) f1))
(assert (= (f3 (f4 (f6 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f17) f15) f1))
(assert (= (f3 (f8 f9 f16) (f4 (f6 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f17)) f1))
(assert (= (f3 (f4 (f6 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f14) f15) f1))
(assert (= (f3 (f8 f9 f16) (f4 (f6 f7 (f8 f9 (f10 f11 (f10 f12 f13)))) f14)) f1))
(assert (forall ((?v0 S6)) (= (= (f3 f15 (f8 f9 ?v0)) f1) (= (f18 (f10 f12 f13) ?v0) f1))))
(assert (forall ((?v0 S6)) (= (= (f18 f19 (f10 f20 ?v0)) f1) (= (f18 (f10 f12 f13) ?v0) f1))))
(assert (forall ((?v0 S6)) (= (= (f3 (f8 f9 ?v0) f15) f1) (= (f18 ?v0 (f10 f12 f13)) f1))))
(assert (forall ((?v0 S6)) (= (= (f18 (f10 f20 ?v0) f19) f1) (= (f18 ?v0 (f10 f12 f13)) f1))))
(assert (= f15 (f8 f9 (f10 f12 f13))))
(assert (= f19 (f10 f20 (f10 f12 f13))))
(assert (= (f8 f9 (f10 f12 f13)) f15))
(assert (= (f10 f20 (f10 f12 f13)) f19))
(assert (= (f21 f22 (f10 f12 f13)) f23))
(assert (= (f8 f9 (f10 f12 f13)) f15))
(assert (= (f10 f20 (f10 f12 f13)) f19))
(assert (forall ((?v0 S2)) (= (f4 (f6 f7 ?v0) (f8 f9 (f10 f12 f13))) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f24 f25 ?v0) (f10 f20 (f10 f12 f13))) ?v0)))
(assert (forall ((?v0 S2)) (= (f4 (f6 f7 (f8 f9 (f10 f12 f13))) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f10 (f24 f25 (f10 f20 (f10 f12 f13))) ?v0) ?v0)))
(assert (forall ((?v0 S2)) (= (f3 ?v0 ?v0) f1)))
(assert (forall ((?v0 S6)) (= (f18 ?v0 ?v0) f1)))
(assert (forall ((?v0 S9)) (= (f26 ?v0 ?v0) f1)))
(assert (forall ((?v0 S2)) (= (f4 (f6 f7 f15) ?v0) ?v0)))
(assert (= (f10 f27 f19) f19))
(assert (= (f4 f5 f15) f15))
(assert (= (f10 f11 f13) f13))
(assert (forall ((?v0 S6)) (= (= f13 (f10 f11 ?v0)) (= f13 ?v0))))
(assert (forall ((?v0 S6)) (= (f18 ?v0 ?v0) f1)))
(assert (= (= f16 f16) true))
(assert (= (= (f18 f16 f16) f1) true))
(assert (forall ((?v0 S6) (?v1 S6)) (or (= (f18 ?v0 ?v1) f1) (= (f18 ?v1 ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f18 (f10 f20 ?v0) (f10 f20 ?v1)) f1) (= (f18 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f26 (f21 f22 ?v0) (f21 f22 ?v1)) f1) (ite (= (f18 ?v0 ?v1) f1) true (= (f18 ?v0 f13) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f10 f20 f16))) (= (= (f10 (f24 f25 ?v0) ?v1) f19) (or (and (= ?v0 f19) (= ?v1 f19)) (and (= ?v0 ?v_0) (= ?v1 ?v_0)))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f18 ?v0 ?v1) f1) (=> (= (f18 ?v1 ?v2) f1) (= (f18 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f18 ?v0 ?v1) f1) (=> (= (f18 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f10 (f24 f25 ?v0) ?v1) f19) (or (= ?v0 f19) (= ?v0 (f10 f20 f16))))))
(assert (not (= (f10 f20 f13) (f10 f20 f16))))
(assert (forall ((?v0 S6)) (= (= (f18 (f10 f12 ?v0) f16) f1) (= (f18 ?v0 f16) f1))))
(assert (forall ((?v0 S6)) (= (= (f18 f16 (f10 f12 ?v0)) f1) (= (f18 f16 ?v0) f1))))
(assert (= (= (f18 f13 f16) f1) false))
(assert (= (= (f18 f16 f13) f1) true))
(assert (forall ((?v0 S6)) (= (= (f18 (f10 f11 ?v0) f16) f1) (= (f18 ?v0 f16) f1))))
(check-sat)
(exit)
