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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 () S3)
(declare-fun f5 (S2 S3) S1)
(declare-fun f6 (S2 S2) S3)
(declare-fun f7 () S2)
(declare-fun f8 () S2)
(declare-fun f9 (S4 S2) S2)
(declare-fun f10 (S5 S2) S4)
(declare-fun f11 () S5)
(declare-fun f12 (S6 S7) S2)
(declare-fun f13 () S6)
(declare-fun f14 (S8 S7) S7)
(declare-fun f15 () S8)
(declare-fun f16 () S8)
(declare-fun f17 () S7)
(declare-fun f18 () S3)
(declare-fun f19 () S4)
(declare-fun f20 (S3 S3) S3)
(declare-fun f21 (S3) S3)
(declare-fun f22 (S9 S7) S8)
(declare-fun f23 () S9)
(declare-fun f24 () S8)
(declare-fun f25 () S7)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (= (= (f3 f4 ?v0) f1) (exists ((?v1 S2)) (and (= (f5 ?v1 (f6 f7 f8)) f1) (= ?v0 (f9 (f10 f11 (f12 f13 (f14 f15 (f14 f16 f17)))) ?v1)))))))
(assert (forall ((?v0 S2)) (= (= (f3 f18 ?v0) f1) (exists ((?v1 S2)) (and (= (f5 ?v1 (f6 f7 f8)) f1) (= ?v0 (f9 f19 (f9 (f10 f11 (f12 f13 (f14 f15 (f14 f16 f17)))) ?v1))))))))
(assert (not (= (f6 f7 (f9 (f10 f11 (f12 f13 (f14 f15 (f14 f16 f17)))) f8)) (f20 (f21 f4) (f21 f18)))))
(assert (= (f9 f19 (f9 f19 f7)) (f12 f13 (f14 f15 (f14 f16 f17)))))
(assert (= (f12 f13 (f14 f15 (f14 f16 f17))) (f9 f19 (f9 f19 f7))))
(assert (= (f12 f13 (f14 f16 f17)) (f9 f19 f7)))
(assert (= (f12 f13 (f14 f16 (f14 f16 f17))) (f9 f19 (f9 f19 (f9 f19 f7)))))
(assert (forall ((?v0 S7)) (= (f14 (f22 f23 ?v0) (f14 f24 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S7)) (= (f14 (f22 f23 (f14 f24 (f14 f16 f17))) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f9 f19 f7))) (= (= (f9 (f10 f11 ?v0) ?v1) ?v_0) (and (= ?v0 ?v_0) (= ?v1 ?v_0))))))
(assert (= f7 (f12 f13 f17)))
(assert (= (f12 f13 f17) f7))
(assert (= f25 (f14 f24 f17)))
(assert (= (f14 f24 f17) f25))
(assert (= (f14 f24 f17) f25))
(assert (= (f12 f13 f17) f7))
(assert (= f25 (f14 f24 f17)))
(assert (forall ((?v0 S7)) (= (f14 (f22 f23 f17) ?v0) f17)))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f14 (f22 f23 (f14 f15 ?v0)) ?v1) (f14 f15 (f14 (f22 f23 ?v0) ?v1)))))
(assert (= f17 f25))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f14 f24 ?v0) (f14 f24 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S7) (?v1 S7)) (let ((?v_0 (f14 f24 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S7) (?v1 S2)) (let ((?v_0 (f12 f13 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f14 f16 ?v0) (f14 f16 ?v1)) (= ?v0 ?v1))))
(assert (= (= f17 f17) true))
(assert (forall ((?v0 S7) (?v1 S7)) (= (= (f14 f15 ?v0) (f14 f15 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f9 f19 ?v0) (f9 f19 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f9 f19 ?v0) (f9 f19 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2)) (not (= (f9 f19 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (not (= ?v0 (f9 f19 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f10 f11 ?v0))) (= (f9 (f10 f11 (f9 ?v_0 ?v1)) ?v2) (f9 ?v_0 (f9 (f10 f11 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f9 (f10 f11 ?v0) ?v1) (f9 (f10 f11 ?v1) ?v0))))
(assert (forall ((?v0 S7) (?v1 S7) (?v2 S7)) (= (f14 (f22 f23 (f14 f24 ?v0)) (f14 (f22 f23 (f14 f24 ?v1)) ?v2)) (f14 (f22 f23 (f14 f24 (f14 (f22 f23 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f14 (f22 f23 (f14 f24 ?v0)) (f14 f24 ?v1)) (f14 f24 (f14 (f22 f23 ?v0) ?v1)))))
(assert (forall ((?v0 S7) (?v1 S7)) (= (f14 f24 (f14 (f22 f23 ?v0) ?v1)) (f14 (f22 f23 (f14 f24 ?v0)) (f14 f24 ?v1)))))
(assert (forall ((?v0 S2)) (=> (= (f9 f19 ?v0) f7) false)))
(assert (forall ((?v0 S2)) (=> (= f7 (f9 f19 ?v0)) false)))
(check-sat)
(exit)