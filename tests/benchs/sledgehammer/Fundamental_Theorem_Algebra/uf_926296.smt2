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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 () S2)
(declare-fun f5 () S2)
(declare-fun f6 (S3 S2) S2)
(declare-fun f7 () S3)
(declare-fun f8 (S4 S2) S3)
(declare-fun f9 () S4)
(declare-fun f10 () S2)
(declare-fun f11 () S2)
(declare-fun f12 (S2 S2) S1)
(declare-fun f13 () S4)
(declare-fun f14 (S5 S6) S2)
(declare-fun f15 () S5)
(declare-fun f16 (S7 S6) S6)
(declare-fun f17 () S7)
(declare-fun f18 () S7)
(declare-fun f19 () S6)
(declare-fun f20 () S4)
(declare-fun f21 (S8 S6) S7)
(declare-fun f22 () S8)
(declare-fun f23 () S7)
(declare-fun f24 () S8)
(declare-fun f25 (S6 S6) S1)
(declare-fun f26 () S7)
(declare-fun f27 () S8)
(declare-fun f28 (S6 S6) S1)
(assert (not (= f1 f2)))
(assert (not false))
(assert (= (f3 f4 f5) f1))
(assert (= (f3 (f6 f7 (f6 (f8 f9 f10) f11)) f5) f1))
(assert (= (f12 (f6 (f8 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) f5) (f6 (f8 f20 (f6 f7 (f6 (f8 f9 f10) f11))) f4)) f1))
(assert (forall ((?v0 S2)) (= (f6 (f8 f13 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f6 (f8 f20 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f16 (f21 f22 ?v0) (f16 f23 (f16 f17 (f16 f18 f19)))) (f16 (f21 f24 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f6 (f8 f13 ?v0) (f14 f15 (f16 f17 (f16 f18 f19)))) (f6 (f8 f20 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f16 (f21 f22 ?v0) (f16 f23 (f16 f17 (f16 f18 f19)))) (f16 (f21 f24 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f6 (f8 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v0) (f6 (f8 f20 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f16 (f21 f22 (f16 f23 (f16 f17 (f16 f18 f19)))) ?v0) (f16 (f21 f24 ?v0) ?v0))))
(assert (forall ((?v0 S2)) (= (f6 (f8 f13 (f14 f15 (f16 f17 (f16 f18 f19)))) ?v0) (f6 (f8 f20 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f16 (f21 f22 (f16 f23 (f16 f17 (f16 f18 f19)))) ?v0) (f16 (f21 f24 ?v0) ?v0))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (= (f25 (f16 f26 (f16 (f21 f27 ?v0) ?v1)) ?v2) f1) (and (= (f25 (f16 (f21 f27 ?v1) ?v2) ?v0) f1) (= (f25 ?v0 (f16 (f21 f24 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f3 (f6 f7 (f6 (f8 f9 ?v0) ?v1)) ?v2) f1) (and (= (f3 (f6 (f8 f9 ?v1) ?v2) ?v0) f1) (= (f3 ?v0 (f6 (f8 f20 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2)) (= (f6 (f8 f13 ?v0) (f14 f15 (f16 f18 f19))) ?v0)))
(assert (forall ((?v0 S6)) (= (f16 (f21 f22 ?v0) (f16 f23 (f16 f18 f19))) ?v0)))
(assert (forall ((?v0 S2)) (= (f6 (f8 f13 (f14 f15 (f16 f18 f19))) ?v0) ?v0)))
(assert (forall ((?v0 S6)) (= (f16 (f21 f22 (f16 f23 (f16 f18 f19))) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f28 (f16 f26 (f16 (f21 f27 ?v0) ?v1)) (f16 (f21 f24 (f16 f26 ?v0)) (f16 f26 ?v1))) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f12 (f6 f7 (f6 (f8 f9 ?v0) ?v1)) (f6 (f8 f20 (f6 f7 ?v0)) (f6 f7 ?v1))) f1)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (f28 (f16 f26 (f16 (f21 f27 (f16 (f21 f24 ?v0) ?v1)) (f16 (f21 f24 ?v2) ?v3))) (f16 (f21 f24 (f16 f26 (f16 (f21 f27 ?v0) ?v2))) (f16 f26 (f16 (f21 f27 ?v1) ?v3)))) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (f12 (f6 f7 (f6 (f8 f9 (f6 (f8 f20 ?v0) ?v1)) (f6 (f8 f20 ?v2) ?v3))) (f6 (f8 f20 (f6 f7 (f6 (f8 f9 ?v0) ?v2))) (f6 f7 (f6 (f8 f9 ?v1) ?v3)))) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (= (= (f3 (f6 (f8 f20 (f6 (f8 f13 ?v0) ?v1)) ?v2) (f6 (f8 f20 (f6 (f8 f13 ?v3) ?v1)) ?v4)) f1) (= (f3 ?v2 (f6 (f8 f20 (f6 (f8 f13 (f6 (f8 f9 ?v3) ?v0)) ?v1)) ?v4)) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6) (?v4 S6)) (= (= (f25 (f16 (f21 f24 (f16 (f21 f22 ?v0) ?v1)) ?v2) (f16 (f21 f24 (f16 (f21 f22 ?v3) ?v1)) ?v4)) f1) (= (f25 ?v2 (f16 (f21 f24 (f16 (f21 f22 (f16 (f21 f27 ?v3) ?v0)) ?v1)) ?v4)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (= (= (f3 (f6 (f8 f20 (f6 (f8 f13 ?v0) ?v1)) ?v2) (f6 (f8 f20 (f6 (f8 f13 ?v3) ?v1)) ?v4)) f1) (= (f3 (f6 (f8 f20 (f6 (f8 f13 (f6 (f8 f9 ?v0) ?v3)) ?v1)) ?v2) ?v4) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6) (?v4 S6)) (= (= (f25 (f16 (f21 f24 (f16 (f21 f22 ?v0) ?v1)) ?v2) (f16 (f21 f24 (f16 (f21 f22 ?v3) ?v1)) ?v4)) f1) (= (f25 (f16 (f21 f24 (f16 (f21 f22 (f16 (f21 f27 ?v0) ?v3)) ?v1)) ?v2) ?v4) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (= (= (f12 (f6 (f8 f20 (f6 (f8 f13 ?v0) ?v1)) ?v2) (f6 (f8 f20 (f6 (f8 f13 ?v3) ?v1)) ?v4)) f1) (= (f12 ?v2 (f6 (f8 f20 (f6 (f8 f13 (f6 (f8 f9 ?v3) ?v0)) ?v1)) ?v4)) f1))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6) (?v4 S6)) (= (= (f28 (f16 (f21 f24 (f16 (f21 f22 ?v0) ?v1)) ?v2) (f16 (f21 f24 (f16 (f21 f22 ?v3) ?v1)) ?v4)) f1) (= (f28 ?v2 (f16 (f21 f24 (f16 (f21 f22 (f16 (f21 f27 ?v3) ?v0)) ?v1)) ?v4)) f1))))
(assert (forall ((?v0 S6)) (= (f16 (f21 f27 ?v0) f19) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f16 (f21 f27 (f16 f17 ?v0)) (f16 f17 ?v1)) (f16 f17 (f16 (f21 f27 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (f16 (f21 f24 ?v0) f19) ?v0)))
(assert (forall ((?v0 S6)) (= (f16 (f21 f24 f19) ?v0) ?v0)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f16 (f21 f24 (f16 f17 ?v0)) (f16 f17 ?v1)) (f16 f17 (f16 (f21 f24 ?v0) ?v1)))))
(assert (forall ((?v0 S6)) (= (f16 f17 ?v0) (f16 (f21 f24 ?v0) ?v0))))
(assert (forall ((?v0 S6)) (= (f16 (f21 f22 f19) ?v0) f19)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f25 (f16 f18 ?v0) (f16 f18 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f25 (f16 f18 ?v0) (f16 f18 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (= (= (f25 f19 f19) f1) false))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f16 (f21 f22 (f16 f17 ?v0)) ?v1) (f16 f17 (f16 (f21 f22 ?v0) ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f25 (f16 f17 ?v0) (f16 f17 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f25 (f16 f17 ?v0) (f16 f17 ?v1)) f1) (= (f25 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f28 (f16 f18 ?v0) (f16 f18 ?v1)) f1) (= (f28 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f28 (f16 f18 ?v0) (f16 f18 ?v1)) f1) (= (f28 ?v0 ?v1) f1))))
(assert (= (= (f28 f19 f19) f1) true))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f28 (f16 f17 ?v0) (f16 f17 ?v1)) f1) (= (f28 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f28 (f16 f17 ?v0) (f16 f17 ?v1)) f1) (= (f28 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f16 (f21 f22 (f16 f18 ?v0)) ?v1) (f16 (f21 f24 (f16 f17 (f16 (f21 f22 ?v0) ?v1))) ?v1))))
(assert (forall ((?v0 S6)) (= (= (f28 (f16 f18 ?v0) f19) f1) (= (f25 ?v0 f19) f1))))
(check-sat)
(exit)