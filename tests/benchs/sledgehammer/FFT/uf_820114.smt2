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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 (S5 S6) S3)
(declare-fun f7 (S7 S3) S5)
(declare-fun f8 () S7)
(declare-fun f9 () S3)
(declare-fun f10 () S6)
(declare-fun f11 () S6)
(declare-fun f12 (S8 S6) S1)
(declare-fun f13 (S6) S8)
(declare-fun f14 (S9 S6) S6)
(declare-fun f15 (S10 S6) S9)
(declare-fun f16 () S10)
(declare-fun f17 () S3)
(declare-fun f18 () S3)
(declare-fun f19 (S11 S11) S1)
(declare-fun f20 () S11)
(declare-fun f21 (S12 S6) S11)
(declare-fun f22 (S13 S11) S12)
(declare-fun f23 () S13)
(declare-fun f24 () S6)
(declare-fun f25 () S10)
(declare-fun f26 () S11)
(declare-fun f27 () S6)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f7 f8 f9))) (not (= (f3 (f4 f5 (f6 ?v_0 f10)) (f6 ?v_0 f11)) (ite (= (f12 (f13 f11) f10) f1) (f6 ?v_0 (f14 (f15 f16 f10) f11)) (f6 (f7 f8 (f3 (f4 f5 f17) f9)) (f14 (f15 f16 f11) f10)))))))
(assert (not (= f9 f18)))
(assert (not (= (f12 (f13 f11) f10) f1)))
(assert (not (= f9 f18)))
(assert (not (= (f12 (f13 f11) f10) f1)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S11)) (let ((?v_0 (f22 f23 ?v2))) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (= (f19 f20 ?v2) f1) (= (f19 (f21 ?v_0 ?v0) (f21 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f25 ?v2))) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (= (f12 (f13 f24) ?v2) f1) (= (f12 (f13 (f14 ?v_0 ?v0)) (f14 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S11) (?v1 S6)) (=> (= (f19 f20 ?v0) f1) (= (f19 f20 (f21 (f22 f23 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f13 f24))) (=> (= (f12 ?v_0 ?v0) f1) (= (f12 ?v_0 (f14 (f15 f25 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S11)) (= (f19 ?v0 ?v0) f1)))
(assert (forall ((?v0 S6)) (= (f12 (f13 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S6) (?v2 S6)) (let ((?v_0 (f7 f8 ?v0))) (=> (not (= ?v0 f18)) (=> (= (f12 (f13 ?v1) ?v2) f1) (= (f6 ?v_0 (f14 (f15 f16 ?v2) ?v1)) (f3 (f4 f5 (f6 ?v_0 ?v2)) (f6 ?v_0 ?v1))))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S11)) (let ((?v_0 (f22 f23 ?v2))) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (= (f19 f26 ?v2) f1) (=> (= (f19 ?v2 f20) f1) (= (f19 (f21 ?v_0 ?v1) (f21 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f25 ?v2))) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (= (f12 (f13 f27) ?v2) f1) (=> (= (f12 (f13 ?v2) f24) f1) (= (f12 (f13 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f12 (f13 (f14 (f15 f16 ?v0) ?v1)) ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f16 ?v2))) (=> (= (f12 (f13 ?v0) ?v1) f1) (= (f12 (f13 (f14 ?v_0 ?v1)) (f14 ?v_0 ?v0)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f12 (f13 ?v0) ?v1) f1) (= (f12 (f13 (f14 (f15 f16 ?v0) ?v2)) (f14 (f15 f16 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f15 f16 ?v1))) (=> (= (f12 (f13 ?v0) ?v1) f1) (= (f14 ?v_0 (f14 ?v_0 ?v0)) ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f13 ?v0))) (=> (= (f12 ?v_0 ?v1) f1) (=> (= (f12 ?v_0 ?v2) f1) (= (= (f14 (f15 f16 ?v1) ?v0) (f14 (f15 f16 ?v2) ?v0)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f13 ?v0)) (?v_1 (f15 f16 ?v1))) (=> (= (f12 ?v_0 ?v1) f1) (=> (= (f12 ?v_0 ?v2) f1) (= (f14 (f15 f16 (f14 ?v_1 ?v0)) (f14 (f15 f16 ?v2) ?v0)) (f14 ?v_1 ?v2)))))))
(assert (forall ((?v0 S6)) (= (f12 (f13 f27) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S6)) (= (= (f6 (f7 f8 ?v0) ?v1) f18) (and (= ?v0 f18) (not (= ?v1 f27))))))
(assert (forall ((?v0 S11) (?v1 S6)) (= (= (f21 (f22 f23 ?v0) ?v1) f26) (and (= ?v0 f26) (not (= ?v1 f27))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 (f15 f25 ?v0) ?v1) f27) (and (= ?v0 f27) (not (= ?v1 f27))))))
(assert (forall ((?v0 S6)) (= (f14 (f15 f25 ?v0) f24) ?v0)))
(assert (forall ((?v0 S11)) (= (f21 (f22 f23 ?v0) f24) ?v0)))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 ?v0) f24) ?v0)))
(assert (forall ((?v0 S6)) (= (= (f12 (f13 ?v0) f27) f1) (= ?v0 f27))))
(assert (forall ((?v0 S6)) (= (= (f12 (f13 f27) ?v0) f1) true)))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f14 (f15 f16 ?v0) ?v1) f27) (=> (= (f14 (f15 f16 ?v1) ?v0) f27) (= ?v0 ?v1)))))
(assert (forall ((?v0 S6)) (= (f14 (f15 f16 ?v0) ?v0) f27)))
(assert (forall ((?v0 S6)) (= (f14 (f15 f16 ?v0) f27) ?v0)))
(assert (forall ((?v0 S6)) (= (f14 (f15 f16 f27) ?v0) f27)))
(assert (forall ((?v0 S6)) (= (f6 (f7 f8 f18) ?v0) (ite (= ?v0 f27) f17 f18))))
(assert (forall ((?v0 S6)) (= (f21 (f22 f23 f26) ?v0) (ite (= ?v0 f27) f20 f26))))
(assert (forall ((?v0 S6)) (= (f14 (f15 f25 f27) ?v0) (ite (= ?v0 f27) f24 f27))))
(assert (forall ((?v0 S3)) (= (f6 (f7 f8 ?v0) f27) f17)))
(assert (forall ((?v0 S11)) (= (f21 (f22 f23 ?v0) f27) f20)))
(assert (forall ((?v0 S6)) (= (f14 (f15 f25 ?v0) f27) f24)))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f12 (f13 ?v0) ?v1) f1) (= (f14 (f15 f16 ?v0) ?v1) f27))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f14 (f15 f16 ?v0) ?v1) f27) (= (f12 (f13 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S6)) (=> (not (= ?v0 f18)) (not (= (f6 (f7 f8 ?v0) ?v1) f18)))))
(assert (forall ((?v0 S11) (?v1 S6)) (=> (not (= ?v0 f26)) (not (= (f21 (f22 f23 ?v0) ?v1) f26)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (=> (= (f19 ?v0 ?v1) f1) false) (=> (=> (= (f19 ?v1 ?v0) f1) false) false))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (=> (= (f12 (f13 ?v0) ?v1) f1) false) (=> (=> (= (f12 (f13 ?v1) ?v0) f1) false) false))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f19 ?v0 ?v1) f1) (=> (= (f19 ?v2 ?v0) f1) (= (f19 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f13 ?v2))) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (= (f12 ?v_0 ?v0) f1) (= (f12 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f19 ?v0 ?v1) f1) (=> (= (f19 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (= (f12 (f13 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f19 ?v0 ?v1) f1) (=> (= (f19 ?v1 ?v2) f1) (= (f19 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f13 ?v0))) (=> (= (f12 ?v_0 ?v1) f1) (=> (= (f12 (f13 ?v1) ?v2) f1) (= (f12 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f19 ?v0 ?v1) f1) (=> (= (f19 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (= (f12 (f13 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f19 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f19 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (= ?v0 ?v2) (= (f12 (f13 ?v2) ?v1) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f19 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f19 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f13 ?v0))) (=> (= (f12 ?v_0 ?v1) f1) (=> (= ?v1 ?v2) (= (f12 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= ?v0 ?v1) (=> (= (f19 ?v2 ?v1) f1) (= (f19 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f13 ?v2))) (=> (= ?v0 ?v1) (=> (= (f12 ?v_0 ?v1) f1) (= (f12 ?v_0 ?v0) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= ?v0 ?v1) (=> (= (f19 ?v1 ?v2) f1) (= (f19 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= ?v0 ?v1) (=> (= (f12 (f13 ?v1) ?v2) f1) (= (f12 (f13 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f19 ?v0 ?v1) f1) (= (= (f19 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f12 (f13 ?v0) ?v1) f1) (= (= (f12 (f13 ?v1) ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= ?v0 ?v1) (= (f19 ?v0 ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= ?v0 ?v1) (= (f12 (f13 ?v0) ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= ?v0 ?v1) (and (= (f19 ?v0 ?v1) f1) (= (f19 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= ?v0 ?v1) (and (= (f12 (f13 ?v0) ?v1) f1) (= (f12 (f13 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (or (= (f19 ?v0 ?v1) f1) (= (f19 ?v1 ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (or (= (f12 (f13 ?v0) ?v1) f1) (= (f12 (f13 ?v1) ?v0) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (= (f12 (f13 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f13 ?v0))) (=> (= (f12 ?v_0 ?v1) f1) (=> (= (f12 (f13 ?v1) ?v2) f1) (= (f12 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= ?v0 ?v1) (= (f12 (f13 ?v0) ?v1) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (or (= (f12 (f13 ?v0) ?v1) f1) (= (f12 (f13 ?v1) ?v0) f1))))
(assert (forall ((?v0 S6)) (= (f12 (f13 ?v0) ?v0) f1)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f15 f16 ?v0))) (= (f14 (f15 f16 (f14 ?v_0 ?v1)) ?v2) (f14 (f15 f16 (f14 ?v_0 ?v2)) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S6)) (=> (= (f19 ?v0 ?v1) f1) (=> (= (f19 f26 ?v0) f1) (= (f19 (f21 (f22 f23 ?v0) ?v2) (f21 (f22 f23 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (=> (= (f12 (f13 ?v0) ?v1) f1) (=> (= (f12 (f13 f27) ?v0) f1) (= (f12 (f13 (f14 (f15 f25 ?v0) ?v2)) (f14 (f15 f25 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S11) (?v1 S6)) (=> (= (f19 f26 ?v0) f1) (= (f19 f26 (f21 (f22 f23 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S6) (?v1 S6)) (let ((?v_0 (f13 f27))) (=> (= (f12 ?v_0 ?v0) f1) (= (f12 ?v_0 (f14 (f15 f25 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S6)) (=> (not (= ?v0 f18)) (= (f6 (f7 f8 (f3 (f4 f5 ?v1) ?v0)) ?v2) (f3 (f4 f5 (f6 (f7 f8 ?v1) ?v2)) (f6 (f7 f8 ?v0) ?v2))))))
(assert (forall ((?v0 S6)) (= (f6 (f7 f8 f17) ?v0) f17)))
(assert (forall ((?v0 S6)) (= (f21 (f22 f23 f20) ?v0) f20)))
(assert (forall ((?v0 S6)) (= (f14 (f15 f25 f24) ?v0) f24)))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f13 ?v0))) (=> (= (f12 ?v_0 ?v1) f1) (=> (= (f12 ?v_0 ?v2) f1) (= (= (f12 (f13 (f14 (f15 f16 ?v1) ?v0)) (f14 (f15 f16 ?v2) ?v0)) f1) (= (f12 (f13 ?v1) ?v2) f1)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 f18)) (= (= (f3 (f4 f5 ?v1) ?v0) f17) (= ?v1 ?v0)))))
(assert (forall ((?v0 S3)) (=> (not (= ?v0 f18)) (= (f3 (f4 f5 ?v0) ?v0) f17))))
(check-sat)
(exit)