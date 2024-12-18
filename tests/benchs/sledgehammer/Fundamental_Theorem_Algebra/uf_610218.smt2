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
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 () S2)
(declare-fun f5 (S3 S2) S2)
(declare-fun f6 (S4 S2) S3)
(declare-fun f7 () S4)
(declare-fun f8 () S2)
(declare-fun f9 (S5 S6) S2)
(declare-fun f10 () S5)
(declare-fun f11 () S6)
(declare-fun f12 () S3)
(declare-fun f13 () S4)
(declare-fun f14 () S2)
(declare-fun f15 () S2)
(declare-fun f16 (S2 S2) S1)
(declare-fun f17 (S7 S6) S6)
(declare-fun f18 (S8 S9) S7)
(declare-fun f19 () S8)
(declare-fun f20 () S9)
(declare-fun f21 () S3)
(declare-fun f22 (S10 S6) S7)
(declare-fun f23 () S10)
(declare-fun f24 () S10)
(declare-fun f25 () S6)
(declare-fun f26 (S11 S11) S1)
(declare-fun f27 () S11)
(declare-fun f28 (S12 S11) S11)
(declare-fun f29 (S13 S11) S12)
(declare-fun f30 () S13)
(declare-fun f31 () S11)
(declare-fun f32 () S13)
(declare-fun f33 () S6)
(declare-fun f34 (S11 S11) S1)
(declare-fun f35 () S12)
(assert (not (= f1 f2)))
(assert (not (= (f3 f4 (f5 (f6 f7 (f5 (f6 f7 f8) (f9 f10 f11))) (f5 f12 (f5 (f6 f13 f14) f15)))) f1)))
(assert (= (f16 f4 (f5 f12 (f5 (f6 f13 f14) f15))) f1))
(assert (= (f16 f4 (f9 f10 f11)) f1))
(assert (= (f16 f4 (f9 f10 f11)) f1))
(assert (= (f16 f4 (f5 f12 (f5 (f6 f13 f14) f15))) f1))
(assert (forall ((?v0 S2)) (= (f3 f4 (f5 (f6 f7 f8) (f5 f12 ?v0))) f1)))
(assert (forall ((?v0 S6)) (=> (= (f16 (f9 f10 ?v0) f14) f1) (= (f16 (f9 f10 (f17 (f18 f19 f20) ?v0)) f15) f1))))
(assert (forall ((?v0 S2)) (not (= (f3 (f5 (f6 f7 (f5 f12 ?v0)) f8) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f3 (f5 f21 ?v0) ?v1) f1) (=> (= (f3 (f5 f21 ?v2) ?v3) f1) (= (f3 (f5 f21 (f5 (f6 f7 ?v0) ?v2)) (f5 (f6 f7 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6) (?v3 S2)) (=> (= (f3 (f9 f10 ?v0) ?v1) f1) (=> (= (f3 (f9 f10 ?v2) ?v3) f1) (= (f3 (f9 f10 (f17 (f22 f23 ?v0) ?v2)) (f5 (f6 f7 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S6) (?v1 S2) (?v2 S6) (?v3 S2)) (=> (= (f3 (f9 f10 ?v0) ?v1) f1) (=> (= (f3 (f9 f10 ?v2) ?v3) f1) (= (f3 (f9 f10 (f17 (f22 f24 ?v0) ?v2)) (f5 (f6 f13 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f3 (f5 f21 ?v0) ?v1) f1) (=> (= (f3 (f5 f21 ?v2) ?v3) f1) (= (f3 (f5 f21 (f5 (f6 f13 ?v0) ?v2)) (f5 (f6 f13 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S6)) (= (= (f3 f4 (f9 f10 ?v0)) f1) (not (= ?v0 f25)))))
(assert (forall ((?v0 S2)) (= (= (f3 f4 (f5 f21 ?v0)) f1) (not (= ?v0 f4)))))
(assert (= (f3 f4 (f5 (f6 f7 f8) f8)) f1))
(assert (= (f26 f27 (f28 (f29 f30 f31) f31)) f1))
(assert (forall ((?v0 S11) (?v1 S11)) (not (= (f26 (f28 (f29 f30 (f28 (f29 f32 ?v0) ?v0)) (f28 (f29 f32 ?v1) ?v1)) f27) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (not (= (f3 (f5 (f6 f7 (f5 (f6 f13 ?v0) ?v0)) (f5 (f6 f13 ?v1) ?v1)) f4) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f26 f27 (f28 (f29 f30 (f28 (f29 f32 ?v0) ?v0)) (f28 (f29 f32 ?v1) ?v1))) f1) (or (not (= ?v0 f27)) (not (= ?v1 f27))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 f4 (f5 (f6 f7 (f5 (f6 f13 ?v0) ?v0)) (f5 (f6 f13 ?v1) ?v1))) f1) (or (not (= ?v0 f4)) (not (= ?v1 f4))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f5 (f6 f7 (f5 (f6 f13 ?v0) ?v0)) (f5 (f6 f13 ?v1) ?v1)) f4) (and (= ?v0 f4) (= ?v1 f4)))))
(assert (= (f9 f10 f33) f8))
(assert (= (f5 f21 f8) f8))
(assert (forall ((?v0 S6)) (not (= (f3 (f9 f10 ?v0) f4) f1))))
(assert (forall ((?v0 S2)) (not (= (f3 (f5 f21 ?v0) f4) f1))))
(assert (exists ((?v0 S2)) (and (= (f3 f4 ?v0) f1) (forall ((?v1 S6)) (=> (= (f16 (f9 f10 ?v1) f14) f1) (= (f16 (f9 f10 (f17 (f18 f19 f20) ?v1)) ?v0) f1))))))
(assert (=> (forall ((?v0 S2)) (=> (forall ((?v1 S6)) (=> (= (f16 (f9 f10 ?v1) f14) f1) (= (f16 (f9 f10 (f17 (f18 f19 f20) ?v1)) ?v0) f1))) false)) false))
(assert (forall ((?v0 S2)) (= (f16 ?v0 ?v0) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f16 ?v0 ?v1) f1) (= (f16 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f16 ?v0 ?v1) f1) (=> (= (f16 ?v1 ?v2) f1) (= (f16 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f16 ?v0 ?v1) f1) (=> (= (f16 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2)) (= (f5 f21 ?v0) (f5 f12 ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f16 ?v0 ?v1) f1) (or (= (f3 ?v0 ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 ?v0 ?v1) f1) (and (= (f16 ?v0 ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f7 ?v2))) (=> (= (f16 ?v0 ?v1) f1) (= (f16 (f5 ?v_0 ?v0) (f5 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f16 (f9 f10 ?v0) (f5 (f6 f7 (f9 f10 (f17 (f22 f23 ?v0) ?v1))) (f9 f10 ?v1))) f1)))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f26 ?v0 ?v1) f1) false) (=> (=> (= (f26 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 ?v0 ?v1) f1) false) (=> (=> (= (f3 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (or (and (= (f16 f4 ?v0) f1) (= (f16 ?v1 f4) f1)) (and (= (f16 ?v0 f4) f1) (= (f16 f4 ?v1) f1))) (= (f16 (f5 (f6 f13 ?v0) ?v1) f4) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (or (and (= (f34 f27 ?v0) f1) (= (f34 ?v1 f27) f1)) (and (= (f34 ?v0 f27) f1) (= (f34 f27 ?v1) f1))) (= (f34 (f28 (f29 f32 ?v0) ?v1) f27) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (or (and (= (f16 f4 ?v0) f1) (= (f16 f4 ?v1) f1)) (and (= (f16 ?v0 f4) f1) (= (f16 ?v1 f4) f1))) (= (f16 f4 (f5 (f6 f13 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (or (and (= (f34 f27 ?v0) f1) (= (f34 f27 ?v1) f1)) (and (= (f34 ?v0 f27) f1) (= (f34 ?v1 f27) f1))) (= (f34 f27 (f28 (f29 f32 ?v0) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f16 ?v0 ?v1) f1) (=> (= (f16 ?v2 ?v3) f1) (=> (= (f16 f4 ?v1) f1) (=> (= (f16 f4 ?v2) f1) (= (f16 (f5 (f6 f13 ?v0) ?v2) (f5 (f6 f13 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f34 ?v2 ?v3) f1) (=> (= (f34 f27 ?v1) f1) (=> (= (f34 f27 ?v2) f1) (= (f34 (f28 (f29 f32 ?v0) ?v2) (f28 (f29 f32 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f16 ?v0 ?v1) f1) (=> (= (f16 ?v2 ?v3) f1) (=> (= (f16 f4 ?v0) f1) (=> (= (f16 f4 ?v2) f1) (= (f16 (f5 (f6 f13 ?v0) ?v2) (f5 (f6 f13 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f34 ?v2 ?v3) f1) (=> (= (f34 f27 ?v0) f1) (=> (= (f34 f27 ?v2) f1) (= (f34 (f28 (f29 f32 ?v0) ?v2) (f28 (f29 f32 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v2))) (=> (= (f16 ?v0 ?v1) f1) (=> (= (f16 ?v2 f4) f1) (= (f16 (f5 ?v_0 ?v1) (f5 ?v_0 ?v0)) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v2))) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f34 ?v2 f27) f1) (= (f34 (f28 ?v_0 ?v1) (f28 ?v_0 ?v0)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f16 ?v0 ?v1) f1) (=> (= (f16 ?v2 f4) f1) (= (f16 (f5 (f6 f13 ?v1) ?v2) (f5 (f6 f13 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f34 ?v2 f27) f1) (= (f34 (f28 (f29 f32 ?v1) ?v2) (f28 (f29 f32 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v2))) (=> (= (f16 ?v0 ?v1) f1) (=> (= (f16 f4 ?v2) f1) (= (f16 (f5 ?v_0 ?v0) (f5 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v2))) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f34 f27 ?v2) f1) (= (f34 (f28 ?v_0 ?v0) (f28 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v2))) (=> (= (f16 ?v0 ?v1) f1) (=> (= (f16 f4 ?v2) f1) (= (f16 (f5 ?v_0 ?v0) (f5 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v2))) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f34 f27 ?v2) f1) (= (f34 (f28 ?v_0 ?v0) (f28 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f16 ?v0 ?v1) f1) (=> (= (f16 f4 ?v2) f1) (= (f16 (f5 (f6 f13 ?v0) ?v2) (f5 (f6 f13 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f34 f27 ?v2) f1) (= (f34 (f28 (f29 f32 ?v0) ?v2) (f28 (f29 f32 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f16 ?v0 f4) f1) (=> (= (f16 ?v1 f4) f1) (= (f16 f4 (f5 (f6 f13 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f34 ?v0 f27) f1) (=> (= (f34 ?v1 f27) f1) (= (f34 f27 (f28 (f29 f32 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f16 ?v0 f4) f1) (=> (= (f16 f4 ?v1) f1) (= (f16 (f5 (f6 f13 ?v0) ?v1) f4) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f34 ?v0 f27) f1) (=> (= (f34 f27 ?v1) f1) (= (f34 (f28 (f29 f32 ?v0) ?v1) f27) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f16 f4 ?v0) f1) (=> (= (f16 ?v1 f4) f1) (= (f16 (f5 (f6 f13 ?v1) ?v0) f4) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f34 f27 ?v0) f1) (=> (= (f34 ?v1 f27) f1) (= (f34 (f28 (f29 f32 ?v1) ?v0) f27) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f16 f4 ?v0) f1) (=> (= (f16 ?v1 f4) f1) (= (f16 (f5 (f6 f13 ?v0) ?v1) f4) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f34 f27 ?v0) f1) (=> (= (f34 ?v1 f27) f1) (= (f34 (f28 (f29 f32 ?v0) ?v1) f27) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f16 f4 ?v0) f1) (=> (= (f16 f4 ?v1) f1) (= (f16 f4 (f5 (f6 f13 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f34 f27 ?v0) f1) (=> (= (f34 f27 ?v1) f1) (= (f34 f27 (f28 (f29 f32 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f16 (f5 (f6 f13 ?v0) ?v1) f4) f1) (or (and (= (f16 f4 ?v0) f1) (= (f16 ?v1 f4) f1)) (and (= (f16 ?v0 f4) f1) (= (f16 f4 ?v1) f1))))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f34 (f28 (f29 f32 ?v0) ?v1) f27) f1) (or (and (= (f34 f27 ?v0) f1) (= (f34 ?v1 f27) f1)) (and (= (f34 ?v0 f27) f1) (= (f34 f27 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f16 f4 (f5 (f6 f13 ?v0) ?v1)) f1) (or (and (= (f16 f4 ?v0) f1) (= (f16 f4 ?v1) f1)) (and (= (f16 ?v0 f4) f1) (= (f16 ?v1 f4) f1))))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f34 f27 (f28 (f29 f32 ?v0) ?v1)) f1) (or (and (= (f34 f27 ?v0) f1) (= (f34 f27 ?v1) f1)) (and (= (f34 ?v0 f27) f1) (= (f34 ?v1 f27) f1))))))
(assert (forall ((?v0 S2)) (= (f16 f4 (f5 (f6 f13 ?v0) ?v0)) f1)))
(assert (forall ((?v0 S11)) (= (f34 f27 (f28 (f29 f32 ?v0) ?v0)) f1)))
(assert (= (f16 f4 f8) f1))
(assert (= (f34 f27 f31) f1))
(assert (not (= (f16 f8 f4) f1)))
(assert (not (= (f34 f31 f27) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (= (f5 (f6 f13 (f5 ?v_0 ?v1)) ?v2) (f5 ?v_0 (f5 (f6 f13 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f5 (f6 f13 ?v0) ?v1) (f5 (f6 f13 ?v1) ?v0))))
(assert (forall ((?v0 S6)) (= (f16 f4 (f9 f10 ?v0)) f1)))
(assert (forall ((?v0 S2)) (= (f16 f4 (f5 f21 ?v0)) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (=> (= (f16 (f5 ?v_0 ?v1) (f5 ?v_0 ?v2)) f1) (=> (= (f3 f4 ?v0) f1) (= (f16 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v0))) (=> (= (f34 (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) f1) (=> (= (f26 f27 ?v0) f1) (= (f34 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f16 (f5 (f6 f13 ?v0) ?v1) (f5 (f6 f13 ?v2) ?v1)) f1) (=> (= (f3 f4 ?v1) f1) (= (f16 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f34 (f28 (f29 f32 ?v0) ?v1) (f28 (f29 f32 ?v2) ?v1)) f1) (=> (= (f26 f27 ?v1) f1) (= (f34 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (=> (= (f3 (f5 ?v_0 ?v1) (f5 ?v_0 ?v2)) f1) (=> (= (f16 f4 ?v0) f1) (= (f3 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v0))) (=> (= (f26 (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) f1) (=> (= (f34 f27 ?v0) f1) (= (f26 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (=> (= (f3 (f5 ?v_0 ?v1) (f5 ?v_0 ?v2)) f1) (=> (= (f16 f4 ?v0) f1) (= (f3 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v0))) (=> (= (f26 (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) f1) (=> (= (f34 f27 ?v0) f1) (= (f26 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f5 (f6 f13 ?v0) ?v1) (f5 (f6 f13 ?v2) ?v1)) f1) (=> (= (f16 f4 ?v1) f1) (= (f3 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f26 (f28 (f29 f32 ?v0) ?v1) (f28 (f29 f32 ?v2) ?v1)) f1) (=> (= (f34 f27 ?v1) f1) (= (f26 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 (f5 (f6 f13 ?v0) ?v1) (f5 (f6 f13 ?v2) ?v1)) f1) (=> (= (f16 f4 ?v1) f1) (= (f3 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f26 (f28 (f29 f32 ?v0) ?v1) (f28 (f29 f32 ?v2) ?v1)) f1) (=> (= (f34 f27 ?v1) f1) (= (f26 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f16 ?v0 ?v1) f1) (=> (= (f3 ?v2 ?v3) f1) (=> (= (f3 f4 ?v0) f1) (=> (= (f16 f4 ?v2) f1) (= (f3 (f5 (f6 f13 ?v0) ?v2) (f5 (f6 f13 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f26 ?v2 ?v3) f1) (=> (= (f26 f27 ?v0) f1) (=> (= (f34 f27 ?v2) f1) (= (f26 (f28 (f29 f32 ?v0) ?v2) (f28 (f29 f32 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f16 ?v2 ?v3) f1) (=> (= (f16 f4 ?v0) f1) (=> (= (f3 f4 ?v2) f1) (= (f3 (f5 (f6 f13 ?v0) ?v2) (f5 (f6 f13 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (=> (= (f26 ?v0 ?v1) f1) (=> (= (f34 ?v2 ?v3) f1) (=> (= (f34 f27 ?v0) f1) (=> (= (f26 f27 ?v2) f1) (= (f26 (f28 (f29 f32 ?v0) ?v2) (f28 (f29 f32 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v2 ?v3) f1) (=> (= (f16 f4 ?v0) f1) (=> (= (f16 f4 ?v2) f1) (= (f3 (f5 (f6 f13 ?v0) ?v2) (f5 (f6 f13 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (=> (= (f26 ?v0 ?v1) f1) (=> (= (f26 ?v2 ?v3) f1) (=> (= (f34 f27 ?v0) f1) (=> (= (f34 f27 ?v2) f1) (= (f26 (f28 (f29 f32 ?v0) ?v2) (f28 (f29 f32 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v2 ?v3) f1) (=> (= (f3 f4 ?v1) f1) (=> (= (f16 f4 ?v2) f1) (= (f3 (f5 (f6 f13 ?v0) ?v2) (f5 (f6 f13 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (=> (= (f26 ?v0 ?v1) f1) (=> (= (f26 ?v2 ?v3) f1) (=> (= (f26 f27 ?v1) f1) (=> (= (f34 f27 ?v2) f1) (= (f26 (f28 (f29 f32 ?v0) ?v2) (f28 (f29 f32 ?v1) ?v3)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (=> (= (f3 ?v0 f4) f1) (= (= (f16 (f5 ?v_0 ?v1) (f5 ?v_0 ?v2)) f1) (= (f16 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v0))) (=> (= (f26 ?v0 f27) f1) (= (= (f34 (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) f1) (= (f34 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (=> (= (f3 f4 ?v0) f1) (= (= (f16 (f5 ?v_0 ?v1) (f5 ?v_0 ?v2)) f1) (= (f16 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v0))) (=> (= (f26 f27 ?v0) f1) (= (= (f34 (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) f1) (= (f34 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f34 (f28 (f29 f30 (f28 (f29 f32 ?v0) ?v0)) (f28 (f29 f32 ?v1) ?v1)) f27) f1) (and (= ?v0 f27) (= ?v1 f27)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f16 (f5 (f6 f7 (f5 (f6 f13 ?v0) ?v0)) (f5 (f6 f13 ?v1) ?v1)) f4) f1) (and (= ?v0 f4) (= ?v1 f4)))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f34 f27 (f28 (f29 f30 (f28 (f29 f32 ?v0) ?v0)) (f28 (f29 f32 ?v1) ?v1))) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f16 f4 (f5 (f6 f7 (f5 (f6 f13 ?v0) ?v0)) (f5 (f6 f13 ?v1) ?v1))) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f16 f4 ?v0) f1) (=> (= (f16 f4 ?v1) f1) (=> (= (f16 ?v1 f8) f1) (= (f16 (f5 (f6 f13 ?v1) ?v0) ?v0) f1))))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f34 f27 ?v0) f1) (=> (= (f34 f27 ?v1) f1) (=> (= (f34 ?v1 f31) f1) (= (f34 (f28 (f29 f32 ?v1) ?v0) ?v0) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f16 f4 ?v0) f1) (=> (= (f16 f4 ?v1) f1) (=> (= (f16 ?v1 f8) f1) (= (f16 (f5 (f6 f13 ?v0) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f34 f27 ?v0) f1) (=> (= (f34 f27 ?v1) f1) (=> (= (f34 ?v1 f31) f1) (= (f34 (f28 (f29 f32 ?v0) ?v1) ?v0) f1))))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (and (or (= (f34 f27 ?v0) f1) (= (f34 ?v0 f27) f1)) (or (= (f34 f27 ?v1) f1) (= (f34 ?v1 f27) f1))) (= (f28 f35 (f28 (f29 f32 ?v0) ?v1)) (f28 (f29 f32 (f28 f35 ?v0)) (f28 f35 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (and (or (= (f16 f4 ?v0) f1) (= (f16 ?v0 f4) f1)) (or (= (f16 f4 ?v1) f1) (= (f16 ?v1 f4) f1))) (= (f5 f12 (f5 (f6 f13 ?v0) ?v1)) (f5 (f6 f13 (f5 f12 ?v0)) (f5 f12 ?v1))))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f34 f27 ?v0) f1) (= (f28 (f29 f32 (f28 f35 ?v1)) ?v0) (f28 f35 (f28 (f29 f32 ?v1) ?v0))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f16 f4 ?v0) f1) (= (f5 (f6 f13 (f5 f12 ?v1)) ?v0) (f5 f12 (f5 (f6 f13 ?v1) ?v0))))))
(assert (forall ((?v0 S6)) (= (= (f16 (f9 f10 ?v0) f4) f1) (= ?v0 f25))))
(assert (forall ((?v0 S2)) (= (= (f16 (f5 f21 ?v0) f4) f1) (= ?v0 f4))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f16 (f9 f10 (f17 (f22 f24 ?v0) ?v1)) (f5 (f6 f13 (f9 f10 ?v0)) (f9 f10 ?v1))) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f16 (f5 f21 (f5 (f6 f13 ?v0) ?v1)) (f5 (f6 f13 (f5 f21 ?v0)) (f5 f21 ?v1))) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (=> (= (f3 f4 ?v0) f1) (= (= (f16 (f5 ?v_0 ?v1) (f5 ?v_0 ?v2)) f1) (= (f16 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 f4 ?v0) f1) (= (= (f16 (f5 (f6 f13 ?v1) ?v0) (f5 (f6 f13 ?v2) ?v0)) f1) (= (f16 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f16 (f5 f21 (f5 (f6 f7 ?v0) ?v1)) (f5 (f6 f7 (f5 f21 ?v0)) (f5 f21 ?v1))) f1)))
(assert (forall ((?v0 S6) (?v1 S6)) (= (f16 (f9 f10 (f17 (f22 f23 ?v0) ?v1)) (f5 (f6 f7 (f9 f10 ?v0)) (f9 f10 ?v1))) f1)))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (= (f17 (f22 f24 ?v0) ?v1) f25) (or (= ?v0 f25) (= ?v1 f25)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f5 (f6 f13 ?v0) ?v1) f4) (or (= ?v0 f4) (= ?v1 f4)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f28 (f29 f32 ?v0) ?v1) f27) (or (= ?v0 f27) (= ?v1 f27)))))
(assert (forall ((?v0 S6) (?v1 S6)) (=> (not (= ?v0 f25)) (=> (not (= ?v1 f25)) (not (= (f17 (f22 f24 ?v0) ?v1) f25))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 f4)) (=> (not (= ?v1 f4)) (not (= (f5 (f6 f13 ?v0) ?v1) f4))))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (not (= ?v0 f27)) (=> (not (= ?v1 f27)) (not (= (f28 (f29 f32 ?v0) ?v1) f27))))))
(assert (forall ((?v0 S6) (?v1 S6)) (= (= (f17 (f22 f24 ?v0) ?v1) f25) (or (= ?v0 f25) (= ?v1 f25)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f5 (f6 f13 ?v0) ?v1) f4) (or (= ?v0 f4) (= ?v1 f4)))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f28 (f29 f32 ?v0) ?v1) f27) (or (= ?v0 f27) (= ?v1 f27)))))
(assert (forall ((?v0 S6)) (= (f17 (f22 f24 ?v0) f25) f25)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f13 ?v0) f4) f4)))
(assert (forall ((?v0 S6)) (= (f17 (f22 f24 ?v0) f25) f25)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f13 ?v0) f4) f4)))
(assert (forall ((?v0 S6)) (= (f17 (f22 f24 ?v0) f25) f25)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f13 ?v0) f4) f4)))
(assert (forall ((?v0 S11)) (= (f28 (f29 f32 ?v0) f27) f27)))
(assert (forall ((?v0 S6)) (= (f17 (f22 f24 f25) ?v0) f25)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f13 f4) ?v0) f4)))
(assert (forall ((?v0 S6)) (= (f17 (f22 f24 f25) ?v0) f25)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f13 f4) ?v0) f4)))
(assert (forall ((?v0 S6)) (= (f17 (f22 f24 f25) ?v0) f25)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f13 f4) ?v0) f4)))
(assert (forall ((?v0 S11)) (= (f28 (f29 f32 f27) ?v0) f27)))
(assert (not (= f25 f33)))
(assert (not (= f4 f8)))
(assert (not (= f27 f31)))
(assert (not (= f33 f25)))
(assert (not (= f8 f4)))
(assert (not (= f31 f27)))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (= (f28 (f29 f30 (f28 (f29 f32 ?v0) ?v1)) (f28 (f29 f30 (f28 (f29 f32 ?v2) ?v1)) ?v3)) (f28 (f29 f30 (f28 (f29 f32 (f28 (f29 f30 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (f5 (f6 f7 (f5 (f6 f13 ?v0) ?v1)) (f5 (f6 f7 (f5 (f6 f13 ?v2) ?v1)) ?v3)) (f5 (f6 f7 (f5 (f6 f13 (f5 (f6 f7 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6) (?v3 S6)) (= (f17 (f22 f23 (f17 (f22 f24 ?v0) ?v1)) (f17 (f22 f23 (f17 (f22 f24 ?v2) ?v1)) ?v3)) (f17 (f22 f23 (f17 (f22 f24 (f17 (f22 f23 ?v0) ?v2)) ?v1)) ?v3))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f5 (f6 f13 (f5 (f6 f7 ?v0) ?v1)) ?v2) (f5 (f6 f7 (f5 (f6 f13 ?v0) ?v2)) (f5 (f6 f13 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f17 (f22 f24 (f17 (f22 f23 ?v0) ?v1)) ?v2) (f17 (f22 f23 (f17 (f22 f24 ?v0) ?v2)) (f17 (f22 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f5 (f6 f13 (f5 (f6 f7 ?v0) ?v1)) ?v2) (f5 (f6 f7 (f5 (f6 f13 ?v0) ?v2)) (f5 (f6 f13 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f17 (f22 f24 (f17 (f22 f23 ?v0) ?v1)) ?v2) (f17 (f22 f23 (f17 (f22 f24 ?v0) ?v2)) (f17 (f22 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (= (f28 (f29 f32 (f28 (f29 f30 ?v0) ?v1)) ?v2) (f28 (f29 f30 (f28 (f29 f32 ?v0) ?v2)) (f28 (f29 f32 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f5 (f6 f13 (f5 (f6 f7 ?v0) ?v1)) ?v2) (f5 (f6 f7 (f5 (f6 f13 ?v0) ?v2)) (f5 (f6 f13 ?v1) ?v2)))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (= (f17 (f22 f24 (f17 (f22 f23 ?v0) ?v1)) ?v2) (f17 (f22 f23 (f17 (f22 f24 ?v0) ?v2)) (f17 (f22 f24 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (= (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f5 (f6 f7 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f22 f24 ?v0))) (= (f17 ?v_0 (f17 (f22 f23 ?v1) ?v2)) (f17 (f22 f23 (f17 ?v_0 ?v1)) (f17 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (= (f5 ?v_0 (f5 (f6 f7 ?v1) ?v2)) (f5 (f6 f7 (f5 ?v_0 ?v1)) (f5 ?v_0 ?v2))))))
(assert (forall ((?v0 S6) (?v1 S6) (?v2 S6)) (let ((?v_0 (f22 f24 ?v0))) (= (f17 ?v_0 (f17 (f22 f23 ?v1) ?v2)) (f17 (f22 f23 (f17 ?v_0 ?v1)) (f17 ?v_0 ?v2))))))
(assert (forall ((?v0 S11)) (let ((?v_0 (f28 f35 ?v0))) (= (f28 (f29 f32 ?v_0) ?v_0) (f28 (f29 f32 ?v0) ?v0)))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f12 ?v0))) (= (f5 (f6 f13 ?v_0) ?v_0) (f5 (f6 f13 ?v0) ?v0)))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (f28 f35 (f28 (f29 f32 ?v0) ?v1)) (f28 (f29 f32 (f28 f35 ?v0)) (f28 f35 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f5 f12 (f5 (f6 f13 ?v0) ?v1)) (f5 (f6 f13 (f5 f12 ?v0)) (f5 f12 ?v1)))))
(assert (= (f28 f35 f31) f31))
(assert (= (f5 f12 f8) f8))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (=> (not (= ?v0 f4)) (= (= (f5 ?v_0 ?v1) (f5 ?v_0 ?v2)) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (not (= ?v0 f4)) (= (= (f5 (f6 f13 ?v1) ?v0) (f5 (f6 f13 ?v2) ?v0)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (=> (= (f16 ?v0 ?v1) f1) (=> (= (f16 ?v2 ?v1) f1) (=> (= (f16 f4 ?v3) f1) (=> (= (f16 f4 ?v4) f1) (=> (= (f5 (f6 f7 ?v3) ?v4) f8) (= (f16 (f5 (f6 f7 (f5 (f6 f13 ?v3) ?v0)) (f5 (f6 f13 ?v4) ?v2)) ?v1) f1))))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11) (?v4 S11)) (=> (= (f34 ?v0 ?v1) f1) (=> (= (f34 ?v2 ?v1) f1) (=> (= (f34 f27 ?v3) f1) (=> (= (f34 f27 ?v4) f1) (=> (= (f28 (f29 f30 ?v3) ?v4) f31) (= (f34 (f28 (f29 f30 (f28 (f29 f32 ?v3) ?v0)) (f28 (f29 f32 ?v4) ?v2)) ?v1) f1))))))))
(assert (not (= f4 f8)))
(assert (forall ((?v0 S2)) (= (f5 (f6 f13 f8) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f5 (f6 f13 (f5 (f6 f7 ?v0) ?v1)) ?v2) (f5 (f6 f7 (f5 (f6 f13 ?v0) ?v2)) (f5 (f6 f13 ?v1) ?v2)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f9 f10 ?v0))) (= (f5 f12 ?v_0) ?v_0))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f5 f21 ?v0))) (= (f5 f12 ?v_0) ?v_0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2) (?v4 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v2 ?v1) f1) (=> (= (f16 f4 ?v3) f1) (=> (= (f16 f4 ?v4) f1) (=> (= (f5 (f6 f7 ?v3) ?v4) f8) (= (f3 (f5 (f6 f7 (f5 (f6 f13 ?v3) ?v0)) (f5 (f6 f13 ?v4) ?v2)) ?v1) f1))))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11) (?v4 S11)) (=> (= (f26 ?v0 ?v1) f1) (=> (= (f26 ?v2 ?v1) f1) (=> (= (f34 f27 ?v3) f1) (=> (= (f34 f27 ?v4) f1) (=> (= (f28 (f29 f30 ?v3) ?v4) f31) (= (f26 (f28 (f29 f30 (f28 (f29 f32 ?v3) ?v0)) (f28 (f29 f32 ?v4) ?v2)) ?v1) f1))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v2))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v2 f4) f1) (= (f3 (f5 ?v_0 ?v1) (f5 ?v_0 ?v0)) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v2))) (=> (= (f26 ?v0 ?v1) f1) (=> (= (f26 ?v2 f27) f1) (= (f26 (f28 ?v_0 ?v1) (f28 ?v_0 ?v0)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v2 f4) f1) (= (f3 (f5 (f6 f13 ?v1) ?v2) (f5 (f6 f13 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f26 ?v0 ?v1) f1) (=> (= (f26 ?v2 f27) f1) (= (f26 (f28 (f29 f32 ?v1) ?v2) (f28 (f29 f32 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v2))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 f4 ?v2) f1) (= (f3 (f5 ?v_0 ?v0) (f5 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v2))) (=> (= (f26 ?v0 ?v1) f1) (=> (= (f26 f27 ?v2) f1) (= (f26 (f28 ?v_0 ?v0) (f28 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v2))) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 f4 ?v2) f1) (= (f3 (f5 ?v_0 ?v0) (f5 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v2))) (=> (= (f26 ?v0 ?v1) f1) (=> (= (f26 f27 ?v2) f1) (= (f26 (f28 ?v_0 ?v0) (f28 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 f4 ?v2) f1) (= (f3 (f5 (f6 f13 ?v0) ?v2) (f5 (f6 f13 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f26 ?v0 ?v1) f1) (=> (= (f26 f27 ?v2) f1) (= (f26 (f28 (f29 f32 ?v0) ?v2) (f28 (f29 f32 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 f4) f1) (=> (= (f3 ?v1 f4) f1) (= (f3 f4 (f5 (f6 f13 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f26 ?v0 f27) f1) (=> (= (f26 ?v1 f27) f1) (= (f26 f27 (f28 (f29 f32 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 f4) f1) (=> (= (f3 f4 ?v1) f1) (= (f3 (f5 (f6 f13 ?v0) ?v1) f4) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f26 ?v0 f27) f1) (=> (= (f26 f27 ?v1) f1) (= (f26 (f28 (f29 f32 ?v0) ?v1) f27) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (=> (= (f3 ?v0 f4) f1) (= (= (f3 (f5 ?v_0 ?v1) (f5 ?v_0 ?v2)) f1) (= (f3 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v0))) (=> (= (f26 ?v0 f27) f1) (= (= (f26 (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) f1) (= (f26 ?v2 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f4 (f5 (f6 f13 ?v0) ?v1)) f1) (=> (= (f3 f4 ?v1) f1) (= (f3 f4 ?v0) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f26 f27 (f28 (f29 f32 ?v0) ?v1)) f1) (=> (= (f26 f27 ?v1) f1) (= (f26 f27 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f4 (f5 (f6 f13 ?v0) ?v1)) f1) (=> (= (f3 f4 ?v0) f1) (= (f3 f4 ?v1) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f26 f27 (f28 (f29 f32 ?v0) ?v1)) f1) (=> (= (f26 f27 ?v0) f1) (= (f26 f27 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f4 ?v0) f1) (=> (= (f3 ?v1 f4) f1) (= (f3 (f5 (f6 f13 ?v1) ?v0) f4) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f26 f27 ?v0) f1) (=> (= (f26 ?v1 f27) f1) (= (f26 (f28 (f29 f32 ?v1) ?v0) f27) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f4 ?v0) f1) (=> (= (f3 ?v1 f4) f1) (= (f3 (f5 (f6 f13 ?v0) ?v1) f4) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f26 f27 ?v0) f1) (=> (= (f26 ?v1 f27) f1) (= (f26 (f28 (f29 f32 ?v0) ?v1) f27) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f4 ?v0) f1) (=> (= (f3 f4 ?v1) f1) (= (f3 f4 (f5 (f6 f13 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f26 f27 ?v0) f1) (=> (= (f26 f27 ?v1) f1) (= (f26 f27 (f28 (f29 f32 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (=> (= (f3 f4 ?v0) f1) (= (= (f3 (f5 ?v_0 ?v1) (f5 ?v_0 ?v2)) f1) (= (f3 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v0))) (=> (= (f26 f27 ?v0) f1) (= (= (f26 (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) f1) (= (f26 ?v1 ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f6 f13 ?v0))) (= (= (f3 (f5 ?v_0 ?v1) (f5 ?v_0 ?v2)) f1) (or (and (= (f3 f4 ?v0) f1) (= (f3 ?v1 ?v2) f1)) (and (= (f3 ?v0 f4) f1) (= (f3 ?v2 ?v1) f1)))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (let ((?v_0 (f29 f32 ?v0))) (= (= (f26 (f28 ?v_0 ?v1) (f28 ?v_0 ?v2)) f1) (or (and (= (f26 f27 ?v0) f1) (= (f26 ?v1 ?v2) f1)) (and (= (f26 ?v0 f27) f1) (= (f26 ?v2 ?v1) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f3 (f5 (f6 f13 ?v0) ?v1) (f5 (f6 f13 ?v2) ?v1)) f1) (or (and (= (f3 f4 ?v1) f1) (= (f3 ?v0 ?v2) f1)) (and (= (f3 ?v1 f4) f1) (= (f3 ?v2 ?v0) f1))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (= (= (f26 (f28 (f29 f32 ?v0) ?v1) (f28 (f29 f32 ?v2) ?v1)) f1) (or (and (= (f26 f27 ?v1) f1) (= (f26 ?v0 ?v2) f1)) (and (= (f26 ?v1 f27) f1) (= (f26 ?v2 ?v0) f1))))))
(assert (forall ((?v0 S2)) (not (= (f3 (f5 (f6 f13 ?v0) ?v0) f4) f1))))
(assert (forall ((?v0 S11)) (not (= (f26 (f28 (f29 f32 ?v0) ?v0) f27) f1))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f26 f27 ?v0) f1) (=> (= (f26 ?v1 ?v2) f1) (= (f26 ?v1 (f28 (f29 f30 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 f4 ?v0) f1) (=> (= (f3 ?v1 ?v2) f1) (= (f3 ?v1 (f5 (f6 f7 ?v0) ?v2)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f28 (f29 f30 (f28 (f29 f32 ?v0) ?v0)) (f28 (f29 f32 ?v1) ?v1)) f27) (and (= ?v0 f27) (= ?v1 f27)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f5 (f6 f7 (f5 (f6 f13 ?v0) ?v0)) (f5 (f6 f13 ?v1) ?v1)) f4) (and (= ?v0 f4) (= ?v1 f4)))))
(assert (= (f3 f4 f8) f1))
(assert (= (f26 f27 f31) f1))
(assert (not (= (f3 f8 f4) f1)))
(assert (not (= (f26 f31 f27) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 f8 ?v0) f1) (=> (= (f3 f8 ?v1) f1) (= (f3 f8 (f5 (f6 f13 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f26 f31 ?v0) f1) (=> (= (f26 f31 ?v1) f1) (= (f26 f31 (f28 (f29 f32 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S2)) (= (f3 ?v0 (f5 (f6 f7 ?v0) f8)) f1)))
(assert (forall ((?v0 S11)) (= (f26 ?v0 (f28 (f29 f30 ?v0) f31)) f1)))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (let ((?v_0 (f28 f35 ?v0)) (?v_1 (f28 f35 ?v2))) (=> (= (f26 ?v_0 ?v1) f1) (=> (= (f26 ?v_1 ?v3) f1) (= (f26 (f28 (f29 f32 ?v_0) ?v_1) (f28 (f29 f32 ?v1) ?v3)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (let ((?v_0 (f5 f12 ?v0)) (?v_1 (f5 f12 ?v2))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 ?v_1 ?v3) f1) (= (f3 (f5 (f6 f13 ?v_0) ?v_1) (f5 (f6 f13 ?v1) ?v3)) f1))))))
(assert (forall ((?v0 S6)) (= (= (f9 f10 ?v0) f4) (= ?v0 f25))))
(assert (forall ((?v0 S2)) (= (= (f5 f21 ?v0) f4) (= ?v0 f4))))
(assert (= (f9 f10 f25) f4))
(assert (= (f5 f21 f4) f4))
(check-sat)
(exit)
