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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S1)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 () S3)
(declare-fun f7 (S5 S3) S3)
(declare-fun f8 (S6 S3) S5)
(declare-fun f9 () S6)
(declare-fun f10 () S6)
(declare-fun f11 () S3)
(declare-fun f12 (S7 S8) S3)
(declare-fun f13 () S7)
(declare-fun f14 () S8)
(declare-fun f15 () S6)
(declare-fun f16 () S5)
(declare-fun f17 () S5)
(declare-fun f18 () S5)
(declare-fun f19 () S3)
(declare-fun f20 () S3)
(declare-fun f21 () S4)
(declare-fun f22 (S9 S3) S8)
(declare-fun f23 () S9)
(declare-fun f24 (S10 S8) S8)
(declare-fun f25 (S11 S8) S10)
(declare-fun f26 () S11)
(declare-fun f27 () S8)
(declare-fun f28 () S3)
(declare-fun f29 (S12 S8) S1)
(declare-fun f30 (S13 S8) S12)
(declare-fun f31 () S13)
(declare-fun f32 () S8)
(declare-fun f33 () S11)
(declare-fun f34 () S13)
(declare-fun f35 () S10)
(declare-fun f36 (S14 S3) S7)
(declare-fun f37 () S14)
(declare-fun f38 () S3)
(declare-fun f39 () S2)
(declare-fun f40 () S8)
(declare-fun f41 () S3)
(declare-fun f42 () S2)
(declare-fun f43 () S3)
(declare-fun f44 () S3)
(declare-fun f45 () S11)
(declare-fun f46 () S11)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (f7 (f8 f10 f11) (f12 f13 f14))) (?v_1 (f7 f17 (f7 f18 f19)))) (not (= (f3 (f4 f5 f6) (f7 (f8 f9 ?v_0) (f7 (f8 f15 (f7 (f8 f9 (f7 f16 ?v_1)) ?v_0)) (f7 (f8 f9 (f7 f16 (f7 f17 ?v_1))) f20)))) f1))))
(assert (let ((?v_1 (f7 (f8 f10 f11) (f12 f13 f14)))) (let ((?v_0 (f8 f9 ?v_1)) (?v_2 (f7 f17 (f7 f18 f19)))) (= (f3 (f4 f5 (f7 (f8 f9 (f7 ?v_0 f20)) (f7 f16 (f7 f17 ?v_2)))) (f7 (f8 f9 (f7 ?v_0 ?v_1)) (f7 f16 ?v_2))) f1))))
(assert (let ((?v_1 (f7 (f8 f10 f11) (f12 f13 f14)))) (let ((?v_0 (f8 f9 ?v_1)) (?v_2 (f7 f17 (f7 f18 f19)))) (= (f3 (f4 f5 (f7 (f8 f9 (f7 ?v_0 f20)) (f7 f16 (f7 f17 ?v_2)))) (f7 (f8 f9 (f7 ?v_0 ?v_1)) (f7 f16 ?v_2))) f1))))
(assert (= (f3 (f4 f5 (f7 (f8 f15 (f7 (f8 f10 f11) (f12 f13 f14))) f20)) f6) f1))
(assert (let ((?v_0 (f8 f9 (f7 f16 (f7 f17 (f7 f17 (f7 f18 f19))))))) (= (f3 (f4 f5 (f7 (f8 f15 (f7 ?v_0 (f7 (f8 f10 f11) (f12 f13 f14)))) (f7 ?v_0 f20))) f6) f1)))
(assert (not (= (f3 (f4 f21 f20) (f7 (f8 f10 f11) (f12 f13 f14))) f1)))
(assert (let ((?v_0 (f7 (f8 f10 f11) (f12 f13 f14))) (?v_1 (f7 f17 (f7 f18 f19)))) (= (f3 (f4 f21 (f7 (f8 f9 ?v_0) (f7 (f8 f15 (f7 (f8 f9 (f7 f16 ?v_1)) ?v_0)) (f7 (f8 f9 (f7 f16 (f7 f17 ?v_1))) f20)))) f6) f1)))
(assert (let ((?v_0 (f7 (f8 f10 f11) (f12 f13 f14)))) (let ((?v_2 (f8 f9 ?v_0)) (?v_1 (f7 f17 (f7 f18 f19)))) (= (f3 (f4 f21 (f7 ?v_2 (f7 (f8 f15 (f7 (f8 f9 (f7 f16 ?v_1)) ?v_0)) (f7 (f8 f9 (f7 f16 (f7 f17 ?v_1))) f20)))) (f7 ?v_2 f6)) f1))))
(assert (let ((?v_0 (f7 f17 (f7 f18 f19)))) (= (f3 (f4 f21 (f7 (f8 f15 (f7 (f8 f9 (f7 f16 ?v_0)) (f7 (f8 f10 f11) (f12 f13 f14)))) (f7 (f8 f9 (f7 f16 (f7 f17 ?v_0))) f20))) f6) f1)))
(assert (= (f3 (f4 f5 f6) (f7 f16 (f7 f17 (f7 f18 f19)))) f1))
(assert (forall ((?v0 S3)) (let ((?v_0 (f7 f16 ?v0))) (= (f12 f13 (f22 f23 ?v0)) (ite (= (f3 (f4 f5 f6) ?v_0) f1) ?v_0 f6)))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f10 f11) (f7 f16 ?v0)) (f7 f16 (f7 (f8 f10 (f7 f18 f19)) ?v0)))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f10 (f7 f16 ?v0)) f11) (f7 f16 (f7 (f8 f10 ?v0) (f7 f18 f19))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 f11) (f7 f16 ?v0)) f1) (= (f3 (f4 f5 (f7 f18 f19)) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 (f7 f16 ?v0)) f11) f1) (= (f3 (f4 f5 ?v0) (f7 f18 f19)) f1))))
(assert (= (f7 (f8 f10 f11) f11) (f7 f16 (f7 f17 (f7 f18 f19)))))
(assert (= (f7 (f8 f10 f11) f11) (f7 f16 (f7 f17 (f7 f18 f19)))))
(assert (= (f24 (f25 f26 f27) f27) (f22 f23 (f7 f17 (f7 f18 f19)))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 ?v0) (f7 f16 (f7 f17 (f7 f18 f19)))) (f7 (f8 f10 ?v0) ?v0))))
(assert (= (f3 (f4 f21 f11) f28) f1))
(assert (= (f3 (f4 f21 f6) (f7 (f8 f10 f11) (f12 f13 f14))) f1))
(assert (= (f29 (f30 f31 f32) f14) f1))
(assert (= f32 (f22 f23 f19)))
(assert (= (f22 f23 f19) f32))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f3 (f4 f21 ?v0) ?v1) f1) (or (= ?v0 ?v1) (= (f3 (f4 f21 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f7 f16 ?v0)) (f7 f16 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f24 (f25 f33 (f22 f23 ?v0)) (f22 f23 ?v1)) (ite (= (f3 (f4 f21 ?v0) f19) f1) f32 (f22 f23 (f7 (f8 f9 ?v0) ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S8)) (= (f24 (f25 f33 (f22 f23 ?v0)) (f24 (f25 f33 (f22 f23 ?v1)) ?v2)) (ite (= (f3 (f4 f21 ?v0) f19) f1) f32 (f24 (f25 f33 (f22 f23 (f7 (f8 f9 ?v0) ?v1))) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f22 f23 ?v0)) (?v_0 (f22 f23 ?v1))) (= (f24 (f25 f26 ?v_1) ?v_0) (ite (= (f3 (f4 f21 ?v0) f19) f1) ?v_0 (ite (= (f3 (f4 f21 ?v1) f19) f1) ?v_1 (f22 f23 (f7 (f8 f10 ?v0) ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f7 f18 ?v0)) (f7 f18 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f7 f18 ?v0)) (f7 f18 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (= (= (f3 (f4 f21 f19) f19) f1) false))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f7 f17 ?v0)) (f7 f17 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f7 f17 ?v0)) (f7 f17 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 ?v0) ?v1) f1) (and (= (f3 (f4 f5 ?v0) ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f7 f16 ?v0)) (f7 f16 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f21 ?v0) ?v1) f1) (= (f3 (f4 f21 (f7 (f8 f10 ?v0) ?v2)) (f7 (f8 f10 ?v1) ?v2)) f1))))
(assert (= (f22 f23 (f7 f18 f19)) f27))
(assert (= f27 (f22 f23 (f7 f18 f19))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (= (f29 (f30 f34 (f22 f23 ?v0)) (f22 f23 ?v1)) f1) (ite (= (f3 ?v_0 ?v1) f1) true (= (f3 ?v_0 f19) f1))))))
(assert (forall ((?v0 S3)) (= (= (f22 f23 ?v0) f32) (= (f3 (f4 f5 ?v0) f19) f1))))
(assert (forall ((?v0 S3)) (= (= f32 (f22 f23 ?v0)) (= (f3 (f4 f5 ?v0) f19) f1))))
(assert (forall ((?v0 S8)) (= (f24 (f25 f33 (f22 f23 (f7 f17 (f7 f18 f19)))) ?v0) (f24 (f25 f26 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f24 (f25 f33 ?v0) (f22 f23 (f7 f17 (f7 f18 f19)))) (f24 (f25 f26 ?v0) ?v0))))
(assert (= (f24 (f25 f26 f27) f27) (f22 f23 (f7 f17 (f7 f18 f19)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f7 f16 ?v0)) f6) f1) (= (f3 (f4 f21 ?v0) f19) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 f6) (f7 f16 ?v0)) f1) (= (f3 (f4 f21 f19) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f7 (f8 f10 ?v0) ?v0)) f6) f1) (= (f3 (f4 f21 ?v0) f6) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f7 f16 ?v0)) (?v_0 (f7 f16 ?v1))) (= (= (f3 (f4 f5 ?v_1) ?v_0) f1) (not (= (f3 (f4 f21 ?v_0) ?v_1) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f22 f23 ?v0)) (?v_0 (f22 f23 ?v1))) (= (= (f29 (f30 f34 ?v_1) ?v_0) f1) (not (= (f29 (f30 f31 ?v_0) ?v_1) f1))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f7 f18 ?v0)) f19) f1) (= (f3 (f4 f21 ?v0) f19) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f7 f18 ?v0)) (f7 f17 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f7 f18 ?v0)) (f7 f17 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f7 f17 ?v0)) f19) f1) (= (f3 (f4 f21 ?v0) f19) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f21 f19))) (= (= (f3 ?v_0 (f7 f17 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f7 f18 ?v0)) f6) f1) (= (f3 (f4 f21 ?v0) f6) f1))))
(assert (= (= (f3 (f4 f21 f19) f6) f1) false))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f7 f17 ?v0)) f6) f1) (= (f3 (f4 f21 ?v0) f6) f1))))
(assert (= (f3 (f4 f21 f6) f11) f1))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v2))) (=> (= (f3 (f4 f21 ?v0) ?v1) f1) (=> (= (f3 (f4 f21 f6) ?v2) f1) (= (f3 (f4 f21 (f7 ?v_0 ?v0)) (f7 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f21 ?v0))) (= (= (f3 ?v_0 (f7 (f8 f10 ?v1) f11)) f1) (or (= (f3 ?v_0 ?v1) f1) (= ?v0 ?v1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3)) (=> (= (f3 (f4 f21 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v2) ?v3) f1) (= (f3 (f4 f21 (f7 (f8 f10 ?v0) ?v2)) (f7 (f8 f10 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S8)) (not (= (f3 (f4 f21 (f12 f13 ?v0)) f6) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 ?v0) ?v1) f1) (= (f3 (f4 f21 (f7 (f8 f15 ?v0) ?v1)) f6) f1))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S3)) (= (f7 (f8 f10 (f12 f13 ?v0)) (f7 (f8 f10 (f12 f13 ?v1)) ?v2)) (f7 (f8 f10 (f12 f13 (f24 (f25 f26 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f7 (f8 f10 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f24 (f25 f26 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f7 (f8 f10 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f24 (f25 f26 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f7 (f8 f9 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f24 (f25 f33 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f7 (f8 f9 (f12 f13 ?v0)) (f12 f13 ?v1)) (f12 f13 (f24 (f25 f33 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f12 f13 (f24 (f25 f33 ?v0) ?v1)) (f7 (f8 f9 (f12 f13 ?v0)) (f12 f13 ?v1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f3 (f4 f5 (f12 f13 ?v0)) (f12 f13 ?v1)) f1) (= (f29 (f30 f34 ?v0) ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f3 (f4 f5 (f12 f13 ?v0)) (f12 f13 ?v1)) f1) (= (f29 (f30 f34 ?v0) ?v1) f1))))
(assert (= (f12 f13 f27) f11))
(assert (= f11 (f12 f13 f27)))
(assert (forall ((?v0 S8)) (= (= (f12 f13 ?v0) f6) (= ?v0 f32))))
(assert (= (f12 f13 f32) f6))
(assert (= f6 (f12 f13 f32)))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f7 f16 ?v0)) f11) f1) (= (f3 (f4 f21 ?v0) (f7 f18 f19)) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 f11) (f7 f16 ?v0)) f1) (= (f3 (f4 f21 (f7 f18 f19)) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 f6) (f7 (f8 f10 (f7 (f8 f9 ?v0) ?v0)) (f7 (f8 f9 ?v1) ?v1))) f1) (or (not (= ?v0 f6)) (not (= ?v1 f6))))))
(assert (forall ((?v0 S3) (?v1 S3)) (not (= (f3 (f4 f21 (f7 (f8 f10 (f7 (f8 f9 ?v0) ?v0)) (f7 (f8 f9 ?v1) ?v1))) f6) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 (f7 f18 ?v0)) f19) f1) (= (f3 (f4 f21 ?v0) f19) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 f19) (f7 f18 ?v0)) f1) (= (f3 (f4 f5 f19) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f7 f18 ?v0)) (f7 f17 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f7 f18 ?v0)) (f7 f17 ?v1)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f7 f17 ?v0)) (f7 f18 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 (f7 f17 ?v0)) (f7 f18 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 f11) ?v0) f1) (= (f3 (f4 f21 f6) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f21 f6) ?v0) f1) (= (= (f7 (f8 f9 ?v0) ?v1) f11) (and (= ?v0 f11) (= ?v1 f11))))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f21 (f7 (f8 f10 (f7 (f8 f10 f11) ?v0)) ?v0)) f6) f1) (= (f3 (f4 f21 ?v0) f6) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f21 ?v0) ?v1) f1) (= (f3 (f4 f5 (f7 (f8 f10 ?v0) f11)) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f7 (f8 f10 ?v0) f11)) ?v1) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f21 ?v0) (f7 (f8 f10 ?v1) f11)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) (f7 (f8 f15 ?v1) f11)) f1) (= (f3 (f4 f21 ?v0) ?v1) f1))))
(assert (forall ((?v0 S8)) (= (= (f3 (f4 f5 (f12 f13 ?v0)) f6) f1) (= ?v0 f32))))
(assert (let ((?v_0 (f7 f18 (f7 f18 f19)))) (= (f7 f16 ?v_0) (f12 f13 (f22 f23 ?v_0)))))
(assert (forall ((?v0 S3)) (=> (= (f3 (f4 f5 f6) ?v0) f1) (= (f3 (f4 f21 f6) (f7 (f8 f10 f11) ?v0)) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f7 f16 ?v0) (f7 f16 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f7 f16 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S8)) (let ((?v_0 (f22 f23 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f7 f18 ?v0) (f7 f18 ?v1)) (= ?v0 ?v1))))
(assert (= (= f19 f19) true))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f7 f17 ?v0) (f7 f17 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f4 f5 ?v0))) (=> (= (f3 ?v_0 ?v1) f1) (=> (= (f3 (f4 f5 ?v1) ?v2) f1) (= (f3 ?v_0 ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3)) (or (= (f3 (f4 f5 ?v0) ?v1) f1) (= (f3 (f4 f5 ?v1) ?v0) f1))))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 ?v0) ?v0) f1)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f7 (f8 f9 (f7 ?v_0 ?v1)) ?v2) (f7 ?v_0 (f7 (f8 f9 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f9 ?v0) ?v1) (f7 (f8 f9 ?v1) ?v0))))
(assert (forall ((?v0 S3)) (= (f7 f16 ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f10 ?v0))) (= (f7 (f8 f10 (f7 ?v_0 ?v1)) ?v2) (f7 ?v_0 (f7 (f8 f10 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_1 (f8 f10 ?v0)) (?v_0 (f8 f10 ?v1))) (= (f7 ?v_1 (f7 ?v_0 ?v2)) (f7 ?v_0 (f7 ?v_1 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f10 ?v0) ?v1) (f7 (f8 f10 ?v1) ?v0))))
(assert (forall ((?v0 S1) (?v1 S8) (?v2 S8)) (let ((?v_0 (= ?v0 f1))) (= (ite ?v_0 (f12 f13 ?v1) (f12 f13 ?v2)) (f12 f13 (ite ?v_0 ?v1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f12 f13 ?v0) (f12 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f12 f13 ?v0) (f12 f13 ?v1)) (= ?v0 ?v1))))
(assert (let ((?v_0 (f7 f17 (f7 f18 f19)))) (= (f7 f16 ?v_0) (f12 f13 (f22 f23 ?v_0)))))
(assert (forall ((?v0 S3)) (= (= (f7 (f8 f10 ?v0) ?v0) f6) (= ?v0 f6))))
(assert (forall ((?v0 S3)) (= (= (f7 f18 ?v0) f19) false)))
(assert (forall ((?v0 S3)) (= (= f19 (f7 f18 ?v0)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f7 f18 ?v0) (f7 f17 ?v1)) false)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f7 f17 ?v0) (f7 f18 ?v1)) false)))
(assert (forall ((?v0 S3)) (= (= (f7 f17 ?v0) f19) (= ?v0 f19))))
(assert (forall ((?v0 S3)) (= (= f19 (f7 f17 ?v0)) (= f19 ?v0))))
(assert (= (f7 f17 f19) f19))
(assert (= f19 f6))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f7 f18 ?v0)) (f7 f18 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f7 f18 ?v0)) (f7 f18 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (= (= (f3 (f4 f5 f19) f19) f1) true))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f7 f17 ?v0)) (f7 f17 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f7 f17 ?v0)) (f7 f17 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (not (= f6 f11)))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 f19) ?v0) f19)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f9 (f7 f17 ?v0)) ?v1) (f7 f17 (f7 (f8 f9 ?v0) ?v1)))))
(assert (= (f3 (f4 f5 f6) f6) f1))
(assert (forall ((?v0 S3)) (= (f7 (f8 f10 ?v0) f19) ?v0)))
(assert (forall ((?v0 S3)) (= (f7 (f8 f10 f19) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f10 (f7 f17 ?v0)) (f7 f17 ?v1)) (f7 f17 (f7 (f8 f10 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (= (f7 f17 ?v0) (f7 (f8 f10 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f10 ?v0) f6) ?v0)))
(assert (forall ((?v0 S3)) (= (f7 (f8 f10 f6) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 ?v0) f11) ?v0)))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 f11) ?v0) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f7 f16 ?v0)) (f7 f16 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f9 (f7 f16 ?v0)) (f7 f16 ?v1)) (f7 f16 (f7 (f8 f9 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f10 ?v2))) (=> (= (f3 (f4 f5 ?v0) ?v1) f1) (= (f3 (f4 f5 (f7 ?v_0 ?v0)) (f7 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f7 (f8 f9 (f7 (f8 f10 ?v0) ?v1)) ?v2) (f7 (f8 f10 (f7 (f8 f9 ?v0) ?v2)) (f7 (f8 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f7 ?v_0 (f7 (f8 f10 ?v1) ?v2)) (f7 (f8 f10 (f7 ?v_0 ?v1)) (f7 ?v_0 ?v2))))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f15 ?v0) f19) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f15 (f7 f17 ?v0)) (f7 f17 ?v1)) (f7 f17 (f7 (f8 f15 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f10 (f7 f16 ?v0)) (f7 f16 ?v1)) (f7 f16 (f7 (f8 f10 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f7 (f8 f9 (f7 (f8 f15 ?v0) ?v1)) ?v2) (f7 (f8 f15 (f7 (f8 f9 ?v0) ?v2)) (f7 (f8 f9 ?v1) ?v2)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 ?v0))) (= (f7 ?v_0 (f7 (f8 f15 ?v1) ?v2)) (f7 (f8 f15 (f7 ?v_0 ?v1)) (f7 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f7 (f8 f10 (f7 (f8 f9 ?v0) ?v0)) (f7 (f8 f9 ?v1) ?v1)) f6) (and (= ?v0 f6) (= ?v1 f6)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f16 ?v2))) (= (f7 (f8 f9 (f7 (f8 f10 ?v0) ?v1)) ?v_0) (f7 (f8 f10 (f7 (f8 f9 ?v0) ?v_0)) (f7 (f8 f9 ?v1) ?v_0))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S3)) (let ((?v_0 (f22 f23 ?v2))) (= (f24 (f25 f33 (f24 (f25 f26 ?v0) ?v1)) ?v_0) (f24 (f25 f26 (f24 (f25 f33 ?v0) ?v_0)) (f24 (f25 f33 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 (f7 f16 ?v0)))) (= (f7 ?v_0 (f7 (f8 f10 ?v1) ?v2)) (f7 (f8 f10 (f7 ?v_0 ?v1)) (f7 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8)) (let ((?v_0 (f25 f33 (f22 f23 ?v0)))) (= (f24 ?v_0 (f24 (f25 f26 ?v1) ?v2)) (f24 (f25 f26 (f24 ?v_0 ?v1)) (f24 ?v_0 ?v2))))))
(assert (= (f7 f16 f19) f6))
(assert (= (f22 f23 f19) f32))
(assert (= (f7 f16 f19) f6))
(assert (= f6 (f7 f16 f19)))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f7 f16 ?v2))) (= (f7 (f8 f9 (f7 (f8 f15 ?v0) ?v1)) ?v_0) (f7 (f8 f15 (f7 (f8 f9 ?v0) ?v_0)) (f7 (f8 f9 ?v1) ?v_0))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f8 f9 (f7 f16 ?v0)))) (= (f7 ?v_0 (f7 (f8 f15 ?v1) ?v2)) (f7 (f8 f15 (f7 ?v_0 ?v1)) (f7 ?v_0 ?v2))))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f10 (f7 f16 f19)) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f7 (f8 f10 ?v0) (f7 f16 f19)) ?v0)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f7 f16 ?v0)) (f7 f16 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f7 (f8 f9 (f7 f16 ?v0)) (f7 (f8 f9 (f7 f16 ?v1)) ?v2)) (f7 (f8 f9 (f7 f16 (f7 (f8 f9 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f9 (f7 f16 ?v0)) (f7 f16 ?v1)) (f7 f16 (f7 (f8 f9 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 f16 (f7 (f8 f9 ?v0) ?v1)) (f7 (f8 f9 (f7 f16 ?v0)) (f7 f16 ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f7 (f8 f10 (f7 f16 ?v0)) (f7 (f8 f10 (f7 f16 ?v1)) ?v2)) (f7 (f8 f10 (f7 f16 (f7 (f8 f10 ?v0) ?v1))) ?v2))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f10 (f7 f16 ?v0)) (f7 f16 ?v1)) (f7 f16 (f7 (f8 f10 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 f16 (f7 (f8 f10 ?v0) ?v1)) (f7 (f8 f10 (f7 f16 ?v0)) (f7 f16 ?v1)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f5 f19))) (= (= (f3 ?v_0 (f7 f18 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f7 f17 ?v0)) (f7 f18 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f7 f17 ?v0)) (f7 f18 ?v1)) f1) (= (f3 (f4 f5 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 (f7 f17 ?v0)) f19) f1) (= (f3 (f4 f5 ?v0) f19) f1))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f5 f19))) (= (= (f3 ?v_0 (f7 f17 ?v0)) f1) (= (f3 ?v_0 ?v0) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f10 (f7 f18 ?v0)) (f7 f17 ?v1)) (f7 f18 (f7 (f8 f10 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f10 (f7 f17 ?v0)) (f7 f18 ?v1)) (f7 f18 (f7 (f8 f10 ?v0) ?v1)))))
(assert (= f6 (f7 f16 f19)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 f16 (f7 (f8 f15 ?v0) ?v1)) (f7 (f8 f15 (f7 f16 ?v0)) (f7 f16 ?v1)))))
(assert (= (f3 (f4 f5 f6) f11) f1))
(assert (forall ((?v0 S3)) (= (f7 f18 ?v0) (f7 (f8 f10 (f7 (f8 f10 f11) ?v0)) ?v0))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f6))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f7 (f8 f9 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S3)) (not (= (f7 (f8 f10 (f7 (f8 f10 f11) ?v0)) ?v0) f6))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f15 (f7 f18 ?v0)) (f7 f18 ?v1)) (f7 f17 (f7 (f8 f15 ?v0) ?v1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f15 (f7 f18 ?v0)) (f7 f17 ?v1)) (f7 f18 (f7 (f8 f15 ?v0) ?v1)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f8 f15 f19))) (= (f7 ?v_0 (f7 f17 ?v0)) (f7 f17 (f7 ?v_0 ?v0))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f6))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f3 ?v_0 (f7 (f8 f10 ?v0) ?v1)) f1))))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f12 f13 ?v0))) (= (f7 f16 ?v_0) ?v_0))))
(assert (forall ((?v0 S8)) (= (f22 f23 (f12 f13 ?v0)) (f24 f35 ?v0))))
(assert (forall ((?v0 S2)) (= (forall ((?v1 S3)) (=> (= (f3 (f4 f5 f6) ?v1) f1) (= (f3 ?v0 ?v1) f1))) (forall ((?v1 S8)) (= (f3 ?v0 (f12 f13 ?v1)) f1)))))
(assert (forall ((?v0 S2)) (= (exists ((?v1 S3)) (and (= (f3 (f4 f5 f6) ?v1) f1) (= (f3 ?v0 ?v1) f1))) (exists ((?v1 S8)) (= (f3 ?v0 (f12 f13 ?v1)) f1)))))
(assert (forall ((?v0 S8)) (= (f3 (f4 f5 f6) (f12 f13 ?v0)) f1)))
(assert (forall ((?v0 S8)) (= (f3 (f4 f5 f6) (f12 f13 ?v0)) f1)))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f1) (exists ((?v2 S8)) (= ?v1 (f7 (f8 f10 ?v0) (f12 f13 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f3 (f4 f5 (f7 (f8 f10 (f7 (f8 f9 ?v0) ?v0)) (f7 (f8 f9 ?v1) ?v1))) f6) f1) (and (= ?v0 f6) (= ?v1 f6)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f3 (f4 f5 f6) (f7 (f8 f10 (f7 (f8 f9 ?v0) ?v0)) (f7 (f8 f9 ?v1) ?v1))) f1)))
(assert (forall ((?v0 S3)) (let ((?v_0 (f7 f16 ?v0))) (= (f7 f16 (f7 f17 ?v0)) (f7 (f8 f10 (f7 (f8 f10 f6) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f7 f16 ?v0))) (= (f7 f16 (f7 f18 ?v0)) (f7 (f8 f10 (f7 (f8 f10 f11) ?v_0)) ?v_0)))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 (f7 f16 (f7 f18 f19))) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 ?v0) (f7 f16 (f7 f18 f19))) ?v0)))
(assert (= (f7 f16 (f7 f18 f19)) f11))
(assert (= (f22 f23 (f7 f18 f19)) f27))
(assert (= (f7 f16 (f7 f18 f19)) f11))
(assert (= f11 (f7 f16 (f7 f18 f19))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (= (f7 (f8 f10 (f7 f16 ?v0)) (f7 (f8 f15 (f7 f16 ?v1)) ?v2)) (f7 (f8 f15 (f7 f16 (f7 (f8 f10 ?v0) ?v1))) ?v2))))
(assert (= f11 (f7 f16 (f7 f18 f19))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (f7 (f8 f9 (f7 f18 ?v0)) ?v1) (f7 (f8 f10 (f7 f17 (f7 (f8 f9 ?v0) ?v1))) ?v1))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 (f7 (f8 f10 f11) f11)) (f7 f16 ?v0)) (f7 f16 (f7 f17 ?v0)))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 (f7 f16 ?v0)) f6) f1) (= (f3 (f4 f5 ?v0) f19) f1))))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 f6) (f7 f16 ?v0)) f1) (= (f3 (f4 f5 f19) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f19))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f7 (f8 f9 (f7 f16 ?v0)) (f7 f16 ?v1)) (f7 f16 (f7 (f8 f9 ?v0) ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f19))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f24 (f25 f33 (f22 f23 ?v0)) (f22 f23 ?v1)) (f22 f23 (f7 (f8 f9 ?v0) ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f19))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f7 (f8 f10 (f7 f16 ?v0)) (f7 f16 ?v1)) (f7 f16 (f7 (f8 f10 ?v0) ?v1))))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f4 f5 f19))) (=> (= (f3 ?v_0 ?v0) f1) (=> (= (f3 ?v_0 ?v1) f1) (= (f24 (f25 f26 (f22 f23 ?v0)) (f22 f23 ?v1)) (f22 f23 (f7 (f8 f10 ?v0) ?v1))))))))
(assert (= (f3 (f4 f5 f6) (f7 f16 (f7 f18 (f7 f18 f19)))) f1))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 (f7 f16 (f7 f17 (f7 f18 f19)))) ?v0) (f7 (f8 f10 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f24 (f25 f33 (f22 f23 (f7 f17 (f7 f18 f19)))) ?v0) (f24 (f25 f26 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 (f7 f16 (f7 f17 (f7 f18 f19)))) ?v0) (f7 (f8 f10 ?v0) ?v0))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 ?v0) (f7 f16 (f7 f17 (f7 f18 f19)))) (f7 (f8 f10 ?v0) ?v0))))
(assert (forall ((?v0 S8)) (= (f24 (f25 f33 ?v0) (f22 f23 (f7 f17 (f7 f18 f19)))) (f24 (f25 f26 ?v0) ?v0))))
(assert (let ((?v_0 (f7 (f8 f10 f11) (f12 f13 f14))) (?v_1 (f7 f17 (f7 f18 f19)))) (let ((?v_2 (f12 (f36 f37 ?v_0) (f22 f23 ?v_1)))) (= (f3 (f4 f5 (f7 (f8 f9 (f7 (f8 f9 (f7 f16 (f7 f17 ?v_1))) ?v_0)) f20)) (f7 (f8 f10 ?v_2) ?v_2)) f1))))
(assert (forall ((?v0 S3)) (=> (= (f3 (f4 f5 f6) ?v0) f1) (=> (= (f3 (f4 f21 ?v0) (f7 f16 (f7 f17 (f7 f18 f19)))) f1) (or (= ?v0 f6) (= ?v0 f11))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f21 f6) ?v0) f1) (=> (= ?v0 (f7 (f8 f10 ?v1) (f7 (f8 f9 ?v0) ?v2))) (=> (= (f3 (f4 f21 ?v1) ?v0) f1) (= (f3 (f4 f5 f11) ?v2) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (=> (= (f3 (f4 f21 f6) ?v0) f1) (=> (= ?v0 (f7 (f8 f10 ?v1) (f7 (f8 f9 ?v0) ?v2))) (=> (= (f3 (f4 f5 f6) ?v1) f1) (= (f3 (f4 f5 ?v2) f11) f1))))))
(assert (let ((?v_1 (f7 (f8 f10 f11) (f12 f13 f14))) (?v_0 (f7 (f8 f10 (f7 (f8 f9 (f7 f16 (f7 f17 (f7 f17 (f7 f18 f19))))) f38)) f11))) (not (=> (= (f3 (f4 f21 ?v_1) ?v_0) f1) (not (= (f3 f39 (f7 (f8 f9 ?v_0) ?v_1)) f1))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f4 f5 f6))) (=> (= (f3 (f4 f21 ?v0) ?v1) f1) (=> (= (f3 (f4 f21 ?v2) ?v1) f1) (=> (= (f3 ?v_0 ?v3) f1) (=> (= (f3 ?v_0 ?v4) f1) (=> (= (f7 (f8 f10 ?v3) ?v4) f11) (= (f3 (f4 f21 (f7 (f8 f10 (f7 (f8 f9 ?v3) ?v0)) (f7 (f8 f9 ?v4) ?v2))) ?v1) f1)))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3) (?v5 S3)) (let ((?v_0 (f7 (f8 f10 (f7 (f8 f9 ?v3) ?v4)) ?v5))) (=> (= (f7 (f8 f10 (f7 (f8 f9 ?v0) ?v1)) ?v2) ?v_0) (=> (= (f3 (f4 f21 ?v_0) f6) f1) (=> (= (f3 (f4 f21 ?v2) ?v0) f1) (=> (= (f3 (f4 f5 f6) ?v5) f1) (=> (= (f3 (f4 f21 f6) ?v3) f1) (=> (= (f3 (f4 f5 ?v3) ?v0) f1) (= (f3 (f4 f5 ?v4) ?v1) f1))))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f8 f9 ?v0)) (?v_1 (f4 f21 ?v0))) (=> (= (f3 (f4 f5 (f7 (f8 f10 (f7 ?v_0 ?v1)) ?v2)) (f7 (f8 f10 (f7 ?v_0 ?v3)) ?v4)) f1) (=> (= (f3 (f4 f5 ?v4) f6) f1) (=> (= (f3 ?v_1 ?v4) f1) (=> (= (f3 ?v_1 ?v2) f1) (= (f3 (f4 f5 ?v3) ?v1) f1))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3) (?v5 S3)) (let ((?v_1 (f4 f5 f6)) (?v_0 (f7 (f8 f10 (f7 (f8 f9 ?v3) ?v4)) ?v5))) (=> (= (f7 (f8 f10 (f7 (f8 f9 ?v0) ?v1)) ?v2) ?v_0) (=> (= (f3 ?v_1 ?v_0) f1) (=> (= (f3 (f4 f21 ?v5) ?v3) f1) (=> (= (f3 ?v_1 ?v2) f1) (=> (= (f3 (f4 f21 f6) ?v3) f1) (=> (= (f3 (f4 f5 ?v3) ?v0) f1) (= (f3 (f4 f5 ?v1) ?v4) f1))))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3) (?v3 S3) (?v4 S3)) (let ((?v_0 (f8 f9 ?v0))) (=> (= (f3 (f4 f5 (f7 (f8 f10 (f7 ?v_0 ?v1)) ?v2)) (f7 (f8 f10 (f7 ?v_0 ?v3)) ?v4)) f1) (=> (= (f3 (f4 f5 f6) ?v2) f1) (=> (= (f3 (f4 f21 ?v2) ?v0) f1) (=> (= (f3 (f4 f21 ?v4) ?v0) f1) (= (f3 (f4 f5 ?v1) ?v3) f1))))))))
(assert (= (f29 (f30 f31 f32) f40) f1))
(assert (= (f3 (f4 f5 f11) f28) f1))
(assert (not (= (f3 f39 (f7 (f8 f9 (f7 (f8 f10 (f7 (f8 f9 (f7 f16 (f7 f17 (f7 f17 (f7 f18 f19))))) f38)) f11)) (f7 (f8 f10 f11) (f12 f13 f32)))) f1)))
(assert (= (f3 (f4 f21 f6) (f7 (f8 f10 (f7 (f8 f9 (f7 f16 (f7 f17 (f7 f17 (f7 f18 f19))))) f38)) f11)) f1))
(assert (= (f3 (f4 f21 f28) (f7 (f8 f10 (f7 (f8 f9 (f7 f16 (f7 f17 (f7 f17 (f7 f18 f19))))) f38)) f11)) f1))
(assert (= (f3 f39 (f7 (f8 f9 (f7 (f8 f10 (f7 (f8 f9 (f7 f16 (f7 f17 (f7 f17 (f7 f18 f19))))) f38)) f11)) f28)) f1))
(assert (let ((?v_1 (f7 (f8 f10 f11) (f12 f13 f14))) (?v_0 (f7 (f8 f10 (f7 (f8 f9 (f7 f16 (f7 f17 (f7 f17 (f7 f18 f19))))) f38)) f11))) (and (= (f3 (f4 f21 ?v_1) ?v_0) f1) (= (f3 f39 (f7 (f8 f9 ?v_0) ?v_1)) f1))))
(assert (=> (forall ((?v0 S3) (?v1 S3)) (let ((?v_1 (f7 f17 (f7 f18 f19)))) (let ((?v_0 (f22 f23 ?v_1))) (=> (= (f7 (f8 f10 (f12 (f36 f37 ?v0) ?v_0)) (f12 (f36 f37 ?v1) ?v_0)) (f7 (f8 f9 (f7 (f8 f10 (f7 (f8 f9 (f7 f16 (f7 f17 ?v_1))) f38)) f11)) (f7 (f8 f10 f11) (f12 f13 f14)))) false)))) false))
(assert (let ((?v_0 (f7 f17 (f7 f18 f19)))) (= (f7 (f8 f10 (f12 (f36 f37 f41) (f22 f23 ?v_0))) f11) (f7 (f8 f9 (f7 (f8 f10 (f7 (f8 f9 (f7 f16 (f7 f17 ?v_0))) f38)) f11)) f28))))
(assert (= (f3 f42 (f7 (f8 f10 (f7 (f8 f9 (f7 f16 (f7 f17 (f7 f17 (f7 f18 f19))))) f38)) f11)) f1))
(assert (let ((?v_1 (f7 f17 (f7 f18 f19)))) (let ((?v_0 (f22 f23 ?v_1))) (= (f7 (f8 f10 (f12 (f36 f37 f43) ?v_0)) (f12 (f36 f37 f44) ?v_0)) (f7 (f8 f9 (f7 (f8 f10 (f7 (f8 f9 (f7 f16 (f7 f17 ?v_1))) f38)) f11)) (f7 (f8 f10 f11) (f12 f13 f14)))))))
(assert (=> (= f28 f11) (exists ((?v0 S3) (?v1 S3)) (let ((?v_1 (f7 f17 (f7 f18 f19)))) (let ((?v_0 (f22 f23 ?v_1))) (= (f7 (f8 f10 (f12 (f36 f37 ?v0) ?v_0)) (f12 (f36 f37 ?v1) ?v_0)) (f7 (f8 f10 (f7 (f8 f9 (f7 f16 (f7 f17 ?v_1))) f38)) f11)))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (f24 (f25 f33 ?v0) ?v1) (ite (= ?v0 f32) f32 (f24 (f25 f26 ?v1) (f24 (f25 f33 (f24 (f25 f45 ?v0) f27)) ?v1))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8)) (let ((?v_0 (f36 f37 ?v0))) (= (f12 (f36 f37 (f12 ?v_0 ?v1)) ?v2) (f12 ?v_0 (f24 (f25 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S3) (?v1 S8) (?v2 S8)) (let ((?v_0 (f36 f37 ?v0))) (= (f12 ?v_0 (f24 (f25 f26 ?v1) ?v2)) (f7 (f8 f9 (f12 ?v_0 ?v1)) (f12 ?v_0 ?v2))))))
(assert (forall ((?v0 S3) (?v1 S3)) (let ((?v_0 (f22 f23 ?v1))) (= (= (f12 (f36 f37 ?v0) ?v_0) f6) (and (= ?v0 f6) (not (= ?v_0 f32)))))))
(assert (forall ((?v0 S8) (?v1 S3)) (let ((?v_0 (f22 f23 ?v1))) (= (= (f24 (f25 f46 ?v0) ?v_0) f32) (and (= ?v0 f32) (not (= ?v_0 f32)))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f22 f23 ?v0))) (= (f12 (f36 f37 f6) ?v_0) (ite (= ?v_0 f32) f11 f6)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f22 f23 ?v0))) (= (f24 (f25 f46 f32) ?v_0) (ite (= ?v_0 f32) f27 f32)))))
(assert (forall ((?v0 S3) (?v1 S8)) (let ((?v_0 (f4 f5 f6))) (=> (= (f3 ?v_0 ?v0) f1) (= (f3 ?v_0 (f12 (f36 f37 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f29 (f30 f34 ?v0) ?v1) f1) (= (f7 (f8 f15 (f12 f13 ?v1)) (f12 f13 ?v0)) (f12 f13 (f24 (f25 f45 ?v1) ?v0))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f3 (f4 f21 (f12 f13 ?v0)) (f12 f13 ?v1)) f1) (= (f29 (f30 f31 ?v0) ?v1) f1))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f3 (f4 f21 (f12 f13 ?v0)) (f12 f13 ?v1)) f1) (= (f29 (f30 f31 ?v0) ?v1) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (= (f3 f39 ?v0) f1) (=> (= (f3 f39 ?v1) f1) (= (f3 f39 (f7 (f8 f9 ?v0) ?v1)) f1)))))
(assert (forall ((?v0 S3) (?v1 S3)) (= (= (f29 (f30 f31 (f22 f23 ?v0)) (f22 f23 ?v1)) f1) (ite (= (f3 (f4 f21 ?v0) ?v1) f1) (= (f3 (f4 f21 f19) ?v1) f1) false))))
(assert (forall ((?v0 S3)) (= (= (f29 (f30 f31 f32) (f22 f23 ?v0)) f1) (= (f3 (f4 f21 f19) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f3 (f4 f21 ?v0) ?v1) f1) false) (=> (=> (= (f3 (f4 f21 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S8)) (= (= (f3 (f4 f21 f6) (f12 f13 ?v0)) f1) (= (f29 (f30 f31 f32) ?v0) f1))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S8)) (let ((?v_0 (f8 f9 (f12 f13 ?v2)))) (=> (= (f3 (f4 f21 ?v0) ?v1) f1) (=> (= (f29 (f30 f31 f32) ?v2) f1) (= (f3 (f4 f21 (f7 ?v_0 ?v0)) (f7 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S8)) (= (f24 (f25 f46 ?v0) (f22 f23 (f7 f18 (f7 f18 f19)))) (f24 (f25 f33 (f24 (f25 f33 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S3)) (= (f12 (f36 f37 ?v0) (f22 f23 (f7 f18 (f7 f18 f19)))) (f7 (f8 f9 (f7 (f8 f9 ?v0) ?v0)) ?v0))))
(assert (forall ((?v0 S8) (?v1 S8)) (let ((?v_1 (f22 f23 (f7 f17 (f7 f18 f19)))) (?v_0 (f25 f46 ?v0))) (= (f24 ?v_0 (f24 (f25 f33 ?v_1) ?v1)) (f24 (f25 f46 (f24 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S8)) (let ((?v_1 (f22 f23 (f7 f17 (f7 f18 f19)))) (?v_0 (f36 f37 ?v0))) (= (f12 ?v_0 (f24 (f25 f33 ?v_1) ?v1)) (f12 (f36 f37 (f12 ?v_0 ?v1)) ?v_1)))))
(assert (forall ((?v0 S3) (?v1 S8)) (=> (= (f3 (f4 f5 (f12 (f36 f37 ?v0) (f24 (f25 f33 (f22 f23 (f7 f17 (f7 f18 f19)))) ?v1))) f6) f1) (= ?v0 f6))))
(assert (= (f12 (f36 f37 f6) (f22 f23 (f7 f17 (f7 f18 f19)))) f6))
(assert (= (f24 (f25 f46 f32) (f22 f23 (f7 f17 (f7 f18 f19)))) f32))
(check-sat)
(exit)