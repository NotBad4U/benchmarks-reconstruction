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
(declare-sort S17 0)
(declare-sort S18 0)
(declare-sort S19 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S4)
(declare-fun f4 () S2)
(declare-fun f5 (S5 S3) S3)
(declare-fun f6 (S6 S3) S5)
(declare-fun f7 () S6)
(declare-fun f8 () S6)
(declare-fun f9 (S7 S8) S3)
(declare-fun f10 () S7)
(declare-fun f11 () S8)
(declare-fun f12 (S9 S10) S3)
(declare-fun f13 () S9)
(declare-fun f14 (S11 S10) S10)
(declare-fun f15 () S11)
(declare-fun f16 () S11)
(declare-fun f17 () S10)
(declare-fun f18 () S3)
(declare-fun f19 () S8)
(declare-fun f20 () S4)
(declare-fun f21 (S3 S3) S1)
(declare-fun f22 () S3)
(declare-fun f23 () S5)
(declare-fun f24 () S5)
(declare-fun f25 () S3)
(declare-fun f26 (S8 S8) S1)
(declare-fun f27 (S12 S8) S4)
(declare-fun f28 () S12)
(declare-fun f29 (S13 S4) S4)
(declare-fun f30 (S14 S4) S13)
(declare-fun f31 () S14)
(declare-fun f32 (S15 S10) S4)
(declare-fun f33 () S15)
(declare-fun f34 () S10)
(declare-fun f35 () S11)
(declare-fun f36 (S16 S10) S8)
(declare-fun f37 () S16)
(declare-fun f38 () S8)
(declare-fun f39 (S17 S10) S11)
(declare-fun f40 () S17)
(declare-fun f41 () S14)
(declare-fun f42 () S8)
(declare-fun f43 (S10 S10) S1)
(declare-fun f44 () S10)
(declare-fun f45 (S18 S8) S8)
(declare-fun f46 (S19 S8) S18)
(declare-fun f47 () S19)
(declare-fun f48 () S4)
(assert (not (= f1 f2)))
(assert (not (not (= (f3 f4 (f5 (f6 f7 (f5 (f6 f8 (f9 f10 f11)) (f5 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) f18))) (f9 f10 f19))) f20))))
(assert (= (f21 f22 (f5 (f6 f7 (f5 (f6 f8 (f9 f10 f11)) (f5 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) f18))) (f9 f10 f19))) f1))
(assert (let ((?v_0 (f5 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) f18))) (= (f21 (f5 (f6 f7 (f5 (f6 f8 (f9 f10 f11)) ?v_0)) (f9 f10 f19)) ?v_0) f1)))
(assert (forall ((?v0 S3)) (=> (= (f21 f22 ?v0) f1) (=> (= (f21 ?v0 (f5 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) f18)) f1) (or (not (= (f5 f23 ?v0) f22)) (not (= (f5 f24 ?v0) f25)))))))
(assert (let ((?v_0 (f5 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) f18))) (= (f21 (f5 (f6 f7 (f5 (f6 f8 (f9 f10 f11)) ?v_0)) (f9 f10 f19)) ?v_0) f1)))
(assert (= (f21 f22 (f5 (f6 f7 (f5 (f6 f8 (f9 f10 f11)) (f5 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) f18))) (f9 f10 f19))) f1))
(assert (forall ((?v0 S3)) (=> (= (f21 f22 ?v0) f1) (=> (= (f21 ?v0 (f5 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) f18)) f1) (or (not (= (f5 f23 ?v0) f22)) (not (= (f5 f24 ?v0) f25)))))))
(assert (= (f26 f11 f19) f1))
(assert (forall ((?v0 S8)) (= (f27 f28 ?v0) (f3 f4 (f5 (f6 f7 (f5 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) f18)) (f9 f10 ?v0))))))
(assert (let ((?v_0 (f12 f13 (f14 f15 (f14 f16 f17))))) (not (= (f5 (f6 f7 f18) ?v_0) ?v_0))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S3)) (let ((?v_0 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17))))) (?v_1 (f6 f7 ?v1))) (= (= ?v0 (f5 ?v_1 (f5 ?v_0 ?v2))) (= (f5 ?v_0 ?v0) (f5 ?v_1 ?v2))))))
(assert (let ((?v_0 (f5 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17)))) f18)) (?v_1 (f9 f10 f19))) (=> (= (f26 f11 f19) f1) (=> (= (f21 f22 (f5 (f6 f7 ?v_0) ?v_1)) f1) (= (f21 (f5 (f6 f7 (f5 (f6 f8 (f9 f10 f11)) ?v_0)) ?v_1) ?v_0) f1)))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 ?v0) (f12 f13 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S4)) (= (f29 (f30 f31 ?v0) (f32 f33 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 ?v0) (f12 f13 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S4)) (= (f29 (f30 f31 ?v0) (f32 f33 (f14 f16 f17))) ?v0)))
(assert (= f34 (f14 f35 (f14 f16 f17))))
(assert (= f25 (f12 f13 (f14 f16 f17))))
(assert (= f20 (f32 f33 (f14 f16 f17))))
(assert (= (f14 f35 (f14 f16 f17)) f34))
(assert (= (f12 f13 (f14 f16 f17)) f25))
(assert (= (f32 f33 (f14 f16 f17)) f20))
(assert (= (f36 f37 (f14 f16 f17)) f38))
(assert (= (f14 f35 (f14 f16 f17)) f34))
(assert (= (f12 f13 (f14 f16 f17)) f25))
(assert (= (f32 f33 (f14 f16 f17)) f20))
(assert (forall ((?v0 S10)) (= (f14 (f39 f40 ?v0) (f14 f35 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 ?v0) (f12 f13 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S4)) (= (f29 (f30 f41 ?v0) (f32 f33 (f14 f16 f17))) ?v0)))
(assert (forall ((?v0 S10)) (= (f14 (f39 f40 (f14 f35 (f14 f16 f17))) ?v0) ?v0)))
(assert (forall ((?v0 S3)) (= (f5 (f6 f8 (f12 f13 (f14 f16 f17))) ?v0) ?v0)))
(assert (forall ((?v0 S4)) (= (f29 (f30 f41 (f32 f33 (f14 f16 f17))) ?v0) ?v0)))
(assert (not (= (f5 (f6 f7 f18) (f12 f13 (f14 f15 (f14 f16 f17)))) f22)))
(assert (= (f26 f42 f11) f1))
(assert (= (f5 f24 f22) f25))
(assert (= (f5 f23 f22) f22))
(assert (forall ((?v0 S3)) (=> (= (f5 f24 ?v0) f25) (= (f5 f23 ?v0) f22))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f43 (f14 f35 ?v0) (f14 f35 ?v1)) f1) (= (f43 ?v0 ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f21 (f12 f13 ?v0) (f12 f13 ?v1)) f1) (= (f43 ?v0 ?v1) f1))))
(assert (forall ((?v0 S10)) (= (f14 (f39 f40 f17) ?v0) f17)))
(assert (forall ((?v0 S10) (?v1 S10)) (= (f14 (f39 f40 (f14 f15 ?v0)) ?v1) (f14 f15 (f14 (f39 f40 ?v0) ?v1)))))
(assert (= f34 (f14 f35 (f14 f16 f17))))
(assert (= (f36 f37 (f14 f16 f17)) f38))
(assert (= f38 (f36 f37 (f14 f16 f17))))
(assert (forall ((?v0 S3)) (=> (= (f21 f22 ?v0) f1) (=> (= (f21 ?v0 f18) f1) (= (f21 f22 (f5 f23 ?v0)) f1)))))
(assert (forall ((?v0 S10)) (= (= (f43 (f14 f35 ?v0) f44) f1) (= (f43 ?v0 f17) f1))))
(assert (forall ((?v0 S10)) (= (= (f21 (f12 f13 ?v0) f22) f1) (= (f43 ?v0 f17) f1))))
(assert (forall ((?v0 S10)) (= (= (f43 f44 (f14 f35 ?v0)) f1) (= (f43 f17 ?v0) f1))))
(assert (forall ((?v0 S10)) (= (= (f21 f22 (f12 f13 ?v0)) f1) (= (f43 f17 ?v0) f1))))
(assert (= (f5 f23 f18) f22))
(assert (= (f21 f22 f18) f1))
(assert (not (= (f21 f18 f22) f1)))
(assert (not (= f18 f22)))
(assert (forall ((?v0 S10)) (= (= (f43 (f14 f35 ?v0) f34) f1) (= (f43 ?v0 (f14 f16 f17)) f1))))
(assert (forall ((?v0 S10)) (= (= (f21 (f12 f13 ?v0) f25) f1) (= (f43 ?v0 (f14 f16 f17)) f1))))
(assert (forall ((?v0 S10)) (= (= (f43 f34 (f14 f35 ?v0)) f1) (= (f43 (f14 f16 f17) ?v0) f1))))
(assert (forall ((?v0 S10)) (= (= (f21 f25 (f12 f13 ?v0)) f1) (= (f43 (f14 f16 f17) ?v0) f1))))
(assert (forall ((?v0 S8)) (let ((?v_0 (f14 f15 (f14 f15 (f14 f16 f17))))) (= (f5 (f6 f8 (f9 f10 ?v0)) (f12 f13 ?v_0)) (f9 f10 (f45 (f46 f47 (f36 f37 ?v_0)) ?v0))))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f14 f35 ?v0) (f14 f35 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f12 f13 ?v0) (f12 f13 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f32 f33 ?v0) (f32 f33 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S10) (?v1 S8)) (let ((?v_0 (f36 f37 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S10) (?v1 S10)) (let ((?v_0 (f14 f35 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S10) (?v1 S3)) (let ((?v_0 (f12 f13 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S10) (?v1 S4)) (let ((?v_0 (f32 f33 ?v0))) (= (= ?v_0 ?v1) (= ?v1 ?v_0)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f14 f16 ?v0) (f14 f16 ?v1)) (= ?v0 ?v1))))
(assert (= (= f17 f17) true))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f14 f15 ?v0) (f14 f15 ?v1)) (= ?v0 ?v1))))
(assert (= (f36 f37 f17) f42))
(assert (= (f14 f35 f17) f44))
(assert (= (f12 f13 f17) f22))
(assert (= (f32 f33 f17) f48))
(assert (= (f14 f35 f17) f44))
(assert (= (f12 f13 f17) f22))
(assert (= (f32 f33 f17) f48))
(assert (= f44 (f14 f35 f17)))
(assert (= f22 (f12 f13 f17)))
(assert (= f48 (f32 f33 f17)))
(assert (forall ((?v0 S3) (?v1 S10) (?v2 S3)) (let ((?v_0 (f12 f13 ?v1))) (let ((?v_1 (f5 (f6 f8 ?v2) ?v_0))) (= (= (f21 (f5 (f6 f7 ?v0) ?v_0) ?v2) f1) (ite (= (f21 f22 ?v_0) f1) (= (f21 ?v0 ?v_1) f1) (ite (= (f21 ?v_0 f22) f1) (= (f21 ?v_1 ?v0) f1) (= (f21 f22 ?v2) f1))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (let ((?v_0 (f12 f13 ?v2))) (let ((?v_1 (f5 (f6 f8 ?v_0) ?v1))) (= (= (f21 (f5 (f6 f7 ?v0) ?v1) ?v_0) f1) (ite (= (f21 f22 ?v1) f1) (= (f21 ?v0 ?v_1) f1) (ite (= (f21 ?v1 f22) f1) (= (f21 ?v_1 ?v0) f1) (= (f21 f22 ?v_0) f1))))))))
(assert (forall ((?v0 S10) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f13 ?v0))) (let ((?v_1 (f5 (f6 f8 ?v_0) ?v2))) (= (= (f21 ?v_0 (f5 (f6 f7 ?v1) ?v2)) f1) (ite (= (f21 f22 ?v2) f1) (= (f21 ?v_1 ?v1) f1) (ite (= (f21 ?v2 f22) f1) (= (f21 ?v1 ?v_1) f1) (= (f21 ?v_0 f22) f1))))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (let ((?v_0 (f12 f13 ?v2))) (let ((?v_1 (f5 (f6 f8 ?v0) ?v_0))) (= (= (f21 ?v0 (f5 (f6 f7 ?v1) ?v_0)) f1) (ite (= (f21 f22 ?v_0) f1) (= (f21 ?v_1 ?v1) f1) (ite (= (f21 ?v_0 f22) f1) (= (f21 ?v1 ?v_1) f1) (= (f21 ?v0 f22) f1))))))))
(assert (forall ((?v0 S3)) (=> (= (f21 f22 ?v0) f1) (=> (= (f21 ?v0 (f12 f13 (f14 f15 (f14 f16 f17)))) f1) (= (f21 f22 (f5 f23 ?v0)) f1)))))
(assert (= (f21 (f5 f24 (f12 f13 (f14 f15 (f14 f16 f17)))) f22) f1))
(assert (forall ((?v0 S3)) (let ((?v_0 (f12 f13 (f14 f15 (f14 f16 f17))))) (=> (= (f21 f22 ?v0) f1) (=> (= (f21 ?v0 ?v_0) f1) (= (f21 (f5 f24 (f5 (f6 f8 ?v_0) ?v0)) f25) f1))))))
(assert (forall ((?v0 S8)) (= (f5 f23 (f5 (f6 f8 (f9 f10 ?v0)) f18)) f22)))
(assert (forall ((?v0 S8)) (= (f5 f23 (f5 (f6 f8 f18) (f9 f10 ?v0))) f22)))
(assert (not (= (f5 f24 (f12 f13 (f14 f15 (f14 f16 f17)))) f22)))
(assert (forall ((?v0 S3) (?v1 S10) (?v2 S3)) (let ((?v_0 (f12 f13 ?v1))) (= (= (f5 (f6 f7 ?v0) ?v_0) ?v2) (ite (not (= ?v_0 f22)) (= ?v0 (f5 (f6 f8 ?v2) ?v_0)) (= ?v2 f22))))))
(assert (forall ((?v0 S4) (?v1 S10) (?v2 S4)) (let ((?v_0 (f32 f33 ?v1))) (= (= (f29 (f30 f31 ?v0) ?v_0) ?v2) (ite (not (= ?v_0 f48)) (= ?v0 (f29 (f30 f41 ?v2) ?v_0)) (= ?v2 f48))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (let ((?v_0 (f12 f13 ?v2))) (= (= (f5 (f6 f7 ?v0) ?v1) ?v_0) (ite (not (= ?v1 f22)) (= ?v0 (f5 (f6 f8 ?v_0) ?v1)) (= ?v_0 f22))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S10)) (let ((?v_0 (f32 f33 ?v2))) (= (= (f29 (f30 f31 ?v0) ?v1) ?v_0) (ite (not (= ?v1 f48)) (= ?v0 (f29 (f30 f41 ?v_0) ?v1)) (= ?v_0 f48))))))
(assert (forall ((?v0 S10) (?v1 S3) (?v2 S3)) (let ((?v_0 (f12 f13 ?v0))) (= (= ?v_0 (f5 (f6 f7 ?v1) ?v2)) (ite (not (= ?v2 f22)) (= (f5 (f6 f8 ?v_0) ?v2) ?v1) (= ?v_0 f22))))))
(assert (forall ((?v0 S10) (?v1 S4) (?v2 S4)) (let ((?v_0 (f32 f33 ?v0))) (= (= ?v_0 (f29 (f30 f31 ?v1) ?v2)) (ite (not (= ?v2 f48)) (= (f29 (f30 f41 ?v_0) ?v2) ?v1) (= ?v_0 f48))))))
(assert (forall ((?v0 S3) (?v1 S3) (?v2 S10)) (let ((?v_0 (f12 f13 ?v2))) (= (= ?v0 (f5 (f6 f7 ?v1) ?v_0)) (ite (not (= ?v_0 f22)) (= (f5 (f6 f8 ?v0) ?v_0) ?v1) (= ?v0 f22))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S10)) (let ((?v_0 (f32 f33 ?v2))) (= (= ?v0 (f29 (f30 f31 ?v1) ?v_0)) (ite (not (= ?v_0 f48)) (= (f29 (f30 f41 ?v0) ?v_0) ?v1) (= ?v0 f48))))))
(assert (forall ((?v0 S3)) (= (f5 (f6 f7 ?v0) (f12 f13 f17)) f22)))
(assert (forall ((?v0 S4)) (= (f29 (f30 f31 ?v0) (f32 f33 f17)) f48)))
(assert (forall ((?v0 S3)) (=> (= (f21 f22 ?v0) f1) (=> (= (f21 ?v0 (f5 (f6 f7 f18) (f12 f13 (f14 f15 (f14 f16 f17))))) f1) (= (f21 f22 (f5 f23 ?v0)) f1)))))
(assert (forall ((?v0 S3)) (=> (= (f21 f22 ?v0) f1) (=> (= (f21 ?v0 (f5 (f6 f7 f18) (f12 f13 (f14 f15 (f14 f16 f17))))) f1) (= (f21 f22 (f5 f24 ?v0)) f1)))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f6 f8 (f12 f13 (f14 f15 (f14 f16 f17)))))) (= (f5 f23 (f5 ?v_0 ?v0)) (f5 (f6 f8 (f5 ?v_0 (f5 f23 ?v0))) (f5 f24 ?v0))))))
(assert (forall ((?v0 S3)) (=> (= (f21 f22 ?v0) f1) (= (f21 f22 (f5 (f6 f7 ?v0) (f12 f13 (f14 f15 (f14 f16 f17))))) f1))))
(check-sat)
(exit)
