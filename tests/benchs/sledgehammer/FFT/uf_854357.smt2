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
(declare-sort S20 0)
(declare-sort S21 0)
(declare-sort S22 0)
(declare-sort S23 0)
(declare-sort S24 0)
(declare-sort S25 0)
(declare-sort S26 0)
(declare-sort S27 0)
(declare-sort S28 0)
(declare-sort S29 0)
(declare-sort S30 0)
(declare-sort S31 0)
(declare-sort S32 0)
(declare-sort S33 0)
(declare-sort S34 0)
(declare-sort S35 0)
(declare-sort S36 0)
(declare-sort S37 0)
(declare-sort S38 0)
(declare-sort S39 0)
(declare-sort S40 0)
(declare-sort S41 0)
(declare-sort S42 0)
(declare-sort S43 0)
(declare-sort S44 0)
(declare-sort S45 0)
(declare-sort S46 0)
(declare-sort S47 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S4)
(declare-fun f4 () S3)
(declare-fun f5 (S5 S4) S4)
(declare-fun f6 (S6 S4) S5)
(declare-fun f7 () S6)
(declare-fun f8 (S7 S8) S4)
(declare-fun f9 (S9 S3) S7)
(declare-fun f10 () S9)
(declare-fun f11 (S10 S4) S3)
(declare-fun f12 () S10)
(declare-fun f13 (S8 S2) S1)
(declare-fun f14 (S2) S8)
(declare-fun f15 () S2)
(declare-fun f16 () S3)
(declare-fun f17 () S2)
(declare-fun f18 (S11 S2) S2)
(declare-fun f19 (S12 S2) S11)
(declare-fun f20 () S12)
(declare-fun f21 () S6)
(declare-fun f22 () S4)
(declare-fun f23 (S13 S2) S8)
(declare-fun f24 (S2) S13)
(declare-fun f25 () S2)
(declare-fun f26 () S3)
(declare-fun f27 () S3)
(declare-fun f28 () S3)
(declare-fun f29 (S14 S2) S3)
(declare-fun f30 (S15 S3) S14)
(declare-fun f31 () S15)
(declare-fun f32 () S12)
(declare-fun f33 () S12)
(declare-fun f34 (S16 S2) S17)
(declare-fun f35 (S18 S2) S16)
(declare-fun f36 (S19 S16) S18)
(declare-fun f37 () S19)
(declare-fun f38 (S20 S8) S17)
(declare-fun f39 (S21 S16) S20)
(declare-fun f40 () S21)
(declare-fun f41 (S22 S11) S12)
(declare-fun f42 () S22)
(declare-fun f43 (S23 S8) S2)
(declare-fun f44 (S24 S11) S23)
(declare-fun f45 () S24)
(declare-fun f46 (S25 S2) S26)
(declare-fun f47 (S27 S2) S25)
(declare-fun f48 (S28 S25) S27)
(declare-fun f49 () S28)
(declare-fun f50 (S29 S8) S26)
(declare-fun f51 (S30 S25) S29)
(declare-fun f52 () S30)
(declare-fun f53 () S15)
(declare-fun f54 () S19)
(declare-fun f55 () S22)
(declare-fun f56 () S28)
(declare-fun f57 (S31 S16) S16)
(declare-fun f58 (S32 S2) S31)
(declare-fun f59 () S32)
(declare-fun f60 (S33 S4) S14)
(declare-fun f61 (S34 S4) S33)
(declare-fun f62 () S34)
(declare-fun f63 () S6)
(declare-fun f64 () S6)
(declare-fun f65 (S35 S17) S18)
(declare-fun f66 (S36 S17) S35)
(declare-fun f67 () S36)
(declare-fun f68 (S37 S17) S17)
(declare-fun f69 (S38 S17) S37)
(declare-fun f70 () S38)
(declare-fun f71 () S38)
(declare-fun f72 (S39 S17) S16)
(declare-fun f73 () S39)
(declare-fun f74 () S38)
(declare-fun f75 (S40 S26) S27)
(declare-fun f76 (S41 S26) S40)
(declare-fun f77 () S41)
(declare-fun f78 (S42 S26) S26)
(declare-fun f79 (S43 S26) S42)
(declare-fun f80 () S43)
(declare-fun f81 () S43)
(declare-fun f82 (S44 S26) S25)
(declare-fun f83 () S44)
(declare-fun f84 () S43)
(declare-fun f85 () S34)
(declare-fun f86 () S36)
(declare-fun f87 () S41)
(declare-fun f88 (S2) S8)
(declare-fun f89 () S17)
(declare-fun f90 () S38)
(declare-fun f91 () S17)
(declare-fun f92 () S4)
(declare-fun f93 () S2)
(declare-fun f94 () S12)
(declare-fun f95 () S26)
(declare-fun f96 (S17 S17) S1)
(declare-fun f97 (S26 S26) S1)
(declare-fun f98 () S26)
(declare-fun f99 (S45 S8) S8)
(declare-fun f100 (S8) S45)
(declare-fun f101 (S46 S46) S46)
(declare-fun f102 (S26 S26) S46)
(declare-fun f103 (S47 S47) S47)
(declare-fun f104 (S17 S17) S47)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2)) (let ((?v_0 (f3 f16 f17))) (= (f3 f4 ?v0) (f5 (f6 f7 (f8 (f9 f10 (f11 f12 (ite (= (f13 (f14 f15) ?v0) f1) (f3 (f11 f12 ?v_0) (f18 (f19 f20 ?v0) f15)) (f3 (f11 f12 (f5 (f6 f21 f22) ?v_0)) (f18 (f19 f20 f15) ?v0))))) (f23 (f24 f25) f17))) (f3 f26 ?v0))))))
(assert (forall ((?v0 S2)) (= (f3 f27 ?v0) (f5 (f6 f7 (f8 (f9 f10 (f11 f12 (f3 (f11 f12 (f5 (f6 f21 f22) (f3 f16 f17))) (f18 (f19 f20 f15) ?v0)))) (f23 (f24 f25) f17))) (f3 f26 ?v0)))))
(assert (forall ((?v0 S2)) (= (f3 f28 ?v0) (f5 (f6 f7 (f8 (f9 f10 (f11 f12 (f3 (f11 f12 (f3 f16 f17)) (f18 (f19 f20 ?v0) f15)))) (f23 (f24 f25) f17))) (f3 f26 ?v0)))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 (f19 f32 ?v2) ?v1))) (= (f3 (f29 (f30 f31 ?v0) ?v1) ?v2) (f8 (f9 f10 ?v0) (f23 (f24 ?v_0) (f18 (f19 f33 ?v_0) ?v1)))))))
(assert (forall ((?v0 S16) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 (f19 f32 ?v2) ?v1))) (= (f34 (f35 (f36 f37 ?v0) ?v1) ?v2) (f38 (f39 f40 ?v0) (f23 (f24 ?v_0) (f18 (f19 f33 ?v_0) ?v1)))))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 (f19 f32 ?v2) ?v1))) (= (f18 (f19 (f41 f42 ?v0) ?v1) ?v2) (f43 (f44 f45 ?v0) (f23 (f24 ?v_0) (f18 (f19 f33 ?v_0) ?v1)))))))
(assert (forall ((?v0 S25) (?v1 S2) (?v2 S2)) (let ((?v_0 (f18 (f19 f32 ?v2) ?v1))) (= (f46 (f47 (f48 f49 ?v0) ?v1) ?v2) (f50 (f51 f52 ?v0) (f23 (f24 ?v_0) (f18 (f19 f33 ?v_0) ?v1)))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (= (f3 (f29 (f30 f53 ?v0) ?v1) ?v2) (f3 ?v0 (f18 (f19 f33 ?v2) ?v1)))))
(assert (forall ((?v0 S16) (?v1 S2) (?v2 S2)) (= (f34 (f35 (f36 f54 ?v0) ?v1) ?v2) (f34 ?v0 (f18 (f19 f33 ?v2) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S2)) (= (f18 (f19 (f41 f55 ?v0) ?v1) ?v2) (f18 ?v0 (f18 (f19 f33 ?v2) ?v1)))))
(assert (forall ((?v0 S25) (?v1 S2) (?v2 S2)) (= (f46 (f47 (f48 f56 ?v0) ?v1) ?v2) (f46 ?v0 (f18 (f19 f33 ?v2) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S16) (?v2 S2)) (= (f34 (f57 (f58 f59 ?v0) ?v1) ?v2) (f34 ?v1 (f18 (f19 f33 ?v2) ?v0)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2) (?v3 S2)) (let ((?v_0 (f11 f12 ?v0))) (= (f3 (f29 (f60 (f61 f62 ?v0) ?v1) ?v2) ?v3) (f5 (f6 f63 (f5 (f6 f7 (f3 (f11 f12 (f5 (f6 f64 ?v0) ?v1)) (f18 (f19 f20 ?v2) ?v3))) (f3 ?v_0 ?v3))) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S2) (?v3 S2)) (let ((?v_0 (f72 f73 ?v0))) (= (f34 (f35 (f65 (f66 f67 ?v0) ?v1) ?v2) ?v3) (f68 (f69 f70 (f68 (f69 f71 (f34 (f72 f73 (f68 (f69 f74 ?v0) ?v1)) (f18 (f19 f20 ?v2) ?v3))) (f34 ?v_0 ?v3))) (f34 ?v_0 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S2) (?v3 S2)) (let ((?v_0 (f82 f83 ?v0))) (= (f46 (f47 (f75 (f76 f77 ?v0) ?v1) ?v2) ?v3) (f78 (f79 f80 (f78 (f79 f81 (f46 (f82 f83 (f78 (f79 f84 ?v0) ?v1)) (f18 (f19 f20 ?v2) ?v3))) (f46 ?v_0 ?v3))) (f46 ?v_0 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2) (?v3 S2)) (let ((?v_0 (f11 f12 ?v0)) (?v_1 (f18 (f19 f20 ?v2) ?v3))) (= (f3 (f29 (f60 (f61 f85 ?v0) ?v1) ?v2) ?v3) (f5 (f6 f7 (f3 ?v_0 ?v3)) (f5 (f6 f63 (f3 (f11 f12 (f5 (f6 f64 ?v0) ?v1)) ?v_1)) (f3 ?v_0 ?v_1)))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S2) (?v3 S2)) (let ((?v_0 (f72 f73 ?v0)) (?v_1 (f18 (f19 f20 ?v2) ?v3))) (= (f34 (f35 (f65 (f66 f86 ?v0) ?v1) ?v2) ?v3) (f68 (f69 f71 (f34 ?v_0 ?v3)) (f68 (f69 f70 (f34 (f72 f73 (f68 (f69 f74 ?v0) ?v1)) ?v_1)) (f34 ?v_0 ?v_1)))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S2) (?v3 S2)) (let ((?v_0 (f82 f83 ?v0)) (?v_1 (f18 (f19 f20 ?v2) ?v3))) (= (f46 (f47 (f75 (f76 f87 ?v0) ?v1) ?v2) ?v3) (f78 (f79 f81 (f46 ?v_0 ?v3)) (f78 (f79 f80 (f46 (f82 f83 (f78 (f79 f84 ?v0) ?v1)) ?v_1)) (f46 ?v_0 ?v_1)))))))
(assert (let ((?v_0 (f24 f25))) (not (= (f8 (f9 f10 f4) (f23 ?v_0 f17)) (f5 (f6 f64 (f8 (f9 f10 f27) (f23 ?v_0 f15))) (f8 (f9 f10 f28) (f23 (f24 f15) f17)))))))
(assert (= (f13 (f88 f15) f17) f1))
(assert (= (f13 (f88 f15) f17) f1))
(assert (forall ((?v0 S2)) (= (f13 (f88 (f18 (f19 f20 f15) ?v0)) f17) f1)))
(assert (forall ((?v0 S2)) (=> (= (f13 (f88 ?v0) f17) f1) (= (f13 (f88 (f18 (f19 f20 ?v0) f15)) f17) f1))))
(assert (= (f3 f16 f25) f22))
(assert (forall ((?v0 S2)) (= (f3 (f11 f12 (f3 f16 ?v0)) ?v0) f22)))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S2)) (let ((?v_0 (f72 f73 ?v0))) (=> (not (= ?v0 f89)) (= (f68 (f69 f90 (f34 ?v_0 ?v1)) (f34 ?v_0 ?v2)) (ite (= (f13 (f14 ?v2) ?v1) f1) (f34 ?v_0 (f18 (f19 f20 ?v1) ?v2)) (f34 (f72 f73 (f68 (f69 f90 f91) ?v0)) (f18 (f19 f20 ?v2) ?v1))))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f12 ?v0))) (=> (not (= ?v0 f92)) (= (f5 (f6 f21 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2)) (ite (= (f13 (f14 ?v2) ?v1) f1) (f3 ?v_0 (f18 (f19 f20 ?v1) ?v2)) (f3 (f11 f12 (f5 (f6 f21 f22) ?v0)) (f18 (f19 f20 ?v2) ?v1))))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S2)) (let ((?v_0 (f23 (f24 f25) ?v2))) (= (f38 (f39 f40 (f35 (f65 (f66 f67 ?v0) ?v1) ?v2)) ?v_0) (f38 (f39 f40 (f35 (f65 (f66 f86 ?v0) ?v1) ?v2)) ?v_0)))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S2)) (let ((?v_0 (f23 (f24 f25) ?v2))) (= (f8 (f9 f10 (f29 (f60 (f61 f62 ?v0) ?v1) ?v2)) ?v_0) (f8 (f9 f10 (f29 (f60 (f61 f85 ?v0) ?v1) ?v2)) ?v_0)))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S2)) (let ((?v_0 (f23 (f24 f25) ?v2))) (= (f50 (f51 f52 (f47 (f75 (f76 f77 ?v0) ?v1) ?v2)) ?v_0) (f50 (f51 f52 (f47 (f75 (f76 f87 ?v0) ?v1) ?v2)) ?v_0)))))
(assert (forall ((?v0 S17) (?v1 S2)) (let ((?v_0 (f72 f73 ?v0))) (=> (not (= ?v0 f91)) (= (f38 (f39 f40 ?v_0) (f23 (f24 f25) ?v1)) (f68 (f69 f90 (f68 (f69 f70 (f34 ?v_0 ?v1)) f91)) (f68 (f69 f70 ?v0) f91)))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f11 f12 ?v0))) (=> (not (= ?v0 f22)) (= (f8 (f9 f10 ?v_0) (f23 (f24 f25) ?v1)) (f5 (f6 f21 (f5 (f6 f63 (f3 ?v_0 ?v1)) f22)) (f5 (f6 f63 ?v0) f22)))))))
(assert (forall ((?v0 S2)) (= (f13 (f14 f25) ?v0) f1)))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f12 ?v0))) (=> (not (= ?v0 f92)) (=> (= (f13 (f14 ?v1) ?v2) f1) (= (f3 ?v_0 (f18 (f19 f20 ?v2) ?v1)) (f5 (f6 f21 (f3 ?v_0 ?v2)) (f3 ?v_0 ?v1))))))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S2)) (let ((?v_0 (f72 f73 ?v0))) (=> (not (= ?v0 f89)) (=> (= (f13 (f14 ?v1) ?v2) f1) (= (f34 ?v_0 (f18 (f19 f20 ?v2) ?v1)) (f68 (f69 f90 (f34 ?v_0 ?v2)) (f34 ?v_0 ?v1))))))))
(assert (forall ((?v0 S17) (?v1 S2)) (let ((?v_0 (f72 f73 ?v0))) (= (f34 ?v_0 ?v1) (ite (= ?v1 f25) f91 (f68 (f69 f71 ?v0) (f34 ?v_0 (f18 (f19 f20 ?v1) f93))))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f19 f94 ?v0))) (= (f18 ?v_0 ?v1) (ite (= ?v1 f25) f93 (f18 (f19 f32 ?v0) (f18 ?v_0 (f18 (f19 f20 ?v1) f93))))))))
(assert (forall ((?v0 S26) (?v1 S2)) (let ((?v_0 (f82 f83 ?v0))) (= (f46 ?v_0 ?v1) (ite (= ?v1 f25) f95 (f78 (f79 f81 ?v0) (f46 ?v_0 (f18 (f19 f20 ?v1) f93))))))))
(assert (forall ((?v0 S4) (?v1 S2)) (let ((?v_0 (f11 f12 ?v0))) (= (f3 ?v_0 ?v1) (ite (= ?v1 f25) f22 (f5 (f6 f7 ?v0) (f3 ?v_0 (f18 (f19 f20 ?v1) f93))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S17)) (let ((?v_0 (f72 f73 ?v2))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f96 f89 ?v2) f1) (=> (= (f96 ?v2 f91) f1) (= (f96 (f34 ?v_0 ?v1) (f34 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f94 ?v2))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f13 (f14 f25) ?v2) f1) (=> (= (f13 (f14 ?v2) f93) f1) (= (f13 (f14 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S26)) (let ((?v_0 (f82 f83 ?v2))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f97 f98 ?v2) f1) (=> (= (f97 ?v2 f95) f1) (= (f97 (f46 ?v_0 ?v1) (f46 ?v_0 ?v0)) f1)))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17) (?v3 S17) (?v4 S17)) (=> (= (f96 ?v0 ?v1) f1) (=> (= (f96 ?v2 ?v1) f1) (=> (= (f96 f89 ?v3) f1) (=> (= (f96 f89 ?v4) f1) (=> (= (f68 (f69 f74 ?v3) ?v4) f91) (= (f96 (f68 (f69 f74 (f68 (f69 f71 ?v3) ?v0)) (f68 (f69 f71 ?v4) ?v2)) ?v1) f1))))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26) (?v3 S26) (?v4 S26)) (=> (= (f97 ?v0 ?v1) f1) (=> (= (f97 ?v2 ?v1) f1) (=> (= (f97 f98 ?v3) f1) (=> (= (f97 f98 ?v4) f1) (=> (= (f78 (f79 f84 ?v3) ?v4) f95) (= (f97 (f78 (f79 f84 (f78 (f79 f81 ?v3) ?v0)) (f78 (f79 f81 ?v4) ?v2)) ?v1) f1))))))))
(assert (forall ((?v0 S16) (?v1 S2) (?v2 S2)) (let ((?v_0 (f24 f25)) (?v_1 (f39 f40 ?v0))) (= (f38 ?v_1 (f23 ?v_0 (f18 (f19 f33 ?v1) ?v2))) (f68 (f69 f74 (f38 (f39 f40 (f35 (f36 f54 ?v0) ?v2)) (f23 ?v_0 ?v1))) (f38 ?v_1 (f23 ?v_0 ?v2)))))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S2)) (let ((?v_0 (f24 f25)) (?v_1 (f44 f45 ?v0))) (= (f43 ?v_1 (f23 ?v_0 (f18 (f19 f33 ?v1) ?v2))) (f18 (f19 f33 (f43 (f44 f45 (f19 (f41 f55 ?v0) ?v2)) (f23 ?v_0 ?v1))) (f43 ?v_1 (f23 ?v_0 ?v2)))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f24 f25)) (?v_1 (f9 f10 ?v0))) (= (f8 ?v_1 (f23 ?v_0 (f18 (f19 f33 ?v1) ?v2))) (f5 (f6 f64 (f8 (f9 f10 (f29 (f30 f53 ?v0) ?v2)) (f23 ?v_0 ?v1))) (f8 ?v_1 (f23 ?v_0 ?v2)))))))
(assert (forall ((?v0 S25) (?v1 S2) (?v2 S2)) (let ((?v_0 (f24 f25)) (?v_1 (f51 f52 ?v0))) (= (f50 ?v_1 (f23 ?v_0 (f18 (f19 f33 ?v1) ?v2))) (f78 (f79 f84 (f50 (f51 f52 (f47 (f48 f56 ?v0) ?v2)) (f23 ?v_0 ?v1))) (f50 ?v_1 (f23 ?v_0 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S16)) (let ((?v_0 (f39 f40 ?v3)) (?v_1 (f24 ?v0))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f13 (f14 ?v1) ?v2) f1) (= (f68 (f69 f70 (f38 ?v_0 (f23 ?v_1 ?v2))) (f38 ?v_0 (f23 ?v_1 ?v1))) (f38 ?v_0 (f23 (f24 ?v1) ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S3)) (let ((?v_0 (f9 f10 ?v3)) (?v_1 (f24 ?v0))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f13 (f14 ?v1) ?v2) f1) (= (f5 (f6 f63 (f8 ?v_0 (f23 ?v_1 ?v2))) (f8 ?v_0 (f23 ?v_1 ?v1))) (f8 ?v_0 (f23 (f24 ?v1) ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S25)) (let ((?v_0 (f51 f52 ?v3)) (?v_1 (f24 ?v0))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f13 (f14 ?v1) ?v2) f1) (= (f78 (f79 f80 (f50 ?v_0 (f23 ?v_1 ?v2))) (f50 ?v_0 (f23 ?v_1 ?v1))) (f50 ?v_0 (f23 (f24 ?v1) ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S16)) (let ((?v_0 (f39 f40 ?v3)) (?v_1 (f24 ?v0))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f13 (f14 ?v1) ?v2) f1) (= (f68 (f69 f74 (f38 ?v_0 (f23 ?v_1 ?v1))) (f38 ?v_0 (f23 (f24 ?v1) ?v2))) (f38 ?v_0 (f23 ?v_1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S11)) (let ((?v_0 (f44 f45 ?v3)) (?v_1 (f24 ?v0))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f13 (f14 ?v1) ?v2) f1) (= (f18 (f19 f33 (f43 ?v_0 (f23 ?v_1 ?v1))) (f43 ?v_0 (f23 (f24 ?v1) ?v2))) (f43 ?v_0 (f23 ?v_1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S3)) (let ((?v_0 (f9 f10 ?v3)) (?v_1 (f24 ?v0))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f13 (f14 ?v1) ?v2) f1) (= (f5 (f6 f64 (f8 ?v_0 (f23 ?v_1 ?v1))) (f8 ?v_0 (f23 (f24 ?v1) ?v2))) (f8 ?v_0 (f23 ?v_1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S25)) (let ((?v_0 (f51 f52 ?v3)) (?v_1 (f24 ?v0))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f13 (f14 ?v1) ?v2) f1) (= (f78 (f79 f84 (f50 ?v_0 (f23 ?v_1 ?v1))) (f50 ?v_0 (f23 (f24 ?v1) ?v2))) (f50 ?v_0 (f23 ?v_1 ?v2))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S17)) (let ((?v_0 (f72 f73 ?v2))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f96 f91 ?v2) f1) (= (f96 (f34 ?v_0 ?v0) (f34 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f94 ?v2))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f13 (f14 f93) ?v2) f1) (= (f13 (f14 (f18 ?v_0 ?v0)) (f18 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S26)) (let ((?v_0 (f82 f83 ?v2))) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f97 f95 ?v2) f1) (= (f97 (f46 ?v_0 ?v0) (f46 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17) (?v3 S17) (?v4 S17)) (let ((?v_0 (f69 f71 ?v0))) (= (f68 (f69 f90 (f68 (f69 f70 (f68 ?v_0 ?v1)) (f68 (f69 f71 ?v2) ?v3))) ?v4) (f68 (f69 f74 (f68 ?v_0 (f68 (f69 f90 (f68 (f69 f70 ?v1) ?v3)) ?v4))) (f68 (f69 f71 (f68 (f69 f90 (f68 (f69 f70 ?v0) ?v2)) ?v4)) ?v3))))))
(assert (forall ((?v0 S4) (?v1 S4) (?v2 S4) (?v3 S4) (?v4 S4)) (let ((?v_0 (f6 f7 ?v0))) (= (f5 (f6 f21 (f5 (f6 f63 (f5 ?v_0 ?v1)) (f5 (f6 f7 ?v2) ?v3))) ?v4) (f5 (f6 f64 (f5 ?v_0 (f5 (f6 f21 (f5 (f6 f63 ?v1) ?v3)) ?v4))) (f5 (f6 f7 (f5 (f6 f21 (f5 (f6 f63 ?v0) ?v2)) ?v4)) ?v3))))))
(assert (forall ((?v0 S2)) (=> (= (f13 (f88 ?v0) f25) f1) false)))
(assert (forall ((?v0 S2)) (not (= (f13 (f88 ?v0) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (not (= (f13 (f88 (f18 (f19 f33 ?v0) ?v1)) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (not (= (f13 (f88 (f18 (f19 f33 ?v0) ?v1)) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (not (= ?v0 ?v1)) (or (= (f13 (f88 ?v0) ?v1) f1) (= (f13 (f88 ?v1) ?v0) f1)))))
(assert (forall ((?v0 S2)) (= (f18 (f19 f32 f93) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= f93 (f18 (f19 f32 ?v0) ?v1)) (and (= ?v0 f93) (= ?v1 f93)))))
(assert (forall ((?v0 S2)) (= (f18 (f19 f32 ?v0) f93) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f18 (f19 f33 ?v0) ?v1) (f18 (f19 f33 ?v1) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_1 (f19 f33 ?v0)) (?v_0 (f19 f33 ?v1))) (= (f18 ?v_1 (f18 ?v_0 ?v2)) (f18 ?v_0 (f18 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f32 ?v0))) (= (f18 ?v_0 (f18 (f19 f33 ?v1) ?v2)) (f18 (f19 f33 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f18 (f19 f32 ?v0) ?v1) f93) (and (= ?v0 f93) (= ?v1 f93)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f33 ?v0))) (= (f18 (f19 f33 (f18 ?v_0 ?v1)) ?v2) (f18 ?v_0 (f18 (f19 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f18 (f19 f32 (f18 (f19 f33 ?v0) ?v1)) ?v2) (f18 (f19 f33 (f18 (f19 f32 ?v0) ?v2)) (f18 (f19 f32 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f33 ?v0))) (= (= (f18 ?v_0 ?v1) (f18 ?v_0 ?v2)) (= ?v1 ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f18 (f19 f33 ?v0) ?v1) (f18 (f19 f33 ?v2) ?v1)) (= ?v0 ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f33 ?v0))) (= (= (f13 (f88 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v2)) f1) (= (f13 (f88 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S17) (?v1 S2)) (let ((?v_0 (f72 f73 ?v0))) (=> (not (= ?v0 f91)) (= (f38 (f39 f40 ?v_0) (f23 (f24 f25) ?v1)) (f68 (f69 f90 (f68 (f69 f70 (f34 ?v_0 ?v1)) f91)) (f68 (f69 f70 ?v0) f91)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= ?v0 ?v1)) (=> (=> (= (f13 (f88 ?v0) ?v1) f1) false) (=> (=> (= (f13 (f88 ?v1) ?v0) f1) false) false)))))
(assert (forall ((?v0 S2)) (=> (= (f13 (f88 ?v0) ?v0) f1) false)))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f13 (f88 ?v0) ?v1) f1) (not (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f13 (f88 ?v0) ?v1) f1) (not (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f88 ?v0))) (=> (= (f13 ?v_0 ?v1) f1) (= (f13 ?v_0 (f18 (f19 f33 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f88 ?v0))) (=> (= (f13 ?v_0 ?v1) f1) (= (f13 ?v_0 (f18 (f19 f33 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f88 ?v0) ?v1) f1) (= (f13 (f88 (f18 (f19 f33 ?v0) ?v2)) (f18 (f19 f33 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f13 (f88 ?v0) ?v1) f1) (=> (= (f13 (f88 ?v2) ?v3) f1) (= (f13 (f88 (f18 (f19 f33 ?v0) ?v2)) (f18 (f19 f33 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f13 (f88 ?v0) ?v1) f1) (=> (= (f18 (f19 f33 ?v2) ?v1) (f18 (f19 f33 ?v0) ?v3)) (= (f13 (f88 ?v2) ?v3) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= ?v0 (f18 (f19 f32 ?v0) ?v1)) (or (= ?v1 f93) (= ?v0 f25)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f88 (f18 (f19 f33 ?v0) ?v1)) ?v2) f1) (= (f13 (f88 ?v0) ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S13)) (let ((?v_0 (= (f13 (f23 ?v2 ?v1) ?v0) f1))) (=> (=> (= (f13 (f88 ?v0) ?v1) f1) ?v_0) (=> (=> (= ?v0 ?v1) ?v_0) (=> (=> (= (f13 (f88 ?v1) ?v0) f1) ?v_0) ?v_0))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f94 ?v0))) (=> (= (f13 (f88 f25) ?v0) f1) (=> (= (f13 (f88 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v2)) f1) (= (f13 (f88 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f88 f25))) (= (= (f13 ?v_0 (f18 (f19 f94 ?v0) ?v1)) f1) (or (= (f13 ?v_0 ?v0) f1) (= ?v1 f25))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f88 f25))) (= (= (f13 ?v_0 (f18 (f19 f33 ?v0) ?v1)) f1) (or (= (f13 ?v_0 ?v0) f1) (= (f13 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f32 ?v2))) (=> (= (f13 (f88 ?v0) ?v1) f1) (=> (= (f13 (f88 f25) ?v2) f1) (= (f13 (f88 (f18 ?v_0 ?v0)) (f18 ?v_0 ?v1)) f1))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f88 ?v0) ?v1) f1) (=> (= (f13 (f88 f25) ?v2) f1) (= (f13 (f88 (f18 (f19 f32 ?v0) ?v2)) (f18 (f19 f32 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f13 (f88 (f18 (f19 f32 ?v0) ?v1)) (f18 (f19 f32 ?v2) ?v1)) f1) (and (= (f13 (f88 f25) ?v1) f1) (= (f13 (f88 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f32 ?v0))) (= (= (f13 (f88 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v2)) f1) (and (= (f13 (f88 f25) ?v0) f1) (= (f13 (f88 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (let ((?v_0 (f88 f25))) (= (= (f13 ?v_0 (f18 (f19 f32 ?v0) ?v1)) f1) (and (= (f13 ?v_0 ?v0) f1) (= (f13 ?v_0 ?v1) f1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (not (= (f13 (f88 ?v0) ?v1) f1)) (= (f18 (f19 f33 ?v1) (f18 (f19 f20 ?v0) ?v1)) ?v0))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f13 (f88 ?v0) (f18 (f19 f20 ?v1) ?v2)) f1) (= (f13 (f88 (f18 (f19 f33 ?v0) ?v2)) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S16)) (let ((?v_0 (f24 f25)) (?v_1 (f39 f40 ?v2))) (= (f38 (f39 f40 (f57 (f58 f59 ?v0) ?v2)) (f23 ?v_0 ?v1)) (f68 (f69 f70 (f38 ?v_1 (f23 ?v_0 (f18 (f19 f33 ?v1) ?v0)))) (f38 ?v_1 (f23 ?v_0 ?v0)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S16)) (let ((?v_0 (f24 f25)) (?v_1 (f39 f40 ?v2))) (= (f38 ?v_1 (f23 ?v_0 (f18 (f19 f33 ?v1) ?v0))) (f68 (f69 f74 (f38 (f39 f40 (f57 (f58 f59 ?v0) ?v2)) (f23 ?v_0 ?v1))) (f38 ?v_1 (f23 ?v_0 ?v0)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f18 (f19 f33 ?v0) ?v1) ?v0) (= ?v1 f25))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f18 (f19 f33 ?v0) ?v1) f25) (and (= ?v0 f25) (= ?v1 f25)))))
(assert (forall ((?v0 S2)) (= (f18 (f19 f33 ?v0) f25) ?v0)))
(assert (forall ((?v0 S2)) (= (f18 (f19 f33 f25) ?v0) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f18 (f19 f32 ?v0) ?v1) (f18 (f19 f32 ?v2) ?v1)) (or (= ?v0 ?v2) (= ?v1 f25)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f32 ?v0))) (= (= (f18 ?v_0 ?v1) (f18 ?v_0 ?v2)) (or (= ?v1 ?v2) (= ?v0 f25))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f18 (f19 f32 ?v0) ?v1) f25) (or (= ?v0 f25) (= ?v1 f25)))))
(assert (forall ((?v0 S2)) (= (f18 (f19 f32 ?v0) f25) f25)))
(assert (forall ((?v0 S2)) (= (f18 (f19 f32 f25) ?v0) f25)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f94 ?v0))) (= (f18 ?v_0 (f18 (f19 f32 ?v1) ?v2)) (f18 (f19 f94 (f18 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S2)) (let ((?v_0 (f72 f73 ?v0))) (= (f34 ?v_0 (f18 (f19 f32 ?v1) ?v2)) (f34 (f72 f73 (f34 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f12 ?v0))) (= (f3 ?v_0 (f18 (f19 f32 ?v1) ?v2)) (f3 (f11 f12 (f3 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S26) (?v1 S2) (?v2 S2)) (let ((?v_0 (f82 f83 ?v0))) (= (f46 ?v_0 (f18 (f19 f32 ?v1) ?v2)) (f46 (f82 f83 (f46 ?v_0 ?v1)) ?v2)))))
(assert (forall ((?v0 S2)) (= (f18 (f19 f94 ?v0) f93) ?v0)))
(assert (forall ((?v0 S17)) (= (f34 (f72 f73 ?v0) f93) ?v0)))
(assert (forall ((?v0 S4)) (= (f3 (f11 f12 ?v0) f93) ?v0)))
(assert (forall ((?v0 S26)) (= (f46 (f82 f83 ?v0) f93) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f14 (f18 (f19 f33 ?v0) ?v1)) ?v2) f1) (=> (=> (= (f13 (f14 ?v0) ?v2) f1) (=> (= (f13 (f14 ?v1) ?v2) f1) false)) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f14 (f18 (f19 f33 ?v0) ?v1)) ?v2) f1) (= (f13 (f14 ?v0) ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f14 (f18 (f19 f33 ?v0) ?v1)) ?v2) f1) (= (f13 (f14 ?v1) ?v2) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f13 (f14 ?v2) ?v3) f1) (= (f13 (f14 (f18 (f19 f33 ?v0) ?v2)) (f18 (f19 f33 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (f13 (f14 (f18 (f19 f33 ?v0) ?v2)) (f18 (f19 f33 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f14 ?v0))) (=> (= (f13 ?v_0 ?v1) f1) (= (f13 ?v_0 (f18 (f19 f33 ?v2) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f14 ?v0))) (=> (= (f13 ?v_0 ?v1) f1) (= (f13 ?v_0 (f18 (f19 f33 ?v1) ?v2)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f33 ?v0))) (= (= (f13 (f14 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v2)) f1) (= (f13 (f14 ?v1) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f13 (f14 ?v0) ?v1) f1) (exists ((?v2 S2)) (= ?v1 (f18 (f19 f33 ?v0) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f13 (f14 ?v0) ?v1) f1) (exists ((?v2 S2)) (= ?v1 (f18 (f19 f33 ?v0) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f13 (f14 ?v0) (f18 (f19 f33 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f13 (f14 ?v0) (f18 (f19 f33 ?v1) ?v0)) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (= (f13 (f14 ?v2) ?v3) f1) (= (f13 (f14 (f18 (f19 f32 ?v0) ?v2)) (f18 (f19 f32 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f32 ?v2))) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (f13 (f14 (f18 ?v_0 ?v0)) (f18 ?v_0 ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (f13 (f14 (f18 (f19 f32 ?v0) ?v2)) (f18 (f19 f32 ?v1) ?v2)) f1))))
(assert (forall ((?v0 S2)) (let ((?v_0 (f19 f32 ?v0))) (= (f13 (f14 ?v0) (f18 ?v_0 (f18 ?v_0 ?v0))) f1))))
(assert (forall ((?v0 S2)) (= (f13 (f14 ?v0) (f18 (f19 f32 ?v0) ?v0)) f1)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f18 (f19 f20 (f18 (f19 f33 ?v0) ?v1)) (f18 (f19 f33 ?v2) ?v1)) (f18 (f19 f20 ?v0) ?v2))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f33 ?v0))) (= (f18 (f19 f20 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v2)) (f18 (f19 f20 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f20 ?v0))) (= (f18 (f19 f20 (f18 ?v_0 ?v1)) ?v2) (f18 ?v_0 (f18 (f19 f33 ?v1) ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f18 (f19 f20 (f18 (f19 f33 ?v0) ?v1)) ?v0) ?v1)))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f18 (f19 f20 (f18 (f19 f33 ?v0) ?v1)) ?v1) ?v0)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (f18 (f19 f32 (f18 (f19 f20 ?v0) ?v1)) ?v2) (f18 (f19 f20 (f18 (f19 f32 ?v0) ?v2)) (f18 (f19 f32 ?v1) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f32 ?v0))) (= (f18 ?v_0 (f18 (f19 f20 ?v1) ?v2)) (f18 (f19 f20 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f13 (f14 (f18 (f19 f32 ?v0) ?v1)) (f18 (f19 f32 ?v2) ?v1)) f1) (=> (= (f13 (f88 f25) ?v1) f1) (= (f13 (f14 ?v0) ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f32 ?v0))) (= (= (f13 (f14 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v2)) f1) (=> (= (f13 (f88 f25) ?v0) f1) (= (f13 (f14 ?v1) ?v2) f1))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (= (= (f13 ?v0 (f18 (f19 f20 ?v1) ?v2)) f1) (and (=> (= (f13 (f88 ?v1) ?v2) f1) (= (f13 ?v0 f25) f1)) (forall ((?v3 S2)) (=> (= ?v1 (f18 (f19 f33 ?v2) ?v3)) (= (f13 ?v0 ?v3) f1)))))))
(assert (forall ((?v0 S8) (?v1 S2) (?v2 S2)) (= (= (f13 ?v0 (f18 (f19 f20 ?v1) ?v2)) f1) (not (or (and (= (f13 (f88 ?v1) ?v2) f1) (not (= (f13 ?v0 f25) f1))) (exists ((?v3 S2)) (and (= ?v1 (f18 (f19 f33 ?v2) ?v3)) (not (= (f13 ?v0 ?v3) f1)))))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f94 ?v0))) (= (f18 ?v_0 (f18 (f19 f33 ?v1) ?v2)) (f18 (f19 f32 (f18 ?v_0 ?v1)) (f18 ?v_0 ?v2))))))
(assert (forall ((?v0 S17) (?v1 S2) (?v2 S2)) (let ((?v_0 (f72 f73 ?v0))) (= (f34 ?v_0 (f18 (f19 f33 ?v1) ?v2)) (f68 (f69 f71 (f34 ?v_0 ?v1)) (f34 ?v_0 ?v2))))))
(assert (forall ((?v0 S4) (?v1 S2) (?v2 S2)) (let ((?v_0 (f11 f12 ?v0))) (= (f3 ?v_0 (f18 (f19 f33 ?v1) ?v2)) (f5 (f6 f7 (f3 ?v_0 ?v1)) (f3 ?v_0 ?v2))))))
(assert (forall ((?v0 S26) (?v1 S2) (?v2 S2)) (let ((?v_0 (f82 f83 ?v0))) (= (f46 ?v_0 (f18 (f19 f33 ?v1) ?v2)) (f78 (f79 f81 (f46 ?v_0 ?v1)) (f46 ?v_0 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f24 ?v0))) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (f99 (f100 (f23 ?v_0 ?v2)) (f23 ?v_0 ?v1)) (f23 (f24 ?v1) ?v2))))))
(assert (forall ((?v0 S26) (?v1 S26) (?v2 S26)) (=> (= (f97 ?v0 ?v1) f1) (= (f101 (f102 ?v0 ?v2) (f102 ?v0 ?v1)) (f102 ?v1 ?v2)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S17)) (=> (= (f96 ?v0 ?v1) f1) (= (f103 (f104 ?v0 ?v2) (f104 ?v0 ?v1)) (f104 ?v1 ?v2)))))
(assert (forall ((?v0 S16) (?v1 S2) (?v2 S2)) (let ((?v_0 (f24 f25))) (= (f38 (f39 f40 (f35 (f36 f37 ?v0) ?v1)) (f23 ?v_0 ?v2)) (f38 (f39 f40 ?v0) (f23 ?v_0 (f18 (f19 f32 ?v2) ?v1)))))))
(assert (forall ((?v0 S3) (?v1 S2) (?v2 S2)) (let ((?v_0 (f24 f25))) (= (f8 (f9 f10 (f29 (f30 f31 ?v0) ?v1)) (f23 ?v_0 ?v2)) (f8 (f9 f10 ?v0) (f23 ?v_0 (f18 (f19 f32 ?v2) ?v1)))))))
(assert (forall ((?v0 S25) (?v1 S2) (?v2 S2)) (let ((?v_0 (f24 f25))) (= (f50 (f51 f52 (f47 (f48 f49 ?v0) ?v1)) (f23 ?v_0 ?v2)) (f50 (f51 f52 ?v0) (f23 ?v_0 (f18 (f19 f32 ?v2) ?v1)))))))
(assert (forall ((?v0 S11) (?v1 S2) (?v2 S2)) (let ((?v_0 (f24 f25))) (= (f43 (f44 f45 (f19 (f41 f42 ?v0) ?v1)) (f23 ?v_0 ?v2)) (f43 (f44 f45 ?v0) (f23 ?v_0 (f18 (f19 f32 ?v2) ?v1)))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (f18 (f19 f20 ?v0) (f18 (f19 f33 ?v0) ?v1)) f25)))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (f18 (f19 f20 (f18 (f19 f33 ?v1) ?v2)) ?v0) (f18 (f19 f33 (f18 (f19 f20 ?v1) ?v0)) ?v2)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (f18 (f19 f33 (f18 (f19 f20 ?v1) ?v0)) ?v2) (f18 (f19 f20 (f18 (f19 f33 ?v1) ?v2)) ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f33 ?v2))) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (f18 (f19 f20 (f18 ?v_0 ?v1)) ?v0) (f18 ?v_0 (f18 (f19 f20 ?v1) ?v0)))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (= (f18 (f19 f20 ?v1) ?v0) ?v2) (= ?v1 (f18 (f19 f33 ?v2) ?v0))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (f18 (f19 f33 (f18 (f19 f20 ?v1) ?v0)) ?v0) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (= (f13 (f14 ?v2) (f18 (f19 f20 ?v1) ?v0)) f1) (= (f13 (f14 (f18 (f19 f33 ?v2) ?v0)) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (let ((?v_0 (f19 f33 ?v2))) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (f18 ?v_0 (f18 (f19 f20 ?v1) ?v0)) (f18 (f19 f20 (f18 ?v_0 ?v1)) ?v0))))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (f18 (f19 f33 ?v0) (f18 (f19 f20 ?v1) ?v0)) ?v1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (f13 (f14 ?v2) (f18 (f19 f20 (f18 (f19 f33 ?v1) ?v2)) ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (= (= (f13 (f14 (f18 (f19 f20 ?v0) ?v1)) ?v2) f1) (= (f13 (f14 ?v0) (f18 (f19 f33 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (= (f18 (f19 f20 ?v2) (f18 (f19 f20 ?v1) ?v0)) (f18 (f19 f20 (f18 (f19 f33 ?v2) ?v0)) ?v1)))))
(assert (forall ((?v0 S2)) (not (= (f3 f16 ?v0) f92))))
(assert (forall ((?v0 S2)) (=> (=> (= ?v0 f25) false) (= (f13 (f88 f25) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f13 (f88 ?v0) ?v1) f1) (not (= ?v1 f25)))))
(assert (forall ((?v0 S2)) (= (= (f13 (f88 ?v0) f25) f1) false)))
(assert (forall ((?v0 S2)) (= (not (= ?v0 f25)) (= (f13 (f88 f25) ?v0) f1))))
(assert (forall ((?v0 S2)) (not (= (f13 (f88 ?v0) f25) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (or (= (f13 (f88 ?v0) ?v1) f1) (= ?v0 ?v1)) (= (f13 (f14 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f13 (f14 ?v0) ?v1) f1) (=> (not (= ?v0 ?v1)) (= (f13 (f88 ?v0) ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f13 (f88 ?v0) ?v1) f1) (= (f13 (f14 ?v0) ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f13 (f14 ?v0) ?v1) f1) (or (= (f13 (f88 ?v0) ?v1) f1) (= ?v0 ?v1)))))
(check-sat)
(exit)