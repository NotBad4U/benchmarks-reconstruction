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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S3 S2) S1)
(declare-fun f4 (S4 S3) S3)
(declare-fun f5 (S2) S4)
(declare-fun f6 (S2 S3) S1)
(declare-fun f7 (S6 S5) S1)
(declare-fun f8 (S7 S6) S6)
(declare-fun f9 (S5) S7)
(declare-fun f10 (S5 S6) S1)
(declare-fun f11 (S9 S8) S1)
(declare-fun f12 (S10 S9) S9)
(declare-fun f13 (S8) S10)
(declare-fun f14 (S8 S9) S1)
(declare-fun f15 (S12 S11) S1)
(declare-fun f16 (S13 S12) S12)
(declare-fun f17 (S11) S13)
(declare-fun f18 (S11 S12) S1)
(declare-fun f19 (S2) S4)
(declare-fun f20 (S5) S7)
(declare-fun f21 (S8) S10)
(declare-fun f22 (S11) S13)
(declare-fun f23 () S3)
(declare-fun f24 () S6)
(declare-fun f25 () S9)
(declare-fun f26 () S12)
(declare-fun f27 () S3)
(declare-fun f28 () S6)
(declare-fun f29 () S9)
(declare-fun f30 () S12)
(declare-fun f31 (S14 S5) S5)
(declare-fun f32 (S15 S11) S14)
(declare-fun f33 () S15)
(declare-fun f34 () S11)
(declare-fun f35 () S5)
(declare-fun f36 (S6) S6)
(declare-fun f37 (S16 S8) S6)
(declare-fun f38 (S2) S16)
(declare-fun f39 () S2)
(declare-fun f40 () S8)
(declare-fun f41 (S17 S11) S5)
(declare-fun f42 () S17)
(declare-fun f43 () S11)
(declare-fun f44 (S5) S7)
(declare-fun f45 () S6)
(declare-fun f46 () S9)
(declare-fun f47 () S11)
(declare-fun f48 (S18 S3) S12)
(declare-fun f49 (S19) S18)
(declare-fun f50 () S19)
(declare-fun f51 () S3)
(declare-fun f52 (S19 S2) S11)
(declare-fun f53 () S3)
(declare-fun f54 () S9)
(declare-fun f55 () S6)
(declare-fun f56 () S12)
(declare-fun f57 (S20 S12) S6)
(declare-fun f58 (S17) S20)
(declare-fun f59 (S14) S7)
(declare-fun f60 (S21 S8) S5)
(declare-fun f61 (S22 S9) S6)
(declare-fun f62 (S21) S22)
(declare-fun f63 (S23 S11) S8)
(declare-fun f64 (S24 S12) S9)
(declare-fun f65 (S23) S24)
(declare-fun f66 (S25 S5) S8)
(declare-fun f67 (S26 S6) S9)
(declare-fun f68 (S25) S26)
(declare-fun f69 (S27 S8) S8)
(declare-fun f70 (S27) S10)
(declare-fun f71 (S28 S11) S11)
(declare-fun f72 (S28) S13)
(declare-fun f73 (S29 S5) S11)
(declare-fun f74 (S30 S6) S12)
(declare-fun f75 (S29) S30)
(declare-fun f76 (S31 S8) S11)
(declare-fun f77 (S32 S9) S12)
(declare-fun f78 (S31) S32)
(declare-fun f79 (S33 S11) S2)
(declare-fun f80 (S34 S12) S3)
(declare-fun f81 (S33) S34)
(declare-fun f82 (S35 S5) S2)
(declare-fun f83 (S36 S6) S3)
(declare-fun f84 (S35) S36)
(declare-fun f85 (S37 S8) S2)
(declare-fun f86 (S38 S9) S3)
(declare-fun f87 (S37) S38)
(declare-fun f88 (S39 S2) S5)
(declare-fun f89 (S40 S3) S6)
(declare-fun f90 (S39) S40)
(declare-fun f91 (S41 S2) S2)
(declare-fun f92 (S41) S4)
(declare-fun f93 (S42 S2) S8)
(declare-fun f94 (S43 S3) S9)
(declare-fun f95 (S42) S43)
(declare-fun f96 (S2) S4)
(declare-fun f97 (S11) S13)
(declare-fun f98 (S8) S10)
(declare-fun f99 () S3)
(declare-fun f100 () S12)
(declare-fun f101 () S9)
(declare-fun f102 (S6) S6)
(declare-fun f103 (S9) S9)
(declare-fun f104 (S12) S12)
(declare-fun f105 (S3) S3)
(assert (not (= f1 f2)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f5 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f6 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f7 (f8 (f9 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f10 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S8)) (= (= (f11 (f12 (f13 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f14 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11)) (= (= (f15 (f16 (f17 ?v0) ?v1) ?v2) f1) (or (= ?v2 ?v0) (= (f18 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f19 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f7 (f8 (f20 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f7 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S8)) (= (= (f11 (f12 (f21 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f11 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11)) (= (= (f15 (f16 (f22 ?v0) ?v1) ?v2) f1) (=> (not (= ?v2 ?v0)) (= (f15 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2)) (= (= (f3 f23 ?v0) f1) false)))
(assert (forall ((?v0 S5)) (= (= (f7 f24 ?v0) f1) false)))
(assert (forall ((?v0 S8)) (= (= (f11 f25 ?v0) f1) false)))
(assert (forall ((?v0 S11)) (= (= (f15 f26 ?v0) f1) false)))
(assert (forall ((?v0 S2)) (= (= (f3 f27 ?v0) f1) true)))
(assert (forall ((?v0 S5)) (= (= (f7 f28 ?v0) f1) true)))
(assert (forall ((?v0 S8)) (= (= (f11 f29 ?v0) f1) true)))
(assert (forall ((?v0 S11)) (= (= (f15 f30 ?v0) f1) true)))
(assert (let ((?v_1 (f36 (f37 (f38 f39) f40))) (?v_0 (f41 f42 f43))) (not (=> (and (= (f10 (f31 (f32 f33 f34) f35) ?v_1) f1) (= (f10 ?v_0 (f36 (f8 (f44 f35) f45))) f1)) (= (f10 ?v_0 ?v_1) f1)))))
(assert (= (f14 f40 f46) f1))
(assert (not (= (f18 f47 (f48 (f49 f50) f51)) f1)))
(assert (forall ((?v0 S2) (?v1 S8)) (= (f10 (f41 f42 (f52 f50 ?v0)) (f37 (f38 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S5)) (=> (= (f10 ?v0 (f36 f45)) f1) false)))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S5) (?v3 S6)) (let ((?v_1 (f44 (f41 f42 ?v0))) (?v_0 (f44 (f31 (f32 f33 ?v1) ?v2)))) (= (f8 ?v_1 (f8 ?v_0 ?v3)) (f8 ?v_0 (f8 ?v_1 ?v3))))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S6)) (let ((?v_0 (f44 (f31 (f32 f33 ?v0) ?v1)))) (= (f36 (f8 ?v_0 ?v2)) (f8 ?v_0 (f36 (f8 (f44 ?v1) ?v2)))))))
(assert (forall ((?v0 S11) (?v1 S6)) (let ((?v_0 (f44 (f41 f42 ?v0)))) (= (f36 (f8 ?v_0 ?v1)) (f8 ?v_0 (f36 ?v1))))))
(assert (forall ((?v0 S8) (?v1 S2)) (=> (= (f14 ?v0 f46) f1) (= (= (f10 (f41 f42 (f52 f50 ?v1)) (f36 (f37 (f38 f39) ?v0))) f1) (= (f6 ?v1 f53) f1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f10 ?v0 ?v1) f1) (= (f10 ?v0 (f36 ?v1)) f1))))
(assert (forall ((?v0 S2)) (= (f3 f51 ?v0) f1)))
(assert (forall ((?v0 S8)) (= (f11 f54 ?v0) f1)))
(assert (forall ((?v0 S5)) (= (f7 f55 ?v0) f1)))
(assert (forall ((?v0 S11)) (= (f15 f56 ?v0) f1)))
(assert (forall ((?v0 S2)) (= (f6 ?v0 f51) f1)))
(assert (forall ((?v0 S11)) (= (f18 ?v0 f56) f1)))
(assert (forall ((?v0 S8)) (= (f14 ?v0 f54) f1)))
(assert (forall ((?v0 S5)) (= (f10 ?v0 f55) f1)))
(assert (forall ((?v0 S2)) (= (= (f6 ?v0 f51) f1) true)))
(assert (forall ((?v0 S11)) (= (= (f18 ?v0 f56) f1) true)))
(assert (forall ((?v0 S8)) (= (= (f14 ?v0 f54) f1) true)))
(assert (forall ((?v0 S5)) (= (= (f10 ?v0 f55) f1) true)))
(assert (forall ((?v0 S5) (?v1 S17) (?v2 S11) (?v3 S12)) (=> (= ?v0 (f41 ?v1 ?v2)) (=> (= (f18 ?v2 ?v3) f1) (= (f10 ?v0 (f57 (f58 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S11) (?v1 S19) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f52 ?v1 ?v2)) (=> (= (f6 ?v2 ?v3) f1) (= (f18 ?v0 (f48 (f49 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S5) (?v1 S14) (?v2 S5) (?v3 S6)) (=> (= ?v0 (f31 ?v1 ?v2)) (=> (= (f10 ?v2 ?v3) f1) (= (f10 ?v0 (f8 (f59 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S5) (?v1 S21) (?v2 S8) (?v3 S9)) (=> (= ?v0 (f60 ?v1 ?v2)) (=> (= (f14 ?v2 ?v3) f1) (= (f10 ?v0 (f61 (f62 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S8) (?v1 S23) (?v2 S11) (?v3 S12)) (=> (= ?v0 (f63 ?v1 ?v2)) (=> (= (f18 ?v2 ?v3) f1) (= (f14 ?v0 (f64 (f65 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S8) (?v1 S25) (?v2 S5) (?v3 S6)) (=> (= ?v0 (f66 ?v1 ?v2)) (=> (= (f10 ?v2 ?v3) f1) (= (f14 ?v0 (f67 (f68 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S8) (?v1 S27) (?v2 S8) (?v3 S9)) (=> (= ?v0 (f69 ?v1 ?v2)) (=> (= (f14 ?v2 ?v3) f1) (= (f14 ?v0 (f12 (f70 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S11) (?v1 S28) (?v2 S11) (?v3 S12)) (=> (= ?v0 (f71 ?v1 ?v2)) (=> (= (f18 ?v2 ?v3) f1) (= (f18 ?v0 (f16 (f72 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S11) (?v1 S29) (?v2 S5) (?v3 S6)) (=> (= ?v0 (f73 ?v1 ?v2)) (=> (= (f10 ?v2 ?v3) f1) (= (f18 ?v0 (f74 (f75 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S11) (?v1 S31) (?v2 S8) (?v3 S9)) (=> (= ?v0 (f76 ?v1 ?v2)) (=> (= (f14 ?v2 ?v3) f1) (= (f18 ?v0 (f77 (f78 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S33) (?v2 S11) (?v3 S12)) (=> (= ?v0 (f79 ?v1 ?v2)) (=> (= (f18 ?v2 ?v3) f1) (= (f6 ?v0 (f80 (f81 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S35) (?v2 S5) (?v3 S6)) (=> (= ?v0 (f82 ?v1 ?v2)) (=> (= (f10 ?v2 ?v3) f1) (= (f6 ?v0 (f83 (f84 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S37) (?v2 S8) (?v3 S9)) (=> (= ?v0 (f85 ?v1 ?v2)) (=> (= (f14 ?v2 ?v3) f1) (= (f6 ?v0 (f86 (f87 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S5) (?v1 S39) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f88 ?v1 ?v2)) (=> (= (f6 ?v2 ?v3) f1) (= (f10 ?v0 (f89 (f90 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S2) (?v1 S41) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f91 ?v1 ?v2)) (=> (= (f6 ?v2 ?v3) f1) (= (f6 ?v0 (f4 (f92 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S8) (?v1 S42) (?v2 S2) (?v3 S3)) (=> (= ?v0 (f93 ?v1 ?v2)) (=> (= (f6 ?v2 ?v3) f1) (= (f14 ?v0 (f94 (f95 ?v1) ?v3)) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S6)) (=> (= (f10 ?v0 (f8 (f44 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f10 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (=> (= (f6 ?v0 (f4 (f96 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f6 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (=> (= (f18 ?v0 (f16 (f97 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f18 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S9)) (=> (= (f14 ?v0 (f12 (f98 ?v1) ?v2)) f1) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f14 ?v0 ?v2) f1) false) false)))))
(assert (forall ((?v0 S2)) (=> (= (f6 ?v0 f99) f1) false)))
(assert (forall ((?v0 S11)) (=> (= (f18 ?v0 f100) f1) false)))
(assert (forall ((?v0 S8)) (=> (= (f14 ?v0 f101) f1) false)))
(assert (forall ((?v0 S5)) (=> (= (f10 ?v0 f45) f1) false)))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (=> (=> (not (= (f10 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f10 ?v0 (f8 (f44 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (=> (not (= (f6 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f6 ?v0 (f4 (f96 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11)) (=> (=> (not (= (f18 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f18 ?v0 (f16 (f97 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S8)) (=> (=> (not (= (f14 ?v0 ?v1) f1)) (= ?v0 ?v2)) (= (f14 ?v0 (f12 (f98 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S8)) (=> (= (f6 ?v0 f53) f1) (= (f10 (f41 f42 (f52 f50 ?v0)) (f37 (f38 f39) ?v1)) f1))))
(assert (forall ((?v0 S11) (?v1 S12)) (= (= (f10 (f41 f42 ?v0) (f57 (f58 f42) ?v1)) f1) (= (f18 ?v0 ?v1) f1))))
(assert (forall ((?v0 S12)) (let ((?v_0 (f57 (f58 f42) ?v0))) (= (f36 ?v_0) ?v_0))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S12)) (not (= (f10 (f31 (f32 f33 ?v0) ?v1) (f57 (f58 f42) ?v2)) f1))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= ?v0 f99) (not (= (f6 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S12) (?v1 S11)) (=> (= ?v0 f100) (not (= (f18 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S9) (?v1 S8)) (=> (= ?v0 f101) (not (= (f14 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S6) (?v1 S5)) (=> (= ?v0 f45) (not (= (f10 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S6)) (= (= (f102 ?v0) f45) (forall ((?v1 S5)) (not (= (f7 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S9)) (= (= (f103 ?v0) f101) (forall ((?v1 S8)) (not (= (f11 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S12)) (= (= (f104 ?v0) f100) (forall ((?v1 S11)) (not (= (f15 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (= (f105 ?v0) f99) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S2)) (= (= (f6 ?v0 f99) f1) false)))
(assert (forall ((?v0 S11)) (= (= (f18 ?v0 f100) f1) false)))
(assert (forall ((?v0 S8)) (= (= (f14 ?v0 f101) f1) false)))
(assert (forall ((?v0 S5)) (= (= (f10 ?v0 f45) f1) false)))
(assert (forall ((?v0 S6)) (= (= f45 (f102 ?v0)) (forall ((?v1 S5)) (not (= (f7 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S9)) (= (= f101 (f103 ?v0)) (forall ((?v1 S8)) (not (= (f11 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S12)) (= (= f100 (f104 ?v0)) (forall ((?v1 S11)) (not (= (f15 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (= f99 (f105 ?v0)) (forall ((?v1 S2)) (not (= (f3 ?v0 ?v1) f1))))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (=> (= (f6 ?v1 f99) f1) (= (f3 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S12)) (= (forall ((?v1 S11)) (=> (= (f18 ?v1 f100) f1) (= (f15 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S9)) (= (forall ((?v1 S8)) (=> (= (f14 ?v1 f101) f1) (= (f11 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S6)) (= (forall ((?v1 S5)) (=> (= (f10 ?v1 f45) f1) (= (f7 ?v0 ?v1) f1))) true)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (and (= (f6 ?v1 f99) f1) (= (f3 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S12)) (= (exists ((?v1 S11)) (and (= (f18 ?v1 f100) f1) (= (f15 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S9)) (= (exists ((?v1 S8)) (and (= (f14 ?v1 f101) f1) (= (f11 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S6)) (= (exists ((?v1 S5)) (and (= (f10 ?v1 f45) f1) (= (f7 ?v0 ?v1) f1))) false)))
(assert (forall ((?v0 S3)) (= (exists ((?v1 S2)) (= (f6 ?v1 ?v0) f1)) (not (= ?v0 f99)))))
(assert (forall ((?v0 S12)) (= (exists ((?v1 S11)) (= (f18 ?v1 ?v0) f1)) (not (= ?v0 f100)))))
(assert (forall ((?v0 S9)) (= (exists ((?v1 S8)) (= (f14 ?v1 ?v0) f1)) (not (= ?v0 f101)))))
(assert (forall ((?v0 S6)) (= (exists ((?v1 S5)) (= (f10 ?v1 ?v0) f1)) (not (= ?v0 f45)))))
(assert (forall ((?v0 S3)) (= (forall ((?v1 S2)) (not (= (f6 ?v1 ?v0) f1))) (= ?v0 f99))))
(assert (forall ((?v0 S12)) (= (forall ((?v1 S11)) (not (= (f18 ?v1 ?v0) f1))) (= ?v0 f100))))
(assert (forall ((?v0 S9)) (= (forall ((?v1 S8)) (not (= (f14 ?v1 ?v0) f1))) (= ?v0 f101))))
(assert (forall ((?v0 S6)) (= (forall ((?v1 S5)) (not (= (f10 ?v1 ?v0) f1))) (= ?v0 f45))))
(assert (= f45 (f102 f24)))
(assert (= f101 (f103 f25)))
(assert (= f100 (f104 f26)))
(assert (= f99 (f105 f23)))
(assert (forall ((?v0 S2)) (= (= (f3 f99 ?v0) f1) (= (f6 ?v0 f99) f1))))
(assert (forall ((?v0 S11)) (= (= (f15 f100 ?v0) f1) (= (f18 ?v0 f100) f1))))
(assert (forall ((?v0 S8)) (= (= (f11 f101 ?v0) f1) (= (f14 ?v0 f101) f1))))
(assert (forall ((?v0 S5)) (= (= (f7 f45 ?v0) f1) (= (f10 ?v0 f45) f1))))
(assert (forall ((?v0 S5) (?v1 S6)) (=> (= (f10 ?v0 ?v1) f1) (= (f8 (f44 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S2) (?v1 S3)) (=> (= (f6 ?v0 ?v1) f1) (= (f4 (f96 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S11) (?v1 S12)) (=> (= (f18 ?v0 ?v1) f1) (= (f16 (f97 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S8) (?v1 S9)) (=> (= (f14 ?v0 ?v1) f1) (= (f12 (f98 ?v0) ?v1) ?v1))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (=> (= (f10 ?v0 ?v1) f1) (= (f10 ?v0 (f8 (f44 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (=> (= (f6 ?v0 ?v1) f1) (= (f6 ?v0 (f4 (f96 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11)) (=> (= (f18 ?v0 ?v1) f1) (= (f18 ?v0 (f16 (f97 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S8)) (=> (= (f14 ?v0 ?v1) f1) (= (f14 ?v0 (f12 (f98 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S6)) (let ((?v_0 (f44 ?v0))) (=> (not (= (f10 ?v0 ?v1) f1)) (=> (not (= (f10 ?v0 ?v2) f1)) (= (= (f8 ?v_0 ?v1) (f8 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S3)) (let ((?v_0 (f96 ?v0))) (=> (not (= (f6 ?v0 ?v1) f1)) (=> (not (= (f6 ?v0 ?v2) f1)) (= (= (f4 ?v_0 ?v1) (f4 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S12)) (let ((?v_0 (f97 ?v0))) (=> (not (= (f18 ?v0 ?v1) f1)) (=> (not (= (f18 ?v0 ?v2) f1)) (= (= (f16 ?v_0 ?v1) (f16 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S9)) (let ((?v_0 (f98 ?v0))) (=> (not (= (f14 ?v0 ?v1) f1)) (=> (not (= (f14 ?v0 ?v2) f1)) (= (= (f12 ?v_0 ?v1) (f12 ?v_0 ?v2)) (= ?v1 ?v2)))))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5)) (= (= (f7 (f8 (f44 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f7 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S8)) (= (= (f11 (f12 (f98 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f11 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2)) (= (= (f3 (f4 (f96 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f3 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11)) (= (= (f15 (f16 (f97 ?v0) ?v1) ?v2) f1) (or (= ?v0 ?v2) (= (f15 ?v1 ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S6)) (= (= (f10 ?v0 (f8 (f44 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f10 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (= (= (f6 ?v0 (f4 (f96 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f6 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (= (= (f18 ?v0 (f16 (f97 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f18 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S9)) (= (= (f14 ?v0 (f12 (f98 ?v1) ?v2)) f1) (or (= ?v0 ?v1) (= (f14 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S6)) (let ((?v_1 (f44 ?v0)) (?v_0 (f44 ?v1))) (= (f8 ?v_1 (f8 ?v_0 ?v2)) (f8 ?v_0 (f8 ?v_1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S9)) (let ((?v_1 (f98 ?v0)) (?v_0 (f98 ?v1))) (= (f12 ?v_1 (f12 ?v_0 ?v2)) (f12 ?v_0 (f12 ?v_1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S3)) (let ((?v_1 (f96 ?v0)) (?v_0 (f96 ?v1))) (= (f4 ?v_1 (f4 ?v_0 ?v2)) (f4 ?v_0 (f4 ?v_1 ?v2))))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S12)) (let ((?v_1 (f97 ?v0)) (?v_0 (f97 ?v1))) (= (f16 ?v_1 (f16 ?v_0 ?v2)) (f16 ?v_0 (f16 ?v_1 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S6)) (let ((?v_0 (f44 ?v0))) (let ((?v_1 (f8 ?v_0 ?v1))) (= (f8 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S8) (?v1 S9)) (let ((?v_0 (f98 ?v0))) (let ((?v_1 (f12 ?v_0 ?v1))) (= (f12 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (let ((?v_0 (f96 ?v0))) (let ((?v_1 (f4 ?v_0 ?v1))) (= (f4 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S11) (?v1 S12)) (let ((?v_0 (f97 ?v0))) (let ((?v_1 (f16 ?v_0 ?v1))) (= (f16 ?v_0 ?v_1) ?v_1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (= (f8 (f44 ?v0) (f102 ?v1)) (f102 (f8 (f20 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S9)) (= (f12 (f98 ?v0) (f103 ?v1)) (f103 (f12 (f21 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f96 ?v0) (f105 ?v1)) (f105 (f4 (f19 ?v0) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S12)) (= (f16 (f97 ?v0) (f104 ?v1)) (f104 (f16 (f22 ?v0) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (= (f8 (f44 ?v0) ?v1) (f102 (f8 (f9 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f4 (f96 ?v0) ?v1) (f105 (f4 (f5 ?v0) ?v1)))))
(assert (forall ((?v0 S11) (?v1 S12)) (= (f16 (f97 ?v0) ?v1) (f104 (f16 (f17 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S9)) (= (f12 (f98 ?v0) ?v1) (f103 (f12 (f13 ?v0) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (= (f10 ?v0 (f8 (f44 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S3)) (= (f6 ?v0 (f4 (f96 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S11) (?v1 S12)) (= (f18 ?v0 (f16 (f97 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S8) (?v1 S9)) (= (f14 ?v0 (f12 (f98 ?v0) ?v1)) f1)))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S11) (?v3 S19)) (=> (= (f6 ?v0 ?v1) f1) (=> (= ?v2 (f52 ?v3 ?v0)) (= (f18 ?v2 (f48 (f49 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S5) (?v3 S17)) (=> (= (f18 ?v0 ?v1) f1) (=> (= ?v2 (f41 ?v3 ?v0)) (= (f10 ?v2 (f57 (f58 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S5) (?v3 S14)) (=> (= (f10 ?v0 ?v1) f1) (=> (= ?v2 (f31 ?v3 ?v0)) (= (f10 ?v2 (f8 (f59 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S5) (?v3 S21)) (=> (= (f14 ?v0 ?v1) f1) (=> (= ?v2 (f60 ?v3 ?v0)) (= (f10 ?v2 (f61 (f62 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S8) (?v3 S23)) (=> (= (f18 ?v0 ?v1) f1) (=> (= ?v2 (f63 ?v3 ?v0)) (= (f14 ?v2 (f64 (f65 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S8) (?v3 S25)) (=> (= (f10 ?v0 ?v1) f1) (=> (= ?v2 (f66 ?v3 ?v0)) (= (f14 ?v2 (f67 (f68 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S8) (?v3 S27)) (=> (= (f14 ?v0 ?v1) f1) (=> (= ?v2 (f69 ?v3 ?v0)) (= (f14 ?v2 (f12 (f70 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S11) (?v3 S28)) (=> (= (f18 ?v0 ?v1) f1) (=> (= ?v2 (f71 ?v3 ?v0)) (= (f18 ?v2 (f16 (f72 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S11) (?v3 S29)) (=> (= (f10 ?v0 ?v1) f1) (=> (= ?v2 (f73 ?v3 ?v0)) (= (f18 ?v2 (f74 (f75 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S11) (?v3 S31)) (=> (= (f14 ?v0 ?v1) f1) (=> (= ?v2 (f76 ?v3 ?v0)) (= (f18 ?v2 (f77 (f78 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S2) (?v3 S33)) (=> (= (f18 ?v0 ?v1) f1) (=> (= ?v2 (f79 ?v3 ?v0)) (= (f6 ?v2 (f80 (f81 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S2) (?v3 S35)) (=> (= (f10 ?v0 ?v1) f1) (=> (= ?v2 (f82 ?v3 ?v0)) (= (f6 ?v2 (f83 (f84 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S2) (?v3 S37)) (=> (= (f14 ?v0 ?v1) f1) (=> (= ?v2 (f85 ?v3 ?v0)) (= (f6 ?v2 (f86 (f87 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S5) (?v3 S39)) (=> (= (f6 ?v0 ?v1) f1) (=> (= ?v2 (f88 ?v3 ?v0)) (= (f10 ?v2 (f89 (f90 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S2) (?v3 S41)) (=> (= (f6 ?v0 ?v1) f1) (=> (= ?v2 (f91 ?v3 ?v0)) (= (f6 ?v2 (f4 (f92 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S8) (?v3 S42)) (=> (= (f6 ?v0 ?v1) f1) (=> (= ?v2 (f93 ?v3 ?v0)) (= (f14 ?v2 (f94 (f95 ?v3) ?v1)) f1)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S19)) (=> (= (f6 ?v0 ?v1) f1) (= (f18 (f52 ?v2 ?v0) (f48 (f49 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S17)) (=> (= (f18 ?v0 ?v1) f1) (= (f10 (f41 ?v2 ?v0) (f57 (f58 ?v2) ?v1)) f1))))
(assert (forall ((?v0 S11) (?v1 S19) (?v2 S3)) (= (= (f18 ?v0 (f48 (f49 ?v1) ?v2)) f1) (exists ((?v3 S2)) (and (= (f6 ?v3 ?v2) f1) (= ?v0 (f52 ?v1 ?v3)))))))
(assert (forall ((?v0 S5) (?v1 S17) (?v2 S12)) (= (= (f10 ?v0 (f57 (f58 ?v1) ?v2)) f1) (exists ((?v3 S11)) (and (= (f18 ?v3 ?v2) f1) (= ?v0 (f41 ?v1 ?v3)))))))
(assert (= f55 (f102 f28)))
(assert (= f56 (f104 f30)))
(assert (= f54 (f103 f29)))
(assert (= f51 (f105 f27)))
(assert (forall ((?v0 S5) (?v1 S6)) (let ((?v_0 (f36 ?v1))) (=> (= (f10 ?v0 (f36 ?v_0)) f1) (= (f10 ?v0 ?v_0) f1)))))
(assert (forall ((?v0 S6)) (let ((?v_0 (f36 ?v0))) (= (f36 ?v_0) ?v_0))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f41 f42 ?v0) (f41 f42 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S11) (?v1 S5) (?v2 S11) (?v3 S5)) (= (= (f31 (f32 f33 ?v0) ?v1) (f31 (f32 f33 ?v2) ?v3)) (and (= ?v0 ?v2) (= ?v1 ?v3)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f52 f50 ?v0) (f52 f50 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f16 (f97 ?v0) f100) (f16 (f97 ?v1) f100)) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f4 (f96 ?v0) f99) (f4 (f96 ?v1) f99)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f12 (f98 ?v0) f101) (f12 (f98 ?v1) f101)) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f8 (f44 ?v0) f45) (f8 (f44 ?v1) f45)) (= ?v0 ?v1))))
(assert (forall ((?v0 S8) (?v1 S8)) (=> (= (f14 ?v0 (f12 (f98 ?v1) f101)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f18 ?v0 (f16 (f97 ?v1) f100)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f6 ?v0 (f4 (f96 ?v1) f99)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S5) (?v1 S5)) (=> (= (f10 ?v0 (f8 (f44 ?v1) f45)) f1) (=> (=> (= ?v0 ?v1) false) false))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11) (?v3 S11)) (= (= (f16 (f97 ?v0) (f16 (f97 ?v1) f100)) (f16 (f97 ?v2) (f16 (f97 ?v3) f100))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2) (?v3 S2)) (= (= (f4 (f96 ?v0) (f4 (f96 ?v1) f99)) (f4 (f96 ?v2) (f4 (f96 ?v3) f99))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8) (?v2 S8) (?v3 S8)) (= (= (f12 (f98 ?v0) (f12 (f98 ?v1) f101)) (f12 (f98 ?v2) (f12 (f98 ?v3) f101))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S5) (?v3 S5)) (= (= (f8 (f44 ?v0) (f8 (f44 ?v1) f45)) (f8 (f44 ?v2) (f8 (f44 ?v3) f45))) (or (and (= ?v0 ?v2) (= ?v1 ?v3)) (and (= ?v0 ?v3) (= ?v1 ?v2))))))
(assert (forall ((?v0 S8) (?v1 S8)) (= (= (f14 ?v0 (f12 (f98 ?v1) f101)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f18 ?v0 (f16 (f97 ?v1) f100)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f6 ?v0 (f4 (f96 ?v1) f99)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f10 ?v0 (f8 (f44 ?v1) f45)) f1) (= ?v0 ?v1))))
(assert (forall ((?v0 S11) (?v1 S12)) (not (= (f16 (f97 ?v0) ?v1) f100))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= (f4 (f96 ?v0) ?v1) f99))))
(assert (forall ((?v0 S8) (?v1 S9)) (not (= (f12 (f98 ?v0) ?v1) f101))))
(assert (forall ((?v0 S5) (?v1 S6)) (not (= (f8 (f44 ?v0) ?v1) f45))))
(assert (forall ((?v0 S11) (?v1 S12)) (not (= f100 (f16 (f97 ?v0) ?v1)))))
(assert (forall ((?v0 S2) (?v1 S3)) (not (= f99 (f4 (f96 ?v0) ?v1)))))
(assert (forall ((?v0 S8) (?v1 S9)) (not (= f101 (f12 (f98 ?v0) ?v1)))))
(assert (forall ((?v0 S5) (?v1 S6)) (not (= f45 (f8 (f44 ?v0) ?v1)))))
(assert (forall ((?v0 S39) (?v1 S3)) (= (= (f89 (f90 ?v0) ?v1) f45) (= ?v1 f99))))
(assert (forall ((?v0 S21) (?v1 S9)) (= (= (f61 (f62 ?v0) ?v1) f45) (= ?v1 f101))))
(assert (forall ((?v0 S35) (?v1 S6)) (= (= (f83 (f84 ?v0) ?v1) f99) (= ?v1 f45))))
(assert (forall ((?v0 S29) (?v1 S6)) (= (= (f74 (f75 ?v0) ?v1) f100) (= ?v1 f45))))
(assert (forall ((?v0 S25) (?v1 S6)) (= (= (f67 (f68 ?v0) ?v1) f101) (= ?v1 f45))))
(assert (forall ((?v0 S19) (?v1 S3)) (= (= (f48 (f49 ?v0) ?v1) f100) (= ?v1 f99))))
(assert (forall ((?v0 S17) (?v1 S12)) (= (= (f57 (f58 ?v0) ?v1) f45) (= ?v1 f100))))
(assert (forall ((?v0 S35)) (= (f83 (f84 ?v0) f45) f99)))
(assert (forall ((?v0 S29)) (= (f74 (f75 ?v0) f45) f100)))
(assert (forall ((?v0 S25)) (= (f67 (f68 ?v0) f45) f101)))
(assert (forall ((?v0 S39)) (= (f89 (f90 ?v0) f99) f45)))
(assert (forall ((?v0 S21)) (= (f61 (f62 ?v0) f101) f45)))
(assert (forall ((?v0 S19)) (= (f48 (f49 ?v0) f99) f100)))
(assert (forall ((?v0 S17)) (= (f57 (f58 ?v0) f100) f45)))
(assert (forall ((?v0 S39) (?v1 S3)) (= (= f45 (f89 (f90 ?v0) ?v1)) (= ?v1 f99))))
(assert (forall ((?v0 S21) (?v1 S9)) (= (= f45 (f61 (f62 ?v0) ?v1)) (= ?v1 f101))))
(assert (forall ((?v0 S35) (?v1 S6)) (= (= f99 (f83 (f84 ?v0) ?v1)) (= ?v1 f45))))
(assert (forall ((?v0 S29) (?v1 S6)) (= (= f100 (f74 (f75 ?v0) ?v1)) (= ?v1 f45))))
(assert (forall ((?v0 S25) (?v1 S6)) (= (= f101 (f67 (f68 ?v0) ?v1)) (= ?v1 f45))))
(assert (forall ((?v0 S19) (?v1 S3)) (= (= f100 (f48 (f49 ?v0) ?v1)) (= ?v1 f99))))
(assert (forall ((?v0 S17) (?v1 S12)) (= (= f45 (f57 (f58 ?v0) ?v1)) (= ?v1 f100))))
(assert (not (= f56 f100)))
(assert (not (= f54 f101)))
(assert (not (= f51 f99)))
(assert (not (= f55 f45)))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S29)) (let ((?v_0 (f74 (f75 ?v2) ?v1))) (=> (= (f10 ?v0 ?v1) f1) (= (f16 (f97 (f73 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S35)) (let ((?v_0 (f83 (f84 ?v2) ?v1))) (=> (= (f10 ?v0 ?v1) f1) (= (f4 (f96 (f82 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S5) (?v1 S6) (?v2 S25)) (let ((?v_0 (f67 (f68 ?v2) ?v1))) (=> (= (f10 ?v0 ?v1) f1) (= (f12 (f98 (f66 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S31)) (let ((?v_0 (f77 (f78 ?v2) ?v1))) (=> (= (f14 ?v0 ?v1) f1) (= (f16 (f97 (f76 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S37)) (let ((?v_0 (f86 (f87 ?v2) ?v1))) (=> (= (f14 ?v0 ?v1) f1) (= (f4 (f96 (f85 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S8) (?v1 S9) (?v2 S27)) (let ((?v_0 (f12 (f70 ?v2) ?v1))) (=> (= (f14 ?v0 ?v1) f1) (= (f12 (f98 (f69 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S28)) (let ((?v_0 (f16 (f72 ?v2) ?v1))) (=> (= (f18 ?v0 ?v1) f1) (= (f16 (f97 (f71 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S33)) (let ((?v_0 (f80 (f81 ?v2) ?v1))) (=> (= (f18 ?v0 ?v1) f1) (= (f4 (f96 (f79 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S23)) (let ((?v_0 (f64 (f65 ?v2) ?v1))) (=> (= (f18 ?v0 ?v1) f1) (= (f12 (f98 (f63 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S41)) (let ((?v_0 (f4 (f92 ?v2) ?v1))) (=> (= (f6 ?v0 ?v1) f1) (= (f4 (f96 (f91 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S42)) (let ((?v_0 (f94 (f95 ?v2) ?v1))) (=> (= (f6 ?v0 ?v1) f1) (= (f12 (f98 (f93 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S2) (?v1 S3) (?v2 S19)) (let ((?v_0 (f48 (f49 ?v2) ?v1))) (=> (= (f6 ?v0 ?v1) f1) (= (f16 (f97 (f52 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S11) (?v1 S12) (?v2 S17)) (let ((?v_0 (f57 (f58 ?v2) ?v1))) (=> (= (f18 ?v0 ?v1) f1) (= (f8 (f44 (f41 ?v2 ?v0)) ?v_0) ?v_0)))))
(assert (forall ((?v0 S39) (?v1 S2) (?v2 S3)) (let ((?v_0 (f90 ?v0))) (= (f8 (f44 (f88 ?v0 ?v1)) (f89 ?v_0 ?v2)) (f89 ?v_0 (f4 (f96 ?v1) ?v2))))))
(assert (forall ((?v0 S21) (?v1 S8) (?v2 S9)) (let ((?v_0 (f62 ?v0))) (= (f8 (f44 (f60 ?v0 ?v1)) (f61 ?v_0 ?v2)) (f61 ?v_0 (f12 (f98 ?v1) ?v2))))))
(assert (forall ((?v0 S29) (?v1 S5) (?v2 S6)) (let ((?v_0 (f75 ?v0))) (= (f16 (f97 (f73 ?v0 ?v1)) (f74 ?v_0 ?v2)) (f74 ?v_0 (f8 (f44 ?v1) ?v2))))))
(assert (forall ((?v0 S35) (?v1 S5) (?v2 S6)) (let ((?v_0 (f84 ?v0))) (= (f4 (f96 (f82 ?v0 ?v1)) (f83 ?v_0 ?v2)) (f83 ?v_0 (f8 (f44 ?v1) ?v2))))))
(assert (forall ((?v0 S25) (?v1 S5) (?v2 S6)) (let ((?v_0 (f68 ?v0))) (= (f12 (f98 (f66 ?v0 ?v1)) (f67 ?v_0 ?v2)) (f67 ?v_0 (f8 (f44 ?v1) ?v2))))))
(assert (forall ((?v0 S19) (?v1 S2) (?v2 S3)) (let ((?v_0 (f49 ?v0))) (= (f16 (f97 (f52 ?v0 ?v1)) (f48 ?v_0 ?v2)) (f48 ?v_0 (f4 (f96 ?v1) ?v2))))))
(assert (forall ((?v0 S17) (?v1 S11) (?v2 S12)) (let ((?v_0 (f58 ?v0))) (= (f8 (f44 (f41 ?v0 ?v1)) (f57 ?v_0 ?v2)) (f57 ?v_0 (f16 (f97 ?v1) ?v2))))))
(assert (forall ((?v0 S29) (?v1 S5) (?v2 S6)) (let ((?v_0 (f75 ?v0))) (= (f74 ?v_0 (f8 (f44 ?v1) ?v2)) (f16 (f97 (f73 ?v0 ?v1)) (f74 ?v_0 ?v2))))))
(assert (forall ((?v0 S35) (?v1 S5) (?v2 S6)) (let ((?v_0 (f84 ?v0))) (= (f83 ?v_0 (f8 (f44 ?v1) ?v2)) (f4 (f96 (f82 ?v0 ?v1)) (f83 ?v_0 ?v2))))))
(assert (forall ((?v0 S25) (?v1 S5) (?v2 S6)) (let ((?v_0 (f68 ?v0))) (= (f67 ?v_0 (f8 (f44 ?v1) ?v2)) (f12 (f98 (f66 ?v0 ?v1)) (f67 ?v_0 ?v2))))))
(assert (forall ((?v0 S39) (?v1 S2) (?v2 S3)) (let ((?v_0 (f90 ?v0))) (= (f89 ?v_0 (f4 (f96 ?v1) ?v2)) (f8 (f44 (f88 ?v0 ?v1)) (f89 ?v_0 ?v2))))))
(assert (forall ((?v0 S21) (?v1 S8) (?v2 S9)) (let ((?v_0 (f62 ?v0))) (= (f61 ?v_0 (f12 (f98 ?v1) ?v2)) (f8 (f44 (f60 ?v0 ?v1)) (f61 ?v_0 ?v2))))))
(assert (forall ((?v0 S19) (?v1 S2) (?v2 S3)) (let ((?v_0 (f49 ?v0))) (= (f48 ?v_0 (f4 (f96 ?v1) ?v2)) (f16 (f97 (f52 ?v0 ?v1)) (f48 ?v_0 ?v2))))))
(assert (forall ((?v0 S17) (?v1 S11) (?v2 S12)) (let ((?v_0 (f58 ?v0))) (= (f57 ?v_0 (f16 (f97 ?v1) ?v2)) (f8 (f44 (f41 ?v0 ?v1)) (f57 ?v_0 ?v2))))))
(assert (forall ((?v0 S5) (?v1 S14) (?v2 S5)) (=> (= ?v0 (f31 ?v1 ?v2)) (= (f10 ?v0 (f8 (f59 ?v1) f55)) f1))))
(assert (forall ((?v0 S5) (?v1 S21) (?v2 S8)) (=> (= ?v0 (f60 ?v1 ?v2)) (= (f10 ?v0 (f61 (f62 ?v1) f54)) f1))))
(assert (forall ((?v0 S8) (?v1 S23) (?v2 S11)) (=> (= ?v0 (f63 ?v1 ?v2)) (= (f14 ?v0 (f64 (f65 ?v1) f56)) f1))))
(assert (forall ((?v0 S8) (?v1 S25) (?v2 S5)) (=> (= ?v0 (f66 ?v1 ?v2)) (= (f14 ?v0 (f67 (f68 ?v1) f55)) f1))))
(assert (forall ((?v0 S8) (?v1 S27) (?v2 S8)) (=> (= ?v0 (f69 ?v1 ?v2)) (= (f14 ?v0 (f12 (f70 ?v1) f54)) f1))))
(assert (forall ((?v0 S11) (?v1 S28) (?v2 S11)) (=> (= ?v0 (f71 ?v1 ?v2)) (= (f18 ?v0 (f16 (f72 ?v1) f56)) f1))))
(assert (forall ((?v0 S11) (?v1 S29) (?v2 S5)) (=> (= ?v0 (f73 ?v1 ?v2)) (= (f18 ?v0 (f74 (f75 ?v1) f55)) f1))))
(assert (forall ((?v0 S11) (?v1 S31) (?v2 S8)) (=> (= ?v0 (f76 ?v1 ?v2)) (= (f18 ?v0 (f77 (f78 ?v1) f54)) f1))))
(assert (forall ((?v0 S2) (?v1 S33) (?v2 S11)) (=> (= ?v0 (f79 ?v1 ?v2)) (= (f6 ?v0 (f80 (f81 ?v1) f56)) f1))))
(assert (forall ((?v0 S2) (?v1 S35) (?v2 S5)) (=> (= ?v0 (f82 ?v1 ?v2)) (= (f6 ?v0 (f83 (f84 ?v1) f55)) f1))))
(assert (forall ((?v0 S2) (?v1 S37) (?v2 S8)) (=> (= ?v0 (f85 ?v1 ?v2)) (= (f6 ?v0 (f86 (f87 ?v1) f54)) f1))))
(assert (forall ((?v0 S11) (?v1 S19) (?v2 S2)) (=> (= ?v0 (f52 ?v1 ?v2)) (= (f18 ?v0 (f48 (f49 ?v1) f51)) f1))))
(assert (forall ((?v0 S5) (?v1 S17) (?v2 S11)) (=> (= ?v0 (f41 ?v1 ?v2)) (= (f10 ?v0 (f57 (f58 ?v1) f56)) f1))))
(assert (forall ((?v0 S14) (?v1 S5)) (= (f10 (f31 ?v0 ?v1) (f8 (f59 ?v0) f55)) f1)))
(assert (forall ((?v0 S21) (?v1 S8)) (= (f10 (f60 ?v0 ?v1) (f61 (f62 ?v0) f54)) f1)))
(assert (forall ((?v0 S23) (?v1 S11)) (= (f14 (f63 ?v0 ?v1) (f64 (f65 ?v0) f56)) f1)))
(assert (forall ((?v0 S25) (?v1 S5)) (= (f14 (f66 ?v0 ?v1) (f67 (f68 ?v0) f55)) f1)))
(assert (forall ((?v0 S27) (?v1 S8)) (= (f14 (f69 ?v0 ?v1) (f12 (f70 ?v0) f54)) f1)))
(assert (forall ((?v0 S28) (?v1 S11)) (= (f18 (f71 ?v0 ?v1) (f16 (f72 ?v0) f56)) f1)))
(assert (forall ((?v0 S29) (?v1 S5)) (= (f18 (f73 ?v0 ?v1) (f74 (f75 ?v0) f55)) f1)))
(assert (forall ((?v0 S31) (?v1 S8)) (= (f18 (f76 ?v0 ?v1) (f77 (f78 ?v0) f54)) f1)))
(assert (forall ((?v0 S33) (?v1 S11)) (= (f6 (f79 ?v0 ?v1) (f80 (f81 ?v0) f56)) f1)))
(assert (forall ((?v0 S35) (?v1 S5)) (= (f6 (f82 ?v0 ?v1) (f83 (f84 ?v0) f55)) f1)))
(assert (forall ((?v0 S37) (?v1 S8)) (= (f6 (f85 ?v0 ?v1) (f86 (f87 ?v0) f54)) f1)))
(assert (forall ((?v0 S19) (?v1 S2)) (= (f18 (f52 ?v0 ?v1) (f48 (f49 ?v0) f51)) f1)))
(assert (forall ((?v0 S17) (?v1 S11)) (= (f10 (f41 ?v0 ?v1) (f57 (f58 ?v0) f56)) f1)))
(assert (forall ((?v0 S5) (?v1 S6)) (let ((?v_0 (f36 ?v1))) (=> (= (f10 ?v0 ?v_0) f1) (= (f36 (f8 (f44 ?v0) ?v1)) ?v_0)))))
(check-sat)
(exit)