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
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S2) S1)
(declare-fun f4 (S4 S3) S2)
(declare-fun f5 () S4)
(declare-fun f6 () S2)
(declare-fun f7 (S5 S3) S3)
(declare-fun f8 (S6 S7) S5)
(declare-fun f9 () S6)
(declare-fun f10 () S7)
(declare-fun f11 (S8 S2) S2)
(declare-fun f12 () S8)
(declare-fun f13 (S2 S2) S1)
(declare-fun f14 () S2)
(declare-fun f15 () S2)
(declare-fun f16 () S3)
(declare-fun f17 (S9 S9) S1)
(declare-fun f18 (S10 S10) S1)
(declare-fun f19 (S11 S11) S1)
(declare-fun f20 (S12 S7) S7)
(declare-fun f21 () S12)
(declare-fun f22 () S5)
(declare-fun f23 (S13 S9) S8)
(declare-fun f24 () S13)
(declare-fun f25 (S14 S9) S9)
(declare-fun f26 () S14)
(declare-fun f27 (S16 S10) S10)
(declare-fun f28 (S17 S15) S16)
(declare-fun f29 () S17)
(declare-fun f30 (S18 S15) S15)
(declare-fun f31 () S18)
(declare-fun f32 () S16)
(declare-fun f33 (S21 S20) S20)
(declare-fun f34 (S22 S19) S21)
(declare-fun f35 () S22)
(declare-fun f36 (S23 S19) S19)
(declare-fun f37 () S23)
(declare-fun f38 () S21)
(declare-fun f39 (S26 S25) S25)
(declare-fun f40 (S27 S24) S26)
(declare-fun f41 () S27)
(declare-fun f42 (S28 S24) S24)
(declare-fun f43 () S28)
(declare-fun f44 () S26)
(declare-fun f45 (S29 S25) S14)
(declare-fun f46 () S29)
(declare-fun f47 (S30 S20) S12)
(declare-fun f48 () S30)
(declare-fun f49 (S31 S11) S11)
(declare-fun f50 (S32 S10) S31)
(declare-fun f51 () S32)
(declare-fun f52 () S31)
(declare-fun f53 () S8)
(declare-fun f54 (S10 S10) S1)
(declare-fun f55 (S25 S25) S1)
(declare-fun f56 (S9 S9) S1)
(declare-fun f57 (S11 S11) S1)
(declare-fun f58 () S7)
(declare-fun f59 () S9)
(declare-fun f60 () S10)
(declare-fun f61 () S11)
(declare-fun f62 () S19)
(declare-fun f63 () S20)
(declare-fun f64 () S24)
(declare-fun f65 () S25)
(declare-fun f66 (S33 S34) S18)
(declare-fun f67 () S33)
(declare-fun f68 () S34)
(declare-fun f69 () S15)
(declare-fun f70 () S11)
(declare-fun f71 () S20)
(declare-fun f72 () S15)
(declare-fun f73 () S25)
(declare-fun f74 () S9)
(declare-fun f75 () S10)
(declare-fun f76 () S7)
(declare-fun f77 () S3)
(declare-fun f78 () S19)
(declare-fun f79 () S34)
(declare-fun f80 () S24)
(declare-fun f81 (S25 S25) S1)
(declare-fun f82 (S15 S15) S1)
(declare-fun f83 (S15 S15) S1)
(assert (not (= f1 f2)))
(assert (not (exists ((?v0 S2)) (forall ((?v1 S2)) (=> (exists ((?v2 S3)) (and (= (f3 (f4 f5 ?v2) f6) f1) (= (f4 f5 (f7 (f8 f9 f10) ?v2)) (f11 f12 ?v1)))) (= (f13 ?v1 ?v0) f1))))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f3 (f4 f5 ?v0) f6) f1) (=> (= (f4 f5 (f7 (f8 f9 f10) ?v0)) (f11 f12 ?v1)) (=> (not (= (f13 ?v1 f14) f1)) false)))))
(assert (forall ((?v0 S3) (?v1 S2)) (=> (= (f3 (f4 f5 ?v0) f6) f1) (=> (= (f4 f5 (f7 (f8 f9 f10) ?v0)) (f11 f12 ?v1)) (=> (not (= (f13 ?v1 f14) f1)) false)))))
(assert (= (f3 f15 f6) f1))
(assert (exists ((?v0 S2) (?v1 S3)) (and (= (f3 (f4 f5 ?v1) f6) f1) (= (f4 f5 (f7 (f8 f9 f10) ?v1)) (f11 f12 ?v0)))))
(assert (let ((?v_0 (f4 f5 (f7 (f8 f9 f10) f16)))) (and (= (f3 (f4 f5 f16) f6) f1) (= ?v_0 (f11 f12 (f11 f12 ?v_0))))))
(assert (=> (not (= (f3 f15 f6) f1)) (exists ((?v0 S3)) (forall ((?v1 S3)) (let ((?v_0 (f8 f9 f10))) (=> (= (f3 (f4 f5 ?v1) f6) f1) (= (f3 (f4 f5 (f7 ?v_0 ?v0)) (f4 f5 (f7 ?v_0 ?v1))) f1)))))))
(assert (forall ((?v0 S3)) (let ((?v_0 (f4 f5 ?v0))) (= (f3 (f11 f12 ?v_0) ?v_0) f1))))
(assert (forall ((?v0 S2)) (= (f3 ?v0 ?v0) f1)))
(assert (forall ((?v0 S9)) (= (f17 ?v0 ?v0) f1)))
(assert (forall ((?v0 S10)) (= (f18 ?v0 ?v0) f1)))
(assert (forall ((?v0 S11)) (= (f19 ?v0 ?v0) f1)))
(assert (forall ((?v0 S7) (?v1 S3)) (= (f7 (f8 f9 (f20 f21 ?v0)) ?v1) (f7 f22 (f7 (f8 f9 ?v0) ?v1)))))
(assert (forall ((?v0 S9) (?v1 S2)) (= (f11 (f23 f24 (f25 f26 ?v0)) ?v1) (f11 f12 (f11 (f23 f24 ?v0) ?v1)))))
(assert (forall ((?v0 S15) (?v1 S10)) (= (f27 (f28 f29 (f30 f31 ?v0)) ?v1) (f27 f32 (f27 (f28 f29 ?v0) ?v1)))))
(assert (forall ((?v0 S19) (?v1 S20)) (= (f33 (f34 f35 (f36 f37 ?v0)) ?v1) (f33 f38 (f33 (f34 f35 ?v0) ?v1)))))
(assert (forall ((?v0 S24) (?v1 S25)) (= (f39 (f40 f41 (f42 f43 ?v0)) ?v1) (f39 f44 (f39 (f40 f41 ?v0) ?v1)))))
(assert (forall ((?v0 S25) (?v1 S9)) (= (f25 (f45 f46 (f39 f44 ?v0)) ?v1) (f25 f26 (f25 (f45 f46 ?v0) ?v1)))))
(assert (forall ((?v0 S20) (?v1 S7)) (= (f20 (f47 f48 (f33 f38 ?v0)) ?v1) (f20 f21 (f20 (f47 f48 ?v0) ?v1)))))
(assert (forall ((?v0 S10) (?v1 S11)) (= (f49 (f50 f51 (f27 f32 ?v0)) ?v1) (f49 f52 (f49 (f50 f51 ?v0) ?v1)))))
(assert (forall ((?v0 S2)) (= (f11 f53 (f11 f12 ?v0)) (f11 f53 ?v0))))
(assert (forall ((?v0 S3)) (= (f4 f5 (f7 f22 ?v0)) (f4 f5 ?v0))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f13 ?v0 ?v1) f1) (and (= (f3 ?v0 ?v1) f1) (not (= ?v0 ?v1))))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f3 ?v0 ?v1) f1) (or (= (f13 ?v0 ?v1) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f13 ?v0 (f11 f12 ?v1)) f1) (= (f13 ?v1 (f11 f12 ?v0)) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f54 ?v0 (f27 f32 ?v1)) f1) (= (f54 ?v1 (f27 f32 ?v0)) f1))))
(assert (forall ((?v0 S25) (?v1 S25)) (= (= (f55 ?v0 (f39 f44 ?v1)) f1) (= (f55 ?v1 (f39 f44 ?v0)) f1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f56 ?v0 (f25 f26 ?v1)) f1) (= (f56 ?v1 (f25 f26 ?v0)) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f57 ?v0 (f49 f52 ?v1)) f1) (= (f57 ?v1 (f49 f52 ?v0)) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f13 (f11 f12 ?v0) ?v1) f1) (= (f13 (f11 f12 ?v1) ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f54 (f27 f32 ?v0) ?v1) f1) (= (f54 (f27 f32 ?v1) ?v0) f1))))
(assert (forall ((?v0 S25) (?v1 S25)) (= (= (f55 (f39 f44 ?v0) ?v1) f1) (= (f55 (f39 f44 ?v1) ?v0) f1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f56 (f25 f26 ?v0) ?v1) f1) (= (f56 (f25 f26 ?v1) ?v0) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f57 (f49 f52 ?v0) ?v1) f1) (= (f57 (f49 f52 ?v1) ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= (f13 (f11 f12 ?v0) (f11 f12 ?v1)) f1) (= (f13 ?v1 ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= (f54 (f27 f32 ?v0) (f27 f32 ?v1)) f1) (= (f54 ?v1 ?v0) f1))))
(assert (forall ((?v0 S25) (?v1 S25)) (= (= (f55 (f39 f44 ?v0) (f39 f44 ?v1)) f1) (= (f55 ?v1 ?v0) f1))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= (f56 (f25 f26 ?v0) (f25 f26 ?v1)) f1) (= (f56 ?v1 ?v0) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= (f57 (f49 f52 ?v0) (f49 f52 ?v1)) f1) (= (f57 ?v1 ?v0) f1))))
(assert (not (= f15 f14)))
(assert (= (f4 f5 f16) f15))
(assert (= (f11 f53 f15) f15))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 f58) ?v0) f16)))
(assert (forall ((?v0 S2)) (= (f11 (f23 f24 f59) ?v0) f15)))
(assert (forall ((?v0 S11)) (= (f49 (f50 f51 f60) ?v0) f61)))
(assert (forall ((?v0 S20)) (= (f33 (f34 f35 f62) ?v0) f63)))
(assert (forall ((?v0 S25)) (= (f39 (f40 f41 f64) ?v0) f65)))
(assert (forall ((?v0 S15)) (= (f30 (f66 f67 f68) ?v0) f69)))
(assert (forall ((?v0 S10)) (= (f27 (f28 f29 f69) ?v0) f60)))
(assert (forall ((?v0 S9)) (= (f25 (f45 f46 f65) ?v0) f59)))
(assert (forall ((?v0 S7)) (= (f20 (f47 f48 f63) ?v0) f58)))
(assert (forall ((?v0 S11)) (= (= f70 ?v0) (= ?v0 f70))))
(assert (forall ((?v0 S2)) (= (= f14 ?v0) (= ?v0 f14))))
(assert (forall ((?v0 S20)) (= (= f71 ?v0) (= ?v0 f71))))
(assert (forall ((?v0 S15)) (= (= f72 ?v0) (= ?v0 f72))))
(assert (forall ((?v0 S25)) (= (= f73 ?v0) (= ?v0 f73))))
(assert (forall ((?v0 S9)) (= (= f74 ?v0) (= ?v0 f74))))
(assert (forall ((?v0 S10)) (= (= f75 ?v0) (= ?v0 f75))))
(assert (forall ((?v0 S7)) (= (= f76 ?v0) (= ?v0 f76))))
(assert (forall ((?v0 S3)) (= (= f77 ?v0) (= ?v0 f77))))
(assert (forall ((?v0 S3)) (= (= f16 ?v0) (= ?v0 f16))))
(assert (forall ((?v0 S2)) (= (= f15 ?v0) (= ?v0 f15))))
(assert (forall ((?v0 S11)) (= (= f61 ?v0) (= ?v0 f61))))
(assert (forall ((?v0 S20)) (= (= f63 ?v0) (= ?v0 f63))))
(assert (forall ((?v0 S25)) (= (= f65 ?v0) (= ?v0 f65))))
(assert (forall ((?v0 S15)) (= (= f69 ?v0) (= ?v0 f69))))
(assert (forall ((?v0 S10)) (= (= f60 ?v0) (= ?v0 f60))))
(assert (forall ((?v0 S9)) (= (= f59 ?v0) (= ?v0 f59))))
(assert (forall ((?v0 S7)) (= (= f58 ?v0) (= ?v0 f58))))
(assert (forall ((?v0 S3)) (= (= (f4 f5 ?v0) f15) (= ?v0 f16))))
(assert (forall ((?v0 S2)) (= (= (f11 f53 ?v0) f15) (= ?v0 f15))))
(assert (forall ((?v0 S3)) (= (f7 (f8 f9 f76) ?v0) f77)))
(assert (forall ((?v0 S11)) (= (f49 (f50 f51 f75) ?v0) f70)))
(assert (forall ((?v0 S2)) (= (f11 (f23 f24 f74) ?v0) f14)))
(assert (forall ((?v0 S20)) (= (f33 (f34 f35 f78) ?v0) f71)))
(assert (forall ((?v0 S15)) (= (f30 (f66 f67 f79) ?v0) f72)))
(assert (forall ((?v0 S25)) (= (f39 (f40 f41 f80) ?v0) f73)))
(assert (forall ((?v0 S9)) (= (f25 (f45 f46 f73) ?v0) f74)))
(assert (forall ((?v0 S10)) (= (f27 (f28 f29 f72) ?v0) f75)))
(assert (forall ((?v0 S7)) (= (f20 (f47 f48 f71) ?v0) f76)))
(assert (forall ((?v0 S2)) (= (= (f11 f12 ?v0) ?v0) (= ?v0 f15))))
(assert (forall ((?v0 S11)) (= (= (f49 f52 ?v0) ?v0) (= ?v0 f61))))
(assert (forall ((?v0 S25)) (= (= (f39 f44 ?v0) ?v0) (= ?v0 f65))))
(assert (forall ((?v0 S15)) (= (= (f30 f31 ?v0) ?v0) (= ?v0 f69))))
(assert (forall ((?v0 S10)) (= (= (f27 f32 ?v0) ?v0) (= ?v0 f60))))
(assert (forall ((?v0 S9)) (= (= (f25 f26 ?v0) ?v0) (= ?v0 f59))))
(assert (forall ((?v0 S3)) (= (= (f7 f22 ?v0) f16) (= ?v0 f16))))
(assert (forall ((?v0 S2)) (= (= (f11 f12 ?v0) f15) (= ?v0 f15))))
(assert (forall ((?v0 S11)) (= (= (f49 f52 ?v0) f61) (= ?v0 f61))))
(assert (forall ((?v0 S20)) (= (= (f33 f38 ?v0) f63) (= ?v0 f63))))
(assert (forall ((?v0 S25)) (= (= (f39 f44 ?v0) f65) (= ?v0 f65))))
(assert (forall ((?v0 S15)) (= (= (f30 f31 ?v0) f69) (= ?v0 f69))))
(assert (forall ((?v0 S10)) (= (= (f27 f32 ?v0) f60) (= ?v0 f60))))
(assert (forall ((?v0 S9)) (= (= (f25 f26 ?v0) f59) (= ?v0 f59))))
(assert (forall ((?v0 S7)) (= (= (f20 f21 ?v0) f58) (= ?v0 f58))))
(assert (forall ((?v0 S2)) (= (= ?v0 (f11 f12 ?v0)) (= ?v0 f15))))
(assert (forall ((?v0 S11)) (= (= ?v0 (f49 f52 ?v0)) (= ?v0 f61))))
(assert (forall ((?v0 S25)) (= (= ?v0 (f39 f44 ?v0)) (= ?v0 f65))))
(assert (forall ((?v0 S15)) (= (= ?v0 (f30 f31 ?v0)) (= ?v0 f69))))
(assert (forall ((?v0 S10)) (= (= ?v0 (f27 f32 ?v0)) (= ?v0 f60))))
(assert (forall ((?v0 S9)) (= (= ?v0 (f25 f26 ?v0)) (= ?v0 f59))))
(assert (forall ((?v0 S3)) (= (= f16 (f7 f22 ?v0)) (= f16 ?v0))))
(assert (forall ((?v0 S2)) (= (= f15 (f11 f12 ?v0)) (= f15 ?v0))))
(assert (forall ((?v0 S11)) (= (= f61 (f49 f52 ?v0)) (= f61 ?v0))))
(assert (forall ((?v0 S20)) (= (= f63 (f33 f38 ?v0)) (= f63 ?v0))))
(assert (forall ((?v0 S25)) (= (= f65 (f39 f44 ?v0)) (= f65 ?v0))))
(assert (forall ((?v0 S15)) (= (= f69 (f30 f31 ?v0)) (= f69 ?v0))))
(assert (forall ((?v0 S10)) (= (= f60 (f27 f32 ?v0)) (= f60 ?v0))))
(assert (forall ((?v0 S9)) (= (= f59 (f25 f26 ?v0)) (= f59 ?v0))))
(assert (forall ((?v0 S7)) (= (= f58 (f20 f21 ?v0)) (= f58 ?v0))))
(assert (= (f7 f22 f16) f16))
(assert (= (f11 f12 f15) f15))
(assert (= (f49 f52 f61) f61))
(assert (= (f33 f38 f63) f63))
(assert (= (f39 f44 f65) f65))
(assert (= (f30 f31 f69) f69))
(assert (= (f27 f32 f60) f60))
(assert (= (f25 f26 f59) f59))
(assert (= (f20 f21 f58) f58))
(assert (forall ((?v0 S3)) (= (= (f3 (f4 f5 ?v0) f15) f1) (= ?v0 f16))))
(assert (forall ((?v0 S2)) (= (= (f3 (f11 f53 ?v0) f15) f1) (= ?v0 f15))))
(assert (forall ((?v0 S3)) (= (= (f13 f15 (f4 f5 ?v0)) f1) (not (= ?v0 f16)))))
(assert (forall ((?v0 S2)) (= (= (f13 f15 (f11 f53 ?v0)) f1) (not (= ?v0 f15)))))
(assert (= (f11 f53 f14) f14))
(assert (= (f4 f5 f77) f14))
(assert (forall ((?v0 S2)) (= (= (f3 (f11 f12 ?v0) ?v0) f1) (= (f3 f15 ?v0) f1))))
(assert (forall ((?v0 S11)) (= (= (f19 (f49 f52 ?v0) ?v0) f1) (= (f19 f61 ?v0) f1))))
(assert (forall ((?v0 S25)) (= (= (f81 (f39 f44 ?v0) ?v0) f1) (= (f81 f65 ?v0) f1))))
(assert (forall ((?v0 S15)) (= (= (f82 (f30 f31 ?v0) ?v0) f1) (= (f82 f69 ?v0) f1))))
(assert (forall ((?v0 S10)) (= (= (f18 (f27 f32 ?v0) ?v0) f1) (= (f18 f60 ?v0) f1))))
(assert (forall ((?v0 S9)) (= (= (f17 (f25 f26 ?v0) ?v0) f1) (= (f17 f59 ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 (f11 f12 ?v0) f15) f1) (= (f3 f15 ?v0) f1))))
(assert (forall ((?v0 S11)) (= (= (f19 (f49 f52 ?v0) f61) f1) (= (f19 f61 ?v0) f1))))
(assert (forall ((?v0 S25)) (= (= (f81 (f39 f44 ?v0) f65) f1) (= (f81 f65 ?v0) f1))))
(assert (forall ((?v0 S15)) (= (= (f82 (f30 f31 ?v0) f69) f1) (= (f82 f69 ?v0) f1))))
(assert (forall ((?v0 S10)) (= (= (f18 (f27 f32 ?v0) f60) f1) (= (f18 f60 ?v0) f1))))
(assert (forall ((?v0 S9)) (= (= (f17 (f25 f26 ?v0) f59) f1) (= (f17 f59 ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 ?v0 (f11 f12 ?v0)) f1) (= (f3 ?v0 f15) f1))))
(assert (forall ((?v0 S11)) (= (= (f19 ?v0 (f49 f52 ?v0)) f1) (= (f19 ?v0 f61) f1))))
(assert (forall ((?v0 S25)) (= (= (f81 ?v0 (f39 f44 ?v0)) f1) (= (f81 ?v0 f65) f1))))
(assert (forall ((?v0 S15)) (= (= (f82 ?v0 (f30 f31 ?v0)) f1) (= (f82 ?v0 f69) f1))))
(assert (forall ((?v0 S10)) (= (= (f18 ?v0 (f27 f32 ?v0)) f1) (= (f18 ?v0 f60) f1))))
(assert (forall ((?v0 S9)) (= (= (f17 ?v0 (f25 f26 ?v0)) f1) (= (f17 ?v0 f59) f1))))
(assert (forall ((?v0 S2)) (= (= (f3 f15 (f11 f12 ?v0)) f1) (= (f3 ?v0 f15) f1))))
(assert (forall ((?v0 S11)) (= (= (f19 f61 (f49 f52 ?v0)) f1) (= (f19 ?v0 f61) f1))))
(assert (forall ((?v0 S25)) (= (= (f81 f65 (f39 f44 ?v0)) f1) (= (f81 ?v0 f65) f1))))
(assert (forall ((?v0 S15)) (= (= (f82 f69 (f30 f31 ?v0)) f1) (= (f82 ?v0 f69) f1))))
(assert (forall ((?v0 S10)) (= (= (f18 f60 (f27 f32 ?v0)) f1) (= (f18 ?v0 f60) f1))))
(assert (forall ((?v0 S9)) (= (= (f17 f59 (f25 f26 ?v0)) f1) (= (f17 ?v0 f59) f1))))
(assert (forall ((?v0 S2)) (= (= (f13 (f11 f12 ?v0) ?v0) f1) (= (f13 f15 ?v0) f1))))
(assert (forall ((?v0 S11)) (= (= (f57 (f49 f52 ?v0) ?v0) f1) (= (f57 f61 ?v0) f1))))
(assert (forall ((?v0 S25)) (= (= (f55 (f39 f44 ?v0) ?v0) f1) (= (f55 f65 ?v0) f1))))
(assert (forall ((?v0 S15)) (= (= (f83 (f30 f31 ?v0) ?v0) f1) (= (f83 f69 ?v0) f1))))
(assert (forall ((?v0 S10)) (= (= (f54 (f27 f32 ?v0) ?v0) f1) (= (f54 f60 ?v0) f1))))
(assert (forall ((?v0 S9)) (= (= (f56 (f25 f26 ?v0) ?v0) f1) (= (f56 f59 ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f13 (f11 f12 ?v0) f15) f1) (= (f13 f15 ?v0) f1))))
(assert (forall ((?v0 S11)) (= (= (f57 (f49 f52 ?v0) f61) f1) (= (f57 f61 ?v0) f1))))
(assert (forall ((?v0 S25)) (= (= (f55 (f39 f44 ?v0) f65) f1) (= (f55 f65 ?v0) f1))))
(assert (forall ((?v0 S15)) (= (= (f83 (f30 f31 ?v0) f69) f1) (= (f83 f69 ?v0) f1))))
(assert (forall ((?v0 S10)) (= (= (f54 (f27 f32 ?v0) f60) f1) (= (f54 f60 ?v0) f1))))
(assert (forall ((?v0 S9)) (= (= (f56 (f25 f26 ?v0) f59) f1) (= (f56 f59 ?v0) f1))))
(assert (forall ((?v0 S2)) (= (= (f13 f15 (f11 f12 ?v0)) f1) (= (f13 ?v0 f15) f1))))
(assert (forall ((?v0 S11)) (= (= (f57 f61 (f49 f52 ?v0)) f1) (= (f57 ?v0 f61) f1))))
(assert (forall ((?v0 S25)) (= (= (f55 f65 (f39 f44 ?v0)) f1) (= (f55 ?v0 f65) f1))))
(assert (forall ((?v0 S15)) (= (= (f83 f69 (f30 f31 ?v0)) f1) (= (f83 ?v0 f69) f1))))
(assert (forall ((?v0 S10)) (= (= (f54 f60 (f27 f32 ?v0)) f1) (= (f54 ?v0 f60) f1))))
(assert (forall ((?v0 S9)) (= (= (f56 f59 (f25 f26 ?v0)) f1) (= (f56 ?v0 f59) f1))))
(assert (forall ((?v0 S3)) (= (f3 f15 (f4 f5 ?v0)) f1)))
(assert (forall ((?v0 S2)) (= (f3 f15 (f11 f53 ?v0)) f1)))
(assert (forall ((?v0 S3)) (not (= (f13 (f4 f5 ?v0) f15) f1))))
(assert (forall ((?v0 S2)) (not (= (f13 (f11 f53 ?v0) f15) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f3 ?v0 ?v1) f1) false) (=> (=> (= (f3 ?v1 ?v0) f1) false) false))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (=> (= (f17 ?v0 ?v1) f1) false) (=> (=> (= (f17 ?v1 ?v0) f1) false) false))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (=> (= (f18 ?v0 ?v1) f1) false) (=> (=> (= (f18 ?v1 ?v0) f1) false) false))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (=> (= (f19 ?v0 ?v1) f1) false) (=> (=> (= (f19 ?v1 ?v0) f1) false) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v2 ?v0) f1) (= (f3 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f17 ?v0 ?v1) f1) (=> (= (f17 ?v2 ?v0) f1) (= (f17 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f18 ?v0 ?v1) f1) (=> (= (f18 ?v2 ?v0) f1) (= (f18 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f19 ?v0 ?v1) f1) (=> (= (f19 ?v2 ?v0) f1) (= (f19 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f17 ?v0 ?v1) f1) (=> (= (f17 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f18 ?v0 ?v1) f1) (=> (= (f18 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f19 ?v0 ?v1) f1) (=> (= (f19 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v1 ?v2) f1) (= (f3 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f17 ?v0 ?v1) f1) (=> (= (f17 ?v1 ?v2) f1) (= (f17 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f18 ?v0 ?v1) f1) (=> (= (f18 ?v1 ?v2) f1) (= (f18 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f19 ?v0 ?v1) f1) (=> (= (f19 ?v1 ?v2) f1) (= (f19 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= (f3 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f17 ?v0 ?v1) f1) (=> (= (f17 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f18 ?v0 ?v1) f1) (=> (= (f18 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f19 ?v0 ?v1) f1) (=> (= (f19 ?v1 ?v0) f1) (= ?v0 ?v1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f3 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f17 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f17 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f18 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f18 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f19 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f19 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f3 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f3 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f17 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f17 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f18 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f18 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f19 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f19 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f3 ?v2 ?v1) f1) (= (f3 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= ?v0 ?v1) (=> (= (f17 ?v2 ?v1) f1) (= (f17 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= ?v0 ?v1) (=> (= (f18 ?v2 ?v1) f1) (= (f18 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= ?v0 ?v1) (=> (= (f19 ?v2 ?v1) f1) (= (f19 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f3 ?v1 ?v2) f1) (= (f3 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= ?v0 ?v1) (=> (= (f17 ?v1 ?v2) f1) (= (f17 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= ?v0 ?v1) (=> (= (f18 ?v1 ?v2) f1) (= (f18 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= ?v0 ?v1) (=> (= (f19 ?v1 ?v2) f1) (= (f19 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f3 ?v0 ?v1) f1) (= (= (f3 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f17 ?v0 ?v1) f1) (= (= (f17 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f18 ?v0 ?v1) f1) (= (= (f18 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f19 ?v0 ?v1) f1) (= (= (f19 ?v1 ?v0) f1) (= ?v1 ?v0)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= ?v0 ?v1) (= (f3 ?v0 ?v1) f1))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= ?v0 ?v1) (= (f17 ?v0 ?v1) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= ?v0 ?v1) (= (f18 ?v0 ?v1) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= ?v0 ?v1) (= (f19 ?v0 ?v1) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (= (= ?v0 ?v1) (and (= (f3 ?v0 ?v1) f1) (= (f3 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S9) (?v1 S9)) (= (= ?v0 ?v1) (and (= (f17 ?v0 ?v1) f1) (= (f17 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S10) (?v1 S10)) (= (= ?v0 ?v1) (and (= (f18 ?v0 ?v1) f1) (= (f18 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S11) (?v1 S11)) (= (= ?v0 ?v1) (and (= (f19 ?v0 ?v1) f1) (= (f19 ?v1 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2)) (or (= (f3 ?v0 ?v1) f1) (= (f3 ?v1 ?v0) f1))))
(assert (forall ((?v0 S9) (?v1 S9)) (or (= (f17 ?v0 ?v1) f1) (= (f17 ?v1 ?v0) f1))))
(assert (forall ((?v0 S10) (?v1 S10)) (or (= (f18 ?v0 ?v1) f1) (= (f18 ?v1 ?v0) f1))))
(assert (forall ((?v0 S11) (?v1 S11)) (or (= (f19 ?v0 ?v1) f1) (= (f19 ?v1 ?v0) f1))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (=> (= (f13 ?v0 ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f13 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (=> (= (f56 ?v0 ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f56 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (=> (= (f54 ?v0 ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f54 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (=> (= (f57 ?v0 ?v1) f1) false) (=> (=> (= ?v0 ?v1) false) (=> (=> (= (f57 ?v1 ?v0) f1) false) false)))))
(assert (forall ((?v0 S2) (?v1 S2)) (=> (= (f13 ?v0 ?v1) f1) (=> (=> (not false) (= (f13 ?v1 ?v0) f1)) false))))
(assert (forall ((?v0 S9) (?v1 S9)) (=> (= (f56 ?v0 ?v1) f1) (=> (=> (not false) (= (f56 ?v1 ?v0) f1)) false))))
(assert (forall ((?v0 S10) (?v1 S10)) (=> (= (f54 ?v0 ?v1) f1) (=> (=> (not false) (= (f54 ?v1 ?v0) f1)) false))))
(assert (forall ((?v0 S11) (?v1 S11)) (=> (= (f57 ?v0 ?v1) f1) (=> (=> (not false) (= (f57 ?v1 ?v0) f1)) false))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 ?v2 ?v0) f1) (= (f13 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f56 ?v2 ?v0) f1) (= (f56 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f54 ?v0 ?v1) f1) (=> (= (f54 ?v2 ?v0) f1) (= (f54 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f57 ?v0 ?v1) f1) (=> (= (f57 ?v2 ?v0) f1) (= (f57 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 ?v0 ?v1) f1) (=> (= (f13 ?v1 ?v2) f1) (= (f13 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f56 ?v0 ?v1) f1) (=> (= (f56 ?v1 ?v2) f1) (= (f56 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f54 ?v0 ?v1) f1) (=> (= (f54 ?v1 ?v2) f1) (= (f54 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f57 ?v0 ?v1) f1) (=> (= (f57 ?v1 ?v2) f1) (= (f57 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f13 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f56 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f56 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f54 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f54 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f57 ?v0 ?v1) f1) (=> (= ?v0 ?v2) (= (f57 ?v2 ?v1) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= (f13 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f13 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= (f56 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f56 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= (f54 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f54 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= (f57 ?v0 ?v1) f1) (=> (= ?v1 ?v2) (= (f57 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f13 ?v2 ?v1) f1) (= (f13 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= ?v0 ?v1) (=> (= (f56 ?v2 ?v1) f1) (= (f56 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= ?v0 ?v1) (=> (= (f54 ?v2 ?v1) f1) (= (f54 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= ?v0 ?v1) (=> (= (f57 ?v2 ?v1) f1) (= (f57 ?v2 ?v0) f1)))))
(assert (forall ((?v0 S2) (?v1 S2) (?v2 S2)) (=> (= ?v0 ?v1) (=> (= (f13 ?v1 ?v2) f1) (= (f13 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S9)) (=> (= ?v0 ?v1) (=> (= (f56 ?v1 ?v2) f1) (= (f56 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S10) (?v1 S10) (?v2 S10)) (=> (= ?v0 ?v1) (=> (= (f54 ?v1 ?v2) f1) (= (f54 ?v0 ?v2) f1)))))
(assert (forall ((?v0 S11) (?v1 S11) (?v2 S11)) (=> (= ?v0 ?v1) (=> (= (f57 ?v1 ?v2) f1) (= (f57 ?v0 ?v2) f1)))))
(check-sat)
(exit)