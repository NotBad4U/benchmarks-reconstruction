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
(declare-sort S48 0)
(declare-sort S49 0)
(declare-sort S50 0)
(declare-sort S51 0)
(declare-sort S52 0)
(declare-sort S53 0)
(declare-sort S54 0)
(declare-sort S55 0)
(declare-sort S56 0)
(declare-sort S57 0)
(declare-sort S58 0)
(declare-sort S59 0)
(declare-sort S60 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 (S2 S3) S3)
(declare-fun f4 (S4 S5) S2)
(declare-fun f5 () S4)
(declare-fun f6 () S5)
(declare-fun f7 () S3)
(declare-fun f8 () S3)
(declare-fun f9 () S5)
(declare-fun f10 () S5)
(declare-fun f11 () S5)
(declare-fun f12 () S5)
(declare-fun f13 () S3)
(declare-fun f14 () S5)
(declare-fun f15 (S7 S6) S6)
(declare-fun f16 (S8 S9) S7)
(declare-fun f17 () S8)
(declare-fun f18 () S9)
(declare-fun f19 () S6)
(declare-fun f20 (S10 S5) S5)
(declare-fun f21 (S11 S12) S10)
(declare-fun f22 () S11)
(declare-fun f23 () S12)
(declare-fun f24 (S14 S13) S13)
(declare-fun f25 (S15 S16) S14)
(declare-fun f26 () S15)
(declare-fun f27 () S16)
(declare-fun f28 () S13)
(declare-fun f29 (S18 S17) S17)
(declare-fun f30 (S19 S20) S18)
(declare-fun f31 () S19)
(declare-fun f32 () S20)
(declare-fun f33 () S17)
(declare-fun f34 (S22 S21) S21)
(declare-fun f35 (S23 S24) S22)
(declare-fun f36 () S23)
(declare-fun f37 () S24)
(declare-fun f38 () S21)
(declare-fun f39 (S26 S25) S25)
(declare-fun f40 (S27 S28) S26)
(declare-fun f41 () S27)
(declare-fun f42 () S28)
(declare-fun f43 () S25)
(declare-fun f44 (S29 S9) S9)
(declare-fun f45 (S30 S25) S29)
(declare-fun f46 () S30)
(declare-fun f47 (S31 S16) S16)
(declare-fun f48 (S32 S21) S31)
(declare-fun f49 () S32)
(declare-fun f50 (S33 S12) S12)
(declare-fun f51 (S34 S17) S33)
(declare-fun f52 () S34)
(declare-fun f53 (S2) S1)
(declare-fun f54 (S35 S5) S6)
(declare-fun f55 () S35)
(declare-fun f56 () S6)
(declare-fun f57 (S36 S3) S35)
(declare-fun f58 () S36)
(declare-fun f59 (S37 S12) S6)
(declare-fun f60 (S38 S5) S37)
(declare-fun f61 () S38)
(declare-fun f62 (S39 S16) S6)
(declare-fun f63 (S40 S13) S39)
(declare-fun f64 () S40)
(declare-fun f65 (S41 S20) S6)
(declare-fun f66 (S42 S17) S41)
(declare-fun f67 () S42)
(declare-fun f68 (S43 S24) S6)
(declare-fun f69 (S44 S21) S43)
(declare-fun f70 () S44)
(declare-fun f71 (S45 S21) S6)
(declare-fun f72 (S46 S16) S45)
(declare-fun f73 () S46)
(declare-fun f74 (S47 S17) S6)
(declare-fun f75 (S48 S12) S47)
(declare-fun f76 () S48)
(declare-fun f77 () S6)
(declare-fun f78 (S49 S5) S10)
(declare-fun f79 () S49)
(declare-fun f80 (S50 S17) S18)
(declare-fun f81 () S50)
(declare-fun f82 (S51 S21) S22)
(declare-fun f83 () S51)
(declare-fun f84 (S52 S25) S26)
(declare-fun f85 () S52)
(declare-fun f86 (S53 S9) S29)
(declare-fun f87 () S53)
(declare-fun f88 (S54 S16) S31)
(declare-fun f89 () S54)
(declare-fun f90 (S55 S12) S33)
(declare-fun f91 () S55)
(declare-fun f92 (S56 S6) S1)
(declare-fun f93 (S6) S56)
(declare-fun f94 () S47)
(declare-fun f95 () S45)
(declare-fun f96 (S57 S25) S6)
(declare-fun f97 () S57)
(declare-fun f98 (S58 S9) S6)
(declare-fun f99 () S58)
(declare-fun f100 () S39)
(declare-fun f101 () S37)
(declare-fun f102 (S6 S6) S1)
(declare-fun f103 (S5 S5) S1)
(declare-fun f104 (S59 S6) S5)
(declare-fun f105 (S60 S5) S59)
(declare-fun f106 () S60)
(assert (not (= f1 f2)))
(assert (not (= (f3 (f4 f5 f6) f7) f8)))
(assert (= (f3 (f4 f5 f9) f7) f8))
(assert (= (f3 (f4 f5 f9) f7) f8))
(assert (forall ((?v0 S3)) (=> (= (f3 (f4 f5 f11) ?v0) f8) (= (f3 (f4 f5 f10) ?v0) f8))))
(assert (forall ((?v0 S3)) (=> (= (f3 (f4 f5 f6) ?v0) f8) (= (f3 (f4 f5 f12) ?v0) f8))))
(assert (= (f3 (f4 f5 f6) f13) f8))
(assert (=> (= f7 f13) false))
(assert (forall ((?v0 S3)) (= (f3 (f4 f5 f14) ?v0) f8)))
(assert (forall ((?v0 S6)) (= (f15 (f16 f17 f18) ?v0) f19)))
(assert (forall ((?v0 S5)) (= (f20 (f21 f22 f23) ?v0) f14)))
(assert (forall ((?v0 S13)) (= (f24 (f25 f26 f27) ?v0) f28)))
(assert (forall ((?v0 S17)) (= (f29 (f30 f31 f32) ?v0) f33)))
(assert (forall ((?v0 S21)) (= (f34 (f35 f36 f37) ?v0) f38)))
(assert (forall ((?v0 S25)) (= (f39 (f40 f41 f42) ?v0) f43)))
(assert (forall ((?v0 S9)) (= (f44 (f45 f46 f43) ?v0) f18)))
(assert (forall ((?v0 S16)) (= (f47 (f48 f49 f38) ?v0) f27)))
(assert (forall ((?v0 S12)) (= (f50 (f51 f52 f33) ?v0) f23)))
(assert (not (= f6 f14)))
(assert (forall ((?v0 S5)) (=> (not (= (f53 (f4 f5 ?v0)) f1)) (exists ((?v1 S3)) (= (f3 (f4 f5 ?v0) ?v1) f8)))))
(assert (forall ((?v0 S5) (?v1 S5)) (= (= (f4 f5 ?v0) (f4 f5 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S21) (?v1 S21)) (= (= (f48 f49 ?v0) (f48 f49 ?v1)) (= ?v0 ?v1))))
(assert (forall ((?v0 S16) (?v1 S16)) (= (= (f25 f26 ?v0) (f25 f26 ?v1)) (= ?v0 ?v1))))
(assert (= (f54 f55 f6) f56))
(assert (forall ((?v0 S6)) (= (= f19 ?v0) (= ?v0 f19))))
(assert (forall ((?v0 S5)) (= (= f14 ?v0) (= ?v0 f14))))
(assert (forall ((?v0 S13)) (= (= f28 ?v0) (= ?v0 f28))))
(assert (forall ((?v0 S3)) (= (= f8 ?v0) (= ?v0 f8))))
(assert (forall ((?v0 S17)) (= (= f33 ?v0) (= ?v0 f33))))
(assert (forall ((?v0 S21)) (= (= f38 ?v0) (= ?v0 f38))))
(assert (forall ((?v0 S25)) (= (= f43 ?v0) (= ?v0 f43))))
(assert (forall ((?v0 S9)) (= (= f18 ?v0) (= ?v0 f18))))
(assert (forall ((?v0 S16)) (= (= f27 ?v0) (= ?v0 f27))))
(assert (forall ((?v0 S12)) (= (= f23 ?v0) (= ?v0 f23))))
(assert (forall ((?v0 S5) (?v1 S3)) (= (= (f3 (f4 f5 ?v0) ?v1) f8) (or (= ?v0 f14) (not (= (f54 (f57 f58 ?v1) ?v0) f19))))))
(assert (forall ((?v0 S12) (?v1 S5)) (= (= (f20 (f21 f22 ?v0) ?v1) f14) (or (= ?v0 f23) (not (= (f59 (f60 f61 ?v1) ?v0) f19))))))
(assert (forall ((?v0 S16) (?v1 S13)) (= (= (f24 (f25 f26 ?v0) ?v1) f28) (or (= ?v0 f27) (not (= (f62 (f63 f64 ?v1) ?v0) f19))))))
(assert (forall ((?v0 S20) (?v1 S17)) (= (= (f29 (f30 f31 ?v0) ?v1) f33) (or (= ?v0 f32) (not (= (f65 (f66 f67 ?v1) ?v0) f19))))))
(assert (forall ((?v0 S24) (?v1 S21)) (= (= (f34 (f35 f36 ?v0) ?v1) f38) (or (= ?v0 f37) (not (= (f68 (f69 f70 ?v1) ?v0) f19))))))
(assert (forall ((?v0 S21) (?v1 S16)) (= (= (f47 (f48 f49 ?v0) ?v1) f27) (or (= ?v0 f38) (not (= (f71 (f72 f73 ?v1) ?v0) f19))))))
(assert (forall ((?v0 S17) (?v1 S12)) (= (= (f50 (f51 f52 ?v0) ?v1) f23) (or (= ?v0 f33) (not (= (f74 (f75 f76 ?v1) ?v0) f19))))))
(assert (not (= f77 f19)))
(assert (not (= (f54 (f57 f58 f13) f6) f19)))
(assert (forall ((?v0 S5) (?v1 S5) (?v2 S3)) (= (f3 (f4 f5 (f20 (f78 f79 ?v0) ?v1)) ?v2) (f3 (f4 f5 ?v0) (f3 (f4 f5 ?v1) ?v2)))))
(assert (forall ((?v0 S17) (?v1 S17) (?v2 S12)) (= (f50 (f51 f52 (f29 (f80 f81 ?v0) ?v1)) ?v2) (f50 (f51 f52 ?v0) (f50 (f51 f52 ?v1) ?v2)))))
(assert (forall ((?v0 S21) (?v1 S21) (?v2 S16)) (= (f47 (f48 f49 (f34 (f82 f83 ?v0) ?v1)) ?v2) (f47 (f48 f49 ?v0) (f47 (f48 f49 ?v1) ?v2)))))
(assert (forall ((?v0 S25) (?v1 S25) (?v2 S9)) (= (f44 (f45 f46 (f39 (f84 f85 ?v0) ?v1)) ?v2) (f44 (f45 f46 ?v0) (f44 (f45 f46 ?v1) ?v2)))))
(assert (forall ((?v0 S9) (?v1 S9) (?v2 S6)) (= (f15 (f16 f17 (f44 (f86 f87 ?v0) ?v1)) ?v2) (f15 (f16 f17 ?v0) (f15 (f16 f17 ?v1) ?v2)))))
(assert (forall ((?v0 S16) (?v1 S16) (?v2 S13)) (= (f24 (f25 f26 (f47 (f88 f89 ?v0) ?v1)) ?v2) (f24 (f25 f26 ?v0) (f24 (f25 f26 ?v1) ?v2)))))
(assert (forall ((?v0 S12) (?v1 S12) (?v2 S5)) (= (f20 (f21 f22 (f50 (f90 f91 ?v0) ?v1)) ?v2) (f20 (f21 f22 ?v0) (f20 (f21 f22 ?v1) ?v2)))))
(assert (forall ((?v0 S3)) (= (f92 (f93 (f54 (f57 f58 ?v0) f6)) f56) f1)))
(assert (not (= f56 f19)))
(assert (not (= f12 f14)))
(assert (not (= (f54 f55 f9) f19)))
(assert (not (= f9 f14)))
(assert (= (f54 f55 f11) f77))
(assert (= (f54 f55 f14) f19))
(assert (= (f74 f94 f33) f19))
(assert (= (f71 f95 f38) f19))
(assert (= (f96 f97 f43) f19))
(assert (= (f98 f99 f18) f19))
(assert (= (f62 f100 f27) f19))
(assert (= (f59 f101 f23) f19))
(assert (forall ((?v0 S5)) (= (f20 (f78 f79 f14) ?v0) f14)))
(assert (forall ((?v0 S17)) (= (f29 (f80 f81 f33) ?v0) f33)))
(assert (forall ((?v0 S21)) (= (f34 (f82 f83 f38) ?v0) f38)))
(assert (forall ((?v0 S25)) (= (f39 (f84 f85 f43) ?v0) f43)))
(assert (forall ((?v0 S9)) (= (f44 (f86 f87 f18) ?v0) f18)))
(assert (forall ((?v0 S16)) (= (f47 (f88 f89 f27) ?v0) f27)))
(assert (forall ((?v0 S12)) (= (f50 (f90 f91 f23) ?v0) f23)))
(assert (forall ((?v0 S5) (?v1 S3)) (=> (not (= ?v0 f14)) (= (f92 (f93 (f54 (f57 f58 ?v1) ?v0)) (f54 f55 ?v0)) f1))))
(assert (forall ((?v0 S17) (?v1 S12)) (=> (not (= ?v0 f33)) (= (f92 (f93 (f74 (f75 f76 ?v1) ?v0)) (f74 f94 ?v0)) f1))))
(assert (forall ((?v0 S21) (?v1 S16)) (=> (not (= ?v0 f38)) (= (f92 (f93 (f71 (f72 f73 ?v1) ?v0)) (f71 f95 ?v0)) f1))))
(assert (forall ((?v0 S16) (?v1 S13)) (=> (not (= ?v0 f27)) (= (f92 (f93 (f62 (f63 f64 ?v1) ?v0)) (f62 f100 ?v0)) f1))))
(assert (forall ((?v0 S12) (?v1 S5)) (=> (not (= ?v0 f23)) (= (f92 (f93 (f59 (f60 f61 ?v1) ?v0)) (f59 f101 ?v0)) f1))))
(assert (forall ((?v0 S5)) (= (= (f4 f5 ?v0) (f4 f5 f14)) (= ?v0 f14))))
(assert (forall ((?v0 S21)) (= (= (f48 f49 ?v0) (f48 f49 f38)) (= ?v0 f38))))
(assert (forall ((?v0 S16)) (= (= (f25 f26 ?v0) (f25 f26 f27)) (= ?v0 f27))))
(assert (forall ((?v0 S2)) (= (= (f53 ?v0) f1) (forall ((?v1 S3) (?v2 S3)) (= (f3 ?v0 ?v1) (f3 ?v0 ?v2))))))
(assert (forall ((?v0 S6)) (= (f92 (f93 f19) ?v0) f1)))
(assert (= (f102 (f54 f55 f9) f56) f1))
(assert (forall ((?v0 S6)) (= (f92 (f93 ?v0) ?v0) f1)))
(assert (=> (= (f54 f55 f9) f19) (= (f103 f6 (f104 (f105 f106 f12) f56)) f1)))
(assert (forall ((?v0 S6)) (= (= (f92 (f93 f19) ?v0) f1) true)))
(assert (forall ((?v0 S6)) (= (= (f92 (f93 ?v0) f19) f1) (= ?v0 f19))))
(check-sat)
(exit)