(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/union_find.spl:49:4-19:Possible heap access through null or dangling reference
  |)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_1$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun n_3$0 () Loc)
(declare-fun tmp_1$0 () Loc)

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 Alloc$0 (setenum$0 tmp_1$0)))
                 (or (in$0 x Alloc$0) (in$0 x (setenum$0 tmp_1$0))))
            (and (not (in$0 x Alloc$0)) (not (in$0 x (setenum$0 tmp_1$0)))
                 (not (in$0 x (union$0 Alloc$0 (setenum$0 tmp_1$0))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 (setenum$0 tmp_1$0)))
                 (or (in$0 x FP$0) (in$0 x (setenum$0 tmp_1$0))))
            (and (not (in$0 x FP$0)) (not (in$0 x (setenum$0 tmp_1$0)))
                 (not (in$0 x (union$0 FP$0 (setenum$0 tmp_1$0))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))))

(assert (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (= emptyset$0 FP$0))

(assert (= FP_1$0 (union$0 FP$0 (setenum$0 tmp_1$0))))

(assert (= n_3$0 tmp_1$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (not (in$0 null$0 Alloc$0)))

(assert (not (in$0 tmp_1$0 Alloc$0)))

(assert (= Alloc_1$0 (union$0 Alloc$0 (setenum$0 tmp_1$0))))

(assert (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (not (= tmp_1$0 null$0)))

(assert (not (in$0 n_3$0 FP_1$0)))

(check-sat)
(exit)
