(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/union_find.spl:20:4-18:Possible heap access through null or dangling reference
  |)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun ep$0 (FldLoc SetLoc Loc) Loc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun Frame$0 (SetLoc SetLoc FldLoc FldLoc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Axiom$0 () Bool)
(declare-fun Axiom_1$0 () Bool)
(declare-fun Axiom_2$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_3$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun X$0 () SetLoc)
(declare-fun X_27$0 () SetLoc)
(declare-fun lseg_set_X$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_struct$0 (SetLoc FldLoc Loc Loc SetLoc) Bool)
(declare-fun n_5$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_2$0 () FldLoc)
(declare-fun res_4$0 () Loc)
(declare-fun root_x$0 () Loc)
(declare-fun sk_?X_14$0 () SetLoc)
(declare-fun sk_?X_15$0 () SetLoc)
(declare-fun sk_?X_16$0 () SetLoc)
(declare-fun sk_?X_17$0 () SetLoc)
(declare-fun sk_?X_18$0 () SetLoc)
(declare-fun sk_?X_19$0 () SetLoc)
(declare-fun sk_?X_20$0 () SetLoc)
(declare-fun sk_?X_21$0 () SetLoc)
(declare-fun sk_?X_22$0 () SetLoc)
(declare-fun sk_?X_23$0 () SetLoc)
(declare-fun sk_?X_24$0 () SetLoc)
(declare-fun sk_?X_25$0 () SetLoc)
(declare-fun sk_?X_26$0 () SetLoc)
(declare-fun sk_?X_27$0 () SetLoc)
(declare-fun x$0 () Loc)

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 res_4$0 ?y ?y)) (= res_4$0 ?y)
            (Btwn$0 next$0 res_4$0 (read$0 next$0 res_4$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 x$0 ?y ?y)) (= x$0 ?y)
            (Btwn$0 next$0 x$0 (read$0 next$0 x$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 res_4$0 ?y ?y)) (= res_4$0 ?y)
            (Btwn$0 next_2$0 res_4$0 (read$0 next_2$0 res_4$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_2$0 null$0 (read$0 next_2$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 x$0 ?y ?y)) (= x$0 ?y)
            (Btwn$0 next_2$0 x$0 (read$0 next_2$0 x$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 res_4$0) res_4$0))
            (not (Btwn$0 next$0 res_4$0 ?y ?y)) (= res_4$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 x$0) x$0)) (not (Btwn$0 next$0 x$0 ?y ?y))
            (= x$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 res_4$0) res_4$0))
            (not (Btwn$0 next_2$0 res_4$0 ?y ?y)) (= res_4$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 null$0) null$0))
            (not (Btwn$0 next_2$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 x$0) x$0))
            (not (Btwn$0 next_2$0 x$0 ?y ?y)) (= x$0 ?y))))

(assert (Btwn$0 next$0 res_4$0 (read$0 next$0 res_4$0) (read$0 next$0 res_4$0)))

(assert (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)))

(assert (Btwn$0 next$0 x$0 (read$0 next$0 x$0) (read$0 next$0 x$0)))

(assert (Btwn$0 next_2$0 res_4$0 (read$0 next_2$0 res_4$0) (read$0 next_2$0 res_4$0)))

(assert (Btwn$0 next_2$0 null$0 (read$0 next_2$0 null$0) (read$0 next_2$0 null$0)))

(assert (Btwn$0 next_2$0 x$0 (read$0 next_2$0 x$0) (read$0 next_2$0 x$0)))

(assert (or (not Axiom_2$0)
    (or (= (read$0 next$0 res_4$0) (read$0 next_2$0 res_4$0))
        (not (in$0 res_4$0 (setminus$0 Alloc$0 FP_2$0))))))

(assert (or (not Axiom_2$0)
    (or (= (read$0 next$0 null$0) (read$0 next_2$0 null$0))
        (not (in$0 null$0 (setminus$0 Alloc$0 FP_2$0))))))

(assert (or (not Axiom_2$0)
    (or (= (read$0 next$0 x$0) (read$0 next_2$0 x$0))
        (not (in$0 x$0 (setminus$0 Alloc$0 FP_2$0))))))

(assert (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_2$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_2$0 null$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 null$0 ?y
                           (ep$0 next$0 FP_2$0 null$0))
                         (and (Btwn$0 next$0 null$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 null$0
                                     (ep$0 next$0 FP_2$0 null$0)
                                     (ep$0 next$0 FP_2$0 null$0))))))))))

(assert (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 n_5$0 ?z ?y)
                     (Btwn$0 next_2$0 n_5$0 ?z ?y))
                (and (not (Btwn$0 next$0 n_5$0 ?z ?y))
                     (not (Btwn$0 next_2$0 n_5$0 ?z ?y)))
                (not
                     (or (Btwn$0 next$0 n_5$0 ?y (ep$0 next$0 FP_2$0 n_5$0))
                         (and (Btwn$0 next$0 n_5$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 n_5$0
                                     (ep$0 next$0 FP_2$0 n_5$0)
                                     (ep$0 next$0 FP_2$0 n_5$0))))))))))

(assert (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or (and (Btwn$0 next$0 x$0 ?z ?y) (Btwn$0 next_2$0 x$0 ?z ?y))
                (and (not (Btwn$0 next$0 x$0 ?z ?y))
                     (not (Btwn$0 next_2$0 x$0 ?z ?y)))
                (not
                     (or (Btwn$0 next$0 x$0 ?y (ep$0 next$0 FP_2$0 x$0))
                         (and (Btwn$0 next$0 x$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 x$0
                                     (ep$0 next$0 FP_2$0 x$0)
                                     (ep$0 next$0 FP_2$0 x$0))))))))))

(assert (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 null$0 FP_2$0)
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_2$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_2$0 null$0 ?z ?y)))
                (not (= null$0 (ep$0 next$0 FP_2$0 null$0)))))))

(assert (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 n_5$0 FP_2$0)
                (and (Btwn$0 next$0 n_5$0 ?z ?y)
                     (Btwn$0 next_2$0 n_5$0 ?z ?y))
                (and (not (Btwn$0 next$0 n_5$0 ?z ?y))
                     (not (Btwn$0 next_2$0 n_5$0 ?z ?y)))
                (not (= n_5$0 (ep$0 next$0 FP_2$0 n_5$0)))))))

(assert (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 x$0 FP_2$0)
                (and (Btwn$0 next$0 x$0 ?z ?y) (Btwn$0 next_2$0 x$0 ?z ?y))
                (and (not (Btwn$0 next$0 x$0 ?z ?y))
                     (not (Btwn$0 next_2$0 x$0 ?z ?y)))
                (not (= x$0 (ep$0 next$0 FP_2$0 x$0)))))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_24$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y sk_?X_24$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 n_5$0 (ep$0 next$0 sk_?X_24$0 n_5$0) ?y)
            (not (Btwn$0 next$0 n_5$0 ?y ?y)) (not (in$0 ?y sk_?X_24$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 x$0 (ep$0 next$0 sk_?X_24$0 x$0) ?y)
            (not (Btwn$0 next$0 x$0 ?y ?y)) (not (in$0 ?y sk_?X_24$0)))))

(assert (or (in$0 (ep$0 next$0 sk_?X_24$0 null$0) sk_?X_24$0)
    (= null$0 (ep$0 next$0 sk_?X_24$0 null$0))))

(assert (or (in$0 (ep$0 next$0 sk_?X_24$0 n_5$0) sk_?X_24$0)
    (= n_5$0 (ep$0 next$0 sk_?X_24$0 n_5$0))))

(assert (or (in$0 (ep$0 next$0 sk_?X_24$0 x$0) sk_?X_24$0)
    (= x$0 (ep$0 next$0 sk_?X_24$0 x$0))))

(assert (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_24$0 null$0)
  (ep$0 next$0 sk_?X_24$0 null$0)))

(assert (Btwn$0 next$0 n_5$0 (ep$0 next$0 sk_?X_24$0 n_5$0)
  (ep$0 next$0 sk_?X_24$0 n_5$0)))

(assert (Btwn$0 next$0 x$0 (ep$0 next$0 sk_?X_24$0 x$0) (ep$0 next$0 sk_?X_24$0 x$0)))

(assert (or (= (read$0 next_2$0 res_4$0) root_x$0) (not (in$0 res_4$0 X_27$0))))

(assert (or (= (read$0 next_2$0 null$0) root_x$0) (not (in$0 null$0 X_27$0))))

(assert (or (= (read$0 next_2$0 x$0) root_x$0) (not (in$0 x$0 X_27$0))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_3$0 Alloc$0))
                 (or (in$0 x FP_3$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_3$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_3$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_24$0 FP$0))
                 (or (in$0 x sk_?X_24$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_24$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_24$0 FP$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_23$0 sk_?X_15$0))
                 (or (in$0 x sk_?X_23$0) (in$0 x sk_?X_15$0)))
            (and (not (in$0 x sk_?X_23$0)) (not (in$0 x sk_?X_15$0))
                 (not (in$0 x (union$0 sk_?X_23$0 sk_?X_15$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_2$0) sk_?X_19$0))
                 (or (in$0 x (setminus$0 FP$0 FP_2$0)) (in$0 x sk_?X_19$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_2$0)))
                 (not (in$0 x sk_?X_19$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_2$0) sk_?X_19$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_14$0 sk_?X_15$0))
                 (or (in$0 x sk_?X_14$0) (in$0 x sk_?X_15$0)))
            (and (not (in$0 x sk_?X_14$0)) (not (in$0 x sk_?X_15$0))
                 (not (in$0 x (union$0 sk_?X_14$0 sk_?X_15$0)))))))

(assert (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_2$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_2$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_2$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_2$0)
                          (setminus$0 Alloc$0 Alloc$0))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_27$0 sk_?X_15$0))
                 (or (in$0 x sk_?X_27$0) (in$0 x sk_?X_15$0)))
            (and (not (in$0 x sk_?X_27$0)) (not (in$0 x sk_?X_15$0))
                 (not (in$0 x (union$0 sk_?X_27$0 sk_?X_15$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_27$0) (in$0 x sk_?X_15$0)
                 (in$0 x (intersection$0 sk_?X_27$0 sk_?X_15$0)))
            (and (or (not (in$0 x sk_?X_27$0)) (not (in$0 x sk_?X_15$0)))
                 (not (in$0 x (intersection$0 sk_?X_27$0 sk_?X_15$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_23$0) (in$0 x sk_?X_15$0)
                 (in$0 x (intersection$0 sk_?X_23$0 sk_?X_15$0)))
            (and (or (not (in$0 x sk_?X_23$0)) (not (in$0 x sk_?X_15$0)))
                 (not (in$0 x (intersection$0 sk_?X_23$0 sk_?X_15$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_14$0) (in$0 x sk_?X_15$0)
                 (in$0 x (intersection$0 sk_?X_14$0 sk_?X_15$0)))
            (and (or (not (in$0 x sk_?X_14$0)) (not (in$0 x sk_?X_15$0)))
                 (not (in$0 x (intersection$0 sk_?X_14$0 sk_?X_15$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_24$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_24$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_24$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_24$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 sk_?X_24$0))
                 (not (in$0 x sk_?X_24$0)))
            (and (or (in$0 x sk_?X_24$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 sk_?X_24$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 sk_?X_24$0))
                 (not (in$0 x sk_?X_24$0)))
            (and (or (in$0 x sk_?X_24$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 sk_?X_24$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))))

(assert (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (= (read$0 next$0 null$0) null$0))

(assert (= (read$0 next_2$0 null$0) null$0))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (Btwn$0 next$0 n_5$0 root_x$0 root_x$0)
    (not (lseg_set_struct$0 sk_?X_27$0 next$0 n_5$0 root_x$0 X_27$0))))

(assert (= FP_3$0
  (union$0 (setminus$0 FP$0 FP_2$0)
    (union$0 (intersection$0 Alloc$0 FP_2$0) (setminus$0 Alloc$0 Alloc$0)))))

(assert (= n_5$0 (read$0 next$0 x$0)))

(assert (= Alloc$0 (union$0 FP_3$0 Alloc$0)))

(assert (= (read$0 next$0 root_x$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_23$0 sk_?X_21$0)))

(assert (= sk_?X_20$0 (union$0 sk_?X_23$0 sk_?X_21$0)))

(assert (= sk_?X_21$0 sk_?X_22$0))

(assert (= sk_?X_23$0 (lseg_set_domain$0 next$0 x$0 root_x$0)))

(assert (lseg_set_struct$0 sk_?X_23$0 next$0 x$0 root_x$0 X$0))

(assert (= emptyset$0 emptyset$0))

(assert (= X_27$0 (lseg_set_X$0 next$0 n_5$0 root_x$0)))

(assert (= sk_?X_24$0 FP_2$0))

(assert (= sk_?X_26$0 (setenum$0 root_x$0)))

(assert (= FP$0 (union$0 FP_2$0 FP$0)))

(assert (= (read$0 next_2$0 root_x$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_14$0 sk_?X_16$0)))

(assert (= sk_?X_14$0 X_27$0))

(assert (= sk_?X_16$0 sk_?X_15$0))

(assert (= sk_?X_18$0 sk_?X_17$0))

(assert (= sk_?X_19$0 sk_?X_18$0))

(assert (not (= n_5$0 null$0)))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 n_5$0 l1 root_x$0)
                 (in$0 l1 (lseg_set_X$0 next$0 n_5$0 root_x$0))
                 (not (= l1 root_x$0)))
            (and (or (= l1 root_x$0) (not (Btwn$0 next$0 n_5$0 l1 root_x$0)))
                 (not (in$0 l1 (lseg_set_X$0 next$0 n_5$0 root_x$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 x$0 l1 root_x$0)
                 (in$0 l1 (lseg_set_X$0 next$0 x$0 root_x$0))
                 (not (= l1 root_x$0)))
            (and (or (= l1 root_x$0) (not (Btwn$0 next$0 x$0 l1 root_x$0)))
                 (not (in$0 l1 (lseg_set_X$0 next$0 x$0 root_x$0)))))))

(assert (or (and Axiom_2$0 Axiom_1$0 Axiom$0)
    (not (Frame$0 FP_2$0 Alloc$0 next$0 next_2$0))))

(assert (or (Btwn$0 next$0 x$0 root_x$0 root_x$0)
    (not (lseg_set_struct$0 sk_?X_23$0 next$0 x$0 root_x$0 X$0))))

(assert (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (Frame$0 FP_2$0 Alloc$0 next$0 next_2$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= emptyset$0 emptyset$0))

(assert (= X$0 (lseg_set_X$0 next$0 x$0 root_x$0)))

(assert (= sk_?X_20$0 FP$0))

(assert (= sk_?X_22$0 (setenum$0 root_x$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (= (read$0 next$0 root_x$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_27$0 sk_?X_25$0)))

(assert (= sk_?X_24$0 (union$0 sk_?X_27$0 sk_?X_25$0)))

(assert (= sk_?X_25$0 sk_?X_26$0))

(assert (= sk_?X_27$0 (lseg_set_domain$0 next$0 n_5$0 root_x$0)))

(assert (lseg_set_struct$0 sk_?X_27$0 next$0 n_5$0 root_x$0 X_27$0))

(assert (= emptyset$0 emptyset$0))

(assert (= res_4$0 root_x$0))

(assert (= sk_?X_15$0 (setenum$0 root_x$0)))

(assert (= sk_?X_17$0 (union$0 sk_?X_14$0 sk_?X_16$0)))

(assert (= sk_?X_19$0
  (union$0 (intersection$0 Alloc$0 FP_2$0) (setminus$0 Alloc$0 Alloc$0))))

(assert (not (in$0 null$0 Alloc$0)))

(assert (not (in$0 x$0 FP_3$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 n_5$0 l1 root_x$0)
                 (in$0 l1 (lseg_set_domain$0 next$0 n_5$0 root_x$0))
                 (not (= l1 root_x$0)))
            (and (or (= l1 root_x$0) (not (Btwn$0 next$0 n_5$0 l1 root_x$0)))
                 (not (in$0 l1 (lseg_set_domain$0 next$0 n_5$0 root_x$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 x$0 l1 root_x$0)
                 (in$0 l1 (lseg_set_domain$0 next$0 x$0 root_x$0))
                 (not (= l1 root_x$0)))
            (and (or (= l1 root_x$0) (not (Btwn$0 next$0 x$0 l1 root_x$0)))
                 (not (in$0 l1 (lseg_set_domain$0 next$0 x$0 root_x$0)))))))

(assert (forall ((?x Loc)) (Btwn$0 next_2$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_2$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?y)) (not (Btwn$0 next_2$0 ?x ?z ?z))
            (Btwn$0 next_2$0 ?x ?y ?z) (Btwn$0 next_2$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z))
            (and (Btwn$0 next_2$0 ?x ?y ?y) (Btwn$0 next_2$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?y)) (not (Btwn$0 next_2$0 ?y ?z ?z))
            (Btwn$0 next_2$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z)) (not (Btwn$0 next_2$0 ?y ?u ?z))
            (and (Btwn$0 next_2$0 ?x ?y ?u) (Btwn$0 next_2$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z)) (not (Btwn$0 next_2$0 ?x ?u ?y))
            (and (Btwn$0 next_2$0 ?x ?u ?z) (Btwn$0 next_2$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))))

(check-sat)
(exit)
