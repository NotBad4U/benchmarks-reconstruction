(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sl/sl_reverse.spl:26:1-2:A postcondition of procedure reverse might not hold at this return point
  tests/spl/sl/sl_reverse.spl:11:10-25:Related location: This is the postcondition that might not hold
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
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun FP_Caller_final_1$0 () SetLoc)
(declare-fun curr_2$0 () Loc)
(declare-fun curr_3$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_1$0 () FldLoc)
(declare-fun rev_1$0 () Loc)
(declare-fun rev_2$0 () Loc)
(declare-fun sk_?X_4$0 () SetLoc)
(declare-fun sk_?X_5$0 () SetLoc)
(declare-fun sk_?X_6$0 () SetLoc)
(declare-fun sk_?X_7$0 () SetLoc)
(declare-fun sk_?X_8$0 () SetLoc)
(declare-fun sk_?X_9$0 () SetLoc)
(declare-fun sk_?X_10$0 () SetLoc)
(declare-fun sk_?X_11$0 () SetLoc)
(declare-fun sk_?e_1$0 () Loc)

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 rev_1$0 ?y ?y)) (= rev_1$0 ?y)
            (Btwn$0 next$0 rev_1$0 (read$0 next$0 rev_1$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_1$0 rev_1$0 ?y ?y)) (= rev_1$0 ?y)
            (Btwn$0 next_1$0 rev_1$0 (read$0 next_1$0 rev_1$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 rev_1$0) rev_1$0))
            (not (Btwn$0 next$0 rev_1$0 ?y ?y)) (= rev_1$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_1$0 rev_1$0) rev_1$0))
            (not (Btwn$0 next_1$0 rev_1$0 ?y ?y)) (= rev_1$0 ?y))))

(assert (Btwn$0 next$0 rev_1$0 (read$0 next$0 rev_1$0) (read$0 next$0 rev_1$0)))

(assert (Btwn$0 next_1$0 rev_1$0 (read$0 next_1$0 rev_1$0) (read$0 next_1$0 rev_1$0)))

(assert (or (not Axiom_2$0)
    (or (= (read$0 next$0 rev_1$0) (read$0 next_1$0 rev_1$0))
        (not (in$0 rev_1$0 (setminus$0 Alloc$0 FP_1$0))))))

(assert (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 curr_2$0 ?z ?y)
                     (Btwn$0 next_1$0 curr_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 curr_2$0 ?z ?y))
                     (not (Btwn$0 next_1$0 curr_2$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 curr_2$0 ?y
                           (ep$0 next$0 FP_1$0 curr_2$0))
                         (and (Btwn$0 next$0 curr_2$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 curr_2$0
                                     (ep$0 next$0 FP_1$0 curr_2$0)
                                     (ep$0 next$0 FP_1$0 curr_2$0))))))))))

(assert (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 rev_1$0 ?z ?y)
                     (Btwn$0 next_1$0 rev_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 rev_1$0 ?z ?y))
                     (not (Btwn$0 next_1$0 rev_1$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 rev_1$0 ?y
                           (ep$0 next$0 FP_1$0 rev_1$0))
                         (and (Btwn$0 next$0 rev_1$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 rev_1$0
                                     (ep$0 next$0 FP_1$0 rev_1$0)
                                     (ep$0 next$0 FP_1$0 rev_1$0))))))))))

(assert (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 rev_2$0 ?z ?y)
                     (Btwn$0 next_1$0 rev_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 rev_2$0 ?z ?y))
                     (not (Btwn$0 next_1$0 rev_2$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 rev_2$0 ?y
                           (ep$0 next$0 FP_1$0 rev_2$0))
                         (and (Btwn$0 next$0 rev_2$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 rev_2$0
                                     (ep$0 next$0 FP_1$0 rev_2$0)
                                     (ep$0 next$0 FP_1$0 rev_2$0))))))))))

(assert (or (not Axiom_1$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 sk_?e_1$0 ?z ?y)
                     (Btwn$0 next_1$0 sk_?e_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_?e_1$0 ?z ?y))
                     (not (Btwn$0 next_1$0 sk_?e_1$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 sk_?e_1$0 ?y
                           (ep$0 next$0 FP_1$0 sk_?e_1$0))
                         (and (Btwn$0 next$0 sk_?e_1$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 sk_?e_1$0
                                     (ep$0 next$0 FP_1$0 sk_?e_1$0)
                                     (ep$0 next$0 FP_1$0 sk_?e_1$0))))))))))

(assert (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 curr_2$0 FP_1$0)
                (and (Btwn$0 next$0 curr_2$0 ?z ?y)
                     (Btwn$0 next_1$0 curr_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 curr_2$0 ?z ?y))
                     (not (Btwn$0 next_1$0 curr_2$0 ?z ?y)))
                (not (= curr_2$0 (ep$0 next$0 FP_1$0 curr_2$0)))))))

(assert (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 rev_1$0 FP_1$0)
                (and (Btwn$0 next$0 rev_1$0 ?z ?y)
                     (Btwn$0 next_1$0 rev_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 rev_1$0 ?z ?y))
                     (not (Btwn$0 next_1$0 rev_1$0 ?z ?y)))
                (not (= rev_1$0 (ep$0 next$0 FP_1$0 rev_1$0)))))))

(assert (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 rev_2$0 FP_1$0)
                (and (Btwn$0 next$0 rev_2$0 ?z ?y)
                     (Btwn$0 next_1$0 rev_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 rev_2$0 ?z ?y))
                     (not (Btwn$0 next_1$0 rev_2$0 ?z ?y)))
                (not (= rev_2$0 (ep$0 next$0 FP_1$0 rev_2$0)))))))

(assert (or (not Axiom$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 sk_?e_1$0 FP_1$0)
                (and (Btwn$0 next$0 sk_?e_1$0 ?z ?y)
                     (Btwn$0 next_1$0 sk_?e_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_?e_1$0 ?z ?y))
                     (not (Btwn$0 next_1$0 sk_?e_1$0 ?z ?y)))
                (not (= sk_?e_1$0 (ep$0 next$0 FP_1$0 sk_?e_1$0)))))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 curr_2$0 (ep$0 next$0 FP_1$0 curr_2$0) ?y)
            (not (Btwn$0 next$0 curr_2$0 ?y ?y)) (not (in$0 ?y FP_1$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 rev_1$0 (ep$0 next$0 FP_1$0 rev_1$0) ?y)
            (not (Btwn$0 next$0 rev_1$0 ?y ?y)) (not (in$0 ?y FP_1$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 rev_2$0 (ep$0 next$0 FP_1$0 rev_2$0) ?y)
            (not (Btwn$0 next$0 rev_2$0 ?y ?y)) (not (in$0 ?y FP_1$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_?e_1$0 (ep$0 next$0 FP_1$0 sk_?e_1$0) ?y)
            (not (Btwn$0 next$0 sk_?e_1$0 ?y ?y)) (not (in$0 ?y FP_1$0)))))

(assert (or (in$0 (ep$0 next$0 FP_1$0 curr_2$0) FP_1$0)
    (= curr_2$0 (ep$0 next$0 FP_1$0 curr_2$0))))

(assert (or (in$0 (ep$0 next$0 FP_1$0 rev_1$0) FP_1$0)
    (= rev_1$0 (ep$0 next$0 FP_1$0 rev_1$0))))

(assert (or (in$0 (ep$0 next$0 FP_1$0 rev_2$0) FP_1$0)
    (= rev_2$0 (ep$0 next$0 FP_1$0 rev_2$0))))

(assert (or (in$0 (ep$0 next$0 FP_1$0 sk_?e_1$0) FP_1$0)
    (= sk_?e_1$0 (ep$0 next$0 FP_1$0 sk_?e_1$0))))

(assert (Btwn$0 next$0 curr_2$0 (ep$0 next$0 FP_1$0 curr_2$0)
  (ep$0 next$0 FP_1$0 curr_2$0)))

(assert (Btwn$0 next$0 rev_1$0 (ep$0 next$0 FP_1$0 rev_1$0)
  (ep$0 next$0 FP_1$0 rev_1$0)))

(assert (Btwn$0 next$0 rev_2$0 (ep$0 next$0 FP_1$0 rev_2$0)
  (ep$0 next$0 FP_1$0 rev_2$0)))

(assert (Btwn$0 next$0 sk_?e_1$0 (ep$0 next$0 FP_1$0 sk_?e_1$0)
  (ep$0 next$0 FP_1$0 sk_?e_1$0)))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 Alloc$0))
                 (or (in$0 x FP_2$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_2$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_1$0 FP$0))
                 (or (in$0 x FP_1$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_1$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_1$0 FP$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_9$0 FP$0))
                 (or (in$0 x sk_?X_9$0) (in$0 x FP$0)))
            (and (not (in$0 x sk_?X_9$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 sk_?X_9$0 FP$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_6$0))
                 (or (in$0 x (setminus$0 FP$0 FP_1$0)) (in$0 x sk_?X_6$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_1$0)))
                 (not (in$0 x sk_?X_6$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_1$0) sk_?X_6$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_1$0 FP_2$0))
                 (or (in$0 x FP_Caller_1$0) (in$0 x FP_2$0)))
            (and (not (in$0 x FP_Caller_1$0)) (not (in$0 x FP_2$0))
                 (not (in$0 x (union$0 FP_Caller_1$0 FP_2$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_4$0 sk_?X_5$0))
                 (or (in$0 x sk_?X_4$0) (in$0 x sk_?X_5$0)))
            (and (not (in$0 x sk_?X_4$0)) (not (in$0 x sk_?X_5$0))
                 (not (in$0 x (union$0 sk_?X_4$0 sk_?X_5$0)))))))

(assert (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_1$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_1$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_1$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_1$0)
                          (setminus$0 Alloc$0 Alloc$0))))))))

(assert (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP$0)
                          (setminus$0 Alloc$0 Alloc$0))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_9$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 sk_?X_9$0 FP$0)))
            (and (or (not (in$0 x sk_?X_9$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 sk_?X_9$0 FP$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_4$0) (in$0 x sk_?X_5$0)
                 (in$0 x (intersection$0 sk_?X_4$0 sk_?X_5$0)))
            (and (or (not (in$0 x sk_?X_4$0)) (not (in$0 x sk_?X_5$0)))
                 (not (in$0 x (intersection$0 sk_?X_4$0 sk_?X_5$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 Alloc$0 FP$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_1$0)
                 (in$0 x (intersection$0 Alloc$0 FP_1$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_1$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_1$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 FP_1$0))
                 (not (in$0 x FP_1$0)))
            (and (or (in$0 x FP_1$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 FP_1$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 FP_1$0))
                 (not (in$0 x FP_1$0)))
            (and (or (in$0 x FP_1$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 FP_1$0)))))))

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

(assert (= (read$0 next_1$0 null$0) null$0))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (Btwn$0 next$0 lst$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_10$0 next$0 lst$0 null$0))))

(assert (or (Btwn$0 next_1$0 curr_3$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_5$0 next_1$0 curr_3$0 null$0))))

(assert (or (Btwn$0 next_1$0 rev_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_11$0 next_1$0 rev_2$0 null$0))))

(assert (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= curr_2$0 lst$0))

(assert (= rev_1$0 null$0))

(assert (= Alloc$0 (union$0 FP_2$0 Alloc$0)))

(assert (= emptyset$0 (intersection$0 sk_?X_4$0 sk_?X_5$0)))

(assert (= sk_?X_5$0 (lseg_domain$0 next_1$0 curr_3$0 null$0)))

(assert (= sk_?X_6$0 (union$0 sk_?X_4$0 sk_?X_5$0)))

(assert (lseg_struct$0 sk_?X_5$0 next_1$0 curr_3$0 null$0))

(assert (= sk_?X_7$0 (union$0 sk_?X_9$0 sk_?X_8$0)))

(assert (= sk_?X_8$0 (lseg_domain$0 next$0 curr_2$0 null$0)))

(assert (= FP$0 (union$0 FP_1$0 FP$0)))

(assert (lseg_struct$0 sk_?X_9$0 next$0 rev_1$0 null$0))

(assert (= sk_?X_10$0 (lseg_domain$0 next$0 lst$0 null$0)))

(assert (lseg_struct$0 sk_?X_10$0 next$0 lst$0 null$0))

(assert (or
    (and (in$0 sk_?e_1$0 (lseg_domain$0 next_1$0 rev_2$0 null$0))
         (not (in$0 sk_?e_1$0 sk_?X_11$0)))
    (and (in$0 sk_?e_1$0 sk_?X_11$0)
         (not (in$0 sk_?e_1$0 (lseg_domain$0 next_1$0 rev_2$0 null$0))))
    (not (Btwn$0 next_1$0 rev_2$0 null$0 null$0))))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_1$0 curr_3$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_1$0 curr_3$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next_1$0 curr_3$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_1$0 curr_3$0 null$0)))))))

(assert (or (and Axiom_2$0 Axiom_1$0 Axiom$0)
    (not (Frame$0 FP_1$0 Alloc$0 next$0 next_1$0))))

(assert (or (Btwn$0 next$0 curr_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_8$0 next$0 curr_2$0 null$0))))

(assert (or (Btwn$0 next$0 rev_1$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_9$0 next$0 rev_1$0 null$0))))

(assert (or (Btwn$0 next_1$0 rev_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_4$0 next_1$0 rev_2$0 null$0))))

(assert (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))))

(assert (= FP_Caller_final_1$0 (union$0 FP_Caller_1$0 FP_2$0)))

(assert (= curr_3$0 null$0))

(assert (Frame$0 FP_1$0 Alloc$0 next$0 next_1$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= sk_?X_4$0 (lseg_domain$0 next_1$0 rev_2$0 null$0)))

(assert (= sk_?X_6$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))))

(assert (lseg_struct$0 sk_?X_4$0 next_1$0 rev_2$0 null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_9$0 sk_?X_8$0)))

(assert (= sk_?X_7$0 FP_1$0))

(assert (= sk_?X_9$0 (lseg_domain$0 next$0 rev_1$0 null$0)))

(assert (lseg_struct$0 sk_?X_8$0 next$0 curr_2$0 null$0))

(assert (= sk_?X_10$0 FP$0))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (= sk_?X_11$0
  (union$0 (intersection$0 Alloc$0 FP$0) (setminus$0 Alloc$0 Alloc$0))))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr_2$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 rev_1$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 rev_1$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 rev_1$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 rev_1$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_1$0 rev_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_1$0 rev_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_1$0 rev_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_1$0 rev_2$0 null$0)))))))

(assert (forall ((?x Loc)) (Btwn$0 next_1$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_1$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?y)) (not (Btwn$0 next_1$0 ?x ?z ?z))
            (Btwn$0 next_1$0 ?x ?y ?z) (Btwn$0 next_1$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z))
            (and (Btwn$0 next_1$0 ?x ?y ?y) (Btwn$0 next_1$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?y)) (not (Btwn$0 next_1$0 ?y ?z ?z))
            (Btwn$0 next_1$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z)) (not (Btwn$0 next_1$0 ?y ?u ?z))
            (and (Btwn$0 next_1$0 ?x ?y ?u) (Btwn$0 next_1$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_1$0 ?x ?y ?z)) (not (Btwn$0 next_1$0 ?x ?u ?y))
            (and (Btwn$0 next_1$0 ?x ?u ?z) (Btwn$0 next_1$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))))

(check-sat)
(exit)
