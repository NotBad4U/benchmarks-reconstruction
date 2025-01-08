(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sl/rec_copy.spl:21:11-41:A precondition for this call of rec_reverse_loop might not hold
  tests/spl/sl/rec_copy.spl:11:11-46:Related location: This is the precondition that might not hold
  |)
(set-info :category "crafted")
(set-info :status unsat)

(declare-sort Loc 0)
(declare-sort SetLoc 0)
(declare-sort FldBool 0)
(declare-sort FldLoc 0)
(declare-fun null$0 () Loc)
(declare-fun read$0 (FldLoc Loc) Loc)
(declare-fun write$0 (FldLoc Loc Loc) FldLoc)
(declare-fun emptyset$0 () SetLoc)
(declare-fun setenum$0 (Loc) SetLoc)
(declare-fun union$0 (SetLoc SetLoc) SetLoc)
(declare-fun intersection$0 (SetLoc SetLoc) SetLoc)
(declare-fun setminus$0 (SetLoc SetLoc) SetLoc)
(declare-fun Btwn$0 (FldLoc Loc Loc Loc) Bool)
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_4$0 () SetLoc)
(declare-fun acc$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun lst_2$0 () Loc)
(declare-fun lst_3$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_6$0 () FldLoc)
(declare-fun old_lst_2$0 () Loc)
(declare-fun sk_?X_98$0 () SetLoc)
(declare-fun sk_?X_99$0 () SetLoc)
(declare-fun sk_?X_100$0 () SetLoc)
(declare-fun sk_?X_101$0 () SetLoc)
(declare-fun sk_?X_102$0 () SetLoc)
(declare-fun sk_?X_103$0 () SetLoc)
(declare-fun sk_?e_9$0 () Loc)
(declare-fun sk_FP_4$0 () SetLoc)

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 lst_2$0 ?y ?y)) (= lst_2$0 ?y)
            (Btwn$0 next$0 lst_2$0 (read$0 next$0 lst_2$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 lst_2$0) lst_2$0))
            (not (Btwn$0 next$0 lst_2$0 ?y ?y)) (= lst_2$0 ?y))))

(assert (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)))

(assert (Btwn$0 next$0 lst_2$0 (read$0 next$0 lst_2$0) (read$0 next$0 lst_2$0)))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_100$0 sk_?X_99$0))
                 (or (in$0 x sk_?X_100$0) (in$0 x sk_?X_99$0)))
            (and (not (in$0 x sk_?X_100$0)) (not (in$0 x sk_?X_99$0))
                 (not (in$0 x (union$0 sk_?X_100$0 sk_?X_99$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_103$0 sk_?X_102$0))
                 (or (in$0 x sk_?X_103$0) (in$0 x sk_?X_102$0)))
            (and (not (in$0 x sk_?X_103$0)) (not (in$0 x sk_?X_102$0))
                 (not (in$0 x (union$0 sk_?X_103$0 sk_?X_102$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_100$0) (in$0 x sk_?X_99$0)
                 (in$0 x (intersection$0 sk_?X_100$0 sk_?X_99$0)))
            (and (or (not (in$0 x sk_?X_100$0)) (not (in$0 x sk_?X_99$0)))
                 (not (in$0 x (intersection$0 sk_?X_100$0 sk_?X_99$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_103$0) (in$0 x sk_?X_102$0)
                 (in$0 x (intersection$0 sk_?X_103$0 sk_?X_102$0)))
            (and (or (not (in$0 x sk_?X_103$0)) (not (in$0 x sk_?X_102$0)))
                 (not (in$0 x (intersection$0 sk_?X_103$0 sk_?X_102$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))))

(assert (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (= (read$0 (write$0 next$0 lst_2$0 acc$0) lst_2$0) acc$0))

(assert (or (= null$0 lst_2$0)
    (= (read$0 next$0 null$0) (read$0 (write$0 next$0 lst_2$0 acc$0) null$0))))

(assert (or (= lst_2$0 lst_2$0)
    (= (read$0 next$0 lst_2$0)
      (read$0 (write$0 next$0 lst_2$0 acc$0) lst_2$0))))

(assert (= (read$0 next$0 null$0) null$0))

(assert (= (read$0 next_6$0 null$0) null$0))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (Btwn$0 next$0 lst_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_100$0 next$0 lst_2$0 null$0))))

(assert (or (Btwn$0 next_6$0 old_lst_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_102$0 next_6$0 old_lst_2$0 null$0))))

(assert (= lst_3$0 (read$0 next$0 lst_2$0)))

(assert (= old_lst_2$0 lst_2$0))

(assert (= emptyset$0 (intersection$0 sk_?X_100$0 sk_?X_99$0)))

(assert (= sk_?X_98$0 FP$0))

(assert (= sk_?X_100$0 (lseg_domain$0 next$0 lst_2$0 null$0)))

(assert (lseg_struct$0 sk_?X_99$0 next$0 acc$0 null$0))

(assert (= sk_?X_101$0 (union$0 sk_?X_103$0 sk_?X_102$0)))

(assert (= sk_?X_103$0 (lseg_domain$0 next_6$0 lst_3$0 null$0)))

(assert (or (in$0 sk_?e_9$0 (intersection$0 sk_?X_103$0 sk_?X_102$0))
    (and (in$0 sk_?e_9$0 sk_FP_4$0) (not (in$0 sk_?e_9$0 FP$0)))
    (not (Btwn$0 next_6$0 lst_3$0 null$0 null$0))
    (not (Btwn$0 next_6$0 old_lst_2$0 null$0 null$0))))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 lst_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 lst_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 lst_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 lst_2$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_6$0 old_lst_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_6$0 old_lst_2$0 null$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next_6$0 old_lst_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_6$0 old_lst_2$0 null$0)))))))

(assert (or (Btwn$0 next$0 acc$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_99$0 next$0 acc$0 null$0))))

(assert (or (Btwn$0 next_6$0 lst_3$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_103$0 next_6$0 lst_3$0 null$0))))

(assert (= FP_Caller_4$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= next_6$0 (write$0 next$0 old_lst_2$0 acc$0)))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= sk_?X_98$0 (union$0 sk_?X_100$0 sk_?X_99$0)))

(assert (= sk_?X_99$0 (lseg_domain$0 next$0 acc$0 null$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (lseg_struct$0 sk_?X_100$0 next$0 lst_2$0 null$0))

(assert (= sk_?X_102$0 (lseg_domain$0 next_6$0 old_lst_2$0 null$0)))

(assert (= sk_FP_4$0 sk_?X_101$0))

(assert (not (= lst_2$0 null$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 acc$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 acc$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 acc$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 acc$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_6$0 lst_3$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_6$0 lst_3$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_6$0 lst_3$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_6$0 lst_3$0 null$0)))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 old_lst_2$0 acc$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v old_lst_2$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z old_lst_2$0
                                               old_lst_2$0)))))
                          (and (not (= old_lst_2$0 ?v))
                               (or (Btwn$0 next$0 ?z old_lst_2$0 ?v)
                                   (and
                                        (Btwn$0 next$0 ?z old_lst_2$0
                                          old_lst_2$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u old_lst_2$0)
                               (or (Btwn$0 next$0 acc$0 ?v old_lst_2$0)
                                   (and (Btwn$0 next$0 acc$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 acc$0 old_lst_2$0
                                               old_lst_2$0)))))
                          (and (not (= old_lst_2$0 ?v))
                               (or (Btwn$0 next$0 ?z old_lst_2$0 ?v)
                                   (and
                                        (Btwn$0 next$0 ?z old_lst_2$0
                                          old_lst_2$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 acc$0 ?u ?v)
                               (or (Btwn$0 next$0 acc$0 ?v old_lst_2$0)
                                   (and (Btwn$0 next$0 acc$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 acc$0 old_lst_2$0
                                               old_lst_2$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v old_lst_2$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not
                                    (Btwn$0 next$0 ?z old_lst_2$0
                                      old_lst_2$0)))))
                 (and (not (= old_lst_2$0 ?v))
                      (or (Btwn$0 next$0 ?z old_lst_2$0 ?v)
                          (and (Btwn$0 next$0 ?z old_lst_2$0 old_lst_2$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u old_lst_2$0)
                      (or (Btwn$0 next$0 acc$0 ?v old_lst_2$0)
                          (and (Btwn$0 next$0 acc$0 ?v ?v)
                               (not
                                    (Btwn$0 next$0 acc$0 old_lst_2$0
                                      old_lst_2$0)))))
                 (and (not (= old_lst_2$0 ?v))
                      (or (Btwn$0 next$0 ?z old_lst_2$0 ?v)
                          (and (Btwn$0 next$0 ?z old_lst_2$0 old_lst_2$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 acc$0 ?u ?v)
                      (or (Btwn$0 next$0 acc$0 ?v old_lst_2$0)
                          (and (Btwn$0 next$0 acc$0 ?v ?v)
                               (not
                                    (Btwn$0 next$0 acc$0 old_lst_2$0
                                      old_lst_2$0)))))
                 (not (Btwn$0 (write$0 next$0 old_lst_2$0 acc$0) ?z ?u ?v))))))

(assert (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))))

(check-sat)
(exit)
