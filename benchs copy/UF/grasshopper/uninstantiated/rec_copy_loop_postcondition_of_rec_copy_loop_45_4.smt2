(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/sl/rec_copy.spl:45:4-32:A postcondition of procedure rec_copy_loop might not hold at this return point
  tests/spl/sl/rec_copy.spl:35:10-46:Related location: This is the postcondition that might not hold
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
(declare-fun Alloc_2$0 () SetLoc)
(declare-fun Alloc_3$0 () SetLoc)
(declare-fun Axiom_6$0 () Bool)
(declare-fun Axiom_7$0 () Bool)
(declare-fun Axiom_8$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_3$0 () SetLoc)
(declare-fun FP_4$0 () SetLoc)
(declare-fun FP_5$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun FP_Caller_final_3$0 () SetLoc)
(declare-fun cp$0 () Loc)
(declare-fun cp_1$0 () Loc)
(declare-fun curr$0 () Loc)
(declare-fun lseg_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_struct$0 (SetLoc FldLoc Loc Loc) Bool)
(declare-fun n_2$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_2$0 () FldLoc)
(declare-fun next_3$0 () FldLoc)
(declare-fun old_cp_2$0 () Loc)
(declare-fun res_6$0 () Loc)
(declare-fun res_7$0 () Loc)
(declare-fun sk_?X_48$0 () SetLoc)
(declare-fun sk_?X_49$0 () SetLoc)
(declare-fun sk_?X_50$0 () SetLoc)
(declare-fun sk_?X_51$0 () SetLoc)
(declare-fun sk_?X_52$0 () SetLoc)
(declare-fun sk_?X_53$0 () SetLoc)
(declare-fun sk_?X_54$0 () SetLoc)
(declare-fun sk_?X_55$0 () SetLoc)
(declare-fun sk_?X_56$0 () SetLoc)
(declare-fun sk_?X_57$0 () SetLoc)
(declare-fun sk_?X_58$0 () SetLoc)
(declare-fun sk_?X_59$0 () SetLoc)
(declare-fun sk_?e_5$0 () Loc)
(declare-fun t_17$0 () Loc)
(declare-fun t_18$0 () Loc)
(declare-fun t_19$0 () Loc)
(declare-fun t_20$0 () Loc)
(declare-fun t_21$0 () Loc)
(declare-fun t_22$0 () Loc)
(declare-fun t_23$0 () Loc)
(declare-fun t_24$0 () Loc)
(declare-fun t_25$0 () Loc)
(declare-fun t_26$0 () Loc)
(declare-fun t_27$0 () Loc)
(declare-fun t_28$0 () Loc)
(declare-fun t_29$0 () Loc)
(declare-fun t_30$0 () Loc)
(declare-fun tmp_1$0 () Loc)

(assert (= (ep$0 next_2$0 FP_4$0 tmp_1$0) t_30$0))

(assert (= (ep$0 next_2$0 FP_4$0 sk_?e_5$0) t_29$0))

(assert (= (ep$0 next_2$0 FP_4$0 res_7$0) t_28$0))

(assert (= (ep$0 next_2$0 FP_4$0 res_6$0) t_27$0))

(assert (= (ep$0 next_2$0 FP_4$0 n_2$0) t_26$0))

(assert (= (ep$0 next_2$0 FP_4$0 curr$0) t_25$0))

(assert (= (ep$0 next_2$0 FP_4$0 cp_1$0) t_24$0))

(assert (= (ep$0 next_2$0 FP_4$0 cp$0) t_23$0))

(assert (= (ep$0 next_2$0 FP_4$0 null$0) t_22$0))

(assert (= (read$0 next_3$0 curr$0) t_21$0))

(assert (= (read$0 next$0 curr$0) t_20$0))

(assert (= (read$0 next$0 cp_1$0) t_19$0))

(assert (= (read$0 (write$0 next$0 cp_1$0 old_cp_2$0) curr$0) t_18$0))

(assert (= (read$0 (write$0 next$0 cp_1$0 old_cp_2$0) cp_1$0) t_17$0))

(assert (forall ((?d_10 Loc) (?x Loc) (?y Loc))
        (or (= ?y ?x)
            (= (read$0 next$0 ?y) (read$0 (write$0 next$0 ?x ?d_10) ?y)))))

(assert (forall ((?d_10 Loc) (?x Loc))
        (= (read$0 (write$0 next$0 ?x ?d_10) ?x) ?d_10)))

(assert (forall ((?f FldLoc)) (= (read$0 ?f null$0) null$0)))

(assert (forall ((x Loc) (y Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$0 x X) (in$0 x (setminus$0 X Y)) (not (in$0 x Y)))
            (and (or (in$0 x Y) (not (in$0 x X)))
                 (not (in$0 x (setminus$0 X Y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$0 x X) (in$0 x Y) (in$0 x (intersection$0 X Y)))
            (and (or (not (in$0 x X)) (not (in$0 x Y)))
                 (not (in$0 x (intersection$0 X Y)))))))

(assert (forall ((X SetLoc) (Y SetLoc) (x Loc))
        (or (and (in$0 x (union$0 X Y)) (or (in$0 x X) (in$0 x Y)))
            (and (not (in$0 x X)) (not (in$0 x Y))
                 (not (in$0 x (union$0 X Y)))))))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (Btwn$0 next$0 curr$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_55$0 next$0 curr$0 null$0))))

(assert (or (Btwn$0 next_2$0 n_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_52$0 next_2$0 n_2$0 null$0))))

(assert (or (Btwn$0 next_3$0 n_2$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_49$0 next_3$0 n_2$0 null$0))))

(assert (or (Btwn$0 next_3$0 res_7$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_57$0 next_3$0 res_7$0 null$0))))

(assert (= FP_3$0 (union$0 FP$0 (setenum$0 tmp_1$0))))

(assert (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= cp_1$0 tmp_1$0))

(assert (= next_2$0 (write$0 next$0 cp_1$0 old_cp_2$0)))

(assert (= res_7$0 res_6$0))

(assert (= Alloc_3$0 (union$0 FP_5$0 Alloc_3$0)))

(assert (= emptyset$0 (intersection$0 sk_?X_48$0 sk_?X_49$0)))

(assert (= sk_?X_49$0 (lseg_domain$0 next_3$0 n_2$0 null$0)))

(assert (= sk_?X_50$0 (union$0 sk_?X_48$0 sk_?X_49$0)))

(assert (lseg_struct$0 sk_?X_49$0 next_3$0 n_2$0 null$0))

(assert (= sk_?X_51$0 (union$0 sk_?X_53$0 sk_?X_52$0)))

(assert (= sk_?X_52$0 (lseg_domain$0 next_2$0 n_2$0 null$0)))

(assert (= FP_3$0 (union$0 FP_4$0 FP_3$0)))

(assert (lseg_struct$0 sk_?X_53$0 next_2$0 cp_1$0 null$0))

(assert (= sk_?X_54$0 (union$0 sk_?X_56$0 sk_?X_55$0)))

(assert (= sk_?X_55$0 (lseg_domain$0 next$0 curr$0 null$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (lseg_struct$0 sk_?X_56$0 next$0 cp$0 null$0))

(assert (= sk_?X_58$0 (lseg_domain$0 next_3$0 curr$0 null$0)))

(assert (or (in$0 sk_?e_5$0 (intersection$0 sk_?X_57$0 sk_?X_58$0))
    (and
         (in$0 sk_?e_5$0
           (union$0 (intersection$0 Alloc_3$0 FP$0)
             (setminus$0 Alloc_3$0 Alloc$0)))
         (not (in$0 sk_?e_5$0 sk_?X_59$0)))
    (and (in$0 sk_?e_5$0 sk_?X_59$0)
         (not
              (in$0 sk_?e_5$0
                (union$0 (intersection$0 Alloc_3$0 FP$0)
                  (setminus$0 Alloc_3$0 Alloc$0)))))
    (not (Btwn$0 next_3$0 curr$0 null$0 null$0))
    (not (Btwn$0 next_3$0 res_7$0 null$0 null$0))))

(assert (not (= tmp_1$0 null$0)))

(assert (not (in$0 null$0 Alloc_3$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 cp$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 cp$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 cp$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 cp$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_2$0 cp_1$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_2$0 cp_1$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_2$0 cp_1$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_2$0 cp_1$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_3$0 curr$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_3$0 curr$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_3$0 curr$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_3$0 curr$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_3$0 res_6$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_3$0 res_6$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_3$0 res_6$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_3$0 res_6$0 null$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) ?y) (not (Btwn$0 ?f ?x ?y ?y))
            (not (in$0 ?y ?X)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (in$0 ?y ?X))
            (in$0 (ep$0 ?f ?X ?x) ?X))))

(assert (or (and Axiom_8$0 Axiom_7$0 Axiom_6$0)
    (not (Frame$0 FP_4$0 Alloc_2$0 next_2$0 next_3$0))))

(assert (or (Btwn$0 next$0 cp$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_56$0 next$0 cp$0 null$0))))

(assert (or (Btwn$0 next_2$0 cp_1$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_53$0 next_2$0 cp_1$0 null$0))))

(assert (or (Btwn$0 next_3$0 curr$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_58$0 next_3$0 curr$0 null$0))))

(assert (or (Btwn$0 next_3$0 res_6$0 null$0 null$0)
    (not (lseg_struct$0 sk_?X_48$0 next_3$0 res_6$0 null$0))))

(assert (= Alloc_2$0 (union$0 Alloc$0 (setenum$0 tmp_1$0))))

(assert (= FP_5$0
  (union$0 (setminus$0 FP_3$0 FP_4$0)
    (union$0 (intersection$0 Alloc_3$0 FP_4$0)
      (setminus$0 Alloc_3$0 Alloc_2$0)))))

(assert (= FP_Caller_final_3$0 (union$0 FP_Caller_2$0 FP_5$0)))

(assert (= n_2$0 (read$0 next_2$0 curr$0)))

(assert (= old_cp_2$0 cp$0))

(assert (Frame$0 FP_4$0 Alloc_2$0 next_2$0 next_3$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= sk_?X_48$0 (lseg_domain$0 next_3$0 res_6$0 null$0)))

(assert (= sk_?X_50$0
  (union$0 (intersection$0 Alloc_3$0 FP_4$0)
    (setminus$0 Alloc_3$0 Alloc_2$0))))

(assert (lseg_struct$0 sk_?X_48$0 next_3$0 res_6$0 null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_53$0 sk_?X_52$0)))

(assert (= sk_?X_51$0 FP_4$0))

(assert (= sk_?X_53$0 (lseg_domain$0 next_2$0 cp_1$0 null$0)))

(assert (lseg_struct$0 sk_?X_52$0 next_2$0 n_2$0 null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_56$0 sk_?X_55$0)))

(assert (= sk_?X_54$0 FP$0))

(assert (= sk_?X_56$0 (lseg_domain$0 next$0 cp$0 null$0)))

(assert (lseg_struct$0 sk_?X_55$0 next$0 curr$0 null$0))

(assert (= sk_?X_57$0 (lseg_domain$0 next_3$0 res_7$0 null$0)))

(assert (= sk_?X_59$0 (union$0 sk_?X_57$0 sk_?X_58$0)))

(assert (not (= curr$0 null$0)))

(assert (not (in$0 null$0 Alloc$0)))

(assert (not (in$0 tmp_1$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next$0 curr$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next$0 curr$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_2$0 n_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_2$0 n_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_2$0 n_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_2$0 n_2$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_3$0 n_2$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_3$0 n_2$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_3$0 n_2$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_3$0 n_2$0 null$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_3$0 res_7$0 l1 null$0)
                 (in$0 l1 (lseg_domain$0 next_3$0 res_7$0 null$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_3$0 res_7$0 l1 null$0)))
                 (not (in$0 l1 (lseg_domain$0 next_3$0 res_7$0 null$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (or (in$0 (ep$0 ?f ?X ?x) ?X) (= ?x (ep$0 ?f ?X ?x)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) (ep$0 ?f ?X ?x))))

(assert (or (not Axiom_6$0)
    (forall ((?x Loc) (?y Loc) (?z Loc))
            (or (in$0 ?x FP_4$0)
                (and (Btwn$0 next_2$0 ?x ?z ?y) (Btwn$0 next_3$0 ?x ?z ?y))
                (and (not (Btwn$0 next_2$0 ?x ?z ?y))
                     (not (Btwn$0 next_3$0 ?x ?z ?y)))
                (not (= ?x (ep$0 next_2$0 FP_4$0 ?x)))))))

(assert (or (not Axiom_7$0)
    (forall ((?x Loc) (?y Loc) (?z Loc))
            (or (and (Btwn$0 next_2$0 ?x ?z ?y) (Btwn$0 next_3$0 ?x ?z ?y))
                (and (not (Btwn$0 next_2$0 ?x ?z ?y))
                     (not (Btwn$0 next_3$0 ?x ?z ?y)))
                (not
                     (or (Btwn$0 next_2$0 ?x ?y (ep$0 next_2$0 FP_4$0 ?x))
                         (and (Btwn$0 next_2$0 ?x ?y ?y)
                              (not
                                   (Btwn$0 next_2$0 ?x
                                     (ep$0 next_2$0 FP_4$0 ?x)
                                     (ep$0 next_2$0 FP_4$0 ?x))))))))))

(assert (or (not Axiom_8$0)
    (forall ((?x Loc))
            (or (= (read$0 next_2$0 ?x) (read$0 next_3$0 ?x))
                (not (in$0 ?x (setminus$0 Alloc_2$0 FP_4$0)))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 cp_1$0 old_cp_2$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v cp_1$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z cp_1$0 cp_1$0)))))
                          (and (not (= cp_1$0 ?v))
                               (or (Btwn$0 next$0 ?z cp_1$0 ?v)
                                   (and (Btwn$0 next$0 ?z cp_1$0 cp_1$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u cp_1$0)
                               (or (Btwn$0 next$0 old_cp_2$0 ?v cp_1$0)
                                   (and (Btwn$0 next$0 old_cp_2$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 old_cp_2$0 cp_1$0
                                               cp_1$0)))))
                          (and (not (= cp_1$0 ?v))
                               (or (Btwn$0 next$0 ?z cp_1$0 ?v)
                                   (and (Btwn$0 next$0 ?z cp_1$0 cp_1$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 old_cp_2$0 ?u ?v)
                               (or (Btwn$0 next$0 old_cp_2$0 ?v cp_1$0)
                                   (and (Btwn$0 next$0 old_cp_2$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 old_cp_2$0 cp_1$0
                                               cp_1$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v cp_1$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z cp_1$0 cp_1$0)))))
                 (and (not (= cp_1$0 ?v))
                      (or (Btwn$0 next$0 ?z cp_1$0 ?v)
                          (and (Btwn$0 next$0 ?z cp_1$0 cp_1$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u cp_1$0)
                      (or (Btwn$0 next$0 old_cp_2$0 ?v cp_1$0)
                          (and (Btwn$0 next$0 old_cp_2$0 ?v ?v)
                               (not (Btwn$0 next$0 old_cp_2$0 cp_1$0 cp_1$0)))))
                 (and (not (= cp_1$0 ?v))
                      (or (Btwn$0 next$0 ?z cp_1$0 ?v)
                          (and (Btwn$0 next$0 ?z cp_1$0 cp_1$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 old_cp_2$0 ?u ?v)
                      (or (Btwn$0 next$0 old_cp_2$0 ?v cp_1$0)
                          (and (Btwn$0 next$0 old_cp_2$0 ?v ?v)
                               (not (Btwn$0 next$0 old_cp_2$0 cp_1$0 cp_1$0)))))
                 (not (Btwn$0 (write$0 next$0 cp_1$0 old_cp_2$0) ?z ?u ?v))))))

(assert (forall ((?f FldLoc) (?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?z)) (not (Btwn$0 ?f ?x ?u ?y))
            (and (Btwn$0 ?f ?x ?u ?z) (Btwn$0 ?f ?u ?y ?z)))))

(assert (forall ((?f FldLoc) (?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?z)) (not (Btwn$0 ?f ?y ?u ?z))
            (and (Btwn$0 ?f ?x ?y ?u) (Btwn$0 ?f ?x ?u ?z)))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (Btwn$0 ?f ?y ?z ?z))
            (Btwn$0 ?f ?x ?z ?z))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?z))
            (and (Btwn$0 ?f ?x ?y ?y) (Btwn$0 ?f ?y ?z ?z)))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (Btwn$0 ?f ?x ?z ?z))
            (Btwn$0 ?f ?x ?y ?z) (Btwn$0 ?f ?x ?z ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (= ?x ?y)
            (Btwn$0 ?f ?x (read$0 ?f ?x) ?y))))

(assert (forall ((?f FldLoc) (?x Loc) (?y Loc))
        (or (not (= (read$0 ?f ?x) ?x)) (not (Btwn$0 ?f ?x ?y ?y)) (= ?x ?y))))

(assert (forall ((?f FldLoc) (?x Loc)) (Btwn$0 ?f ?x (read$0 ?f ?x) (read$0 ?f ?x))))

(assert (forall ((?f FldLoc) (?x Loc)) (Btwn$0 ?f ?x ?x ?x)))

(check-sat)
(exit)
