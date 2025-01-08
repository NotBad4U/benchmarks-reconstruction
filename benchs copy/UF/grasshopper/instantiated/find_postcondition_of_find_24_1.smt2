(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/union_find.spl:24:1-2:A postcondition of procedure find might not hold at this return point
  tests/spl/union_find.spl:13:10:Related location: This is the postcondition that might not hold
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
(declare-fun Axiom_3$0 () Bool)
(declare-fun Axiom_4$0 () Bool)
(declare-fun Axiom_5$0 () Bool)
(declare-fun Axiom_6$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_3$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun FP_Caller_final_3$0 () SetLoc)
(declare-fun X$0 () SetLoc)
(declare-fun X_27$0 () SetLoc)
(declare-fun lseg_set_X$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_struct$0 (SetLoc FldLoc Loc Loc SetLoc) Bool)
(declare-fun n_5$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_2$0 () FldLoc)
(declare-fun next_3$0 () FldLoc)
(declare-fun res_3$0 () Loc)
(declare-fun res_4$0 () Loc)
(declare-fun root_x$0 () Loc)
(declare-fun sk_?X_28$0 () SetLoc)
(declare-fun sk_?X_29$0 () SetLoc)
(declare-fun sk_?X_30$0 () SetLoc)
(declare-fun sk_?X_31$0 () SetLoc)
(declare-fun sk_?X_32$0 () SetLoc)
(declare-fun sk_?X_33$0 () SetLoc)
(declare-fun sk_?X_34$0 () SetLoc)
(declare-fun sk_?X_35$0 () SetLoc)
(declare-fun sk_?X_36$0 () SetLoc)
(declare-fun sk_?X_37$0 () SetLoc)
(declare-fun sk_?X_38$0 () SetLoc)
(declare-fun sk_?X_39$0 () SetLoc)
(declare-fun sk_?X_40$0 () SetLoc)
(declare-fun sk_?X_41$0 () SetLoc)
(declare-fun sk_?X_42$0 () SetLoc)
(declare-fun sk_?X_43$0 () SetLoc)
(declare-fun sk_?X_44$0 () SetLoc)
(declare-fun sk_?X_45$0 () SetLoc)
(declare-fun sk_?X_46$0 () SetLoc)
(declare-fun sk_?X_47$0 () SetLoc)
(declare-fun sk_?e_2$0 () Loc)
(declare-fun sk_z$0 () Loc)
(declare-fun x$0 () Loc)

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 root_x$0 ?y ?y)) (= root_x$0 ?y)
            (Btwn$0 next$0 root_x$0 (read$0 next$0 root_x$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 sk_z$0 ?y ?y)) (= sk_z$0 ?y)
            (Btwn$0 next$0 sk_z$0 (read$0 next$0 sk_z$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 x$0 ?y ?y)) (= x$0 ?y)
            (Btwn$0 next$0 x$0 (read$0 next$0 x$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_2$0 null$0 (read$0 next_2$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 root_x$0 ?y ?y)) (= root_x$0 ?y)
            (Btwn$0 next_2$0 root_x$0 (read$0 next_2$0 root_x$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 sk_z$0 ?y ?y)) (= sk_z$0 ?y)
            (Btwn$0 next_2$0 sk_z$0 (read$0 next_2$0 sk_z$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_2$0 x$0 ?y ?y)) (= x$0 ?y)
            (Btwn$0 next_2$0 x$0 (read$0 next_2$0 x$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_3$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_3$0 null$0 (read$0 next_3$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_3$0 root_x$0 ?y ?y)) (= root_x$0 ?y)
            (Btwn$0 next_3$0 root_x$0 (read$0 next_3$0 root_x$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_3$0 sk_z$0 ?y ?y)) (= sk_z$0 ?y)
            (Btwn$0 next_3$0 sk_z$0 (read$0 next_3$0 sk_z$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 root_x$0) root_x$0))
            (not (Btwn$0 next$0 root_x$0 ?y ?y)) (= root_x$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 sk_z$0) sk_z$0))
            (not (Btwn$0 next$0 sk_z$0 ?y ?y)) (= sk_z$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 x$0) x$0)) (not (Btwn$0 next$0 x$0 ?y ?y))
            (= x$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 null$0) null$0))
            (not (Btwn$0 next_2$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 root_x$0) root_x$0))
            (not (Btwn$0 next_2$0 root_x$0 ?y ?y)) (= root_x$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 sk_z$0) sk_z$0))
            (not (Btwn$0 next_2$0 sk_z$0 ?y ?y)) (= sk_z$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_2$0 x$0) x$0))
            (not (Btwn$0 next_2$0 x$0 ?y ?y)) (= x$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_3$0 null$0) null$0))
            (not (Btwn$0 next_3$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_3$0 root_x$0) root_x$0))
            (not (Btwn$0 next_3$0 root_x$0 ?y ?y)) (= root_x$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_3$0 sk_z$0) sk_z$0))
            (not (Btwn$0 next_3$0 sk_z$0 ?y ?y)) (= sk_z$0 ?y))))

(assert (Btwn$0 next$0 root_x$0 (read$0 next$0 root_x$0) (read$0 next$0 root_x$0)))

(assert (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)))

(assert (Btwn$0 next$0 sk_z$0 (read$0 next$0 sk_z$0) (read$0 next$0 sk_z$0)))

(assert (Btwn$0 next$0 x$0 (read$0 next$0 x$0) (read$0 next$0 x$0)))

(assert (Btwn$0 next_2$0 null$0 (read$0 next_2$0 null$0) (read$0 next_2$0 null$0)))

(assert (Btwn$0 next_2$0 root_x$0 (read$0 next_2$0 root_x$0)
  (read$0 next_2$0 root_x$0)))

(assert (Btwn$0 next_2$0 sk_z$0 (read$0 next_2$0 sk_z$0) (read$0 next_2$0 sk_z$0)))

(assert (Btwn$0 next_2$0 x$0 (read$0 next_2$0 x$0) (read$0 next_2$0 x$0)))

(assert (Btwn$0 next_3$0 null$0 (read$0 next_3$0 null$0) (read$0 next_3$0 null$0)))

(assert (Btwn$0 next_3$0 root_x$0 (read$0 next_3$0 root_x$0)
  (read$0 next_3$0 root_x$0)))

(assert (Btwn$0 next_3$0 sk_z$0 (read$0 next_3$0 sk_z$0) (read$0 next_3$0 sk_z$0)))

(assert (or (not Axiom_6$0)
    (or (= (read$0 next$0 null$0) (read$0 next_2$0 null$0))
        (not (in$0 null$0 (setminus$0 Alloc$0 FP_2$0))))))

(assert (or (not Axiom_6$0)
    (or (= (read$0 next$0 root_x$0) (read$0 next_2$0 root_x$0))
        (not (in$0 root_x$0 (setminus$0 Alloc$0 FP_2$0))))))

(assert (or (not Axiom_6$0)
    (or (= (read$0 next$0 sk_z$0) (read$0 next_2$0 sk_z$0))
        (not (in$0 sk_z$0 (setminus$0 Alloc$0 FP_2$0))))))

(assert (or (not Axiom_6$0)
    (or (= (read$0 next$0 x$0) (read$0 next_2$0 x$0))
        (not (in$0 x$0 (setminus$0 Alloc$0 FP_2$0))))))

(assert (or (not Axiom_5$0)
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

(assert (or (not Axiom_5$0)
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

(assert (or (not Axiom_5$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 sk_?e_2$0 ?z ?y)
                     (Btwn$0 next_2$0 sk_?e_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_?e_2$0 ?z ?y))
                     (not (Btwn$0 next_2$0 sk_?e_2$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 sk_?e_2$0 ?y
                           (ep$0 next$0 FP_2$0 sk_?e_2$0))
                         (and (Btwn$0 next$0 sk_?e_2$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 sk_?e_2$0
                                     (ep$0 next$0 FP_2$0 sk_?e_2$0)
                                     (ep$0 next$0 FP_2$0 sk_?e_2$0))))))))))

(assert (or (not Axiom_5$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 sk_z$0 ?z ?y)
                     (Btwn$0 next_2$0 sk_z$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_z$0 ?z ?y))
                     (not (Btwn$0 next_2$0 sk_z$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 sk_z$0 ?y
                           (ep$0 next$0 FP_2$0 sk_z$0))
                         (and (Btwn$0 next$0 sk_z$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 sk_z$0
                                     (ep$0 next$0 FP_2$0 sk_z$0)
                                     (ep$0 next$0 FP_2$0 sk_z$0))))))))))

(assert (or (not Axiom_5$0)
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

(assert (or (not Axiom_4$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 null$0 FP_2$0)
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_2$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_2$0 null$0 ?z ?y)))
                (not (= null$0 (ep$0 next$0 FP_2$0 null$0)))))))

(assert (or (not Axiom_4$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 n_5$0 FP_2$0)
                (and (Btwn$0 next$0 n_5$0 ?z ?y)
                     (Btwn$0 next_2$0 n_5$0 ?z ?y))
                (and (not (Btwn$0 next$0 n_5$0 ?z ?y))
                     (not (Btwn$0 next_2$0 n_5$0 ?z ?y)))
                (not (= n_5$0 (ep$0 next$0 FP_2$0 n_5$0)))))))

(assert (or (not Axiom_4$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 sk_?e_2$0 FP_2$0)
                (and (Btwn$0 next$0 sk_?e_2$0 ?z ?y)
                     (Btwn$0 next_2$0 sk_?e_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_?e_2$0 ?z ?y))
                     (not (Btwn$0 next_2$0 sk_?e_2$0 ?z ?y)))
                (not (= sk_?e_2$0 (ep$0 next$0 FP_2$0 sk_?e_2$0)))))))

(assert (or (not Axiom_4$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 sk_z$0 FP_2$0)
                (and (Btwn$0 next$0 sk_z$0 ?z ?y)
                     (Btwn$0 next_2$0 sk_z$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_z$0 ?z ?y))
                     (not (Btwn$0 next_2$0 sk_z$0 ?z ?y)))
                (not (= sk_z$0 (ep$0 next$0 FP_2$0 sk_z$0)))))))

(assert (or (not Axiom_4$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 x$0 FP_2$0)
                (and (Btwn$0 next$0 x$0 ?z ?y) (Btwn$0 next_2$0 x$0 ?z ?y))
                (and (not (Btwn$0 next$0 x$0 ?z ?y))
                     (not (Btwn$0 next_2$0 x$0 ?z ?y)))
                (not (= x$0 (ep$0 next$0 FP_2$0 x$0)))))))

(assert (or (not Axiom_3$0)
    (or (= (read$0 next_2$0 null$0) root_x$0) (not (in$0 null$0 X_27$0)))))

(assert (or (not Axiom_3$0)
    (or (= (read$0 next_2$0 root_x$0) root_x$0) (not (in$0 root_x$0 X_27$0)))))

(assert (or (not Axiom_3$0)
    (or (= (read$0 next_2$0 sk_z$0) root_x$0) (not (in$0 sk_z$0 X_27$0)))))

(assert (or (not Axiom_3$0)
    (or (= (read$0 next_2$0 x$0) root_x$0) (not (in$0 x$0 X_27$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 FP_2$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y FP_2$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 n_5$0 (ep$0 next$0 FP_2$0 n_5$0) ?y)
            (not (Btwn$0 next$0 n_5$0 ?y ?y)) (not (in$0 ?y FP_2$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_?e_2$0 (ep$0 next$0 FP_2$0 sk_?e_2$0) ?y)
            (not (Btwn$0 next$0 sk_?e_2$0 ?y ?y)) (not (in$0 ?y FP_2$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_z$0 (ep$0 next$0 FP_2$0 sk_z$0) ?y)
            (not (Btwn$0 next$0 sk_z$0 ?y ?y)) (not (in$0 ?y FP_2$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 x$0 (ep$0 next$0 FP_2$0 x$0) ?y)
            (not (Btwn$0 next$0 x$0 ?y ?y)) (not (in$0 ?y FP_2$0)))))

(assert (or (in$0 (ep$0 next$0 FP_2$0 null$0) FP_2$0)
    (= null$0 (ep$0 next$0 FP_2$0 null$0))))

(assert (or (in$0 (ep$0 next$0 FP_2$0 n_5$0) FP_2$0)
    (= n_5$0 (ep$0 next$0 FP_2$0 n_5$0))))

(assert (or (in$0 (ep$0 next$0 FP_2$0 sk_?e_2$0) FP_2$0)
    (= sk_?e_2$0 (ep$0 next$0 FP_2$0 sk_?e_2$0))))

(assert (or (in$0 (ep$0 next$0 FP_2$0 sk_z$0) FP_2$0)
    (= sk_z$0 (ep$0 next$0 FP_2$0 sk_z$0))))

(assert (or (in$0 (ep$0 next$0 FP_2$0 x$0) FP_2$0) (= x$0 (ep$0 next$0 FP_2$0 x$0))))

(assert (Btwn$0 next$0 null$0 (ep$0 next$0 FP_2$0 null$0)
  (ep$0 next$0 FP_2$0 null$0)))

(assert (Btwn$0 next$0 n_5$0 (ep$0 next$0 FP_2$0 n_5$0) (ep$0 next$0 FP_2$0 n_5$0)))

(assert (Btwn$0 next$0 sk_?e_2$0 (ep$0 next$0 FP_2$0 sk_?e_2$0)
  (ep$0 next$0 FP_2$0 sk_?e_2$0)))

(assert (Btwn$0 next$0 sk_z$0 (ep$0 next$0 FP_2$0 sk_z$0)
  (ep$0 next$0 FP_2$0 sk_z$0)))

(assert (Btwn$0 next$0 x$0 (ep$0 next$0 FP_2$0 x$0) (ep$0 next$0 FP_2$0 x$0)))

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
            (and
                 (in$0 x
                   (union$0 (setminus$0 FP$0 FP_2$0)
                     (union$0 (intersection$0 Alloc$0 FP_2$0)
                       (setminus$0 Alloc$0 Alloc$0))))
                 (or (in$0 x (setminus$0 FP$0 FP_2$0))
                     (in$0 x
                       (union$0 (intersection$0 Alloc$0 FP_2$0)
                         (setminus$0 Alloc$0 Alloc$0)))))
            (and (not (in$0 x (setminus$0 FP$0 FP_2$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_2$0)
                          (setminus$0 Alloc$0 Alloc$0))))
                 (not
                      (in$0 x
                        (union$0 (setminus$0 FP$0 FP_2$0)
                          (union$0 (intersection$0 Alloc$0 FP_2$0)
                            (setminus$0 Alloc$0 Alloc$0)))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_2$0 FP$0))
                 (or (in$0 x FP_2$0) (in$0 x FP$0)))
            (and (not (in$0 x FP_2$0)) (not (in$0 x FP$0))
                 (not (in$0 x (union$0 FP_2$0 FP$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_3$0 Alloc$0))
                 (or (in$0 x FP_3$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_3$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_3$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_38$0 sk_?X_40$0))
                 (or (in$0 x sk_?X_38$0) (in$0 x sk_?X_40$0)))
            (and (not (in$0 x sk_?X_38$0)) (not (in$0 x sk_?X_40$0))
                 (not (in$0 x (union$0 sk_?X_38$0 sk_?X_40$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_47$0 sk_?X_45$0))
                 (or (in$0 x sk_?X_47$0) (in$0 x sk_?X_45$0)))
            (and (not (in$0 x sk_?X_47$0)) (not (in$0 x sk_?X_45$0))
                 (not (in$0 x (union$0 sk_?X_47$0 sk_?X_45$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_31$0 sk_?X_29$0))
                 (or (in$0 x sk_?X_31$0) (in$0 x sk_?X_29$0)))
            (and (not (in$0 x sk_?X_31$0)) (not (in$0 x sk_?X_29$0))
                 (not (in$0 x (union$0 sk_?X_31$0 sk_?X_29$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP$0 FP_Caller$0))
                 (or (in$0 x FP$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x FP$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 FP$0 FP_Caller$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller_2$0 FP_3$0))
                 (or (in$0 x FP_Caller_2$0) (in$0 x FP_3$0)))
            (and (not (in$0 x FP_Caller_2$0)) (not (in$0 x FP_3$0))
                 (not (in$0 x (union$0 FP_Caller_2$0 FP_3$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 X$0 sk_?X_29$0))
                 (or (in$0 x X$0) (in$0 x sk_?X_29$0)))
            (and (not (in$0 x X$0)) (not (in$0 x sk_?X_29$0))
                 (not (in$0 x (union$0 X$0 sk_?X_29$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_31$0) (in$0 x sk_?X_29$0)
                 (in$0 x (intersection$0 sk_?X_31$0 sk_?X_29$0)))
            (and (or (not (in$0 x sk_?X_31$0)) (not (in$0 x sk_?X_29$0)))
                 (not (in$0 x (intersection$0 sk_?X_31$0 sk_?X_29$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP$0)
                 (in$0 x (intersection$0 Alloc$0 FP$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_2$0)
                 (in$0 x (intersection$0 Alloc$0 FP_2$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_2$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_2$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x X$0) (in$0 x sk_?X_29$0)
                 (in$0 x (intersection$0 X$0 sk_?X_29$0)))
            (and (or (not (in$0 x X$0)) (not (in$0 x sk_?X_29$0)))
                 (not (in$0 x (intersection$0 X$0 sk_?X_29$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_38$0) (in$0 x sk_?X_40$0)
                 (in$0 x (intersection$0 sk_?X_38$0 sk_?X_40$0)))
            (and (or (not (in$0 x sk_?X_38$0)) (not (in$0 x sk_?X_40$0)))
                 (not (in$0 x (intersection$0 sk_?X_38$0 sk_?X_40$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_47$0) (in$0 x sk_?X_45$0)
                 (in$0 x (intersection$0 sk_?X_47$0 sk_?X_45$0)))
            (and (or (not (in$0 x sk_?X_47$0)) (not (in$0 x sk_?X_45$0)))
                 (not (in$0 x (intersection$0 sk_?X_47$0 sk_?X_45$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 FP_2$0))
                 (not (in$0 x FP_2$0)))
            (and (or (in$0 x FP_2$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 FP_2$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP$0) (in$0 x (setminus$0 FP$0 FP_2$0))
                 (not (in$0 x FP_2$0)))
            (and (or (in$0 x FP_2$0) (not (in$0 x FP$0)))
                 (not (in$0 x (setminus$0 FP$0 FP_2$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0) (in$0 x (setminus$0 FP_Caller$0 FP$0))
                 (not (in$0 x FP$0)))
            (and (or (in$0 x FP$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 FP$0)))))))

(assert (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (= (read$0 (write$0 next_2$0 x$0 res_4$0) x$0) res_4$0))

(assert (or (= null$0 x$0)
    (= (read$0 next_2$0 null$0)
      (read$0 (write$0 next_2$0 x$0 res_4$0) null$0))))

(assert (or (= root_x$0 x$0)
    (= (read$0 next_2$0 root_x$0)
      (read$0 (write$0 next_2$0 x$0 res_4$0) root_x$0))))

(assert (or (= sk_z$0 x$0)
    (= (read$0 next_2$0 sk_z$0)
      (read$0 (write$0 next_2$0 x$0 res_4$0) sk_z$0))))

(assert (or (= x$0 x$0)
    (= (read$0 next_2$0 x$0) (read$0 (write$0 next_2$0 x$0 res_4$0) x$0))))

(assert (= (read$0 next$0 null$0) null$0))

(assert (= (read$0 next_2$0 null$0) null$0))

(assert (= (read$0 next_3$0 null$0) null$0))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (Btwn$0 next$0 n_5$0 root_x$0 root_x$0)
    (not (lseg_set_struct$0 sk_?X_47$0 next$0 n_5$0 root_x$0 X_27$0))))

(assert (or
    (and
         (= FP_3$0
           (union$0 (setminus$0 FP$0 FP_2$0)
             (union$0 (intersection$0 Alloc$0 FP_2$0)
               (setminus$0 Alloc$0 Alloc$0))))
         (= next_3$0 (write$0 next_2$0 x$0 res_4$0))
         (Frame$0 FP_2$0 Alloc$0 next$0 next_2$0)
         (= Alloc$0 (union$0 FP_3$0 Alloc$0))
         (and (= (read$0 next$0 root_x$0) null$0) (= emptyset$0 emptyset$0)
              (= emptyset$0 (intersection$0 sk_?X_47$0 sk_?X_45$0))
              (= X_27$0 (lseg_set_X$0 next$0 n_5$0 root_x$0))
              (= sk_?X_44$0 (union$0 sk_?X_47$0 sk_?X_45$0))
              (= sk_?X_44$0 FP_2$0) (= sk_?X_45$0 sk_?X_46$0)
              (= sk_?X_46$0 (setenum$0 root_x$0))
              (= sk_?X_47$0 (lseg_set_domain$0 next$0 n_5$0 root_x$0))
              (= FP$0 (union$0 FP_2$0 FP$0))
              (lseg_set_struct$0 sk_?X_47$0 next$0 n_5$0 root_x$0 X_27$0))
         (and (= (read$0 next_2$0 root_x$0) null$0) (= emptyset$0 emptyset$0)
              (= emptyset$0 (intersection$0 sk_?X_38$0 sk_?X_40$0))
              (= res_4$0 root_x$0) (= sk_?X_38$0 X_27$0)
              (= sk_?X_39$0 (setenum$0 root_x$0)) (= sk_?X_40$0 sk_?X_39$0)
              (= sk_?X_41$0 (union$0 sk_?X_38$0 sk_?X_40$0))
              (= sk_?X_42$0 sk_?X_41$0)
              (= sk_?X_43$0
                (union$0 (intersection$0 Alloc$0 FP_2$0)
                  (setminus$0 Alloc$0 Alloc$0)))
              (= sk_?X_43$0 sk_?X_42$0) Axiom_3$0)
         (not (= n_5$0 null$0)) (not (in$0 null$0 Alloc$0)))
    (and (= FP_3$0 FP$0) (= n_5$0 null$0) (= next_3$0 next$0) (= res_3$0 x$0)
         (= res_4$0 res_3$0))))

(assert (= FP_Caller_final_3$0 (union$0 FP_Caller_2$0 FP_3$0)))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= emptyset$0 emptyset$0))

(assert (= X$0 (lseg_set_X$0 next$0 x$0 root_x$0)))

(assert (= sk_?X_28$0 FP$0))

(assert (= sk_?X_30$0 (setenum$0 root_x$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (= sk_?X_32$0 X$0))

(assert (= sk_?X_34$0 sk_?X_33$0))

(assert (= sk_?X_36$0 sk_?X_35$0))

(assert (or (in$0 sk_?e_2$0 (intersection$0 sk_?X_32$0 sk_?X_34$0))
    (and
         (in$0 sk_?e_2$0
           (union$0 (intersection$0 Alloc$0 FP$0)
             (setminus$0 Alloc$0 Alloc$0)))
         (not (in$0 sk_?e_2$0 sk_?X_37$0)))
    (and (in$0 sk_?e_2$0 sk_?X_37$0)
         (not
              (in$0 sk_?e_2$0
                (union$0 (intersection$0 Alloc$0 FP$0)
                  (setminus$0 Alloc$0 Alloc$0)))))
    (and (in$0 sk_z$0 X$0) (not (= (read$0 next_3$0 sk_z$0) root_x$0)))
    (not (= (read$0 next_3$0 root_x$0) null$0)) (not (= res_4$0 root_x$0))))

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

(assert (or (and Axiom_6$0 Axiom_5$0 Axiom_4$0)
    (not (Frame$0 FP_2$0 Alloc$0 next$0 next_2$0))))

(assert (or (Btwn$0 next$0 x$0 root_x$0 root_x$0)
    (not (lseg_set_struct$0 sk_?X_31$0 next$0 x$0 root_x$0 X$0))))

(assert (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= n_5$0 (read$0 next$0 x$0)))

(assert (= (read$0 next$0 root_x$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_31$0 sk_?X_29$0)))

(assert (= sk_?X_28$0 (union$0 sk_?X_31$0 sk_?X_29$0)))

(assert (= sk_?X_29$0 sk_?X_30$0))

(assert (= sk_?X_31$0 (lseg_set_domain$0 next$0 x$0 root_x$0)))

(assert (lseg_set_struct$0 sk_?X_31$0 next$0 x$0 root_x$0 X$0))

(assert (= sk_?X_33$0 (setenum$0 root_x$0)))

(assert (= sk_?X_35$0 (union$0 sk_?X_32$0 sk_?X_34$0)))

(assert (= sk_?X_37$0 sk_?X_36$0))

(assert (not (in$0 null$0 Alloc$0)))

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

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next_2$0 x$0 res_4$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next_2$0 ?z ?u ?v)
                               (or (Btwn$0 next_2$0 ?z ?v x$0)
                                   (and (Btwn$0 next_2$0 ?z ?v ?v)
                                        (not (Btwn$0 next_2$0 ?z x$0 x$0)))))
                          (and (not (= x$0 ?v))
                               (or (Btwn$0 next_2$0 ?z x$0 ?v)
                                   (and (Btwn$0 next_2$0 ?z x$0 x$0)
                                        (not (Btwn$0 next_2$0 ?z ?v ?v))))
                               (Btwn$0 next_2$0 ?z ?u x$0)
                               (or (Btwn$0 next_2$0 res_4$0 ?v x$0)
                                   (and (Btwn$0 next_2$0 res_4$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_2$0 res_4$0 x$0
                                               x$0)))))
                          (and (not (= x$0 ?v))
                               (or (Btwn$0 next_2$0 ?z x$0 ?v)
                                   (and (Btwn$0 next_2$0 ?z x$0 x$0)
                                        (not (Btwn$0 next_2$0 ?z ?v ?v))))
                               (Btwn$0 next_2$0 res_4$0 ?u ?v)
                               (or (Btwn$0 next_2$0 res_4$0 ?v x$0)
                                   (and (Btwn$0 next_2$0 res_4$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_2$0 res_4$0 x$0
                                               x$0))))))))
             (or
                 (and (Btwn$0 next_2$0 ?z ?u ?v)
                      (or (Btwn$0 next_2$0 ?z ?v x$0)
                          (and (Btwn$0 next_2$0 ?z ?v ?v)
                               (not (Btwn$0 next_2$0 ?z x$0 x$0)))))
                 (and (not (= x$0 ?v))
                      (or (Btwn$0 next_2$0 ?z x$0 ?v)
                          (and (Btwn$0 next_2$0 ?z x$0 x$0)
                               (not (Btwn$0 next_2$0 ?z ?v ?v))))
                      (Btwn$0 next_2$0 ?z ?u x$0)
                      (or (Btwn$0 next_2$0 res_4$0 ?v x$0)
                          (and (Btwn$0 next_2$0 res_4$0 ?v ?v)
                               (not (Btwn$0 next_2$0 res_4$0 x$0 x$0)))))
                 (and (not (= x$0 ?v))
                      (or (Btwn$0 next_2$0 ?z x$0 ?v)
                          (and (Btwn$0 next_2$0 ?z x$0 x$0)
                               (not (Btwn$0 next_2$0 ?z ?v ?v))))
                      (Btwn$0 next_2$0 res_4$0 ?u ?v)
                      (or (Btwn$0 next_2$0 res_4$0 ?v x$0)
                          (and (Btwn$0 next_2$0 res_4$0 ?v ?v)
                               (not (Btwn$0 next_2$0 res_4$0 x$0 x$0)))))
                 (not (Btwn$0 (write$0 next_2$0 x$0 res_4$0) ?z ?u ?v))))))

(assert (forall ((?x Loc)) (Btwn$0 next_3$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next_2$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_3$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_2$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_3$0 ?x ?y ?y)) (not (Btwn$0 next_3$0 ?x ?z ?z))
            (Btwn$0 next_3$0 ?x ?y ?z) (Btwn$0 next_3$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?y)) (not (Btwn$0 next_2$0 ?x ?z ?z))
            (Btwn$0 next_2$0 ?x ?y ?z) (Btwn$0 next_2$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_3$0 ?x ?y ?z))
            (and (Btwn$0 next_3$0 ?x ?y ?y) (Btwn$0 next_3$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z))
            (and (Btwn$0 next_2$0 ?x ?y ?y) (Btwn$0 next_2$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_3$0 ?x ?y ?y)) (not (Btwn$0 next_3$0 ?y ?z ?z))
            (Btwn$0 next_3$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?y)) (not (Btwn$0 next_2$0 ?y ?z ?z))
            (Btwn$0 next_2$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_3$0 ?x ?y ?z)) (not (Btwn$0 next_3$0 ?y ?u ?z))
            (and (Btwn$0 next_3$0 ?x ?y ?u) (Btwn$0 next_3$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z)) (not (Btwn$0 next_2$0 ?y ?u ?z))
            (and (Btwn$0 next_2$0 ?x ?y ?u) (Btwn$0 next_2$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_3$0 ?x ?y ?z)) (not (Btwn$0 next_3$0 ?x ?u ?y))
            (and (Btwn$0 next_3$0 ?x ?u ?z) (Btwn$0 next_3$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_2$0 ?x ?y ?z)) (not (Btwn$0 next_2$0 ?x ?u ?y))
            (and (Btwn$0 next_2$0 ?x ?u ?z) (Btwn$0 next_2$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))))

(check-sat)
(exit)
