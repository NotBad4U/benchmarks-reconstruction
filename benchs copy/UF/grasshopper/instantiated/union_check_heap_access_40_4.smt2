(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/union_find.spl:40:4-16:Possible heap access through null or dangling reference
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
(declare-fun Axiom_10$0 () Bool)
(declare-fun Axiom_11$0 () Bool)
(declare-fun Axiom_12$0 () Bool)
(declare-fun Axiom_13$0 () Bool)
(declare-fun Axiom_14$0 () Bool)
(declare-fun Axiom_15$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_4$0 () SetLoc)
(declare-fun FP_5$0 () SetLoc)
(declare-fun FP_6$0 () SetLoc)
(declare-fun FP_7$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_3$0 () SetLoc)
(declare-fun X_1$0 () SetLoc)
(declare-fun X_28$0 () SetLoc)
(declare-fun X_29$0 () SetLoc)
(declare-fun Y$0 () SetLoc)
(declare-fun lseg_set_X$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_struct$0 (SetLoc FldLoc Loc Loc SetLoc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_4$0 () FldLoc)
(declare-fun next_5$0 () FldLoc)
(declare-fun root_x_1$0 () Loc)
(declare-fun root_y$0 () Loc)
(declare-fun s_2$0 () Loc)
(declare-fun sk_?X_84$0 () SetLoc)
(declare-fun sk_?X_85$0 () SetLoc)
(declare-fun sk_?X_86$0 () SetLoc)
(declare-fun sk_?X_87$0 () SetLoc)
(declare-fun sk_?X_88$0 () SetLoc)
(declare-fun sk_?X_89$0 () SetLoc)
(declare-fun sk_?X_90$0 () SetLoc)
(declare-fun sk_?X_91$0 () SetLoc)
(declare-fun sk_?X_92$0 () SetLoc)
(declare-fun sk_?X_93$0 () SetLoc)
(declare-fun sk_?X_94$0 () SetLoc)
(declare-fun sk_?X_95$0 () SetLoc)
(declare-fun sk_?X_96$0 () SetLoc)
(declare-fun sk_?X_97$0 () SetLoc)
(declare-fun sk_?X_98$0 () SetLoc)
(declare-fun sk_?X_99$0 () SetLoc)
(declare-fun sk_?X_100$0 () SetLoc)
(declare-fun sk_?X_101$0 () SetLoc)
(declare-fun sk_?X_102$0 () SetLoc)
(declare-fun sk_?X_103$0 () SetLoc)
(declare-fun sk_?X_104$0 () SetLoc)
(declare-fun sk_?X_105$0 () SetLoc)
(declare-fun sk_?X_106$0 () SetLoc)
(declare-fun sk_?X_107$0 () SetLoc)
(declare-fun sk_?X_108$0 () SetLoc)
(declare-fun sk_?X_109$0 () SetLoc)
(declare-fun sk_?X_110$0 () SetLoc)
(declare-fun sk_?X_111$0 () SetLoc)
(declare-fun sk_?X_112$0 () SetLoc)
(declare-fun t_2$0 () Loc)
(declare-fun x_1$0 () Loc)
(declare-fun y$0 () Loc)

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 t_2$0 ?y ?y)) (= t_2$0 ?y)
            (Btwn$0 next$0 t_2$0 (read$0 next$0 t_2$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 s_2$0 ?y ?y)) (= s_2$0 ?y)
            (Btwn$0 next$0 s_2$0 (read$0 next$0 s_2$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_4$0 t_2$0 ?y ?y)) (= t_2$0 ?y)
            (Btwn$0 next_4$0 t_2$0 (read$0 next_4$0 t_2$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_4$0 s_2$0 ?y ?y)) (= s_2$0 ?y)
            (Btwn$0 next_4$0 s_2$0 (read$0 next_4$0 s_2$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_4$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_4$0 null$0 (read$0 next_4$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_5$0 s_2$0 ?y ?y)) (= s_2$0 ?y)
            (Btwn$0 next_5$0 s_2$0 (read$0 next_5$0 s_2$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_5$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_5$0 null$0 (read$0 next_5$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_5$0 t_2$0 ?y ?y)) (= t_2$0 ?y)
            (Btwn$0 next_5$0 t_2$0 (read$0 next_5$0 t_2$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 t_2$0) t_2$0))
            (not (Btwn$0 next$0 t_2$0 ?y ?y)) (= t_2$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 s_2$0) s_2$0))
            (not (Btwn$0 next$0 s_2$0 ?y ?y)) (= s_2$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_4$0 t_2$0) t_2$0))
            (not (Btwn$0 next_4$0 t_2$0 ?y ?y)) (= t_2$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_4$0 s_2$0) s_2$0))
            (not (Btwn$0 next_4$0 s_2$0 ?y ?y)) (= s_2$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_4$0 null$0) null$0))
            (not (Btwn$0 next_4$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_5$0 s_2$0) s_2$0))
            (not (Btwn$0 next_5$0 s_2$0 ?y ?y)) (= s_2$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_5$0 null$0) null$0))
            (not (Btwn$0 next_5$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_5$0 t_2$0) t_2$0))
            (not (Btwn$0 next_5$0 t_2$0 ?y ?y)) (= t_2$0 ?y))))

(assert (Btwn$0 next$0 t_2$0 (read$0 next$0 t_2$0) (read$0 next$0 t_2$0)))

(assert (Btwn$0 next$0 s_2$0 (read$0 next$0 s_2$0) (read$0 next$0 s_2$0)))

(assert (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)))

(assert (Btwn$0 next_4$0 t_2$0 (read$0 next_4$0 t_2$0) (read$0 next_4$0 t_2$0)))

(assert (Btwn$0 next_4$0 s_2$0 (read$0 next_4$0 s_2$0) (read$0 next_4$0 s_2$0)))

(assert (Btwn$0 next_4$0 null$0 (read$0 next_4$0 null$0) (read$0 next_4$0 null$0)))

(assert (Btwn$0 next_5$0 s_2$0 (read$0 next_5$0 s_2$0) (read$0 next_5$0 s_2$0)))

(assert (Btwn$0 next_5$0 null$0 (read$0 next_5$0 null$0) (read$0 next_5$0 null$0)))

(assert (Btwn$0 next_5$0 t_2$0 (read$0 next_5$0 t_2$0) (read$0 next_5$0 t_2$0)))

(assert (or (not Axiom_15$0)
    (or (= (read$0 next$0 t_2$0) (read$0 next_4$0 t_2$0))
        (not (in$0 t_2$0 (setminus$0 Alloc$0 FP_4$0))))))

(assert (or (not Axiom_15$0)
    (or (= (read$0 next$0 s_2$0) (read$0 next_4$0 s_2$0))
        (not (in$0 s_2$0 (setminus$0 Alloc$0 FP_4$0))))))

(assert (or (not Axiom_15$0)
    (or (= (read$0 next$0 null$0) (read$0 next_4$0 null$0))
        (not (in$0 null$0 (setminus$0 Alloc$0 FP_4$0))))))

(assert (or (not Axiom_14$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_4$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_4$0 null$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 null$0 ?y
                           (ep$0 next$0 FP_4$0 null$0))
                         (and (Btwn$0 next$0 null$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 null$0
                                     (ep$0 next$0 FP_4$0 null$0)
                                     (ep$0 next$0 FP_4$0 null$0))))))))))

(assert (or (not Axiom_14$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 t_2$0 ?z ?y)
                     (Btwn$0 next_4$0 t_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 t_2$0 ?z ?y))
                     (not (Btwn$0 next_4$0 t_2$0 ?z ?y)))
                (not
                     (or (Btwn$0 next$0 t_2$0 ?y (ep$0 next$0 FP_4$0 t_2$0))
                         (and (Btwn$0 next$0 t_2$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 t_2$0
                                     (ep$0 next$0 FP_4$0 t_2$0)
                                     (ep$0 next$0 FP_4$0 t_2$0))))))))))

(assert (or (not Axiom_14$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 x_1$0 ?z ?y)
                     (Btwn$0 next_4$0 x_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 x_1$0 ?z ?y))
                     (not (Btwn$0 next_4$0 x_1$0 ?z ?y)))
                (not
                     (or (Btwn$0 next$0 x_1$0 ?y (ep$0 next$0 FP_4$0 x_1$0))
                         (and (Btwn$0 next$0 x_1$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 x_1$0
                                     (ep$0 next$0 FP_4$0 x_1$0)
                                     (ep$0 next$0 FP_4$0 x_1$0))))))))))

(assert (or (not Axiom_14$0)
    (forall ((?y Loc) (?z Loc))
            (or (and (Btwn$0 next$0 y$0 ?z ?y) (Btwn$0 next_4$0 y$0 ?z ?y))
                (and (not (Btwn$0 next$0 y$0 ?z ?y))
                     (not (Btwn$0 next_4$0 y$0 ?z ?y)))
                (not
                     (or (Btwn$0 next$0 y$0 ?y (ep$0 next$0 FP_4$0 y$0))
                         (and (Btwn$0 next$0 y$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 y$0
                                     (ep$0 next$0 FP_4$0 y$0)
                                     (ep$0 next$0 FP_4$0 y$0))))))))))

(assert (or (not Axiom_13$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 null$0 FP_4$0)
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_4$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_4$0 null$0 ?z ?y)))
                (not (= null$0 (ep$0 next$0 FP_4$0 null$0)))))))

(assert (or (not Axiom_13$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 t_2$0 FP_4$0)
                (and (Btwn$0 next$0 t_2$0 ?z ?y)
                     (Btwn$0 next_4$0 t_2$0 ?z ?y))
                (and (not (Btwn$0 next$0 t_2$0 ?z ?y))
                     (not (Btwn$0 next_4$0 t_2$0 ?z ?y)))
                (not (= t_2$0 (ep$0 next$0 FP_4$0 t_2$0)))))))

(assert (or (not Axiom_13$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 x_1$0 FP_4$0)
                (and (Btwn$0 next$0 x_1$0 ?z ?y)
                     (Btwn$0 next_4$0 x_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 x_1$0 ?z ?y))
                     (not (Btwn$0 next_4$0 x_1$0 ?z ?y)))
                (not (= x_1$0 (ep$0 next$0 FP_4$0 x_1$0)))))))

(assert (or (not Axiom_13$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 y$0 FP_4$0)
                (and (Btwn$0 next$0 y$0 ?z ?y) (Btwn$0 next_4$0 y$0 ?z ?y))
                (and (not (Btwn$0 next$0 y$0 ?z ?y))
                     (not (Btwn$0 next_4$0 y$0 ?z ?y)))
                (not (= y$0 (ep$0 next$0 FP_4$0 y$0)))))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next_4$0 null$0 (ep$0 next_4$0 FP_6$0 null$0) ?y)
            (not (Btwn$0 next_4$0 null$0 ?y ?y)) (not (in$0 ?y FP_6$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next_4$0 t_2$0 (ep$0 next_4$0 FP_6$0 t_2$0) ?y)
            (not (Btwn$0 next_4$0 t_2$0 ?y ?y)) (not (in$0 ?y FP_6$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next_4$0 x_1$0 (ep$0 next_4$0 FP_6$0 x_1$0) ?y)
            (not (Btwn$0 next_4$0 x_1$0 ?y ?y)) (not (in$0 ?y FP_6$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next_4$0 y$0 (ep$0 next_4$0 FP_6$0 y$0) ?y)
            (not (Btwn$0 next_4$0 y$0 ?y ?y)) (not (in$0 ?y FP_6$0)))))

(assert (or (in$0 (ep$0 next$0 sk_?X_109$0 null$0) sk_?X_109$0)
    (= null$0 (ep$0 next$0 sk_?X_109$0 null$0))))

(assert (or (in$0 (ep$0 next$0 sk_?X_109$0 t_2$0) sk_?X_109$0)
    (= t_2$0 (ep$0 next$0 sk_?X_109$0 t_2$0))))

(assert (or (in$0 (ep$0 next$0 sk_?X_109$0 x_1$0) sk_?X_109$0)
    (= x_1$0 (ep$0 next$0 sk_?X_109$0 x_1$0))))

(assert (or (in$0 (ep$0 next$0 sk_?X_109$0 y$0) sk_?X_109$0)
    (= y$0 (ep$0 next$0 sk_?X_109$0 y$0))))

(assert (Btwn$0 next_4$0 null$0 (ep$0 next_4$0 FP_6$0 null$0)
  (ep$0 next_4$0 FP_6$0 null$0)))

(assert (Btwn$0 next_4$0 t_2$0 (ep$0 next_4$0 FP_6$0 t_2$0)
  (ep$0 next_4$0 FP_6$0 t_2$0)))

(assert (Btwn$0 next_4$0 x_1$0 (ep$0 next_4$0 FP_6$0 x_1$0)
  (ep$0 next_4$0 FP_6$0 x_1$0)))

(assert (Btwn$0 next_4$0 y$0 (ep$0 next_4$0 FP_6$0 y$0) (ep$0 next_4$0 FP_6$0 y$0)))

(assert (or (not Axiom_12$0)
    (or (= (read$0 next_4$0 s_2$0) (read$0 next_5$0 s_2$0))
        (not (in$0 s_2$0 (setminus$0 Alloc$0 FP_6$0))))))

(assert (or (not Axiom_12$0)
    (or (= (read$0 next_4$0 null$0) (read$0 next_5$0 null$0))
        (not (in$0 null$0 (setminus$0 Alloc$0 FP_6$0))))))

(assert (or (not Axiom_12$0)
    (or (= (read$0 next_4$0 t_2$0) (read$0 next_5$0 t_2$0))
        (not (in$0 t_2$0 (setminus$0 Alloc$0 FP_6$0))))))

(assert (or (not Axiom_11$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next_4$0 null$0 ?z ?y)
                     (Btwn$0 next_5$0 null$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 null$0 ?z ?y))
                     (not (Btwn$0 next_5$0 null$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next_4$0 null$0 ?y
                           (ep$0 next_4$0 FP_6$0 null$0))
                         (and (Btwn$0 next_4$0 null$0 ?y ?y)
                              (not
                                   (Btwn$0 next_4$0 null$0
                                     (ep$0 next_4$0 FP_6$0 null$0)
                                     (ep$0 next_4$0 FP_6$0 null$0))))))))))

(assert (or (not Axiom_11$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next_4$0 t_2$0 ?z ?y)
                     (Btwn$0 next_5$0 t_2$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 t_2$0 ?z ?y))
                     (not (Btwn$0 next_5$0 t_2$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next_4$0 t_2$0 ?y
                           (ep$0 next_4$0 FP_6$0 t_2$0))
                         (and (Btwn$0 next_4$0 t_2$0 ?y ?y)
                              (not
                                   (Btwn$0 next_4$0 t_2$0
                                     (ep$0 next_4$0 FP_6$0 t_2$0)
                                     (ep$0 next_4$0 FP_6$0 t_2$0))))))))))

(assert (or (not Axiom_11$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next_4$0 x_1$0 ?z ?y)
                     (Btwn$0 next_5$0 x_1$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 x_1$0 ?z ?y))
                     (not (Btwn$0 next_5$0 x_1$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next_4$0 x_1$0 ?y
                           (ep$0 next_4$0 FP_6$0 x_1$0))
                         (and (Btwn$0 next_4$0 x_1$0 ?y ?y)
                              (not
                                   (Btwn$0 next_4$0 x_1$0
                                     (ep$0 next_4$0 FP_6$0 x_1$0)
                                     (ep$0 next_4$0 FP_6$0 x_1$0))))))))))

(assert (or (not Axiom_11$0)
    (forall ((?y Loc) (?z Loc))
            (or (and (Btwn$0 next_4$0 y$0 ?z ?y) (Btwn$0 next_5$0 y$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 y$0 ?z ?y))
                     (not (Btwn$0 next_5$0 y$0 ?z ?y)))
                (not
                     (or (Btwn$0 next_4$0 y$0 ?y (ep$0 next_4$0 FP_6$0 y$0))
                         (and (Btwn$0 next_4$0 y$0 ?y ?y)
                              (not
                                   (Btwn$0 next_4$0 y$0
                                     (ep$0 next_4$0 FP_6$0 y$0)
                                     (ep$0 next_4$0 FP_6$0 y$0))))))))))

(assert (or (not Axiom_10$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 null$0 FP_6$0)
                (and (Btwn$0 next_4$0 null$0 ?z ?y)
                     (Btwn$0 next_5$0 null$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 null$0 ?z ?y))
                     (not (Btwn$0 next_5$0 null$0 ?z ?y)))
                (not (= null$0 (ep$0 next_4$0 FP_6$0 null$0)))))))

(assert (or (not Axiom_10$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 t_2$0 FP_6$0)
                (and (Btwn$0 next_4$0 t_2$0 ?z ?y)
                     (Btwn$0 next_5$0 t_2$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 t_2$0 ?z ?y))
                     (not (Btwn$0 next_5$0 t_2$0 ?z ?y)))
                (not (= t_2$0 (ep$0 next_4$0 FP_6$0 t_2$0)))))))

(assert (or (not Axiom_10$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 x_1$0 FP_6$0)
                (and (Btwn$0 next_4$0 x_1$0 ?z ?y)
                     (Btwn$0 next_5$0 x_1$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 x_1$0 ?z ?y))
                     (not (Btwn$0 next_5$0 x_1$0 ?z ?y)))
                (not (= x_1$0 (ep$0 next_4$0 FP_6$0 x_1$0)))))))

(assert (or (not Axiom_10$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 y$0 FP_6$0)
                (and (Btwn$0 next_4$0 y$0 ?z ?y) (Btwn$0 next_5$0 y$0 ?z ?y))
                (and (not (Btwn$0 next_4$0 y$0 ?z ?y))
                     (not (Btwn$0 next_5$0 y$0 ?z ?y)))
                (not (= y$0 (ep$0 next_4$0 FP_6$0 y$0)))))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_109$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y sk_?X_109$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 t_2$0 (ep$0 next$0 sk_?X_109$0 t_2$0) ?y)
            (not (Btwn$0 next$0 t_2$0 ?y ?y)) (not (in$0 ?y sk_?X_109$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 x_1$0 (ep$0 next$0 sk_?X_109$0 x_1$0) ?y)
            (not (Btwn$0 next$0 x_1$0 ?y ?y)) (not (in$0 ?y sk_?X_109$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 y$0 (ep$0 next$0 sk_?X_109$0 y$0) ?y)
            (not (Btwn$0 next$0 y$0 ?y ?y)) (not (in$0 ?y sk_?X_109$0)))))

(assert (or (in$0 (ep$0 next_4$0 FP_6$0 null$0) FP_6$0)
    (= null$0 (ep$0 next_4$0 FP_6$0 null$0))))

(assert (or (in$0 (ep$0 next_4$0 FP_6$0 t_2$0) FP_6$0)
    (= t_2$0 (ep$0 next_4$0 FP_6$0 t_2$0))))

(assert (or (in$0 (ep$0 next_4$0 FP_6$0 x_1$0) FP_6$0)
    (= x_1$0 (ep$0 next_4$0 FP_6$0 x_1$0))))

(assert (or (in$0 (ep$0 next_4$0 FP_6$0 y$0) FP_6$0)
    (= y$0 (ep$0 next_4$0 FP_6$0 y$0))))

(assert (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_109$0 null$0)
  (ep$0 next$0 sk_?X_109$0 null$0)))

(assert (Btwn$0 next$0 t_2$0 (ep$0 next$0 sk_?X_109$0 t_2$0)
  (ep$0 next$0 sk_?X_109$0 t_2$0)))

(assert (Btwn$0 next$0 x_1$0 (ep$0 next$0 sk_?X_109$0 x_1$0)
  (ep$0 next$0 sk_?X_109$0 x_1$0)))

(assert (Btwn$0 next$0 y$0 (ep$0 next$0 sk_?X_109$0 y$0)
  (ep$0 next$0 sk_?X_109$0 y$0)))

(assert (or (= (read$0 next_5$0 s_2$0) root_y$0) (not (in$0 s_2$0 X_29$0))))

(assert (or (= (read$0 next_5$0 null$0) root_y$0) (not (in$0 null$0 X_29$0))))

(assert (or (= (read$0 next_5$0 t_2$0) root_y$0) (not (in$0 t_2$0 X_29$0))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_7$0 Alloc$0))
                 (or (in$0 x FP_7$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_7$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_7$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_5$0 Alloc$0))
                 (or (in$0 x FP_5$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_5$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_5$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_6$0 FP_5$0))
                 (or (in$0 x FP_6$0) (in$0 x FP_5$0)))
            (and (not (in$0 x FP_6$0)) (not (in$0 x FP_5$0))
                 (not (in$0 x (union$0 FP_6$0 FP_5$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_4$0) sk_?X_104$0))
                 (or (in$0 x (setminus$0 FP$0 FP_4$0)) (in$0 x sk_?X_104$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_4$0)))
                 (not (in$0 x sk_?X_104$0))
                 (not
                      (in$0 x (union$0 (setminus$0 FP$0 FP_4$0) sk_?X_104$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_108$0 sk_?X_106$0))
                 (or (in$0 x sk_?X_108$0) (in$0 x sk_?X_106$0)))
            (and (not (in$0 x sk_?X_108$0)) (not (in$0 x sk_?X_106$0))
                 (not (in$0 x (union$0 sk_?X_108$0 sk_?X_106$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP_5$0 FP_6$0) sk_?X_97$0))
                 (or (in$0 x (setminus$0 FP_5$0 FP_6$0)) (in$0 x sk_?X_97$0)))
            (and (not (in$0 x (setminus$0 FP_5$0 FP_6$0)))
                 (not (in$0 x sk_?X_97$0))
                 (not
                      (in$0 x
                        (union$0 (setminus$0 FP_5$0 FP_6$0) sk_?X_97$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_84$0 FP_Caller$0))
                 (or (in$0 x sk_?X_84$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x sk_?X_84$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 sk_?X_84$0 FP_Caller$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_109$0 sk_?X_84$0))
                 (or (in$0 x sk_?X_109$0) (in$0 x sk_?X_84$0)))
            (and (not (in$0 x sk_?X_109$0)) (not (in$0 x sk_?X_84$0))
                 (not (in$0 x (union$0 sk_?X_109$0 sk_?X_84$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_90$0 sk_?X_85$0))
                 (or (in$0 x sk_?X_90$0) (in$0 x sk_?X_85$0)))
            (and (not (in$0 x sk_?X_90$0)) (not (in$0 x sk_?X_85$0))
                 (not (in$0 x (union$0 sk_?X_90$0 sk_?X_85$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_89$0 sk_?X_106$0))
                 (or (in$0 x sk_?X_89$0) (in$0 x sk_?X_106$0)))
            (and (not (in$0 x sk_?X_89$0)) (not (in$0 x sk_?X_106$0))
                 (not (in$0 x (union$0 sk_?X_89$0 sk_?X_106$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_92$0 sk_?X_91$0))
                 (or (in$0 x sk_?X_92$0) (in$0 x sk_?X_91$0)))
            (and (not (in$0 x sk_?X_92$0)) (not (in$0 x sk_?X_91$0))
                 (not (in$0 x (union$0 sk_?X_92$0 sk_?X_91$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_93$0 sk_?X_106$0))
                 (or (in$0 x sk_?X_93$0) (in$0 x sk_?X_106$0)))
            (and (not (in$0 x sk_?X_93$0)) (not (in$0 x sk_?X_106$0))
                 (not (in$0 x (union$0 sk_?X_93$0 sk_?X_106$0)))))))

(assert (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_6$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_6$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_6$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_6$0)
                          (setminus$0 Alloc$0 Alloc$0))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_99$0 sk_?X_89$0))
                 (or (in$0 x sk_?X_99$0) (in$0 x sk_?X_89$0)))
            (and (not (in$0 x sk_?X_99$0)) (not (in$0 x sk_?X_89$0))
                 (not (in$0 x (union$0 sk_?X_99$0 sk_?X_89$0)))))))

(assert (forall ((x Loc))
        (or
            (and
                 (in$0 x
                   (union$0 (intersection$0 Alloc$0 FP_4$0)
                     (setminus$0 Alloc$0 Alloc$0)))
                 (or (in$0 x (intersection$0 Alloc$0 FP_4$0))
                     (in$0 x (setminus$0 Alloc$0 Alloc$0))))
            (and (not (in$0 x (intersection$0 Alloc$0 FP_4$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))
                 (not
                      (in$0 x
                        (union$0 (intersection$0 Alloc$0 FP_4$0)
                          (setminus$0 Alloc$0 Alloc$0))))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_92$0 sk_?X_89$0))
                 (or (in$0 x sk_?X_92$0) (in$0 x sk_?X_89$0)))
            (and (not (in$0 x sk_?X_92$0)) (not (in$0 x sk_?X_89$0))
                 (not (in$0 x (union$0 sk_?X_92$0 sk_?X_89$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_108$0) (in$0 x sk_?X_106$0)
                 (in$0 x (intersection$0 sk_?X_108$0 sk_?X_106$0)))
            (and (or (not (in$0 x sk_?X_108$0)) (not (in$0 x sk_?X_106$0)))
                 (not (in$0 x (intersection$0 sk_?X_108$0 sk_?X_106$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_99$0) (in$0 x sk_?X_89$0)
                 (in$0 x (intersection$0 sk_?X_99$0 sk_?X_89$0)))
            (and (or (not (in$0 x sk_?X_99$0)) (not (in$0 x sk_?X_89$0)))
                 (not (in$0 x (intersection$0 sk_?X_99$0 sk_?X_89$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_93$0) (in$0 x sk_?X_106$0)
                 (in$0 x (intersection$0 sk_?X_93$0 sk_?X_106$0)))
            (and (or (not (in$0 x sk_?X_93$0)) (not (in$0 x sk_?X_106$0)))
                 (not (in$0 x (intersection$0 sk_?X_93$0 sk_?X_106$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_92$0) (in$0 x sk_?X_89$0)
                 (in$0 x (intersection$0 sk_?X_92$0 sk_?X_89$0)))
            (and (or (not (in$0 x sk_?X_92$0)) (not (in$0 x sk_?X_89$0)))
                 (not (in$0 x (intersection$0 sk_?X_92$0 sk_?X_89$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_90$0) (in$0 x sk_?X_85$0)
                 (in$0 x (intersection$0 sk_?X_90$0 sk_?X_85$0)))
            (and (or (not (in$0 x sk_?X_90$0)) (not (in$0 x sk_?X_85$0)))
                 (not (in$0 x (intersection$0 sk_?X_90$0 sk_?X_85$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_109$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_109$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_109$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_109$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x FP_6$0)
                 (in$0 x (intersection$0 Alloc$0 FP_6$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x FP_6$0)))
                 (not (in$0 x (intersection$0 Alloc$0 FP_6$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 sk_?X_109$0))
                 (not (in$0 x sk_?X_109$0)))
            (and (or (in$0 x sk_?X_109$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 sk_?X_109$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 FP_6$0))
                 (not (in$0 x FP_6$0)))
            (and (or (in$0 x FP_6$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 FP_6$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_84$0)
                 (in$0 x (setminus$0 sk_?X_84$0 sk_?X_109$0))
                 (not (in$0 x sk_?X_109$0)))
            (and (or (in$0 x sk_?X_109$0) (not (in$0 x sk_?X_84$0)))
                 (not (in$0 x (setminus$0 sk_?X_84$0 sk_?X_109$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP_5$0) (in$0 x (setminus$0 FP_5$0 FP_6$0))
                 (not (in$0 x FP_6$0)))
            (and (or (in$0 x FP_6$0) (not (in$0 x FP_5$0)))
                 (not (in$0 x (setminus$0 FP_5$0 FP_6$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0)
                 (in$0 x (setminus$0 FP_Caller$0 sk_?X_84$0))
                 (not (in$0 x sk_?X_84$0)))
            (and (or (in$0 x sk_?X_84$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 sk_?X_84$0)))))))

(assert (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (= (read$0 next$0 null$0) null$0))

(assert (= (read$0 next_4$0 null$0) null$0))

(assert (= (read$0 next_5$0 null$0) null$0))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0)
    (not (lseg_set_struct$0 sk_?X_92$0 next$0 x_1$0 root_x_1$0 X_1$0))))

(assert (or (Btwn$0 next$0 y$0 root_y$0 root_y$0)
    (not (lseg_set_struct$0 sk_?X_91$0 next$0 y$0 root_y$0 Y$0))))

(assert (= FP_5$0
  (union$0 (setminus$0 FP$0 FP_4$0)
    (union$0 (intersection$0 Alloc$0 FP_4$0) (setminus$0 Alloc$0 Alloc$0)))))

(assert (= FP_Caller_3$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (Frame$0 FP_6$0 Alloc$0 next_4$0 next_5$0))

(assert (= Alloc$0 (union$0 FP_7$0 Alloc$0)))

(assert (= (read$0 next$0 root_x_1$0) null$0))

(assert (= emptyset$0 emptyset$0))

(assert (= X_1$0 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)))

(assert (= sk_?X_84$0 (union$0 sk_?X_90$0 sk_?X_85$0)))

(assert (= sk_?X_85$0 (union$0 sk_?X_88$0 sk_?X_86$0)))

(assert (= sk_?X_87$0 (setenum$0 root_y$0)))

(assert (= sk_?X_89$0 (setenum$0 root_x_1$0)))

(assert (= sk_?X_91$0 (lseg_set_domain$0 next$0 y$0 root_y$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (lseg_set_struct$0 sk_?X_92$0 next$0 x_1$0 root_x_1$0 X_1$0))

(assert (= emptyset$0 emptyset$0))

(assert (= X_28$0 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)))

(assert (= sk_?X_109$0 FP_4$0))

(assert (= sk_?X_111$0 (setenum$0 root_x_1$0)))

(assert (= FP$0 (union$0 FP_4$0 FP$0)))

(assert (= (read$0 next_4$0 root_x_1$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_99$0 sk_?X_101$0)))

(assert (= sk_?X_100$0 (setenum$0 root_x_1$0)))

(assert (= sk_?X_102$0 (union$0 sk_?X_99$0 sk_?X_101$0)))

(assert (= sk_?X_104$0
  (union$0 (intersection$0 Alloc$0 FP_4$0) (setminus$0 Alloc$0 Alloc$0))))

(assert (= t_2$0 root_x_1$0))

(assert (= (read$0 next_4$0 root_y$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_108$0 sk_?X_106$0)))

(assert (= sk_?X_105$0 (union$0 sk_?X_108$0 sk_?X_106$0)))

(assert (= sk_?X_106$0 sk_?X_107$0))

(assert (= sk_?X_108$0 (lseg_set_domain$0 next_4$0 y$0 root_y$0)))

(assert (lseg_set_struct$0 sk_?X_108$0 next_4$0 y$0 root_y$0 X_29$0))

(assert (= emptyset$0 emptyset$0))

(assert (= s_2$0 root_y$0))

(assert (= sk_?X_94$0 (setenum$0 root_y$0)))

(assert (= sk_?X_96$0 (union$0 sk_?X_93$0 sk_?X_95$0)))

(assert (= sk_?X_98$0
  (union$0 (intersection$0 Alloc$0 FP_6$0) (setminus$0 Alloc$0 Alloc$0))))

(assert (not (in$0 null$0 Alloc$0)))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 x_1$0 l1 root_x_1$0)
                 (in$0 l1 (lseg_set_X$0 next$0 x_1$0 root_x_1$0))
                 (not (= l1 root_x_1$0)))
            (and
                 (or (= l1 root_x_1$0)
                     (not (Btwn$0 next$0 x_1$0 l1 root_x_1$0)))
                 (not (in$0 l1 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 y$0 l1 root_y$0)
                 (in$0 l1 (lseg_set_X$0 next$0 y$0 root_y$0))
                 (not (= l1 root_y$0)))
            (and (or (= l1 root_y$0) (not (Btwn$0 next$0 y$0 l1 root_y$0)))
                 (not (in$0 l1 (lseg_set_X$0 next$0 y$0 root_y$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_4$0 y$0 l1 root_y$0)
                 (in$0 l1 (lseg_set_X$0 next_4$0 y$0 root_y$0))
                 (not (= l1 root_y$0)))
            (and (or (= l1 root_y$0) (not (Btwn$0 next_4$0 y$0 l1 root_y$0)))
                 (not (in$0 l1 (lseg_set_X$0 next_4$0 y$0 root_y$0)))))))

(assert (or (and Axiom_15$0 Axiom_14$0 Axiom_13$0)
    (not (Frame$0 FP_4$0 Alloc$0 next$0 next_4$0))))

(assert (or (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0)
    (not (lseg_set_struct$0 sk_?X_112$0 next$0 x_1$0 root_x_1$0 X_28$0))))

(assert (or (Btwn$0 next_4$0 y$0 root_y$0 root_y$0)
    (not (lseg_set_struct$0 sk_?X_108$0 next_4$0 y$0 root_y$0 X_29$0))))

(assert (= FP_7$0
  (union$0 (setminus$0 FP_5$0 FP_6$0)
    (union$0 (intersection$0 Alloc$0 FP_6$0) (setminus$0 Alloc$0 Alloc$0)))))

(assert (Frame$0 FP_4$0 Alloc$0 next$0 next_4$0))

(assert (= Alloc$0 (union$0 FP_5$0 Alloc$0)))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= (read$0 next$0 root_y$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_90$0 sk_?X_85$0)))

(assert (= Y$0 (lseg_set_X$0 next$0 y$0 root_y$0)))

(assert (= sk_?X_84$0 FP$0))

(assert (= sk_?X_86$0 sk_?X_87$0))

(assert (= sk_?X_88$0 sk_?X_89$0))

(assert (= sk_?X_90$0 (union$0 sk_?X_92$0 sk_?X_91$0)))

(assert (= sk_?X_92$0 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)))

(assert (lseg_set_struct$0 sk_?X_91$0 next$0 y$0 root_y$0 Y$0))

(assert (= (read$0 next$0 root_x_1$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_112$0 sk_?X_110$0)))

(assert (= sk_?X_109$0 (union$0 sk_?X_112$0 sk_?X_110$0)))

(assert (= sk_?X_110$0 sk_?X_111$0))

(assert (= sk_?X_112$0 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)))

(assert (lseg_set_struct$0 sk_?X_112$0 next$0 x_1$0 root_x_1$0 X_28$0))

(assert (= emptyset$0 emptyset$0))

(assert (= sk_?X_99$0 X_28$0))

(assert (= sk_?X_101$0 sk_?X_100$0))

(assert (= sk_?X_103$0 sk_?X_102$0))

(assert (= sk_?X_104$0 sk_?X_103$0))

(assert (forall ((z Loc))
        (or
            (and (Btwn$0 next_4$0 z root_x_1$0 root_x_1$0)
                 (forall ((?x Loc))
                         (or (= ?x z) (= ?x root_x_1$0)
                             (not (Btwn$0 next_4$0 z ?x root_x_1$0)))))
            (not (in$0 z X_28$0)))))

(assert (= emptyset$0 emptyset$0))

(assert (= X_29$0 (lseg_set_X$0 next_4$0 y$0 root_y$0)))

(assert (= sk_?X_105$0 FP_6$0))

(assert (= sk_?X_107$0 (setenum$0 root_y$0)))

(assert (= FP_5$0 (union$0 FP_6$0 FP_5$0)))

(assert (= (read$0 next_5$0 root_y$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_93$0 sk_?X_95$0)))

(assert (= sk_?X_93$0 X_29$0))

(assert (= sk_?X_95$0 sk_?X_94$0))

(assert (= sk_?X_97$0 sk_?X_96$0))

(assert (= sk_?X_98$0 sk_?X_97$0))

(assert (not (= t_2$0 s_2$0)))

(assert (not (in$0 null$0 Alloc$0)))

(assert (not (in$0 t_2$0 FP_7$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 x_1$0 l1 root_x_1$0)
                 (in$0 l1 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0))
                 (not (= l1 root_x_1$0)))
            (and
                 (or (= l1 root_x_1$0)
                     (not (Btwn$0 next$0 x_1$0 l1 root_x_1$0)))
                 (not (in$0 l1 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 y$0 l1 root_y$0)
                 (in$0 l1 (lseg_set_domain$0 next$0 y$0 root_y$0))
                 (not (= l1 root_y$0)))
            (and (or (= l1 root_y$0) (not (Btwn$0 next$0 y$0 l1 root_y$0)))
                 (not (in$0 l1 (lseg_set_domain$0 next$0 y$0 root_y$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_4$0 y$0 l1 root_y$0)
                 (in$0 l1 (lseg_set_domain$0 next_4$0 y$0 root_y$0))
                 (not (= l1 root_y$0)))
            (and (or (= l1 root_y$0) (not (Btwn$0 next_4$0 y$0 l1 root_y$0)))
                 (not (in$0 l1 (lseg_set_domain$0 next_4$0 y$0 root_y$0)))))))

(assert (or (and Axiom_12$0 Axiom_11$0 Axiom_10$0)
    (not (Frame$0 FP_6$0 Alloc$0 next_4$0 next_5$0))))

(assert (forall ((?x Loc)) (Btwn$0 next_5$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next_4$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_5$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_4$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?y)) (not (Btwn$0 next_5$0 ?x ?z ?z))
            (Btwn$0 next_5$0 ?x ?y ?z) (Btwn$0 next_5$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?y)) (not (Btwn$0 next_4$0 ?x ?z ?z))
            (Btwn$0 next_4$0 ?x ?y ?z) (Btwn$0 next_4$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?z))
            (and (Btwn$0 next_5$0 ?x ?y ?y) (Btwn$0 next_5$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?z))
            (and (Btwn$0 next_4$0 ?x ?y ?y) (Btwn$0 next_4$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?y)) (not (Btwn$0 next_5$0 ?y ?z ?z))
            (Btwn$0 next_5$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?y)) (not (Btwn$0 next_4$0 ?y ?z ?z))
            (Btwn$0 next_4$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?z)) (not (Btwn$0 next_5$0 ?y ?u ?z))
            (and (Btwn$0 next_5$0 ?x ?y ?u) (Btwn$0 next_5$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?z)) (not (Btwn$0 next_4$0 ?y ?u ?z))
            (and (Btwn$0 next_4$0 ?x ?y ?u) (Btwn$0 next_4$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_5$0 ?x ?y ?z)) (not (Btwn$0 next_5$0 ?x ?u ?y))
            (and (Btwn$0 next_5$0 ?x ?u ?z) (Btwn$0 next_5$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?z)) (not (Btwn$0 next_4$0 ?x ?u ?y))
            (and (Btwn$0 next_4$0 ?x ?u ?z) (Btwn$0 next_4$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))))

(check-sat)
(exit)
