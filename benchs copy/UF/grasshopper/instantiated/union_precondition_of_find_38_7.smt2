(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/union_find.spl:38:7-22:A precondition for this call of find might not hold
  tests/spl/union_find.spl:12:11-58:Related location: This is the precondition that might not hold
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
(declare-fun Axiom_7$0 () Bool)
(declare-fun Axiom_8$0 () Bool)
(declare-fun Axiom_9$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_4$0 () SetLoc)
(declare-fun FP_5$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_3$0 () SetLoc)
(declare-fun X_1$0 () SetLoc)
(declare-fun X_28$0 () SetLoc)
(declare-fun Y$0 () SetLoc)
(declare-fun lseg_set_X$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_struct$0 (SetLoc FldLoc Loc Loc SetLoc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_4$0 () FldLoc)
(declare-fun root_x_1$0 () Loc)
(declare-fun root_y$0 () Loc)
(declare-fun sk_?X_61$0 () SetLoc)
(declare-fun sk_?X_62$0 () SetLoc)
(declare-fun sk_?X_63$0 () SetLoc)
(declare-fun sk_?X_64$0 () SetLoc)
(declare-fun sk_?X_65$0 () SetLoc)
(declare-fun sk_?X_66$0 () SetLoc)
(declare-fun sk_?X_67$0 () SetLoc)
(declare-fun sk_?X_68$0 () SetLoc)
(declare-fun sk_?X_69$0 () SetLoc)
(declare-fun sk_?X_70$0 () SetLoc)
(declare-fun sk_?X_71$0 () SetLoc)
(declare-fun sk_?X_72$0 () SetLoc)
(declare-fun sk_?X_73$0 () SetLoc)
(declare-fun sk_?X_74$0 () SetLoc)
(declare-fun sk_?X_75$0 () SetLoc)
(declare-fun sk_?X_76$0 () SetLoc)
(declare-fun sk_?X_77$0 () SetLoc)
(declare-fun sk_?X_78$0 () SetLoc)
(declare-fun sk_?X_79$0 () SetLoc)
(declare-fun sk_?X_80$0 () SetLoc)
(declare-fun sk_?X_81$0 () SetLoc)
(declare-fun sk_?X_82$0 () SetLoc)
(declare-fun sk_?X_83$0 () SetLoc)
(declare-fun sk_?e_4$0 () Loc)
(declare-fun sk_FP_2$0 () SetLoc)
(declare-fun sk_X_2$0 () SetLoc)
(declare-fun t_2$0 () Loc)
(declare-fun x_1$0 () Loc)
(declare-fun y$0 () Loc)

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 t_2$0 ?y ?y)) (= t_2$0 ?y)
            (Btwn$0 next$0 t_2$0 (read$0 next$0 t_2$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 root_y$0 ?y ?y)) (= root_y$0 ?y)
            (Btwn$0 next$0 root_y$0 (read$0 next$0 root_y$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next$0 null$0 (read$0 next$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_4$0 t_2$0 ?y ?y)) (= t_2$0 ?y)
            (Btwn$0 next_4$0 t_2$0 (read$0 next_4$0 t_2$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_4$0 null$0 ?y ?y)) (= null$0 ?y)
            (Btwn$0 next_4$0 null$0 (read$0 next_4$0 null$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (Btwn$0 next_4$0 root_y$0 ?y ?y)) (= root_y$0 ?y)
            (Btwn$0 next_4$0 root_y$0 (read$0 next_4$0 root_y$0) ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 t_2$0) t_2$0))
            (not (Btwn$0 next$0 t_2$0 ?y ?y)) (= t_2$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 root_y$0) root_y$0))
            (not (Btwn$0 next$0 root_y$0 ?y ?y)) (= root_y$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next$0 null$0) null$0))
            (not (Btwn$0 next$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_4$0 t_2$0) t_2$0))
            (not (Btwn$0 next_4$0 t_2$0 ?y ?y)) (= t_2$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_4$0 null$0) null$0))
            (not (Btwn$0 next_4$0 null$0 ?y ?y)) (= null$0 ?y))))

(assert (forall ((?y Loc))
        (or (not (= (read$0 next_4$0 root_y$0) root_y$0))
            (not (Btwn$0 next_4$0 root_y$0 ?y ?y)) (= root_y$0 ?y))))

(assert (Btwn$0 next$0 t_2$0 (read$0 next$0 t_2$0) (read$0 next$0 t_2$0)))

(assert (Btwn$0 next$0 root_y$0 (read$0 next$0 root_y$0) (read$0 next$0 root_y$0)))

(assert (Btwn$0 next$0 null$0 (read$0 next$0 null$0) (read$0 next$0 null$0)))

(assert (Btwn$0 next_4$0 t_2$0 (read$0 next_4$0 t_2$0) (read$0 next_4$0 t_2$0)))

(assert (Btwn$0 next_4$0 null$0 (read$0 next_4$0 null$0) (read$0 next_4$0 null$0)))

(assert (Btwn$0 next_4$0 root_y$0 (read$0 next_4$0 root_y$0)
  (read$0 next_4$0 root_y$0)))

(assert (or (not Axiom_9$0)
    (or (= (read$0 next$0 t_2$0) (read$0 next_4$0 t_2$0))
        (not (in$0 t_2$0 (setminus$0 Alloc$0 FP_4$0))))))

(assert (or (not Axiom_9$0)
    (or (= (read$0 next$0 null$0) (read$0 next_4$0 null$0))
        (not (in$0 null$0 (setminus$0 Alloc$0 FP_4$0))))))

(assert (or (not Axiom_9$0)
    (or (= (read$0 next$0 root_y$0) (read$0 next_4$0 root_y$0))
        (not (in$0 root_y$0 (setminus$0 Alloc$0 FP_4$0))))))

(assert (or (not Axiom_8$0)
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

(assert (or (not Axiom_8$0)
    (forall ((?y Loc) (?z Loc))
            (or
                (and (Btwn$0 next$0 sk_?e_4$0 ?z ?y)
                     (Btwn$0 next_4$0 sk_?e_4$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_?e_4$0 ?z ?y))
                     (not (Btwn$0 next_4$0 sk_?e_4$0 ?z ?y)))
                (not
                     (or
                         (Btwn$0 next$0 sk_?e_4$0 ?y
                           (ep$0 next$0 FP_4$0 sk_?e_4$0))
                         (and (Btwn$0 next$0 sk_?e_4$0 ?y ?y)
                              (not
                                   (Btwn$0 next$0 sk_?e_4$0
                                     (ep$0 next$0 FP_4$0 sk_?e_4$0)
                                     (ep$0 next$0 FP_4$0 sk_?e_4$0))))))))))

(assert (or (not Axiom_8$0)
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

(assert (or (not Axiom_8$0)
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

(assert (or (not Axiom_7$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 null$0 FP_4$0)
                (and (Btwn$0 next$0 null$0 ?z ?y)
                     (Btwn$0 next_4$0 null$0 ?z ?y))
                (and (not (Btwn$0 next$0 null$0 ?z ?y))
                     (not (Btwn$0 next_4$0 null$0 ?z ?y)))
                (not (= null$0 (ep$0 next$0 FP_4$0 null$0)))))))

(assert (or (not Axiom_7$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 sk_?e_4$0 FP_4$0)
                (and (Btwn$0 next$0 sk_?e_4$0 ?z ?y)
                     (Btwn$0 next_4$0 sk_?e_4$0 ?z ?y))
                (and (not (Btwn$0 next$0 sk_?e_4$0 ?z ?y))
                     (not (Btwn$0 next_4$0 sk_?e_4$0 ?z ?y)))
                (not (= sk_?e_4$0 (ep$0 next$0 FP_4$0 sk_?e_4$0)))))))

(assert (or (not Axiom_7$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 x_1$0 FP_4$0)
                (and (Btwn$0 next$0 x_1$0 ?z ?y)
                     (Btwn$0 next_4$0 x_1$0 ?z ?y))
                (and (not (Btwn$0 next$0 x_1$0 ?z ?y))
                     (not (Btwn$0 next_4$0 x_1$0 ?z ?y)))
                (not (= x_1$0 (ep$0 next$0 FP_4$0 x_1$0)))))))

(assert (or (not Axiom_7$0)
    (forall ((?y Loc) (?z Loc))
            (or (in$0 y$0 FP_4$0)
                (and (Btwn$0 next$0 y$0 ?z ?y) (Btwn$0 next_4$0 y$0 ?z ?y))
                (and (not (Btwn$0 next$0 y$0 ?z ?y))
                     (not (Btwn$0 next_4$0 y$0 ?z ?y)))
                (not (= y$0 (ep$0 next$0 FP_4$0 y$0)))))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_76$0 null$0) ?y)
            (not (Btwn$0 next$0 null$0 ?y ?y)) (not (in$0 ?y sk_?X_76$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 sk_?e_4$0 (ep$0 next$0 sk_?X_76$0 sk_?e_4$0) ?y)
            (not (Btwn$0 next$0 sk_?e_4$0 ?y ?y)) (not (in$0 ?y sk_?X_76$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 x_1$0 (ep$0 next$0 sk_?X_76$0 x_1$0) ?y)
            (not (Btwn$0 next$0 x_1$0 ?y ?y)) (not (in$0 ?y sk_?X_76$0)))))

(assert (forall ((?y Loc))
        (or (Btwn$0 next$0 y$0 (ep$0 next$0 sk_?X_76$0 y$0) ?y)
            (not (Btwn$0 next$0 y$0 ?y ?y)) (not (in$0 ?y sk_?X_76$0)))))

(assert (or (in$0 (ep$0 next$0 sk_?X_76$0 null$0) sk_?X_76$0)
    (= null$0 (ep$0 next$0 sk_?X_76$0 null$0))))

(assert (or (in$0 (ep$0 next$0 sk_?X_76$0 sk_?e_4$0) sk_?X_76$0)
    (= sk_?e_4$0 (ep$0 next$0 sk_?X_76$0 sk_?e_4$0))))

(assert (or (in$0 (ep$0 next$0 sk_?X_76$0 x_1$0) sk_?X_76$0)
    (= x_1$0 (ep$0 next$0 sk_?X_76$0 x_1$0))))

(assert (or (in$0 (ep$0 next$0 sk_?X_76$0 y$0) sk_?X_76$0)
    (= y$0 (ep$0 next$0 sk_?X_76$0 y$0))))

(assert (Btwn$0 next$0 null$0 (ep$0 next$0 sk_?X_76$0 null$0)
  (ep$0 next$0 sk_?X_76$0 null$0)))

(assert (Btwn$0 next$0 sk_?e_4$0 (ep$0 next$0 sk_?X_76$0 sk_?e_4$0)
  (ep$0 next$0 sk_?X_76$0 sk_?e_4$0)))

(assert (Btwn$0 next$0 x_1$0 (ep$0 next$0 sk_?X_76$0 x_1$0)
  (ep$0 next$0 sk_?X_76$0 x_1$0)))

(assert (Btwn$0 next$0 y$0 (ep$0 next$0 sk_?X_76$0 y$0) (ep$0 next$0 sk_?X_76$0 y$0)))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_Caller$0 Alloc$0))
                 (or (in$0 x FP_Caller$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_Caller$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_Caller$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 FP_5$0 Alloc$0))
                 (or (in$0 x FP_5$0) (in$0 x Alloc$0)))
            (and (not (in$0 x FP_5$0)) (not (in$0 x Alloc$0))
                 (not (in$0 x (union$0 FP_5$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 (setminus$0 FP$0 FP_4$0) sk_?X_73$0))
                 (or (in$0 x (setminus$0 FP$0 FP_4$0)) (in$0 x sk_?X_73$0)))
            (and (not (in$0 x (setminus$0 FP$0 FP_4$0)))
                 (not (in$0 x sk_?X_73$0))
                 (not (in$0 x (union$0 (setminus$0 FP$0 FP_4$0) sk_?X_73$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_61$0 FP_Caller$0))
                 (or (in$0 x sk_?X_61$0) (in$0 x FP_Caller$0)))
            (and (not (in$0 x sk_?X_61$0)) (not (in$0 x FP_Caller$0))
                 (not (in$0 x (union$0 sk_?X_61$0 FP_Caller$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_76$0 sk_?X_61$0))
                 (or (in$0 x sk_?X_76$0) (in$0 x sk_?X_61$0)))
            (and (not (in$0 x sk_?X_76$0)) (not (in$0 x sk_?X_61$0))
                 (not (in$0 x (union$0 sk_?X_76$0 sk_?X_61$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_67$0 sk_?X_62$0))
                 (or (in$0 x sk_?X_67$0) (in$0 x sk_?X_62$0)))
            (and (not (in$0 x sk_?X_67$0)) (not (in$0 x sk_?X_62$0))
                 (not (in$0 x (union$0 sk_?X_67$0 sk_?X_62$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_77$0 sk_?X_82$0))
                 (or (in$0 x sk_?X_77$0) (in$0 x sk_?X_82$0)))
            (and (not (in$0 x sk_?X_77$0)) (not (in$0 x sk_?X_82$0))
                 (not (in$0 x (union$0 sk_?X_77$0 sk_?X_82$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_79$0 sk_?X_68$0))
                 (or (in$0 x sk_?X_79$0) (in$0 x sk_?X_68$0)))
            (and (not (in$0 x sk_?X_79$0)) (not (in$0 x sk_?X_68$0))
                 (not (in$0 x (union$0 sk_?X_79$0 sk_?X_68$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 X_1$0 sk_?X_77$0))
                 (or (in$0 x X_1$0) (in$0 x sk_?X_77$0)))
            (and (not (in$0 x X_1$0)) (not (in$0 x sk_?X_77$0))
                 (not (in$0 x (union$0 X_1$0 sk_?X_77$0)))))))

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
            (and (in$0 x (union$0 sk_?X_79$0 sk_?X_77$0))
                 (or (in$0 x sk_?X_79$0) (in$0 x sk_?X_77$0)))
            (and (not (in$0 x sk_?X_79$0)) (not (in$0 x sk_?X_77$0))
                 (not (in$0 x (union$0 sk_?X_79$0 sk_?X_77$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x (union$0 sk_?X_83$0 sk_?X_82$0))
                 (or (in$0 x sk_?X_83$0) (in$0 x sk_?X_82$0)))
            (and (not (in$0 x sk_?X_83$0)) (not (in$0 x sk_?X_82$0))
                 (not (in$0 x (union$0 sk_?X_83$0 sk_?X_82$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_79$0) (in$0 x sk_?X_77$0)
                 (in$0 x (intersection$0 sk_?X_79$0 sk_?X_77$0)))
            (and (or (not (in$0 x sk_?X_79$0)) (not (in$0 x sk_?X_77$0)))
                 (not (in$0 x (intersection$0 sk_?X_79$0 sk_?X_77$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_67$0) (in$0 x sk_?X_62$0)
                 (in$0 x (intersection$0 sk_?X_67$0 sk_?X_62$0)))
            (and (or (not (in$0 x sk_?X_67$0)) (not (in$0 x sk_?X_62$0)))
                 (not (in$0 x (intersection$0 sk_?X_67$0 sk_?X_62$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x X_1$0) (in$0 x sk_?X_77$0)
                 (in$0 x (intersection$0 X_1$0 sk_?X_77$0)))
            (and (or (not (in$0 x X_1$0)) (not (in$0 x sk_?X_77$0)))
                 (not (in$0 x (intersection$0 X_1$0 sk_?X_77$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x sk_?X_76$0)
                 (in$0 x (intersection$0 Alloc$0 sk_?X_76$0)))
            (and (or (not (in$0 x Alloc$0)) (not (in$0 x sk_?X_76$0)))
                 (not (in$0 x (intersection$0 Alloc$0 sk_?X_76$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_83$0) (in$0 x sk_?X_82$0)
                 (in$0 x (intersection$0 sk_?X_83$0 sk_?X_82$0)))
            (and (or (not (in$0 x sk_?X_83$0)) (not (in$0 x sk_?X_82$0)))
                 (not (in$0 x (intersection$0 sk_?X_83$0 sk_?X_82$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 Alloc$0))
                 (not (in$0 x Alloc$0)))
            (and (or (in$0 x Alloc$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 Alloc$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x Alloc$0) (in$0 x (setminus$0 Alloc$0 sk_?X_76$0))
                 (not (in$0 x sk_?X_76$0)))
            (and (or (in$0 x sk_?X_76$0) (not (in$0 x Alloc$0)))
                 (not (in$0 x (setminus$0 Alloc$0 sk_?X_76$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x sk_?X_61$0)
                 (in$0 x (setminus$0 sk_?X_61$0 sk_?X_76$0))
                 (not (in$0 x sk_?X_76$0)))
            (and (or (in$0 x sk_?X_76$0) (not (in$0 x sk_?X_61$0)))
                 (not (in$0 x (setminus$0 sk_?X_61$0 sk_?X_76$0)))))))

(assert (forall ((x Loc))
        (or
            (and (in$0 x FP_Caller$0)
                 (in$0 x (setminus$0 FP_Caller$0 sk_?X_61$0))
                 (not (in$0 x sk_?X_61$0)))
            (and (or (in$0 x sk_?X_61$0) (not (in$0 x FP_Caller$0)))
                 (not (in$0 x (setminus$0 FP_Caller$0 sk_?X_61$0)))))))

(assert (forall ((y Loc) (x Loc))
        (or (and (= x y) (in$0 x (setenum$0 y)))
            (and (not (= x y)) (not (in$0 x (setenum$0 y)))))))

(assert (= (read$0 next$0 null$0) null$0))

(assert (= (read$0 next_4$0 null$0) null$0))

(assert (forall ((x Loc)) (not (in$0 x emptyset$0))))

(assert (or (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0)
    (not (lseg_set_struct$0 sk_?X_69$0 next$0 x_1$0 root_x_1$0 X_1$0))))

(assert (or (Btwn$0 next$0 y$0 root_y$0 root_y$0)
    (not (lseg_set_struct$0 sk_?X_68$0 next$0 y$0 root_y$0 Y$0))))

(assert (= FP_5$0
  (union$0 (setminus$0 FP$0 FP_4$0)
    (union$0 (intersection$0 Alloc$0 FP_4$0) (setminus$0 Alloc$0 Alloc$0)))))

(assert (Frame$0 FP_4$0 Alloc$0 next$0 next_4$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= (read$0 next$0 root_y$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_67$0 sk_?X_62$0)))

(assert (= Y$0 (lseg_set_X$0 next$0 y$0 root_y$0)))

(assert (= sk_?X_61$0 FP$0))

(assert (= sk_?X_63$0 sk_?X_64$0))

(assert (= sk_?X_65$0 sk_?X_66$0))

(assert (= sk_?X_67$0 (union$0 sk_?X_69$0 sk_?X_68$0)))

(assert (= sk_?X_69$0 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)))

(assert (lseg_set_struct$0 sk_?X_68$0 next$0 y$0 root_y$0 Y$0))

(assert (= (read$0 next$0 root_x_1$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_79$0 sk_?X_77$0)))

(assert (= sk_?X_76$0 (union$0 sk_?X_79$0 sk_?X_77$0)))

(assert (= sk_?X_77$0 sk_?X_78$0))

(assert (= sk_?X_79$0 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)))

(assert (lseg_set_struct$0 sk_?X_79$0 next$0 x_1$0 root_x_1$0 X_28$0))

(assert (= emptyset$0 emptyset$0))

(assert (= sk_?X_70$0 X_28$0))

(assert (= sk_?X_72$0 sk_?X_71$0))

(assert (= sk_?X_74$0 sk_?X_73$0))

(assert (= sk_?X_75$0 sk_?X_74$0))

(assert (forall ((z Loc))
        (or
            (and (Btwn$0 next_4$0 z root_x_1$0 root_x_1$0)
                 (forall ((?x Loc))
                         (or (= ?x z) (= ?x root_x_1$0)
                             (not (Btwn$0 next_4$0 z ?x root_x_1$0)))))
            (not (in$0 z X_28$0)))))

(assert (= sk_?X_81$0 sk_?X_82$0))

(assert (= sk_?X_83$0 (lseg_set_domain$0 next_4$0 y$0 root_y$0)))

(assert (= sk_X_2$0 (lseg_set_X$0 next_4$0 y$0 root_y$0)))

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

(assert (or (and Axiom_9$0 Axiom_8$0 Axiom_7$0)
    (not (Frame$0 FP_4$0 Alloc$0 next$0 next_4$0))))

(assert (or (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0)
    (not (lseg_set_struct$0 sk_?X_79$0 next$0 x_1$0 root_x_1$0 X_28$0))))

(assert (or (Btwn$0 next_4$0 y$0 root_y$0 root_y$0)
    (not (lseg_set_struct$0 sk_?X_83$0 next_4$0 y$0 root_y$0 sk_X_2$0))))

(assert (= FP_Caller_3$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= Alloc$0 (union$0 FP_5$0 Alloc$0)))

(assert (= (read$0 next$0 root_x_1$0) null$0))

(assert (= emptyset$0 emptyset$0))

(assert (= X_1$0 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)))

(assert (= sk_?X_61$0 (union$0 sk_?X_67$0 sk_?X_62$0)))

(assert (= sk_?X_62$0 (union$0 sk_?X_65$0 sk_?X_63$0)))

(assert (= sk_?X_64$0 (setenum$0 root_y$0)))

(assert (= sk_?X_66$0 (setenum$0 root_x_1$0)))

(assert (= sk_?X_68$0 (lseg_set_domain$0 next$0 y$0 root_y$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (lseg_set_struct$0 sk_?X_69$0 next$0 x_1$0 root_x_1$0 X_1$0))

(assert (= emptyset$0 emptyset$0))

(assert (= X_28$0 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)))

(assert (= sk_?X_76$0 FP_4$0))

(assert (= sk_?X_78$0 (setenum$0 root_x_1$0)))

(assert (= FP$0 (union$0 FP_4$0 FP$0)))

(assert (= (read$0 next_4$0 root_x_1$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_70$0 sk_?X_72$0)))

(assert (= sk_?X_71$0 (setenum$0 root_x_1$0)))

(assert (= sk_?X_73$0 (union$0 sk_?X_70$0 sk_?X_72$0)))

(assert (= sk_?X_75$0
  (union$0 (intersection$0 Alloc$0 FP_4$0) (setminus$0 Alloc$0 Alloc$0))))

(assert (= t_2$0 root_x_1$0))

(assert (= sk_?X_80$0 (union$0 sk_?X_83$0 sk_?X_81$0)))

(assert (= sk_?X_82$0 (setenum$0 root_y$0)))

(assert (= sk_FP_2$0 sk_?X_80$0))

(assert (or (in$0 sk_?e_4$0 (intersection$0 sk_?X_83$0 sk_?X_81$0))
    (and (in$0 sk_?e_4$0 sk_FP_2$0) (not (in$0 sk_?e_4$0 FP_5$0)))
    (not (= (read$0 next_4$0 root_y$0) null$0))
    (not (Btwn$0 next_4$0 y$0 root_y$0 root_y$0))))

(assert (not (in$0 null$0 Alloc$0)))

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

(assert (forall ((?x Loc)) (Btwn$0 next_4$0 ?x ?x ?x)))

(assert (forall ((?x Loc)) (Btwn$0 next$0 ?x ?x ?x)))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next_4$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc)) (or (not (Btwn$0 next$0 ?x ?y ?x)) (= ?x ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?y)) (not (Btwn$0 next_4$0 ?x ?z ?z))
            (Btwn$0 next_4$0 ?x ?y ?z) (Btwn$0 next_4$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?x ?z ?z))
            (Btwn$0 next$0 ?x ?y ?z) (Btwn$0 next$0 ?x ?z ?y))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?z))
            (and (Btwn$0 next_4$0 ?x ?y ?y) (Btwn$0 next_4$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z))
            (and (Btwn$0 next$0 ?x ?y ?y) (Btwn$0 next$0 ?y ?z ?z)))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?y)) (not (Btwn$0 next_4$0 ?y ?z ?z))
            (Btwn$0 next_4$0 ?x ?z ?z))))

(assert (forall ((?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?y)) (not (Btwn$0 next$0 ?y ?z ?z))
            (Btwn$0 next$0 ?x ?z ?z))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?z)) (not (Btwn$0 next_4$0 ?y ?u ?z))
            (and (Btwn$0 next_4$0 ?x ?y ?u) (Btwn$0 next_4$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?y ?u ?z))
            (and (Btwn$0 next$0 ?x ?y ?u) (Btwn$0 next$0 ?x ?u ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next_4$0 ?x ?y ?z)) (not (Btwn$0 next_4$0 ?x ?u ?y))
            (and (Btwn$0 next_4$0 ?x ?u ?z) (Btwn$0 next_4$0 ?u ?y ?z)))))

(assert (forall ((?u Loc) (?x Loc) (?y Loc) (?z Loc))
        (or (not (Btwn$0 next$0 ?x ?y ?z)) (not (Btwn$0 next$0 ?x ?u ?y))
            (and (Btwn$0 next$0 ?x ?u ?z) (Btwn$0 next$0 ?u ?y ?z)))))

(check-sat)
(exit)
