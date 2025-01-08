(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/union_find.spl:42:1-2:A postcondition of procedure union might not hold at this return point
  tests/spl/union_find.spl:30:10:Related location: This is the postcondition that might not hold
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
(declare-fun Axiom_16$0 () Bool)
(declare-fun Axiom_17$0 () Bool)
(declare-fun Axiom_18$0 () Bool)
(declare-fun Axiom_19$0 () Bool)
(declare-fun Axiom_20$0 () Bool)
(declare-fun Axiom_21$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_4$0 () SetLoc)
(declare-fun FP_5$0 () SetLoc)
(declare-fun FP_6$0 () SetLoc)
(declare-fun FP_7$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_3$0 () SetLoc)
(declare-fun FP_Caller_final_4$0 () SetLoc)
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
(declare-fun next_6$0 () FldLoc)
(declare-fun root_x_1$0 () Loc)
(declare-fun root_y$0 () Loc)
(declare-fun s_2$0 () Loc)
(declare-fun sk_?X_113$0 () SetLoc)
(declare-fun sk_?X_114$0 () SetLoc)
(declare-fun sk_?X_115$0 () SetLoc)
(declare-fun sk_?X_116$0 () SetLoc)
(declare-fun sk_?X_117$0 () SetLoc)
(declare-fun sk_?X_118$0 () SetLoc)
(declare-fun sk_?X_119$0 () SetLoc)
(declare-fun sk_?X_120$0 () SetLoc)
(declare-fun sk_?X_121$0 () SetLoc)
(declare-fun sk_?X_122$0 () SetLoc)
(declare-fun sk_?X_123$0 () SetLoc)
(declare-fun sk_?X_124$0 () SetLoc)
(declare-fun sk_?X_125$0 () SetLoc)
(declare-fun sk_?X_126$0 () SetLoc)
(declare-fun sk_?X_127$0 () SetLoc)
(declare-fun sk_?X_128$0 () SetLoc)
(declare-fun sk_?X_129$0 () SetLoc)
(declare-fun sk_?X_130$0 () SetLoc)
(declare-fun sk_?X_131$0 () SetLoc)
(declare-fun sk_?X_132$0 () SetLoc)
(declare-fun sk_?X_133$0 () SetLoc)
(declare-fun sk_?X_134$0 () SetLoc)
(declare-fun sk_?X_135$0 () SetLoc)
(declare-fun sk_?X_136$0 () SetLoc)
(declare-fun sk_?X_137$0 () SetLoc)
(declare-fun sk_?X_138$0 () SetLoc)
(declare-fun sk_?X_139$0 () SetLoc)
(declare-fun sk_?X_140$0 () SetLoc)
(declare-fun sk_?X_141$0 () SetLoc)
(declare-fun sk_?X_142$0 () SetLoc)
(declare-fun sk_?X_143$0 () SetLoc)
(declare-fun sk_?X_144$0 () SetLoc)
(declare-fun sk_?X_145$0 () SetLoc)
(declare-fun sk_?X_146$0 () SetLoc)
(declare-fun sk_?X_147$0 () SetLoc)
(declare-fun sk_?X_148$0 () SetLoc)
(declare-fun sk_?X_149$0 () SetLoc)
(declare-fun sk_?X_150$0 () SetLoc)
(declare-fun sk_?X_151$0 () SetLoc)
(declare-fun sk_?X_152$0 () SetLoc)
(declare-fun sk_?e_5$0 () Loc)
(declare-fun sk_z_1$0 () Loc)
(declare-fun sk_z_2$0 () Loc)
(declare-fun t_2$0 () Loc)
(declare-fun t_33$0 () Loc)
(declare-fun t_34$0 () Loc)
(declare-fun t_35$0 () Loc)
(declare-fun t_36$0 () Loc)
(declare-fun t_37$0 () Loc)
(declare-fun t_38$0 () Loc)
(declare-fun t_39$0 () Loc)
(declare-fun t_40$0 () Loc)
(declare-fun t_41$0 () Loc)
(declare-fun t_42$0 () Loc)
(declare-fun t_43$0 () Loc)
(declare-fun t_44$0 () Loc)
(declare-fun t_45$0 () Loc)
(declare-fun t_46$0 () Loc)
(declare-fun t_47$0 () Loc)
(declare-fun t_48$0 () Loc)
(declare-fun t_49$0 () Loc)
(declare-fun t_50$0 () Loc)
(declare-fun t_51$0 () Loc)
(declare-fun t_52$0 () Loc)
(declare-fun t_53$0 () Loc)
(declare-fun t_54$0 () Loc)
(declare-fun t_55$0 () Loc)
(declare-fun t_56$0 () Loc)
(declare-fun t_57$0 () Loc)
(declare-fun t_58$0 () Loc)
(declare-fun t_59$0 () Loc)
(declare-fun x_1$0 () Loc)
(declare-fun y$0 () Loc)

(assert (= (ep$0 next_4$0 FP_6$0 y$0) t_59$0))

(assert (= (ep$0 next_4$0 FP_6$0 x_1$0) t_58$0))

(assert (= (ep$0 next_4$0 FP_6$0 sk_z_2$0) t_57$0))

(assert (= (ep$0 next_4$0 FP_6$0 sk_z_1$0) t_56$0))

(assert (= (ep$0 next_4$0 FP_6$0 sk_?e_5$0) t_55$0))

(assert (= (ep$0 next_4$0 FP_6$0 null$0) t_54$0))

(assert (= (ep$0 next$0 FP_4$0 y$0) t_53$0))

(assert (= (ep$0 next$0 FP_4$0 x_1$0) t_52$0))

(assert (= (ep$0 next$0 FP_4$0 sk_z_2$0) t_51$0))

(assert (= (ep$0 next$0 FP_4$0 sk_z_1$0) t_50$0))

(assert (= (ep$0 next$0 FP_4$0 sk_?e_5$0) t_49$0))

(assert (= (ep$0 next$0 FP_4$0 null$0) t_48$0))

(assert (= (read$0 next_5$0 t_2$0) t_47$0))

(assert (= (read$0 next_5$0 sk_z_2$0) t_46$0))

(assert (= (read$0 next_5$0 sk_z_1$0) t_45$0))

(assert (= (read$0 next_5$0 root_x_1$0) t_44$0))

(assert (= (read$0 next_4$0 t_2$0) t_43$0))

(assert (= (read$0 next_4$0 sk_z_2$0) t_42$0))

(assert (= (read$0 next_4$0 sk_z_1$0) t_41$0))

(assert (= (read$0 next$0 t_2$0) t_40$0))

(assert (= (read$0 next$0 sk_z_2$0) t_39$0))

(assert (= (read$0 next$0 sk_z_1$0) t_38$0))

(assert (= (read$0 (write$0 next_5$0 t_2$0 s_2$0) t_2$0) t_37$0))

(assert (= (read$0 (write$0 next_5$0 t_2$0 s_2$0) sk_z_2$0) t_36$0))

(assert (= (read$0 (write$0 next_5$0 t_2$0 s_2$0) sk_z_1$0) t_35$0))

(assert (= (read$0 (write$0 next_5$0 t_2$0 s_2$0) root_y$0) t_34$0))

(assert (= (read$0 (write$0 next_5$0 t_2$0 s_2$0) root_x_1$0) t_33$0))

(assert (forall ((?d_11 Loc) (?x Loc) (?y Loc))
        (or (= ?y ?x)
            (= (read$0 next_5$0 ?y) (read$0 (write$0 next_5$0 ?x ?d_11) ?y)))))

(assert (forall ((?d_11 Loc) (?x Loc))
        (= (read$0 (write$0 next_5$0 ?x ?d_11) ?x) ?d_11)))

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

(assert (or (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0)
    (not (lseg_set_struct$0 sk_?X_141$0 next$0 x_1$0 root_x_1$0 X_28$0))))

(assert (or (Btwn$0 next_4$0 y$0 root_y$0 root_y$0)
    (not (lseg_set_struct$0 sk_?X_137$0 next_4$0 y$0 root_y$0 X_29$0))))

(assert (= FP_5$0
  (union$0 (setminus$0 FP$0 FP_4$0)
    (union$0 (intersection$0 Alloc$0 FP_4$0) (setminus$0 Alloc$0 Alloc$0)))))

(assert (= FP_Caller_3$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (Frame$0 FP_4$0 Alloc$0 next$0 next_4$0))

(assert (= Alloc$0 (union$0 FP_5$0 Alloc$0)))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= (read$0 next$0 root_y$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_119$0 sk_?X_114$0)))

(assert (= Y$0 (lseg_set_X$0 next$0 y$0 root_y$0)))

(assert (= sk_?X_113$0 FP$0))

(assert (= sk_?X_115$0 sk_?X_116$0))

(assert (= sk_?X_117$0 sk_?X_118$0))

(assert (= sk_?X_119$0 (union$0 sk_?X_121$0 sk_?X_120$0)))

(assert (= sk_?X_121$0 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)))

(assert (lseg_set_struct$0 sk_?X_120$0 next$0 y$0 root_y$0 Y$0))

(assert (= (read$0 next$0 root_x_1$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_141$0 sk_?X_139$0)))

(assert (= sk_?X_138$0 (union$0 sk_?X_141$0 sk_?X_139$0)))

(assert (= sk_?X_139$0 sk_?X_140$0))

(assert (= sk_?X_141$0 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)))

(assert (lseg_set_struct$0 sk_?X_141$0 next$0 x_1$0 root_x_1$0 X_28$0))

(assert (= emptyset$0 emptyset$0))

(assert (= sk_?X_128$0 X_28$0))

(assert (= sk_?X_130$0 sk_?X_129$0))

(assert (= sk_?X_132$0 sk_?X_131$0))

(assert (= sk_?X_133$0 sk_?X_132$0))

(assert (forall ((z Loc))
        (or
            (and (Btwn$0 next_4$0 z root_x_1$0 root_x_1$0)
                 (forall ((?x Loc))
                         (or (= ?x z) (= ?x root_x_1$0)
                             (not (Btwn$0 next_4$0 z ?x root_x_1$0)))))
            (not (in$0 z X_28$0)))))

(assert (= emptyset$0 emptyset$0))

(assert (= X_29$0 (lseg_set_X$0 next_4$0 y$0 root_y$0)))

(assert (= sk_?X_134$0 FP_6$0))

(assert (= sk_?X_136$0 (setenum$0 root_y$0)))

(assert (= FP_5$0 (union$0 FP_6$0 FP_5$0)))

(assert (= (read$0 next_5$0 root_y$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_122$0 sk_?X_124$0)))

(assert (= sk_?X_122$0 X_29$0))

(assert (= sk_?X_124$0 sk_?X_123$0))

(assert (= sk_?X_126$0 sk_?X_125$0))

(assert (= sk_?X_127$0 sk_?X_126$0))

(assert (= sk_?X_142$0 X_1$0))

(assert (= sk_?X_144$0 (union$0 sk_?X_142$0 sk_?X_143$0)))

(assert (= sk_?X_146$0 sk_?X_145$0))

(assert (= sk_?X_148$0 sk_?X_147$0))

(assert (= sk_?X_150$0 (union$0 sk_?X_148$0 sk_?X_149$0)))

(assert (= sk_?X_152$0 sk_?X_151$0))

(assert (not (in$0 null$0 Alloc$0)))

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

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (or (in$0 (ep$0 ?f ?X ?x) ?X) (= ?x (ep$0 ?f ?X ?x)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) (ep$0 ?f ?X ?x))))

(assert (or (not Axiom_16$0)
    (forall ((?x Loc) (?y Loc) (?z Loc))
            (or (in$0 ?x FP_6$0)
                (and (Btwn$0 next_4$0 ?x ?z ?y) (Btwn$0 next_5$0 ?x ?z ?y))
                (and (not (Btwn$0 next_4$0 ?x ?z ?y))
                     (not (Btwn$0 next_5$0 ?x ?z ?y)))
                (not (= ?x (ep$0 next_4$0 FP_6$0 ?x)))))))

(assert (or (not Axiom_17$0)
    (forall ((?x Loc) (?y Loc) (?z Loc))
            (or (and (Btwn$0 next_4$0 ?x ?z ?y) (Btwn$0 next_5$0 ?x ?z ?y))
                (and (not (Btwn$0 next_4$0 ?x ?z ?y))
                     (not (Btwn$0 next_5$0 ?x ?z ?y)))
                (not
                     (or (Btwn$0 next_4$0 ?x ?y (ep$0 next_4$0 FP_6$0 ?x))
                         (and (Btwn$0 next_4$0 ?x ?y ?y)
                              (not
                                   (Btwn$0 next_4$0 ?x
                                     (ep$0 next_4$0 FP_6$0 ?x)
                                     (ep$0 next_4$0 FP_6$0 ?x))))))))))

(assert (or (not Axiom_18$0)
    (forall ((?x Loc))
            (or (= (read$0 next_4$0 ?x) (read$0 next_5$0 ?x))
                (not (in$0 ?x (setminus$0 Alloc$0 FP_6$0)))))))

(assert (or (and Axiom_21$0 Axiom_20$0 Axiom_19$0)
    (not (Frame$0 FP_4$0 Alloc$0 next$0 next_4$0))))

(assert (or (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0)
    (not (lseg_set_struct$0 sk_?X_121$0 next$0 x_1$0 root_x_1$0 X_1$0))))

(assert (or (Btwn$0 next$0 y$0 root_y$0 root_y$0)
    (not (lseg_set_struct$0 sk_?X_120$0 next$0 y$0 root_y$0 Y$0))))

(assert (or (and (= next_6$0 (write$0 next_5$0 t_2$0 s_2$0)) (not (= t_2$0 s_2$0)))
    (and (= next_6$0 next_5$0) (= t_2$0 s_2$0))))

(assert (= FP_7$0
  (union$0 (setminus$0 FP_5$0 FP_6$0)
    (union$0 (intersection$0 Alloc$0 FP_6$0) (setminus$0 Alloc$0 Alloc$0)))))

(assert (= FP_Caller_final_4$0 (union$0 FP_Caller_3$0 FP_7$0)))

(assert (Frame$0 FP_6$0 Alloc$0 next_4$0 next_5$0))

(assert (= Alloc$0 (union$0 FP_7$0 Alloc$0)))

(assert (= (read$0 next$0 root_x_1$0) null$0))

(assert (= emptyset$0 emptyset$0))

(assert (= X_1$0 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)))

(assert (= sk_?X_113$0 (union$0 sk_?X_119$0 sk_?X_114$0)))

(assert (= sk_?X_114$0 (union$0 sk_?X_117$0 sk_?X_115$0)))

(assert (= sk_?X_116$0 (setenum$0 root_y$0)))

(assert (= sk_?X_118$0 (setenum$0 root_x_1$0)))

(assert (= sk_?X_120$0 (lseg_set_domain$0 next$0 y$0 root_y$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (lseg_set_struct$0 sk_?X_121$0 next$0 x_1$0 root_x_1$0 X_1$0))

(assert (= emptyset$0 emptyset$0))

(assert (= X_28$0 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)))

(assert (= sk_?X_138$0 FP_4$0))

(assert (= sk_?X_140$0 (setenum$0 root_x_1$0)))

(assert (= FP$0 (union$0 FP_4$0 FP$0)))

(assert (= (read$0 next_4$0 root_x_1$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_128$0 sk_?X_130$0)))

(assert (= sk_?X_129$0 (setenum$0 root_x_1$0)))

(assert (= sk_?X_131$0 (union$0 sk_?X_128$0 sk_?X_130$0)))

(assert (= sk_?X_133$0
  (union$0 (intersection$0 Alloc$0 FP_4$0) (setminus$0 Alloc$0 Alloc$0))))

(assert (= t_2$0 root_x_1$0))

(assert (= (read$0 next_4$0 root_y$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_137$0 sk_?X_135$0)))

(assert (= sk_?X_134$0 (union$0 sk_?X_137$0 sk_?X_135$0)))

(assert (= sk_?X_135$0 sk_?X_136$0))

(assert (= sk_?X_137$0 (lseg_set_domain$0 next_4$0 y$0 root_y$0)))

(assert (lseg_set_struct$0 sk_?X_137$0 next_4$0 y$0 root_y$0 X_29$0))

(assert (= emptyset$0 emptyset$0))

(assert (= s_2$0 root_y$0))

(assert (= sk_?X_123$0 (setenum$0 root_y$0)))

(assert (= sk_?X_125$0 (union$0 sk_?X_122$0 sk_?X_124$0)))

(assert (= sk_?X_127$0
  (union$0 (intersection$0 Alloc$0 FP_6$0) (setminus$0 Alloc$0 Alloc$0))))

(assert (forall ((z Loc))
        (or (= (read$0 next_5$0 z) root_y$0) (not (in$0 z X_29$0)))))

(assert (= sk_?X_143$0 Y$0))

(assert (= sk_?X_145$0 sk_?X_144$0))

(assert (= sk_?X_147$0 (setenum$0 root_y$0)))

(assert (= sk_?X_149$0 (setenum$0 root_x_1$0)))

(assert (= sk_?X_151$0 (union$0 sk_?X_146$0 sk_?X_150$0)))

(assert (or (in$0 sk_?e_5$0 (intersection$0 sk_?X_146$0 sk_?X_150$0))
    (and
         (in$0 sk_?e_5$0
           (union$0 (intersection$0 Alloc$0 FP$0)
             (setminus$0 Alloc$0 Alloc$0)))
         (not (in$0 sk_?e_5$0 sk_?X_152$0)))
    (and (in$0 sk_?e_5$0 sk_?X_152$0)
         (not
              (in$0 sk_?e_5$0
                (union$0 (intersection$0 Alloc$0 FP$0)
                  (setminus$0 Alloc$0 Alloc$0)))))
    (and (in$0 sk_z_1$0 (setminus$0 X_1$0 Y$0))
         (not (= (read$0 next_6$0 sk_z_1$0) root_x_1$0)))
    (and (in$0 sk_z_2$0 Y$0) (not (= (read$0 next_6$0 sk_z_2$0) root_y$0)))
    (and (not (= (read$0 next_6$0 root_x_1$0) root_y$0))
         (not (= root_x_1$0 root_y$0)))
    (not (= (read$0 next_6$0 root_y$0) null$0))))

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

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) ?y) (not (Btwn$0 ?f ?x ?y ?y))
            (not (in$0 ?y ?X)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (in$0 ?y ?X))
            (in$0 (ep$0 ?f ?X ?x) ?X))))

(assert (or (and Axiom_18$0 Axiom_17$0 Axiom_16$0)
    (not (Frame$0 FP_6$0 Alloc$0 next_4$0 next_5$0))))

(assert (or (not Axiom_19$0)
    (forall ((?x Loc) (?y Loc) (?z Loc))
            (or (in$0 ?x FP_4$0)
                (and (Btwn$0 next$0 ?x ?z ?y) (Btwn$0 next_4$0 ?x ?z ?y))
                (and (not (Btwn$0 next$0 ?x ?z ?y))
                     (not (Btwn$0 next_4$0 ?x ?z ?y)))
                (not (= ?x (ep$0 next$0 FP_4$0 ?x)))))))

(assert (or (not Axiom_20$0)
    (forall ((?x Loc) (?y Loc) (?z Loc))
            (or (and (Btwn$0 next$0 ?x ?z ?y) (Btwn$0 next_4$0 ?x ?z ?y))
                (and (not (Btwn$0 next$0 ?x ?z ?y))
                     (not (Btwn$0 next_4$0 ?x ?z ?y)))
                (not
                     (or (Btwn$0 next$0 ?x ?y (ep$0 next$0 FP_4$0 ?x))
                         (and (Btwn$0 next$0 ?x ?y ?y)
                              (not
                                   (Btwn$0 next$0 ?x (ep$0 next$0 FP_4$0 ?x)
                                     (ep$0 next$0 FP_4$0 ?x))))))))))

(assert (or (not Axiom_21$0)
    (forall ((?x Loc))
            (or (= (read$0 next$0 ?x) (read$0 next_4$0 ?x))
                (not (in$0 ?x (setminus$0 Alloc$0 FP_4$0)))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next_5$0 t_2$0 s_2$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next_5$0 ?z ?u ?v)
                               (or (Btwn$0 next_5$0 ?z ?v t_2$0)
                                   (and (Btwn$0 next_5$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next_5$0 ?z t_2$0 t_2$0)))))
                          (and (not (= t_2$0 ?v))
                               (or (Btwn$0 next_5$0 ?z t_2$0 ?v)
                                   (and (Btwn$0 next_5$0 ?z t_2$0 t_2$0)
                                        (not (Btwn$0 next_5$0 ?z ?v ?v))))
                               (Btwn$0 next_5$0 ?z ?u t_2$0)
                               (or (Btwn$0 next_5$0 s_2$0 ?v t_2$0)
                                   (and (Btwn$0 next_5$0 s_2$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_5$0 s_2$0 t_2$0
                                               t_2$0)))))
                          (and (not (= t_2$0 ?v))
                               (or (Btwn$0 next_5$0 ?z t_2$0 ?v)
                                   (and (Btwn$0 next_5$0 ?z t_2$0 t_2$0)
                                        (not (Btwn$0 next_5$0 ?z ?v ?v))))
                               (Btwn$0 next_5$0 s_2$0 ?u ?v)
                               (or (Btwn$0 next_5$0 s_2$0 ?v t_2$0)
                                   (and (Btwn$0 next_5$0 s_2$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_5$0 s_2$0 t_2$0
                                               t_2$0))))))))
             (or
                 (and (Btwn$0 next_5$0 ?z ?u ?v)
                      (or (Btwn$0 next_5$0 ?z ?v t_2$0)
                          (and (Btwn$0 next_5$0 ?z ?v ?v)
                               (not (Btwn$0 next_5$0 ?z t_2$0 t_2$0)))))
                 (and (not (= t_2$0 ?v))
                      (or (Btwn$0 next_5$0 ?z t_2$0 ?v)
                          (and (Btwn$0 next_5$0 ?z t_2$0 t_2$0)
                               (not (Btwn$0 next_5$0 ?z ?v ?v))))
                      (Btwn$0 next_5$0 ?z ?u t_2$0)
                      (or (Btwn$0 next_5$0 s_2$0 ?v t_2$0)
                          (and (Btwn$0 next_5$0 s_2$0 ?v ?v)
                               (not (Btwn$0 next_5$0 s_2$0 t_2$0 t_2$0)))))
                 (and (not (= t_2$0 ?v))
                      (or (Btwn$0 next_5$0 ?z t_2$0 ?v)
                          (and (Btwn$0 next_5$0 ?z t_2$0 t_2$0)
                               (not (Btwn$0 next_5$0 ?z ?v ?v))))
                      (Btwn$0 next_5$0 s_2$0 ?u ?v)
                      (or (Btwn$0 next_5$0 s_2$0 ?v t_2$0)
                          (and (Btwn$0 next_5$0 s_2$0 ?v ?v)
                               (not (Btwn$0 next_5$0 s_2$0 t_2$0 t_2$0)))))
                 (not (Btwn$0 (write$0 next_5$0 t_2$0 s_2$0) ?z ?u ?v))))))

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
