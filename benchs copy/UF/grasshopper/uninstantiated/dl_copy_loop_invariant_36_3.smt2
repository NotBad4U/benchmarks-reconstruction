(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/dl/dl_copy.spl:36:3-4:An invariant might not be maintained by a loop in procedure dl_copy
  tests/spl/dl/dl_copy.spl:20:14:Related location: This is the loop invariant that might not be maintained
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
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Alloc_2$0 () SetLoc)
(declare-fun Axiom_29$0 () Bool)
(declare-fun Axiom_30$0 () Bool)
(declare-fun Axiom_31$0 () Bool)
(declare-fun Axiom_32$0 () Bool)
(declare-fun Axiom_33$0 () Bool)
(declare-fun Axiom_34$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_3$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun a_2$0 () Loc)
(declare-fun a_init$0 () Loc)
(declare-fun b_2$0 () Loc)
(declare-fun b_init$0 () Loc)
(declare-fun c_3$0 () Loc)
(declare-fun c_4$0 () Loc)
(declare-fun c_init$0 () Loc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_5$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun d_3$0 () Loc)
(declare-fun d_4$0 () Loc)
(declare-fun d_init$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun next_2$0 () FldLoc)
(declare-fun next_3$0 () FldLoc)
(declare-fun old_curr_4$0 () Loc)
(declare-fun old_curr_5$0 () Loc)
(declare-fun old_curr_init$0 () Loc)
(declare-fun old_d_2$0 () Loc)
(declare-fun old_d_4$0 () Loc)
(declare-fun old_d_init$0 () Loc)
(declare-fun prev$0 () FldLoc)
(declare-fun prev_2$0 () FldLoc)
(declare-fun sk_?X_40$0 () SetLoc)
(declare-fun sk_?X_41$0 () SetLoc)
(declare-fun sk_?X_42$0 () SetLoc)
(declare-fun sk_?X_43$0 () SetLoc)
(declare-fun sk_?X_44$0 () SetLoc)
(declare-fun sk_?X_45$0 () SetLoc)
(declare-fun sk_?X_46$0 () SetLoc)
(declare-fun sk_?X_47$0 () SetLoc)
(declare-fun sk_?X_48$0 () SetLoc)
(declare-fun sk_?X_49$0 () SetLoc)
(declare-fun sk_FP_1$0 () SetLoc)
(declare-fun sk_l1_2$0 () Loc)
(declare-fun sk_l2_2$0 () Loc)
(declare-fun t_71$0 () Loc)
(declare-fun t_72$0 () Loc)
(declare-fun t_73$0 () Loc)
(declare-fun t_74$0 () Loc)
(declare-fun t_75$0 () Loc)
(declare-fun t_76$0 () Loc)
(declare-fun t_77$0 () Loc)
(declare-fun t_78$0 () Loc)
(declare-fun t_79$0 () Loc)
(declare-fun t_80$0 () Loc)
(declare-fun t_81$0 () Loc)
(declare-fun t_82$0 () Loc)
(declare-fun t_83$0 () Loc)
(declare-fun t_84$0 () Loc)
(declare-fun t_85$0 () Loc)
(declare-fun t_86$0 () Loc)
(declare-fun t_87$0 () Loc)
(declare-fun t_88$0 () Loc)
(declare-fun t_89$0 () Loc)
(declare-fun t_90$0 () Loc)
(declare-fun t_91$0 () Loc)
(declare-fun t_92$0 () Loc)
(declare-fun t_93$0 () Loc)
(declare-fun t_94$0 () Loc)
(declare-fun t_95$0 () Loc)
(declare-fun t_96$0 () Loc)
(declare-fun t_97$0 () Loc)
(declare-fun t_98$0 () Loc)
(declare-fun t_99$0 () Loc)
(declare-fun t_100$0 () Loc)
(declare-fun t_101$0 () Loc)
(declare-fun t_102$0 () Loc)
(declare-fun t_103$0 () Loc)
(declare-fun t_104$0 () Loc)
(declare-fun t_105$0 () Loc)
(declare-fun t_106$0 () Loc)
(declare-fun t_107$0 () Loc)
(declare-fun t_108$0 () Loc)
(declare-fun t_109$0 () Loc)
(declare-fun t_110$0 () Loc)
(declare-fun t_111$0 () Loc)
(declare-fun t_112$0 () Loc)
(declare-fun t_113$0 () Loc)
(declare-fun t_114$0 () Loc)
(declare-fun t_115$0 () Loc)
(declare-fun t_116$0 () Loc)
(declare-fun tmp_2$0 () Loc)
(declare-fun tmp_3$0 () Loc)
(declare-fun tmp_init$0 () Loc)

(assert (= (read$0 prev$0 sk_l2_2$0) t_116$0))

(assert (= (read$0 prev$0 sk_l1_2$0) t_115$0))

(assert (= (read$0 prev$0 d_4$0) t_114$0))

(assert (= (read$0 prev$0 curr_5$0) t_113$0))

(assert (= (read$0 prev$0 c_3$0) t_112$0))

(assert (= (read$0 prev$0 a_2$0) t_111$0))

(assert (= (read$0 next_2$0 sk_l2_2$0) t_110$0))

(assert (= (read$0 next_2$0 sk_l1_2$0) t_109$0))

(assert (= (read$0 next_2$0 old_d_4$0) t_108$0))

(assert (= (read$0 next_2$0 old_curr_5$0) t_107$0))

(assert (= (read$0 next_2$0 d_4$0) t_106$0))

(assert (= (read$0 next_2$0 curr_4$0) t_105$0))

(assert (= (read$0 next_2$0 b_2$0) t_104$0))

(assert (= (read$0 next$0 sk_l2_2$0) t_103$0))

(assert (= (read$0 next$0 sk_l1_2$0) t_102$0))

(assert (= (read$0 next$0 old_d_4$0) t_101$0))

(assert (= (read$0 next$0 old_curr_5$0) t_100$0))

(assert (= (read$0 next$0 d_4$0) t_99$0))

(assert (= (read$0 next$0 curr_4$0) t_98$0))

(assert (= (read$0 next$0 b_2$0) t_97$0))

(assert (= (read$0 (write$0 prev$0 d_4$0 old_d_4$0) sk_l2_2$0) t_96$0))

(assert (= (read$0 (write$0 prev$0 d_4$0 old_d_4$0) sk_l1_2$0) t_95$0))

(assert (= (read$0 (write$0 prev$0 d_4$0 old_d_4$0) d_4$0) t_94$0))

(assert (= (read$0 (write$0 prev$0 d_4$0 old_d_4$0) curr_init$0) t_93$0))

(assert (= (read$0 (write$0 prev$0 d_4$0 old_d_4$0) curr_5$0) t_92$0))

(assert (= (read$0 (write$0 prev$0 d_4$0 old_d_4$0) c_init$0) t_91$0))

(assert (= (read$0 (write$0 prev$0 d_4$0 old_d_4$0) c_3$0) t_90$0))

(assert (= (read$0 (write$0 prev$0 d_4$0 old_d_4$0) a_init$0) t_89$0))

(assert (= (read$0 (write$0 prev$0 d_4$0 old_d_4$0) a_2$0) t_88$0))

(assert (= (read$0 (write$0 next_2$0 old_d_4$0 d_4$0) sk_l2_2$0) t_87$0))

(assert (= (read$0 (write$0 next_2$0 old_d_4$0 d_4$0) sk_l1_2$0) t_86$0))

(assert (= (read$0 (write$0 next_2$0 old_d_4$0 d_4$0) old_d_4$0) t_85$0))

(assert (= (read$0 (write$0 next_2$0 old_d_4$0 d_4$0) old_curr_5$0) t_84$0))

(assert (= (read$0 (write$0 next_2$0 old_d_4$0 d_4$0) d_4$0) t_83$0))

(assert (= (read$0 (write$0 next_2$0 old_d_4$0 d_4$0) curr_4$0) t_82$0))

(assert (= (read$0 (write$0 next_2$0 old_d_4$0 d_4$0) b_2$0) t_81$0))

(assert (= (read$0 (write$0 next$0 d_4$0 null$0) sk_l2_2$0) t_80$0))

(assert (= (read$0 (write$0 next$0 d_4$0 null$0) sk_l1_2$0) t_79$0))

(assert (= (read$0 (write$0 next$0 d_4$0 null$0) old_d_4$0) t_78$0))

(assert (= (read$0 (write$0 next$0 d_4$0 null$0) old_curr_init$0) t_77$0))

(assert (= (read$0 (write$0 next$0 d_4$0 null$0) old_curr_5$0) t_76$0))

(assert (= (read$0 (write$0 next$0 d_4$0 null$0) d_init$0) t_75$0))

(assert (= (read$0 (write$0 next$0 d_4$0 null$0) d_4$0) t_74$0))

(assert (= (read$0 (write$0 next$0 d_4$0 null$0) curr_4$0) t_73$0))

(assert (= (read$0 (write$0 next$0 d_4$0 null$0) b_init$0) t_72$0))

(assert (= (read$0 (write$0 next$0 d_4$0 null$0) b_2$0) t_71$0))

(assert (forall ((?d_15 Loc) (?x Loc) (?y Loc))
        (or (= ?y ?x)
            (= (read$0 prev$0 ?y) (read$0 (write$0 prev$0 ?x ?d_15) ?y)))))

(assert (forall ((?d_15 Loc) (?x Loc))
        (= (read$0 (write$0 prev$0 ?x ?d_15) ?x) ?d_15)))

(assert (forall ((?d_14 Loc) (?x Loc) (?y Loc))
        (or (= ?y ?x)
            (= (read$0 next_2$0 ?y) (read$0 (write$0 next_2$0 ?x ?d_14) ?y)))))

(assert (forall ((?d_14 Loc) (?x Loc))
        (= (read$0 (write$0 next_2$0 ?x ?d_14) ?x) ?d_14)))

(assert (forall ((?d_13 Loc) (?x Loc) (?y Loc))
        (or (= ?y ?x)
            (= (read$0 next$0 ?y) (read$0 (write$0 next$0 ?x ?d_13) ?y)))))

(assert (forall ((?d_13 Loc) (?x Loc))
        (= (read$0 (write$0 next$0 ?x ?d_13) ?x) ?d_13)))

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

(assert (or (not Axiom_29$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_44$0)) (not (in$0 l2 sk_?X_44$0))))))

(assert (or
    (and (Btwn$0 next$0 c_init$0 null$0 null$0)
         (or (and (= null$0 d_init$0) (= c_init$0 null$0))
             (and (= (read$0 next$0 d_init$0) null$0)
                  (= (read$0 prev$0 c_init$0) null$0)
                  (in$0 d_init$0 sk_?X_41$0)))
         Axiom_30$0)
    (not
         (dlseg_struct$0 sk_?X_41$0 next$0 prev$0 c_init$0 null$0 null$0
           d_init$0))))

(assert (or (not Axiom_31$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_43$0)) (not (in$0 l2 sk_?X_43$0))))))

(assert (or
    (and (Btwn$0 next_3$0 a_2$0 curr_5$0 curr_5$0)
         (or (and (= null$0 old_curr_5$0) (= a_2$0 curr_5$0))
             (and (= (read$0 next_3$0 old_curr_5$0) curr_5$0)
                  (= (read$0 prev_2$0 a_2$0) null$0)
                  (in$0 old_curr_5$0 sk_?X_49$0)))
         Axiom_32$0)
    (not
         (dlseg_struct$0 sk_?X_49$0 next_3$0 prev_2$0 a_2$0 null$0 curr_5$0
           old_curr_5$0))))

(assert (or (not Axiom_33$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev_2$0 l2) l1) (not (= (read$0 next_3$0 l1) l2))
                (not (in$0 l1 sk_?X_46$0)) (not (in$0 l2 sk_?X_46$0))))))

(assert (or
    (and (Btwn$0 next_3$0 curr_5$0 null$0 null$0)
         (or
             (and (= (read$0 next_3$0 b_2$0) null$0)
                  (= (read$0 prev_2$0 curr_5$0) old_curr_5$0)
                  (in$0 b_2$0 sk_?X_48$0))
             (and (= curr_5$0 null$0) (= old_curr_5$0 b_2$0)))
         Axiom_34$0)
    (not
         (dlseg_struct$0 sk_?X_48$0 next_3$0 prev_2$0 curr_5$0 old_curr_5$0
           null$0 b_2$0))))

(assert (= Alloc_2$0 (union$0 Alloc$0 (setenum$0 tmp_3$0))))

(assert (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= b_2$0 b_init$0))

(assert (= curr_4$0 curr_init$0))

(assert (= d_3$0 d_init$0))

(assert (= next_2$0 (write$0 next$0 d_4$0 null$0)))

(assert (= old_curr_5$0 curr_4$0))

(assert (= old_d_4$0 d_3$0))

(assert (= tmp_2$0 tmp_init$0))

(assert (= emptyset$0 (intersection$0 sk_?X_42$0 sk_?X_41$0)))

(assert (= sk_?X_40$0 (union$0 sk_?X_42$0 sk_?X_41$0)))

(assert (= sk_?X_41$0 (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 null$0 d_init$0)))

(assert (= sk_?X_43$0
  (dlseg_domain$0 next$0 prev$0 curr_init$0 old_curr_init$0 null$0 b_init$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (dlseg_struct$0 sk_?X_43$0 next$0 prev$0 curr_init$0 old_curr_init$0 null$0
  b_init$0))

(assert (= sk_?X_45$0 (union$0 sk_?X_47$0 sk_?X_46$0)))

(assert (= sk_?X_47$0 (union$0 sk_?X_49$0 sk_?X_48$0)))

(assert (= sk_?X_49$0
  (dlseg_domain$0 next_3$0 prev_2$0 a_2$0 null$0 curr_5$0 old_curr_5$0)))

(assert (or (in$0 sk_l1_2$0 (intersection$0 sk_?X_49$0 sk_?X_48$0))
    (in$0 sk_l2_2$0 (intersection$0 sk_?X_47$0 sk_?X_46$0))
    (and (= (read$0 next_3$0 sk_l1_2$0) sk_l2_2$0)
         (in$0 sk_l1_2$0 sk_?X_48$0) (in$0 sk_l2_2$0 sk_?X_48$0)
         (not (= (read$0 prev_2$0 sk_l2_2$0) sk_l1_2$0)))
    (and (= (read$0 next_3$0 sk_l1_2$0) sk_l2_2$0)
         (in$0 sk_l1_2$0 sk_?X_49$0) (in$0 sk_l2_2$0 sk_?X_49$0)
         (not (= (read$0 prev_2$0 sk_l2_2$0) sk_l1_2$0)))
    (and (= (read$0 next_3$0 sk_l2_2$0) sk_l1_2$0)
         (in$0 sk_l1_2$0 sk_?X_46$0) (in$0 sk_l2_2$0 sk_?X_46$0)
         (not (= (read$0 prev_2$0 sk_l1_2$0) sk_l2_2$0)))
    (and (in$0 sk_l2_2$0 sk_FP_1$0) (not (in$0 sk_l2_2$0 FP_3$0)))
    (and (or (not (= null$0 d_4$0)) (not (= c_3$0 null$0)))
         (or (not (= (read$0 next_3$0 d_4$0) null$0))
             (not (= (read$0 prev_2$0 c_3$0) null$0))
             (not (in$0 d_4$0 sk_?X_46$0))))
    (and (or (not (= null$0 old_curr_5$0)) (not (= a_2$0 curr_5$0)))
         (or (not (= (read$0 next_3$0 old_curr_5$0) curr_5$0))
             (not (= (read$0 prev_2$0 a_2$0) null$0))
             (not (in$0 old_curr_5$0 sk_?X_49$0))))
    (and
         (or (not (= (read$0 next_3$0 b_2$0) null$0))
             (not (= (read$0 prev_2$0 curr_5$0) old_curr_5$0))
             (not (in$0 b_2$0 sk_?X_48$0)))
         (or (not (= curr_5$0 null$0)) (not (= old_curr_5$0 b_2$0))))
    (not (Btwn$0 next_3$0 a_2$0 curr_5$0 curr_5$0))
    (not (Btwn$0 next_3$0 c_3$0 null$0 null$0))
    (not (Btwn$0 next_3$0 curr_5$0 null$0 null$0))))

(assert (not (= tmp_3$0 null$0)))

(assert (not (in$0 tmp_3$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 null$0
                     d_init$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 c_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 null$0
                          d_init$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_3$0 a_2$0 l1 curr_5$0)
                 (in$0 l1
                   (dlseg_domain$0 next_3$0 prev_2$0 a_2$0 null$0 curr_5$0
                     old_curr_5$0))
                 (not (= l1 curr_5$0)))
            (and
                 (or (= l1 curr_5$0)
                     (not (Btwn$0 next_3$0 a_2$0 l1 curr_5$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next_3$0 prev_2$0 a_2$0 null$0
                          curr_5$0 old_curr_5$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_3$0 curr_5$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next_3$0 prev_2$0 curr_5$0 old_curr_5$0
                     null$0 b_2$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next_3$0 curr_5$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next_3$0 prev_2$0 curr_5$0
                          old_curr_5$0 null$0 b_2$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (or (in$0 (ep$0 ?f ?X ?x) ?X) (= ?x (ep$0 ?f ?X ?x)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) (ep$0 ?f ?X ?x))))

(assert (or
    (and (Btwn$0 next$0 a_init$0 curr_init$0 curr_init$0)
         (or (and (= null$0 old_curr_init$0) (= a_init$0 curr_init$0))
             (and (= (read$0 next$0 old_curr_init$0) curr_init$0)
                  (= (read$0 prev$0 a_init$0) null$0)
                  (in$0 old_curr_init$0 sk_?X_44$0)))
         Axiom_29$0)
    (not
         (dlseg_struct$0 sk_?X_44$0 next$0 prev$0 a_init$0 null$0 curr_init$0
           old_curr_init$0))))

(assert (or (not Axiom_30$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_41$0)) (not (in$0 l2 sk_?X_41$0))))))

(assert (or
    (and (Btwn$0 next$0 curr_init$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 b_init$0) null$0)
                  (= (read$0 prev$0 curr_init$0) old_curr_init$0)
                  (in$0 b_init$0 sk_?X_43$0))
             (and (= curr_init$0 null$0) (= old_curr_init$0 b_init$0)))
         Axiom_31$0)
    (not
         (dlseg_struct$0 sk_?X_43$0 next$0 prev$0 curr_init$0 old_curr_init$0
           null$0 b_init$0))))

(assert (or (not Axiom_32$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev_2$0 l2) l1) (not (= (read$0 next_3$0 l1) l2))
                (not (in$0 l1 sk_?X_49$0)) (not (in$0 l2 sk_?X_49$0))))))

(assert (or
    (and (Btwn$0 next_3$0 c_3$0 null$0 null$0)
         (or (and (= null$0 d_4$0) (= c_3$0 null$0))
             (and (= (read$0 next_3$0 d_4$0) null$0)
                  (= (read$0 prev_2$0 c_3$0) null$0) (in$0 d_4$0 sk_?X_46$0)))
         Axiom_33$0)
    (not
         (dlseg_struct$0 sk_?X_46$0 next_3$0 prev_2$0 c_3$0 null$0 null$0
           d_4$0))))

(assert (or (not Axiom_34$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev_2$0 l2) l1) (not (= (read$0 next_3$0 l1) l2))
                (not (in$0 l1 sk_?X_48$0)) (not (in$0 l2 sk_?X_48$0))))))

(assert (or
    (and (= c_3$0 c_4$0) (= c_4$0 d_4$0) (= next_3$0 next_2$0)
         (= old_d_4$0 null$0))
    (and (= next_3$0 (write$0 next_2$0 old_d_4$0 d_4$0))
         (not (= old_d_4$0 null$0)))))

(assert (= FP_3$0 (union$0 FP$0 (setenum$0 tmp_3$0))))

(assert (= a_2$0 a_init$0))

(assert (= c_3$0 c_init$0))

(assert (= curr_5$0 (read$0 next_3$0 curr_4$0)))

(assert (= d_4$0 tmp_3$0))

(assert (= old_curr_4$0 old_curr_init$0))

(assert (= old_d_2$0 old_d_init$0))

(assert (= prev_2$0 (write$0 prev$0 d_4$0 old_d_4$0)))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= emptyset$0 (intersection$0 sk_?X_44$0 sk_?X_43$0)))

(assert (= sk_?X_40$0 FP$0))

(assert (= sk_?X_42$0 (union$0 sk_?X_44$0 sk_?X_43$0)))

(assert (= sk_?X_44$0
  (dlseg_domain$0 next$0 prev$0 a_init$0 null$0 curr_init$0 old_curr_init$0)))

(assert (dlseg_struct$0 sk_?X_41$0 next$0 prev$0 c_init$0 null$0 null$0 d_init$0))

(assert (dlseg_struct$0 sk_?X_44$0 next$0 prev$0 a_init$0 null$0 curr_init$0
  old_curr_init$0))

(assert (= sk_?X_46$0 (dlseg_domain$0 next_3$0 prev_2$0 c_3$0 null$0 null$0 d_4$0)))

(assert (= sk_?X_48$0
  (dlseg_domain$0 next_3$0 prev_2$0 curr_5$0 old_curr_5$0 null$0 b_2$0)))

(assert (= sk_FP_1$0 sk_?X_45$0))

(assert (not (= curr_4$0 null$0)))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a_init$0 l1 curr_init$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a_init$0 null$0 curr_init$0
                     old_curr_init$0))
                 (not (= l1 curr_init$0)))
            (and
                 (or (= l1 curr_init$0)
                     (not (Btwn$0 next$0 a_init$0 l1 curr_init$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a_init$0 null$0
                          curr_init$0 old_curr_init$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_init$0 old_curr_init$0
                     null$0 b_init$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_init$0
                          old_curr_init$0 null$0 b_init$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_3$0 c_3$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next_3$0 prev_2$0 c_3$0 null$0 null$0
                     d_4$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_3$0 c_3$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next_3$0 prev_2$0 c_3$0 null$0 null$0
                          d_4$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) ?y) (not (Btwn$0 ?f ?x ?y ?y))
            (not (in$0 ?y ?X)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (in$0 ?y ?X))
            (in$0 (ep$0 ?f ?X ?x) ?X))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 d_4$0 null$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v d_4$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not (Btwn$0 next$0 ?z d_4$0 d_4$0)))))
                          (and (not (= d_4$0 ?v))
                               (or (Btwn$0 next$0 ?z d_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z d_4$0 d_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u d_4$0)
                               (or (Btwn$0 next$0 null$0 ?v d_4$0)
                                   (and (Btwn$0 next$0 null$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 null$0 d_4$0
                                               d_4$0)))))
                          (and (not (= d_4$0 ?v))
                               (or (Btwn$0 next$0 ?z d_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z d_4$0 d_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 null$0 ?u ?v)
                               (or (Btwn$0 next$0 null$0 ?v d_4$0)
                                   (and (Btwn$0 next$0 null$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 null$0 d_4$0
                                               d_4$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v d_4$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z d_4$0 d_4$0)))))
                 (and (not (= d_4$0 ?v))
                      (or (Btwn$0 next$0 ?z d_4$0 ?v)
                          (and (Btwn$0 next$0 ?z d_4$0 d_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u d_4$0)
                      (or (Btwn$0 next$0 null$0 ?v d_4$0)
                          (and (Btwn$0 next$0 null$0 ?v ?v)
                               (not (Btwn$0 next$0 null$0 d_4$0 d_4$0)))))
                 (and (not (= d_4$0 ?v))
                      (or (Btwn$0 next$0 ?z d_4$0 ?v)
                          (and (Btwn$0 next$0 ?z d_4$0 d_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 null$0 ?u ?v)
                      (or (Btwn$0 next$0 null$0 ?v d_4$0)
                          (and (Btwn$0 next$0 null$0 ?v ?v)
                               (not (Btwn$0 next$0 null$0 d_4$0 d_4$0)))))
                 (not (Btwn$0 (write$0 next$0 d_4$0 null$0) ?z ?u ?v))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next_2$0 old_d_4$0 d_4$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next_2$0 ?z ?u ?v)
                               (or (Btwn$0 next_2$0 ?z ?v old_d_4$0)
                                   (and (Btwn$0 next_2$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next_2$0 ?z old_d_4$0
                                               old_d_4$0)))))
                          (and (not (= old_d_4$0 ?v))
                               (or (Btwn$0 next_2$0 ?z old_d_4$0 ?v)
                                   (and
                                        (Btwn$0 next_2$0 ?z old_d_4$0
                                          old_d_4$0)
                                        (not (Btwn$0 next_2$0 ?z ?v ?v))))
                               (Btwn$0 next_2$0 ?z ?u old_d_4$0)
                               (or (Btwn$0 next_2$0 d_4$0 ?v old_d_4$0)
                                   (and (Btwn$0 next_2$0 d_4$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_2$0 d_4$0 old_d_4$0
                                               old_d_4$0)))))
                          (and (not (= old_d_4$0 ?v))
                               (or (Btwn$0 next_2$0 ?z old_d_4$0 ?v)
                                   (and
                                        (Btwn$0 next_2$0 ?z old_d_4$0
                                          old_d_4$0)
                                        (not (Btwn$0 next_2$0 ?z ?v ?v))))
                               (Btwn$0 next_2$0 d_4$0 ?u ?v)
                               (or (Btwn$0 next_2$0 d_4$0 ?v old_d_4$0)
                                   (and (Btwn$0 next_2$0 d_4$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_2$0 d_4$0 old_d_4$0
                                               old_d_4$0))))))))
             (or
                 (and (Btwn$0 next_2$0 ?z ?u ?v)
                      (or (Btwn$0 next_2$0 ?z ?v old_d_4$0)
                          (and (Btwn$0 next_2$0 ?z ?v ?v)
                               (not (Btwn$0 next_2$0 ?z old_d_4$0 old_d_4$0)))))
                 (and (not (= old_d_4$0 ?v))
                      (or (Btwn$0 next_2$0 ?z old_d_4$0 ?v)
                          (and (Btwn$0 next_2$0 ?z old_d_4$0 old_d_4$0)
                               (not (Btwn$0 next_2$0 ?z ?v ?v))))
                      (Btwn$0 next_2$0 ?z ?u old_d_4$0)
                      (or (Btwn$0 next_2$0 d_4$0 ?v old_d_4$0)
                          (and (Btwn$0 next_2$0 d_4$0 ?v ?v)
                               (not
                                    (Btwn$0 next_2$0 d_4$0 old_d_4$0
                                      old_d_4$0)))))
                 (and (not (= old_d_4$0 ?v))
                      (or (Btwn$0 next_2$0 ?z old_d_4$0 ?v)
                          (and (Btwn$0 next_2$0 ?z old_d_4$0 old_d_4$0)
                               (not (Btwn$0 next_2$0 ?z ?v ?v))))
                      (Btwn$0 next_2$0 d_4$0 ?u ?v)
                      (or (Btwn$0 next_2$0 d_4$0 ?v old_d_4$0)
                          (and (Btwn$0 next_2$0 d_4$0 ?v ?v)
                               (not
                                    (Btwn$0 next_2$0 d_4$0 old_d_4$0
                                      old_d_4$0)))))
                 (not (Btwn$0 (write$0 next_2$0 old_d_4$0 d_4$0) ?z ?u ?v))))))

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
