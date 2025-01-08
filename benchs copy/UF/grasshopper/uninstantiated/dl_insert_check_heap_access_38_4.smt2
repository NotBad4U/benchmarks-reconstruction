(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/dl/dl_insert.spl:38:4-20:Possible heap access through null or dangling reference
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
(declare-fun Axiom_21$0 () Bool)
(declare-fun Axiom_22$0 () Bool)
(declare-fun Axiom_23$0 () Bool)
(declare-fun Axiom_24$0 () Bool)
(declare-fun Axiom_25$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_1$0 () SetLoc)
(declare-fun FP_2$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_1$0 () SetLoc)
(declare-fun a$0 () Loc)
(declare-fun b$0 () Loc)
(declare-fun c_1$0 () Loc)
(declare-fun c_2$0 () Loc)
(declare-fun c_3$0 () Loc)
(declare-fun curr_2$0 () Loc)
(declare-fun curr_3$0 () Loc)
(declare-fun d_1$0 () Loc)
(declare-fun d_2$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun elt$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_1$0 () FldLoc)
(declare-fun next_2$0 () FldLoc)
(declare-fun nondet_2$0 () Bool)
(declare-fun prev$0 () FldLoc)
(declare-fun prev_1$0 () FldLoc)
(declare-fun prv_2$0 () Loc)
(declare-fun prv_3$0 () Loc)
(declare-fun sk_?X_53$0 () SetLoc)
(declare-fun sk_?X_54$0 () SetLoc)
(declare-fun sk_?X_55$0 () SetLoc)
(declare-fun sk_?X_56$0 () SetLoc)
(declare-fun sk_?X_57$0 () SetLoc)
(declare-fun sk_?X_58$0 () SetLoc)
(declare-fun sk_?X_59$0 () SetLoc)
(declare-fun sk_?X_60$0 () SetLoc)
(declare-fun sk_?X_61$0 () SetLoc)
(declare-fun sk_?X_62$0 () SetLoc)
(declare-fun sk_?X_63$0 () SetLoc)
(declare-fun sk_?X_64$0 () SetLoc)
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
(declare-fun t_117$0 () Loc)
(declare-fun t_118$0 () Loc)
(declare-fun t_119$0 () Loc)
(declare-fun t_120$0 () Loc)
(declare-fun t_121$0 () Loc)
(declare-fun t_122$0 () Loc)
(declare-fun t_123$0 () Loc)
(declare-fun t_124$0 () Loc)
(declare-fun t_125$0 () Loc)
(declare-fun t_126$0 () Loc)
(declare-fun t_127$0 () Loc)
(declare-fun t_128$0 () Loc)
(declare-fun t_129$0 () Loc)
(declare-fun t_130$0 () Loc)
(declare-fun t_131$0 () Loc)

(assert (= (ep$0 prev$0 FP_1$0 prv_3$0) t_131$0))

(assert (= (ep$0 prev$0 FP_1$0 prv_2$0) t_130$0))

(assert (= (ep$0 prev$0 FP_1$0 elt$0) t_129$0))

(assert (= (ep$0 prev$0 FP_1$0 d_2$0) t_128$0))

(assert (= (ep$0 prev$0 FP_1$0 d_1$0) t_127$0))

(assert (= (ep$0 prev$0 FP_1$0 curr_3$0) t_126$0))

(assert (= (ep$0 prev$0 FP_1$0 curr_2$0) t_125$0))

(assert (= (ep$0 prev$0 FP_1$0 c_2$0) t_124$0))

(assert (= (ep$0 prev$0 FP_1$0 c_1$0) t_123$0))

(assert (= (ep$0 prev$0 FP_1$0 b$0) t_122$0))

(assert (= (ep$0 prev$0 FP_1$0 a$0) t_121$0))

(assert (= (ep$0 prev$0 FP_1$0 null$0) t_120$0))

(assert (= (ep$0 next$0 FP_1$0 prv_3$0) t_119$0))

(assert (= (ep$0 next$0 FP_1$0 prv_2$0) t_118$0))

(assert (= (ep$0 next$0 FP_1$0 elt$0) t_117$0))

(assert (= (ep$0 next$0 FP_1$0 d_2$0) t_116$0))

(assert (= (ep$0 next$0 FP_1$0 d_1$0) t_115$0))

(assert (= (ep$0 next$0 FP_1$0 curr_3$0) t_114$0))

(assert (= (ep$0 next$0 FP_1$0 curr_2$0) t_113$0))

(assert (= (ep$0 next$0 FP_1$0 c_2$0) t_112$0))

(assert (= (ep$0 next$0 FP_1$0 c_1$0) t_111$0))

(assert (= (ep$0 next$0 FP_1$0 b$0) t_110$0))

(assert (= (ep$0 next$0 FP_1$0 a$0) t_109$0))

(assert (= (ep$0 next$0 FP_1$0 null$0) t_108$0))

(assert (= (read$0 next_1$0 prv_3$0) t_107$0))

(assert (= (read$0 (write$0 prev$0 curr_3$0 elt$0) curr_3$0) t_106$0))

(assert (= (read$0 (write$0 prev$0 curr_3$0 elt$0) curr_2$0) t_105$0))

(assert (= (read$0 (write$0 prev$0 curr_3$0 elt$0) c_2$0) t_104$0))

(assert (= (read$0 (write$0 prev$0 curr_3$0 elt$0) c_1$0) t_103$0))

(assert (= (read$0 (write$0 prev$0 curr_3$0 elt$0) a$0) t_102$0))

(assert (= (read$0 (write$0 next_1$0 prv_3$0 elt$0) prv_3$0) t_101$0))

(assert (= (read$0 (write$0 next$0 elt$0 curr_3$0) prv_3$0) t_100$0))

(assert (= (read$0 (write$0 next$0 elt$0 curr_3$0) prv_2$0) t_99$0))

(assert (= (read$0 (write$0 next$0 elt$0 curr_3$0) elt$0) t_98$0))

(assert (= (read$0 (write$0 next$0 elt$0 curr_3$0) d_2$0) t_97$0))

(assert (= (read$0 (write$0 next$0 elt$0 curr_3$0) d_1$0) t_96$0))

(assert (= (read$0 (write$0 next$0 elt$0 curr_3$0) curr_3$0) t_95$0))

(assert (= (read$0 (write$0 next$0 elt$0 curr_3$0) b$0) t_94$0))

(assert (forall ((?d_13 Loc) (?x Loc) (?y Loc))
        (or (= ?y ?x)
            (= (read$0 prev$0 ?y) (read$0 (write$0 prev$0 ?x ?d_13) ?y)))))

(assert (forall ((?d_13 Loc) (?x Loc))
        (= (read$0 (write$0 prev$0 ?x ?d_13) ?x) ?d_13)))

(assert (forall ((?d_12 Loc) (?x Loc) (?y Loc))
        (or (= ?y ?x)
            (= (read$0 next_1$0 ?y) (read$0 (write$0 next_1$0 ?x ?d_12) ?y)))))

(assert (forall ((?d_12 Loc) (?x Loc))
        (= (read$0 (write$0 next_1$0 ?x ?d_12) ?x) ?d_12)))

(assert (forall ((?d_11 Loc) (?x Loc) (?y Loc))
        (or (= ?y ?x)
            (= (read$0 next$0 ?y) (read$0 (write$0 next$0 ?x ?d_11) ?y)))))

(assert (forall ((?d_11 Loc) (?x Loc))
        (= (read$0 (write$0 next$0 ?x ?d_11) ?x) ?d_11)))

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

(assert (or (= (read$0 next$0 curr_3$0) null$0) (not nondet_2$0)))

(assert (or (not Axiom_21$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_64$0)) (not (in$0 l2 sk_?X_64$0))))))

(assert (or
    (and (Btwn$0 next$0 c_1$0 curr_2$0 curr_2$0)
         (or (and (= null$0 prv_2$0) (= c_1$0 curr_2$0))
             (and (= (read$0 next$0 prv_2$0) curr_2$0)
                  (= (read$0 prev$0 c_1$0) null$0) (in$0 prv_2$0 sk_?X_60$0)))
         Axiom_22$0)
    (not
         (dlseg_struct$0 sk_?X_60$0 next$0 prev$0 c_1$0 null$0 curr_2$0
           prv_2$0))))

(assert (or (not Axiom_23$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_53$0)) (not (in$0 l2 sk_?X_53$0))))))

(assert (or
    (and (Btwn$0 next$0 curr_2$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_1$0) null$0)
                  (= (read$0 prev$0 curr_2$0) prv_2$0)
                  (in$0 d_1$0 sk_?X_58$0))
             (and (= curr_2$0 null$0) (= prv_2$0 d_1$0)))
         Axiom_24$0)
    (not
         (dlseg_struct$0 sk_?X_58$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
           d_1$0))))

(assert (or (not Axiom_25$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_55$0)) (not (in$0 l2 sk_?X_55$0))))))

(assert (or
    (and (= c_2$0 c_3$0) (= c_3$0 elt$0) (= next_2$0 next_1$0)
         (= prv_3$0 null$0))
    (and (= next_2$0 (write$0 next_1$0 prv_3$0 elt$0))
         (not (= prv_3$0 null$0)))))

(assert (= FP_Caller_1$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= c_2$0 c_1$0))

(assert (= d_1$0 b$0))

(assert (= next_1$0 (write$0 next$0 elt$0 curr_3$0)))

(assert (= prv_2$0 null$0))

(assert (Frame$0 FP_1$0 Alloc$0 prev$0 prev$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= emptyset$0 emptyset$0))

(assert (= sk_?X_61$0 (union$0 sk_?X_64$0 sk_?X_62$0)))

(assert (= sk_?X_62$0 sk_?X_63$0))

(assert (= sk_?X_64$0 (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))

(assert (dlseg_struct$0 sk_?X_64$0 next$0 prev$0 a$0 null$0 null$0 b$0))

(assert (= emptyset$0 (intersection$0 sk_?X_54$0 sk_?X_55$0)))

(assert (= sk_?X_54$0 sk_?X_53$0))

(assert (= sk_?X_56$0
  (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0))))

(assert (dlseg_struct$0 sk_?X_53$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0))

(assert (not (= curr_3$0 null$0)))

(assert (= emptyset$0 (intersection$0 sk_?X_59$0 sk_?X_58$0)))

(assert (= sk_?X_57$0 FP_1$0))

(assert (= sk_?X_59$0 sk_?X_60$0))

(assert (= FP$0 (union$0 FP_1$0 FP$0)))

(assert (dlseg_struct$0 sk_?X_60$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0))

(assert (not (= a$0 null$0)))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 a$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 a$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 a$0 null$0 null$0 b$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_2$0 l1 curr_3$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0
                     prv_3$0))
                 (not (= l1 curr_3$0)))
            (and (or (= l1 curr_3$0) (not (Btwn$0 next$0 c_2$0 l1 curr_3$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0
                          prv_3$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_3$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
                     d_2$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_3$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
                          d_2$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (or (in$0 (ep$0 ?f ?X ?x) ?X) (= ?x (ep$0 ?f ?X ?x)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) (ep$0 ?f ?X ?x))))

(assert (or
    (and (Btwn$0 next$0 a$0 null$0 null$0)
         (or (and (= null$0 b$0) (= a$0 null$0))
             (and (= (read$0 next$0 b$0) null$0)
                  (= (read$0 prev$0 a$0) null$0) (in$0 b$0 sk_?X_64$0)))
         Axiom_21$0)
    (not (dlseg_struct$0 sk_?X_64$0 next$0 prev$0 a$0 null$0 null$0 b$0))))

(assert (or (not Axiom_22$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_60$0)) (not (in$0 l2 sk_?X_60$0))))))

(assert (or
    (and (Btwn$0 next$0 c_2$0 curr_3$0 curr_3$0)
         (or (and (= null$0 prv_3$0) (= c_2$0 curr_3$0))
             (and (= (read$0 next$0 prv_3$0) curr_3$0)
                  (= (read$0 prev$0 c_2$0) null$0) (in$0 prv_3$0 sk_?X_53$0)))
         Axiom_23$0)
    (not
         (dlseg_struct$0 sk_?X_53$0 next$0 prev$0 c_2$0 null$0 curr_3$0
           prv_3$0))))

(assert (or (not Axiom_24$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_58$0)) (not (in$0 l2 sk_?X_58$0))))))

(assert (or
    (and (Btwn$0 next$0 curr_3$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_2$0) null$0)
                  (= (read$0 prev$0 curr_3$0) prv_3$0)
                  (in$0 d_2$0 sk_?X_55$0))
             (and (= curr_3$0 null$0) (= prv_3$0 d_2$0)))
         Axiom_25$0)
    (not
         (dlseg_struct$0 sk_?X_55$0 next$0 prev$0 curr_3$0 prv_3$0 null$0
           d_2$0))))

(assert (= FP_2$0
  (union$0 (setminus$0 FP$0 FP_1$0)
    (union$0 (intersection$0 Alloc$0 FP_1$0) (setminus$0 Alloc$0 Alloc$0)))))

(assert (= c_1$0 a$0))

(assert (= curr_2$0 c_1$0))

(assert (= d_2$0 d_1$0))

(assert (= prev_1$0 (write$0 prev$0 curr_3$0 elt$0)))

(assert (Frame$0 FP_1$0 Alloc$0 next$0 next$0))

(assert (= Alloc$0 (union$0 FP_2$0 Alloc$0)))

(assert (= (read$0 next$0 elt$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_64$0 sk_?X_62$0)))

(assert (= sk_?X_61$0 FP$0))

(assert (= sk_?X_63$0 (setenum$0 elt$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (= emptyset$0 emptyset$0))

(assert (= sk_?X_53$0 (dlseg_domain$0 next$0 prev$0 c_2$0 null$0 curr_3$0 prv_3$0)))

(assert (= sk_?X_55$0 (dlseg_domain$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0)))

(assert (= sk_?X_56$0 (union$0 sk_?X_54$0 sk_?X_55$0)))

(assert (dlseg_struct$0 sk_?X_55$0 next$0 prev$0 curr_3$0 prv_3$0 null$0 d_2$0))

(assert (= emptyset$0 emptyset$0))

(assert (= sk_?X_57$0 (union$0 sk_?X_59$0 sk_?X_58$0)))

(assert (= sk_?X_58$0 (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0)))

(assert (= sk_?X_60$0 (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0 prv_2$0)))

(assert (dlseg_struct$0 sk_?X_58$0 next$0 prev$0 curr_2$0 prv_2$0 null$0 d_1$0))

(assert (not (= curr_2$0 null$0)))

(assert (not (in$0 null$0 Alloc$0)))

(assert (not (in$0 elt$0 FP_2$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_1$0 l1 curr_2$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0
                     prv_2$0))
                 (not (= l1 curr_2$0)))
            (and (or (= l1 curr_2$0) (not (Btwn$0 next$0 c_1$0 l1 curr_2$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_1$0 null$0 curr_2$0
                          prv_2$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_2$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
                     d_1$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_2$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_2$0 prv_2$0 null$0
                          d_1$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) ?y) (not (Btwn$0 ?f ?x ?y ?y))
            (not (in$0 ?y ?X)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (in$0 ?y ?X))
            (in$0 (ep$0 ?f ?X ?x) ?X))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 elt$0 curr_3$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v elt$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not (Btwn$0 next$0 ?z elt$0 elt$0)))))
                          (and (not (= elt$0 ?v))
                               (or (Btwn$0 next$0 ?z elt$0 ?v)
                                   (and (Btwn$0 next$0 ?z elt$0 elt$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u elt$0)
                               (or (Btwn$0 next$0 curr_3$0 ?v elt$0)
                                   (and (Btwn$0 next$0 curr_3$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 curr_3$0 elt$0
                                               elt$0)))))
                          (and (not (= elt$0 ?v))
                               (or (Btwn$0 next$0 ?z elt$0 ?v)
                                   (and (Btwn$0 next$0 ?z elt$0 elt$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 curr_3$0 ?u ?v)
                               (or (Btwn$0 next$0 curr_3$0 ?v elt$0)
                                   (and (Btwn$0 next$0 curr_3$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 curr_3$0 elt$0
                                               elt$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v elt$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z elt$0 elt$0)))))
                 (and (not (= elt$0 ?v))
                      (or (Btwn$0 next$0 ?z elt$0 ?v)
                          (and (Btwn$0 next$0 ?z elt$0 elt$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u elt$0)
                      (or (Btwn$0 next$0 curr_3$0 ?v elt$0)
                          (and (Btwn$0 next$0 curr_3$0 ?v ?v)
                               (not (Btwn$0 next$0 curr_3$0 elt$0 elt$0)))))
                 (and (not (= elt$0 ?v))
                      (or (Btwn$0 next$0 ?z elt$0 ?v)
                          (and (Btwn$0 next$0 ?z elt$0 elt$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 curr_3$0 ?u ?v)
                      (or (Btwn$0 next$0 curr_3$0 ?v elt$0)
                          (and (Btwn$0 next$0 curr_3$0 ?v ?v)
                               (not (Btwn$0 next$0 curr_3$0 elt$0 elt$0)))))
                 (not (Btwn$0 (write$0 next$0 elt$0 curr_3$0) ?z ?u ?v))))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next_1$0 prv_3$0 elt$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next_1$0 ?z ?u ?v)
                               (or (Btwn$0 next_1$0 ?z ?v prv_3$0)
                                   (and (Btwn$0 next_1$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next_1$0 ?z prv_3$0
                                               prv_3$0)))))
                          (and (not (= prv_3$0 ?v))
                               (or (Btwn$0 next_1$0 ?z prv_3$0 ?v)
                                   (and (Btwn$0 next_1$0 ?z prv_3$0 prv_3$0)
                                        (not (Btwn$0 next_1$0 ?z ?v ?v))))
                               (Btwn$0 next_1$0 ?z ?u prv_3$0)
                               (or (Btwn$0 next_1$0 elt$0 ?v prv_3$0)
                                   (and (Btwn$0 next_1$0 elt$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_1$0 elt$0 prv_3$0
                                               prv_3$0)))))
                          (and (not (= prv_3$0 ?v))
                               (or (Btwn$0 next_1$0 ?z prv_3$0 ?v)
                                   (and (Btwn$0 next_1$0 ?z prv_3$0 prv_3$0)
                                        (not (Btwn$0 next_1$0 ?z ?v ?v))))
                               (Btwn$0 next_1$0 elt$0 ?u ?v)
                               (or (Btwn$0 next_1$0 elt$0 ?v prv_3$0)
                                   (and (Btwn$0 next_1$0 elt$0 ?v ?v)
                                        (not
                                             (Btwn$0 next_1$0 elt$0 prv_3$0
                                               prv_3$0))))))))
             (or
                 (and (Btwn$0 next_1$0 ?z ?u ?v)
                      (or (Btwn$0 next_1$0 ?z ?v prv_3$0)
                          (and (Btwn$0 next_1$0 ?z ?v ?v)
                               (not (Btwn$0 next_1$0 ?z prv_3$0 prv_3$0)))))
                 (and (not (= prv_3$0 ?v))
                      (or (Btwn$0 next_1$0 ?z prv_3$0 ?v)
                          (and (Btwn$0 next_1$0 ?z prv_3$0 prv_3$0)
                               (not (Btwn$0 next_1$0 ?z ?v ?v))))
                      (Btwn$0 next_1$0 ?z ?u prv_3$0)
                      (or (Btwn$0 next_1$0 elt$0 ?v prv_3$0)
                          (and (Btwn$0 next_1$0 elt$0 ?v ?v)
                               (not (Btwn$0 next_1$0 elt$0 prv_3$0 prv_3$0)))))
                 (and (not (= prv_3$0 ?v))
                      (or (Btwn$0 next_1$0 ?z prv_3$0 ?v)
                          (and (Btwn$0 next_1$0 ?z prv_3$0 prv_3$0)
                               (not (Btwn$0 next_1$0 ?z ?v ?v))))
                      (Btwn$0 next_1$0 elt$0 ?u ?v)
                      (or (Btwn$0 next_1$0 elt$0 ?v prv_3$0)
                          (and (Btwn$0 next_1$0 elt$0 ?v ?v)
                               (not (Btwn$0 next_1$0 elt$0 prv_3$0 prv_3$0)))))
                 (not (Btwn$0 (write$0 next_1$0 prv_3$0 elt$0) ?z ?u ?v))))))

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
