(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/dl/dl_insert.spl:30:5-6:An invariant might not be maintained by a loop in procedure dl_insert
  tests/spl/dl/dl_insert.spl:25:16-88:Related location: This is the loop invariant that might not be maintained
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
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun Axiom_34$0 () Bool)
(declare-fun Axiom_35$0 () Bool)
(declare-fun Axiom_36$0 () Bool)
(declare-fun Axiom_37$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun c_6$0 () Loc)
(declare-fun c_init$0 () Loc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_5$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun d_5$0 () Loc)
(declare-fun d_init$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun nondet_3$0 () Bool)
(declare-fun nondet_init$0 () Bool)
(declare-fun prev$0 () FldLoc)
(declare-fun prv_4$0 () Loc)
(declare-fun prv_5$0 () Loc)
(declare-fun prv_init$0 () Loc)
(declare-fun sk_?X_95$0 () SetLoc)
(declare-fun sk_?X_96$0 () SetLoc)
(declare-fun sk_?X_97$0 () SetLoc)
(declare-fun sk_?X_98$0 () SetLoc)
(declare-fun sk_?X_99$0 () SetLoc)
(declare-fun sk_?X_100$0 () SetLoc)
(declare-fun sk_?X_101$0 () SetLoc)
(declare-fun sk_?X_102$0 () SetLoc)
(declare-fun sk_FP_1$0 () SetLoc)
(declare-fun sk_l1_3$0 () Loc)
(declare-fun sk_l2_3$0 () Loc)

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

(assert (or
    (and (Btwn$0 next$0 c_6$0 curr_5$0 curr_5$0)
         (or (and (= null$0 prv_5$0) (= c_6$0 curr_5$0))
             (and (= (read$0 next$0 prv_5$0) curr_5$0)
                  (= (read$0 prev$0 c_6$0) null$0)
                  (in$0 prv_5$0 sk_?X_102$0)))
         Axiom_34$0)
    (not
         (dlseg_struct$0 sk_?X_102$0 next$0 prev$0 c_6$0 null$0 curr_5$0
           prv_5$0))))

(assert (or (not Axiom_35$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_98$0)) (not (in$0 l2 sk_?X_98$0))))))

(assert (or
    (and (Btwn$0 next$0 curr_5$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_5$0) null$0)
                  (= (read$0 prev$0 curr_5$0) prv_5$0)
                  (in$0 d_5$0 sk_?X_100$0))
             (and (= curr_5$0 null$0) (= prv_5$0 d_5$0)))
         Axiom_36$0)
    (not
         (dlseg_struct$0 sk_?X_100$0 next$0 prev$0 curr_5$0 prv_5$0 null$0
           d_5$0))))

(assert (or (not Axiom_37$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_96$0)) (not (in$0 l2 sk_?X_96$0))))))

(assert (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= curr_4$0 curr_init$0))

(assert (= d_5$0 d_init$0))

(assert (= prv_4$0 prv_init$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= emptyset$0 emptyset$0))

(assert (= sk_?X_95$0 (union$0 sk_?X_97$0 sk_?X_96$0)))

(assert (= sk_?X_96$0
  (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0 null$0 d_init$0)))

(assert (= sk_?X_98$0
  (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 curr_init$0 prv_init$0)))

(assert (dlseg_struct$0 sk_?X_96$0 next$0 prev$0 curr_init$0 prv_init$0 null$0
  d_init$0))

(assert (not (= curr_init$0 null$0)))

(assert (= sk_?X_100$0 (dlseg_domain$0 next$0 prev$0 curr_5$0 prv_5$0 null$0 d_5$0)))

(assert (= sk_?X_102$0 (dlseg_domain$0 next$0 prev$0 c_6$0 null$0 curr_5$0 prv_5$0)))

(assert (or (= curr_5$0 null$0)
    (in$0 sk_l2_3$0 (intersection$0 sk_?X_101$0 sk_?X_100$0))
    (and (= (read$0 next$0 sk_l1_3$0) sk_l2_3$0) (in$0 sk_l1_3$0 sk_?X_100$0)
         (in$0 sk_l2_3$0 sk_?X_100$0)
         (not (= (read$0 prev$0 sk_l2_3$0) sk_l1_3$0)))
    (and (= (read$0 next$0 sk_l1_3$0) sk_l2_3$0) (in$0 sk_l1_3$0 sk_?X_102$0)
         (in$0 sk_l2_3$0 sk_?X_102$0)
         (not (= (read$0 prev$0 sk_l2_3$0) sk_l1_3$0)))
    (and (in$0 sk_l1_3$0 sk_FP_1$0) (not (in$0 sk_l1_3$0 FP$0)))
    (and (or (not (= null$0 prv_5$0)) (not (= c_6$0 curr_5$0)))
         (or (not (= (read$0 next$0 prv_5$0) curr_5$0))
             (not (= (read$0 prev$0 c_6$0) null$0))
             (not (in$0 prv_5$0 sk_?X_102$0))))
    (and
         (or (not (= (read$0 next$0 d_5$0) null$0))
             (not (= (read$0 prev$0 curr_5$0) prv_5$0))
             (not (in$0 d_5$0 sk_?X_100$0)))
         (or (not (= curr_5$0 null$0)) (not (= prv_5$0 d_5$0))))
    (not (Btwn$0 next$0 c_6$0 curr_5$0 curr_5$0))
    (not (Btwn$0 next$0 curr_5$0 null$0 null$0))))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_init$0 l1 curr_init$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_init$0 null$0 curr_init$0
                     prv_init$0))
                 (not (= l1 curr_init$0)))
            (and
                 (or (= l1 curr_init$0)
                     (not (Btwn$0 next$0 c_init$0 l1 curr_init$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_init$0 null$0
                          curr_init$0 prv_init$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0
                     null$0 d_init$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0
                          null$0 d_init$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (or (in$0 (ep$0 ?f ?X ?x) ?X) (= ?x (ep$0 ?f ?X ?x)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) (ep$0 ?f ?X ?x))))

(assert (or (not Axiom_34$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_102$0)) (not (in$0 l2 sk_?X_102$0))))))

(assert (or
    (and (Btwn$0 next$0 c_init$0 curr_init$0 curr_init$0)
         (or (and (= null$0 prv_init$0) (= c_init$0 curr_init$0))
             (and (= (read$0 next$0 prv_init$0) curr_init$0)
                  (= (read$0 prev$0 c_init$0) null$0)
                  (in$0 prv_init$0 sk_?X_98$0)))
         Axiom_35$0)
    (not
         (dlseg_struct$0 sk_?X_98$0 next$0 prev$0 c_init$0 null$0 curr_init$0
           prv_init$0))))

(assert (or (not Axiom_36$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_100$0)) (not (in$0 l2 sk_?X_100$0))))))

(assert (or
    (and (Btwn$0 next$0 curr_init$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 d_init$0) null$0)
                  (= (read$0 prev$0 curr_init$0) prv_init$0)
                  (in$0 d_init$0 sk_?X_96$0))
             (and (= curr_init$0 null$0) (= prv_init$0 d_init$0)))
         Axiom_37$0)
    (not
         (dlseg_struct$0 sk_?X_96$0 next$0 prev$0 curr_init$0 prv_init$0
           null$0 d_init$0))))

(assert (= c_6$0 c_init$0))

(assert (= curr_5$0 (read$0 next$0 curr_4$0)))

(assert (= nondet_3$0 nondet_init$0))

(assert (= prv_5$0 curr_4$0))

(assert nondet_3$0)

(assert (= emptyset$0 (intersection$0 sk_?X_97$0 sk_?X_96$0)))

(assert (= sk_?X_95$0 FP$0))

(assert (= sk_?X_97$0 sk_?X_98$0))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (dlseg_struct$0 sk_?X_98$0 next$0 prev$0 c_init$0 null$0 curr_init$0
  prv_init$0))

(assert (= sk_?X_99$0 (union$0 sk_?X_101$0 sk_?X_100$0)))

(assert (= sk_?X_101$0 sk_?X_102$0))

(assert (= sk_FP_1$0 sk_?X_99$0))

(assert (not (= (read$0 next$0 curr_4$0) null$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 c_6$0 l1 curr_5$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 c_6$0 null$0 curr_5$0
                     prv_5$0))
                 (not (= l1 curr_5$0)))
            (and (or (= l1 curr_5$0) (not (Btwn$0 next$0 c_6$0 l1 curr_5$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 c_6$0 null$0 curr_5$0
                          prv_5$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_5$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_5$0 prv_5$0 null$0
                     d_5$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next$0 curr_5$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_5$0 prv_5$0 null$0
                          d_5$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) ?y) (not (Btwn$0 ?f ?x ?y ?y))
            (not (in$0 ?y ?X)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (in$0 ?y ?X))
            (in$0 (ep$0 ?f ?X ?x) ?X))))

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
