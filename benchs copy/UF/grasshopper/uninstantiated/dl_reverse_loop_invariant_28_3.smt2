(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/dl/dl_reverse.spl:28:3-4:An invariant might not be maintained by a loop in procedure dl_reverse
  tests/spl/dl/dl_reverse.spl:19:14:Related location: This is the loop invariant that might not be maintained
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
(declare-fun Axiom_19$0 () Bool)
(declare-fun Axiom_20$0 () Bool)
(declare-fun Axiom_21$0 () Bool)
(declare-fun Axiom_22$0 () Bool)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_2$0 () SetLoc)
(declare-fun curr_4$0 () Loc)
(declare-fun curr_5$0 () Loc)
(declare-fun curr_init$0 () Loc)
(declare-fun dlseg_domain$0 (FldLoc FldLoc Loc Loc Loc Loc) SetLoc)
(declare-fun dlseg_struct$0 (SetLoc FldLoc FldLoc Loc Loc Loc Loc) Bool)
(declare-fun end_2$0 () Loc)
(declare-fun end_init$0 () Loc)
(declare-fun next$0 () FldLoc)
(declare-fun next_2$0 () FldLoc)
(declare-fun prev$0 () FldLoc)
(declare-fun prev_2$0 () FldLoc)
(declare-fun prv_4$0 () Loc)
(declare-fun prv_5$0 () Loc)
(declare-fun prv_init$0 () Loc)
(declare-fun sk_?X_21$0 () SetLoc)
(declare-fun sk_?X_22$0 () SetLoc)
(declare-fun sk_?X_23$0 () SetLoc)
(declare-fun sk_?X_24$0 () SetLoc)
(declare-fun sk_?X_25$0 () SetLoc)
(declare-fun sk_?X_26$0 () SetLoc)
(declare-fun sk_FP_1$0 () SetLoc)
(declare-fun sk_l1_2$0 () Loc)
(declare-fun sk_l2_2$0 () Loc)
(declare-fun start_2$0 () Loc)
(declare-fun start_init$0 () Loc)
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
(declare-fun tmp_2$0 () Loc)
(declare-fun tmp_4$0 () Loc)
(declare-fun tmp_init$0 () Loc)

(assert (= (read$0 prev$0 sk_l2_2$0) t_56$0))

(assert (= (read$0 prev$0 prv_5$0) t_55$0))

(assert (= (read$0 prev$0 curr_5$0) t_54$0))

(assert (= (read$0 next$0 tmp_4$0) t_53$0))

(assert (= (read$0 next$0 start_2$0) t_52$0))

(assert (= (read$0 next$0 sk_l1_2$0) t_51$0))

(assert (= (read$0 next$0 end_2$0) t_50$0))

(assert (= (read$0 (write$0 prev$0 prv_5$0 curr_5$0) sk_l2_2$0) t_49$0))

(assert (= (read$0 (write$0 prev$0 prv_5$0 curr_5$0) prv_init$0) t_48$0))

(assert (= (read$0 (write$0 prev$0 prv_5$0 curr_5$0) prv_5$0) t_47$0))

(assert (= (read$0 (write$0 prev$0 prv_5$0 curr_5$0) curr_init$0) t_46$0))

(assert (= (read$0 (write$0 prev$0 prv_5$0 curr_5$0) curr_5$0) t_45$0))

(assert (= (read$0 (write$0 next$0 tmp_4$0 prv_4$0) tmp_4$0) t_44$0))

(assert (= (read$0 (write$0 next$0 tmp_4$0 prv_4$0) start_init$0) t_43$0))

(assert (= (read$0 (write$0 next$0 tmp_4$0 prv_4$0) start_2$0) t_42$0))

(assert (= (read$0 (write$0 next$0 tmp_4$0 prv_4$0) sk_l1_2$0) t_41$0))

(assert (= (read$0 (write$0 next$0 tmp_4$0 prv_4$0) end_init$0) t_40$0))

(assert (= (read$0 (write$0 next$0 tmp_4$0 prv_4$0) end_2$0) t_39$0))

(assert (= (read$0 (write$0 next$0 tmp_4$0 prv_4$0) curr_4$0) t_38$0))

(assert (forall ((?d_8 Loc) (?x Loc) (?y Loc))
        (or (= ?y ?x)
            (= (read$0 prev$0 ?y) (read$0 (write$0 prev$0 ?x ?d_8) ?y)))))

(assert (forall ((?d_8 Loc) (?x Loc)) (= (read$0 (write$0 prev$0 ?x ?d_8) ?x) ?d_8)))

(assert (forall ((?d_7 Loc) (?x Loc) (?y Loc))
        (or (= ?y ?x)
            (= (read$0 next$0 ?y) (read$0 (write$0 next$0 ?x ?d_7) ?y)))))

(assert (forall ((?d_7 Loc) (?x Loc)) (= (read$0 (write$0 next$0 ?x ?d_7) ?x) ?d_7)))

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
    (and (Btwn$0 next$0 curr_init$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 end_init$0) null$0)
                  (= (read$0 prev$0 curr_init$0) prv_init$0)
                  (in$0 end_init$0 sk_?X_23$0))
             (and (= curr_init$0 null$0) (= prv_init$0 end_init$0)))
         Axiom_19$0)
    (not
         (dlseg_struct$0 sk_?X_23$0 next$0 prev$0 curr_init$0 prv_init$0
           null$0 end_init$0))))

(assert (or (not Axiom_20$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_22$0)) (not (in$0 l2 sk_?X_22$0))))))

(assert (or
    (and (Btwn$0 next_2$0 curr_5$0 null$0 null$0)
         (or
             (and (= (read$0 next_2$0 end_2$0) null$0)
                  (= (read$0 prev_2$0 curr_5$0) prv_5$0)
                  (in$0 end_2$0 sk_?X_26$0))
             (and (= curr_5$0 null$0) (= prv_5$0 end_2$0)))
         Axiom_21$0)
    (not
         (dlseg_struct$0 sk_?X_26$0 next_2$0 prev_2$0 curr_5$0 prv_5$0 null$0
           end_2$0))))

(assert (or (not Axiom_22$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev_2$0 l2) l1) (not (= (read$0 next_2$0 l1) l2))
                (not (in$0 l1 sk_?X_25$0)) (not (in$0 l2 sk_?X_25$0))))))

(assert (= FP_Caller_2$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= curr_5$0 (read$0 next$0 curr_4$0)))

(assert (= next_2$0 (write$0 next$0 tmp_4$0 prv_4$0)))

(assert (= prv_4$0 prv_init$0))

(assert (= start_2$0 start_init$0))

(assert (= tmp_4$0 curr_4$0))

(assert (= emptyset$0 (intersection$0 sk_?X_23$0 sk_?X_22$0)))

(assert (= sk_?X_21$0 FP$0))

(assert (= sk_?X_23$0
  (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0 null$0 end_init$0)))

(assert (dlseg_struct$0 sk_?X_22$0 next$0 prev$0 prv_init$0 curr_init$0 null$0
  start_init$0))

(assert (= sk_?X_24$0 (union$0 sk_?X_26$0 sk_?X_25$0)))

(assert (= sk_?X_26$0
  (dlseg_domain$0 next_2$0 prev_2$0 curr_5$0 prv_5$0 null$0 end_2$0)))

(assert (or (in$0 sk_l2_2$0 (intersection$0 sk_?X_26$0 sk_?X_25$0))
    (and (= (read$0 next_2$0 sk_l1_2$0) sk_l2_2$0)
         (in$0 sk_l1_2$0 sk_?X_25$0) (in$0 sk_l2_2$0 sk_?X_25$0)
         (not (= (read$0 prev_2$0 sk_l2_2$0) sk_l1_2$0)))
    (and (= (read$0 next_2$0 sk_l1_2$0) sk_l2_2$0)
         (in$0 sk_l1_2$0 sk_?X_26$0) (in$0 sk_l2_2$0 sk_?X_26$0)
         (not (= (read$0 prev_2$0 sk_l2_2$0) sk_l1_2$0)))
    (and (in$0 sk_l1_2$0 sk_FP_1$0) (not (in$0 sk_l1_2$0 FP$0)))
    (and
         (or (not (= (read$0 next_2$0 end_2$0) null$0))
             (not (= (read$0 prev_2$0 curr_5$0) prv_5$0))
             (not (in$0 end_2$0 sk_?X_26$0)))
         (or (not (= curr_5$0 null$0)) (not (= prv_5$0 end_2$0))))
    (and
         (or (not (= (read$0 next_2$0 start_2$0) null$0))
             (not (= (read$0 prev_2$0 prv_5$0) curr_5$0))
             (not (in$0 start_2$0 sk_?X_25$0)))
         (or (not (= curr_5$0 start_2$0)) (not (= prv_5$0 null$0))))
    (not (Btwn$0 next_2$0 curr_5$0 null$0 null$0))
    (not (Btwn$0 next_2$0 prv_5$0 null$0 null$0))))

(assert (not (in$0 null$0 Alloc$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 prv_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 prv_init$0 curr_init$0
                     null$0 start_init$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 prv_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 prv_init$0 curr_init$0
                          null$0 start_init$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_2$0 prv_5$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next_2$0 prev_2$0 prv_5$0 curr_5$0 null$0
                     start_2$0))
                 (not (= l1 null$0)))
            (and (or (= l1 null$0) (not (Btwn$0 next_2$0 prv_5$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next_2$0 prev_2$0 prv_5$0 curr_5$0
                          null$0 start_2$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (or (in$0 (ep$0 ?f ?X ?x) ?X) (= ?x (ep$0 ?f ?X ?x)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) (ep$0 ?f ?X ?x))))

(assert (or (not Axiom_19$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev$0 l2) l1) (not (= (read$0 next$0 l1) l2))
                (not (in$0 l1 sk_?X_23$0)) (not (in$0 l2 sk_?X_23$0))))))

(assert (or
    (and (Btwn$0 next$0 prv_init$0 null$0 null$0)
         (or
             (and (= (read$0 next$0 start_init$0) null$0)
                  (= (read$0 prev$0 prv_init$0) curr_init$0)
                  (in$0 start_init$0 sk_?X_22$0))
             (and (= curr_init$0 start_init$0) (= prv_init$0 null$0)))
         Axiom_20$0)
    (not
         (dlseg_struct$0 sk_?X_22$0 next$0 prev$0 prv_init$0 curr_init$0
           null$0 start_init$0))))

(assert (or (not Axiom_21$0)
    (forall ((l1 Loc) (l2 Loc))
            (or (= (read$0 prev_2$0 l2) l1) (not (= (read$0 next_2$0 l1) l2))
                (not (in$0 l1 sk_?X_26$0)) (not (in$0 l2 sk_?X_26$0))))))

(assert (or
    (and (Btwn$0 next_2$0 prv_5$0 null$0 null$0)
         (or
             (and (= (read$0 next_2$0 start_2$0) null$0)
                  (= (read$0 prev_2$0 prv_5$0) curr_5$0)
                  (in$0 start_2$0 sk_?X_25$0))
             (and (= curr_5$0 start_2$0) (= prv_5$0 null$0)))
         Axiom_22$0)
    (not
         (dlseg_struct$0 sk_?X_25$0 next_2$0 prev_2$0 prv_5$0 curr_5$0 null$0
           start_2$0))))

(assert (= curr_4$0 curr_init$0))

(assert (= end_2$0 end_init$0))

(assert (= prev_2$0 (write$0 prev$0 prv_5$0 curr_5$0)))

(assert (= prv_5$0 tmp_4$0))

(assert (= tmp_2$0 tmp_init$0))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= sk_?X_21$0 (union$0 sk_?X_23$0 sk_?X_22$0)))

(assert (= sk_?X_22$0
  (dlseg_domain$0 next$0 prev$0 prv_init$0 curr_init$0 null$0 start_init$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (dlseg_struct$0 sk_?X_23$0 next$0 prev$0 curr_init$0 prv_init$0 null$0
  end_init$0))

(assert (= sk_?X_25$0
  (dlseg_domain$0 next_2$0 prev_2$0 prv_5$0 curr_5$0 null$0 start_2$0)))

(assert (= sk_FP_1$0 sk_?X_24$0))

(assert (not (= curr_4$0 null$0)))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next$0 curr_init$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0
                     null$0 end_init$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next$0 curr_init$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next$0 prev$0 curr_init$0 prv_init$0
                          null$0 end_init$0)))))))

(assert (forall ((l1 Loc))
        (or
            (and (Btwn$0 next_2$0 curr_5$0 l1 null$0)
                 (in$0 l1
                   (dlseg_domain$0 next_2$0 prev_2$0 curr_5$0 prv_5$0 null$0
                     end_2$0))
                 (not (= l1 null$0)))
            (and
                 (or (= l1 null$0)
                     (not (Btwn$0 next_2$0 curr_5$0 l1 null$0)))
                 (not
                      (in$0 l1
                        (dlseg_domain$0 next_2$0 prev_2$0 curr_5$0 prv_5$0
                          null$0 end_2$0)))))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) ?y) (not (Btwn$0 ?f ?x ?y ?y))
            (not (in$0 ?y ?X)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc) (?y Loc))
        (or (not (Btwn$0 ?f ?x ?y ?y)) (not (in$0 ?y ?X))
            (in$0 (ep$0 ?f ?X ?x) ?X))))

(assert (forall ((?u Loc) (?v Loc) (?z Loc))
        (and
             (or (Btwn$0 (write$0 next$0 tmp_4$0 prv_4$0) ?z ?u ?v)
                 (not
                      (or
                          (and (Btwn$0 next$0 ?z ?u ?v)
                               (or (Btwn$0 next$0 ?z ?v tmp_4$0)
                                   (and (Btwn$0 next$0 ?z ?v ?v)
                                        (not
                                             (Btwn$0 next$0 ?z tmp_4$0
                                               tmp_4$0)))))
                          (and (not (= tmp_4$0 ?v))
                               (or (Btwn$0 next$0 ?z tmp_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z tmp_4$0 tmp_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 ?z ?u tmp_4$0)
                               (or (Btwn$0 next$0 prv_4$0 ?v tmp_4$0)
                                   (and (Btwn$0 next$0 prv_4$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 prv_4$0 tmp_4$0
                                               tmp_4$0)))))
                          (and (not (= tmp_4$0 ?v))
                               (or (Btwn$0 next$0 ?z tmp_4$0 ?v)
                                   (and (Btwn$0 next$0 ?z tmp_4$0 tmp_4$0)
                                        (not (Btwn$0 next$0 ?z ?v ?v))))
                               (Btwn$0 next$0 prv_4$0 ?u ?v)
                               (or (Btwn$0 next$0 prv_4$0 ?v tmp_4$0)
                                   (and (Btwn$0 next$0 prv_4$0 ?v ?v)
                                        (not
                                             (Btwn$0 next$0 prv_4$0 tmp_4$0
                                               tmp_4$0))))))))
             (or
                 (and (Btwn$0 next$0 ?z ?u ?v)
                      (or (Btwn$0 next$0 ?z ?v tmp_4$0)
                          (and (Btwn$0 next$0 ?z ?v ?v)
                               (not (Btwn$0 next$0 ?z tmp_4$0 tmp_4$0)))))
                 (and (not (= tmp_4$0 ?v))
                      (or (Btwn$0 next$0 ?z tmp_4$0 ?v)
                          (and (Btwn$0 next$0 ?z tmp_4$0 tmp_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 ?z ?u tmp_4$0)
                      (or (Btwn$0 next$0 prv_4$0 ?v tmp_4$0)
                          (and (Btwn$0 next$0 prv_4$0 ?v ?v)
                               (not (Btwn$0 next$0 prv_4$0 tmp_4$0 tmp_4$0)))))
                 (and (not (= tmp_4$0 ?v))
                      (or (Btwn$0 next$0 ?z tmp_4$0 ?v)
                          (and (Btwn$0 next$0 ?z tmp_4$0 tmp_4$0)
                               (not (Btwn$0 next$0 ?z ?v ?v))))
                      (Btwn$0 next$0 prv_4$0 ?u ?v)
                      (or (Btwn$0 next$0 prv_4$0 ?v tmp_4$0)
                          (and (Btwn$0 next$0 prv_4$0 ?v ?v)
                               (not (Btwn$0 next$0 prv_4$0 tmp_4$0 tmp_4$0)))))
                 (not (Btwn$0 (write$0 next$0 tmp_4$0 prv_4$0) ?z ?u ?v))))))

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
