(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
  GRASShopper benchmarks.
  Authors: Ruzica Piskac, Thomas Wies, and Damien Zufferey
  URL: http://cs.nyu.edu/wies/software/grasshopper
  See also: GRASShopper - Complete Heap Verification with Mixed Specifications. In TACAS 2014, pages 124-139.

  If this benchmark is satisfiable, GRASShopper reports the following error message:
  tests/spl/union_find.spl:37:7-22:A precondition for this call of find might not hold
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
(declare-fun in$0 (Loc SetLoc) Bool)
(declare-fun Alloc$0 () SetLoc)
(declare-fun FP$0 () SetLoc)
(declare-fun FP_Caller$0 () SetLoc)
(declare-fun FP_Caller_3$0 () SetLoc)
(declare-fun X_1$0 () SetLoc)
(declare-fun Y$0 () SetLoc)
(declare-fun lseg_set_X$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_domain$0 (FldLoc Loc Loc) SetLoc)
(declare-fun lseg_set_struct$0 (SetLoc FldLoc Loc Loc SetLoc) Bool)
(declare-fun next$0 () FldLoc)
(declare-fun root_x_1$0 () Loc)
(declare-fun root_y$0 () Loc)
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
(declare-fun sk_?X_60$0 () SetLoc)
(declare-fun sk_?e_3$0 () Loc)
(declare-fun sk_FP_1$0 () SetLoc)
(declare-fun sk_X_1$0 () SetLoc)
(declare-fun x_1$0 () Loc)
(declare-fun y$0 () Loc)

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
    (not (lseg_set_struct$0 sk_?X_60$0 next$0 x_1$0 root_x_1$0 sk_X_1$0))))

(assert (= FP_Caller_3$0 (setminus$0 FP_Caller$0 FP$0)))

(assert (= (read$0 next$0 root_x_1$0) null$0))

(assert (= emptyset$0 emptyset$0))

(assert (= X_1$0 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)))

(assert (= sk_?X_48$0 (union$0 sk_?X_54$0 sk_?X_49$0)))

(assert (= sk_?X_49$0 (union$0 sk_?X_52$0 sk_?X_50$0)))

(assert (= sk_?X_51$0 (setenum$0 root_y$0)))

(assert (= sk_?X_53$0 (setenum$0 root_x_1$0)))

(assert (= sk_?X_55$0 (lseg_set_domain$0 next$0 y$0 root_y$0)))

(assert (= FP_Caller$0 (union$0 FP$0 FP_Caller$0)))

(assert (lseg_set_struct$0 sk_?X_56$0 next$0 x_1$0 root_x_1$0 X_1$0))

(assert (= sk_?X_58$0 sk_?X_59$0))

(assert (= sk_?X_60$0 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)))

(assert (= sk_X_1$0 (lseg_set_X$0 next$0 x_1$0 root_x_1$0)))

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

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (or (in$0 (ep$0 ?f ?X ?x) ?X) (= ?x (ep$0 ?f ?X ?x)))))

(assert (forall ((?X SetLoc) (?f FldLoc) (?x Loc))
        (Btwn$0 ?f ?x (ep$0 ?f ?X ?x) (ep$0 ?f ?X ?x))))

(assert (or (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0)
    (not (lseg_set_struct$0 sk_?X_56$0 next$0 x_1$0 root_x_1$0 X_1$0))))

(assert (or (Btwn$0 next$0 y$0 root_y$0 root_y$0)
    (not (lseg_set_struct$0 sk_?X_55$0 next$0 y$0 root_y$0 Y$0))))

(assert (= Alloc$0 (union$0 FP_Caller$0 Alloc$0)))

(assert (= (read$0 next$0 root_y$0) null$0))

(assert (= emptyset$0 (intersection$0 sk_?X_54$0 sk_?X_49$0)))

(assert (= Y$0 (lseg_set_X$0 next$0 y$0 root_y$0)))

(assert (= sk_?X_48$0 FP$0))

(assert (= sk_?X_50$0 sk_?X_51$0))

(assert (= sk_?X_52$0 sk_?X_53$0))

(assert (= sk_?X_54$0 (union$0 sk_?X_56$0 sk_?X_55$0)))

(assert (= sk_?X_56$0 (lseg_set_domain$0 next$0 x_1$0 root_x_1$0)))

(assert (lseg_set_struct$0 sk_?X_55$0 next$0 y$0 root_y$0 Y$0))

(assert (= sk_?X_57$0 (union$0 sk_?X_60$0 sk_?X_58$0)))

(assert (= sk_?X_59$0 (setenum$0 root_x_1$0)))

(assert (= sk_FP_1$0 sk_?X_57$0))

(assert (or (in$0 sk_?e_3$0 (intersection$0 sk_?X_60$0 sk_?X_58$0))
    (and (in$0 sk_?e_3$0 sk_FP_1$0) (not (in$0 sk_?e_3$0 FP$0)))
    (not (= (read$0 next$0 root_x_1$0) null$0))
    (not (Btwn$0 next$0 x_1$0 root_x_1$0 root_x_1$0))))

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
