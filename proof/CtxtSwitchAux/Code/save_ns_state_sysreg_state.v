Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _ret := 1%positive.
Definition _t'1 := 2%positive.
Definition _t'10 := 3%positive.
Definition _t'11 := 4%positive.
Definition _t'12 := 5%positive.
Definition _t'13 := 6%positive.
Definition _t'14 := 7%positive.
Definition _t'15 := 8%positive.
Definition _t'16 := 9%positive.
Definition _t'17 := 10%positive.
Definition _t'18 := 11%positive.
Definition _t'19 := 12%positive.
Definition _t'2 := 13%positive.
Definition _t'20 := 14%positive.
Definition _t'21 := 15%positive.
Definition _t'22 := 16%positive.
Definition _t'23 := 17%positive.
Definition _t'24 := 18%positive.
Definition _t'25 := 19%positive.
Definition _t'26 := 20%positive.
Definition _t'27 := 21%positive.
Definition _t'28 := 22%positive.
Definition _t'29 := 23%positive.
Definition _t'3 := 24%positive.
Definition _t'30 := 25%positive.
Definition _t'31 := 26%positive.
Definition _t'32 := 27%positive.
Definition _t'33 := 28%positive.
Definition _t'34 := 29%positive.
Definition _t'35 := 30%positive.
Definition _t'36 := 31%positive.
Definition _t'37 := 32%positive.
Definition _t'4 := 33%positive.
Definition _t'5 := 34%positive.
Definition _t'6 := 35%positive.
Definition _t'7 := 36%positive.
Definition _t'8 := 37%positive.
Definition _t'9 := 38%positive.

Definition save_ns_state_sysreg_state_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong cc_default))
        ((Econst_int (Int.repr 38) tuint) :: nil))
      (Scall None
        (Evar _set_ns_state (Tfunction (Tcons tuint (Tcons tulong Tnil)) tvoid
                              cc_default))
        ((Econst_int (Int.repr 38) tuint) :: (Etempvar _t'1 tulong) :: nil)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong cc_default))
          ((Econst_int (Int.repr 43) tuint) :: nil))
        (Scall None
          (Evar _set_ns_state (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                tvoid cc_default))
          ((Econst_int (Int.repr 43) tuint) :: (Etempvar _t'2 tulong) :: nil)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong cc_default))
            ((Econst_int (Int.repr 44) tuint) :: nil))
          (Scall None
            (Evar _set_ns_state (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                  tvoid cc_default))
            ((Econst_int (Int.repr 44) tuint) :: (Etempvar _t'3 tulong) :: nil)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                   cc_default))
              ((Econst_int (Int.repr 45) tuint) :: nil))
            (Scall None
              (Evar _set_ns_state (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                    tvoid cc_default))
              ((Econst_int (Int.repr 45) tuint) :: (Etempvar _t'4 tulong) ::
               nil)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                     cc_default))
                ((Econst_int (Int.repr 39) tuint) :: nil))
              (Scall None
                (Evar _set_ns_state (Tfunction
                                      (Tcons tuint (Tcons tulong Tnil)) tvoid
                                      cc_default))
                ((Econst_int (Int.repr 39) tuint) :: (Etempvar _t'5 tulong) ::
                 nil)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                       cc_default))
                  ((Econst_int (Int.repr 40) tuint) :: nil))
                (Scall None
                  (Evar _set_ns_state (Tfunction
                                        (Tcons tuint (Tcons tulong Tnil)) tvoid
                                        cc_default))
                  ((Econst_int (Int.repr 40) tuint) ::
                   (Etempvar _t'6 tulong) :: nil)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                         cc_default))
                    ((Econst_int (Int.repr 41) tuint) :: nil))
                  (Scall None
                    (Evar _set_ns_state (Tfunction
                                          (Tcons tuint (Tcons tulong Tnil))
                                          tvoid cc_default))
                    ((Econst_int (Int.repr 41) tuint) ::
                     (Etempvar _t'7 tulong) :: nil)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'8)
                      (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                           cc_default))
                      ((Econst_int (Int.repr 42) tuint) :: nil))
                    (Scall None
                      (Evar _set_ns_state (Tfunction
                                            (Tcons tuint (Tcons tulong Tnil))
                                            tvoid cc_default))
                      ((Econst_int (Int.repr 42) tuint) ::
                       (Etempvar _t'8 tulong) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'9)
                        (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                             cc_default))
                        ((Econst_int (Int.repr 46) tuint) :: nil))
                      (Scall None
                        (Evar _set_ns_state (Tfunction
                                              (Tcons tuint (Tcons tulong Tnil))
                                              tvoid cc_default))
                        ((Econst_int (Int.repr 46) tuint) ::
                         (Etempvar _t'9 tulong) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'10)
                          (Evar _sysreg_read (Tfunction (Tcons tuint Tnil)
                                               tulong cc_default))
                          ((Econst_int (Int.repr 47) tuint) :: nil))
                        (Scall None
                          (Evar _set_ns_state (Tfunction
                                                (Tcons tuint
                                                  (Tcons tulong Tnil)) tvoid
                                                cc_default))
                          ((Econst_int (Int.repr 47) tuint) ::
                           (Etempvar _t'10 tulong) :: nil)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'11)
                            (Evar _sysreg_read (Tfunction (Tcons tuint Tnil)
                                                 tulong cc_default))
                            ((Econst_int (Int.repr 48) tuint) :: nil))
                          (Scall None
                            (Evar _set_ns_state (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tulong Tnil)) tvoid
                                                  cc_default))
                            ((Econst_int (Int.repr 48) tuint) ::
                             (Etempvar _t'11 tulong) :: nil)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'12)
                              (Evar _sysreg_read (Tfunction (Tcons tuint Tnil)
                                                   tulong cc_default))
                              ((Econst_int (Int.repr 49) tuint) :: nil))
                            (Scall None
                              (Evar _set_ns_state (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tulong Tnil))
                                                    tvoid cc_default))
                              ((Econst_int (Int.repr 49) tuint) ::
                               (Etempvar _t'12 tulong) :: nil)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'13)
                                (Evar _sysreg_read (Tfunction
                                                     (Tcons tuint Tnil) tulong
                                                     cc_default))
                                ((Econst_int (Int.repr 50) tuint) :: nil))
                              (Scall None
                                (Evar _set_ns_state (Tfunction
                                                      (Tcons tuint
                                                        (Tcons tulong Tnil))
                                                      tvoid cc_default))
                                ((Econst_int (Int.repr 50) tuint) ::
                                 (Etempvar _t'13 tulong) :: nil)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'14)
                                  (Evar _sysreg_read (Tfunction
                                                       (Tcons tuint Tnil)
                                                       tulong cc_default))
                                  ((Econst_int (Int.repr 51) tuint) :: nil))
                                (Scall None
                                  (Evar _set_ns_state (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tulong Tnil))
                                                        tvoid cc_default))
                                  ((Econst_int (Int.repr 51) tuint) ::
                                   (Etempvar _t'14 tulong) :: nil)))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'15)
                                    (Evar _sysreg_read (Tfunction
                                                         (Tcons tuint Tnil)
                                                         tulong cc_default))
                                    ((Econst_int (Int.repr 52) tuint) :: nil))
                                  (Scall None
                                    (Evar _set_ns_state (Tfunction
                                                          (Tcons tuint
                                                            (Tcons tulong Tnil))
                                                          tvoid cc_default))
                                    ((Econst_int (Int.repr 52) tuint) ::
                                     (Etempvar _t'15 tulong) :: nil)))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'16)
                                      (Evar _sysreg_read (Tfunction
                                                           (Tcons tuint Tnil)
                                                           tulong cc_default))
                                      ((Econst_int (Int.repr 53) tuint) :: nil))
                                    (Scall None
                                      (Evar _set_ns_state (Tfunction
                                                            (Tcons tuint
                                                              (Tcons tulong
                                                                Tnil)) tvoid
                                                            cc_default))
                                      ((Econst_int (Int.repr 53) tuint) ::
                                       (Etempvar _t'16 tulong) :: nil)))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'17)
                                        (Evar _sysreg_read (Tfunction
                                                             (Tcons tuint Tnil)
                                                             tulong cc_default))
                                        ((Econst_int (Int.repr 54) tuint) ::
                                         nil))
                                      (Scall None
                                        (Evar _set_ns_state (Tfunction
                                                              (Tcons tuint
                                                                (Tcons tulong
                                                                  Tnil)) tvoid
                                                              cc_default))
                                        ((Econst_int (Int.repr 54) tuint) ::
                                         (Etempvar _t'17 tulong) :: nil)))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'18)
                                          (Evar _sysreg_read (Tfunction
                                                               (Tcons tuint
                                                                 Tnil) tulong
                                                               cc_default))
                                          ((Econst_int (Int.repr 55) tuint) ::
                                           nil))
                                        (Scall None
                                          (Evar _set_ns_state (Tfunction
                                                                (Tcons tuint
                                                                  (Tcons tulong
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                          ((Econst_int (Int.repr 55) tuint) ::
                                           (Etempvar _t'18 tulong) :: nil)))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'19)
                                            (Evar _sysreg_read (Tfunction
                                                                 (Tcons tuint
                                                                   Tnil) tulong
                                                                 cc_default))
                                            ((Econst_int (Int.repr 56) tuint) ::
                                             nil))
                                          (Scall None
                                            (Evar _set_ns_state (Tfunction
                                                                  (Tcons tuint
                                                                    (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                  tvoid
                                                                  cc_default))
                                            ((Econst_int (Int.repr 56) tuint) ::
                                             (Etempvar _t'19 tulong) :: nil)))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'20)
                                              (Evar _sysreg_read (Tfunction
                                                                   (Tcons tuint
                                                                     Tnil)
                                                                   tulong
                                                                   cc_default))
                                              ((Econst_int (Int.repr 57) tuint) ::
                                               nil))
                                            (Scall None
                                              (Evar _set_ns_state (Tfunction
                                                                    (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                    tvoid
                                                                    cc_default))
                                              ((Econst_int (Int.repr 57) tuint) ::
                                               (Etempvar _t'20 tulong) :: nil)))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'21)
                                                (Evar _sysreg_read (Tfunction
                                                                     (Tcons
                                                                      tuint
                                                                      Tnil)
                                                                     tulong
                                                                     cc_default))
                                                ((Econst_int (Int.repr 58) tuint) ::
                                                 nil))
                                              (Scall None
                                                (Evar _set_ns_state (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                      tvoid
                                                                      cc_default))
                                                ((Econst_int (Int.repr 58) tuint) ::
                                                 (Etempvar _t'21 tulong) ::
                                                 nil)))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'22)
                                                  (Evar _sysreg_read (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil)
                                                                      tulong
                                                                      cc_default))
                                                  ((Econst_int (Int.repr 59) tuint) ::
                                                   nil))
                                                (Scall None
                                                  (Evar _set_ns_state (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                      tvoid
                                                                      cc_default))
                                                  ((Econst_int (Int.repr 59) tuint) ::
                                                   (Etempvar _t'22 tulong) ::
                                                   nil)))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'23)
                                                    (Evar _sysreg_read 
                                                    (Tfunction
                                                      (Tcons tuint Tnil) tulong
                                                      cc_default))
                                                    ((Econst_int (Int.repr 60) tuint) ::
                                                     nil))
                                                  (Scall None
                                                    (Evar _set_ns_state 
                                                    (Tfunction
                                                      (Tcons tuint
                                                        (Tcons tulong Tnil))
                                                      tvoid cc_default))
                                                    ((Econst_int (Int.repr 60) tuint) ::
                                                     (Etempvar _t'23 tulong) ::
                                                     nil)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Scall (Some _t'24)
                                                      (Evar _sysreg_read 
                                                      (Tfunction
                                                        (Tcons tuint Tnil)
                                                        tulong cc_default))
                                                      ((Econst_int (Int.repr 61) tuint) ::
                                                       nil))
                                                    (Scall None
                                                      (Evar _set_ns_state 
                                                      (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tulong Tnil))
                                                        tvoid cc_default))
                                                      ((Econst_int (Int.repr 61) tuint) ::
                                                       (Etempvar _t'24 tulong) ::
                                                       nil)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _t'25)
                                                        (Evar _sysreg_read 
                                                        (Tfunction
                                                          (Tcons tuint Tnil)
                                                          tulong cc_default))
                                                        ((Econst_int (Int.repr 62) tuint) ::
                                                         nil))
                                                      (Scall None
                                                        (Evar _set_ns_state 
                                                        (Tfunction
                                                          (Tcons tuint
                                                            (Tcons tulong Tnil))
                                                          tvoid cc_default))
                                                        ((Econst_int (Int.repr 62) tuint) ::
                                                         (Etempvar _t'25 tulong) ::
                                                         nil)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'26)
                                                          (Evar _sysreg_read 
                                                          (Tfunction
                                                            (Tcons tuint Tnil)
                                                            tulong cc_default))
                                                          ((Econst_int (Int.repr 63) tuint) ::
                                                           nil))
                                                        (Scall None
                                                          (Evar _set_ns_state 
                                                          (Tfunction
                                                            (Tcons tuint
                                                              (Tcons tulong
                                                                Tnil)) tvoid
                                                            cc_default))
                                                          ((Econst_int (Int.repr 63) tuint) ::
                                                           (Etempvar _t'26 tulong) ::
                                                           nil)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'27)
                                                            (Evar _sysreg_read 
                                                            (Tfunction
                                                              (Tcons tuint
                                                                Tnil) tulong
                                                              cc_default))
                                                            ((Econst_int (Int.repr 64) tuint) ::
                                                             nil))
                                                          (Scall None
                                                            (Evar _set_ns_state 
                                                            (Tfunction
                                                              (Tcons tuint
                                                                (Tcons tulong
                                                                  Tnil)) tvoid
                                                              cc_default))
                                                            ((Econst_int (Int.repr 64) tuint) ::
                                                             (Etempvar _t'27 tulong) ::
                                                             nil)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Scall (Some _t'28)
                                                              (Evar _sysreg_read 
                                                              (Tfunction
                                                                (Tcons tuint
                                                                  Tnil) tulong
                                                                cc_default))
                                                              ((Econst_int (Int.repr 65) tuint) ::
                                                               nil))
                                                            (Scall None
                                                              (Evar _set_ns_state 
                                                              (Tfunction
                                                                (Tcons tuint
                                                                  (Tcons tulong
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                                              ((Econst_int (Int.repr 65) tuint) ::
                                                               (Etempvar _t'28 tulong) ::
                                                               nil)))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Scall (Some _t'29)
                                                                (Evar _sysreg_read 
                                                                (Tfunction
                                                                  (Tcons tuint
                                                                    Tnil)
                                                                  tulong
                                                                  cc_default))
                                                                ((Econst_int (Int.repr 66) tuint) ::
                                                                 nil))
                                                              (Scall None
                                                                (Evar _set_ns_state 
                                                                (Tfunction
                                                                  (Tcons tuint
                                                                    (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                  tvoid
                                                                  cc_default))
                                                                ((Econst_int (Int.repr 66) tuint) ::
                                                                 (Etempvar _t'29 tulong) ::
                                                                 nil)))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Scall (Some _t'30)
                                                                  (Evar _sysreg_read 
                                                                  (Tfunction
                                                                    (Tcons
                                                                      tuint
                                                                      Tnil)
                                                                    tulong
                                                                    cc_default))
                                                                  ((Econst_int (Int.repr 67) tuint) ::
                                                                   nil))
                                                                (Scall None
                                                                  (Evar _set_ns_state 
                                                                  (Tfunction
                                                                    (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Econst_int (Int.repr 67) tuint) ::
                                                                   (Etempvar _t'30 tulong) ::
                                                                   nil)))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Scall (Some _t'31)
                                                                    (Evar _sysreg_read 
                                                                    (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil)
                                                                      tulong
                                                                      cc_default))
                                                                    ((Econst_int (Int.repr 68) tuint) ::
                                                                     nil))
                                                                  (Scall None
                                                                    (Evar _set_ns_state 
                                                                    (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                      tvoid
                                                                      cc_default))
                                                                    ((Econst_int (Int.repr 68) tuint) ::
                                                                     (Etempvar _t'31 tulong) ::
                                                                     nil)))
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Scall (Some _t'32)
                                                                      (Evar _sysreg_read 
                                                                      (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil)
                                                                      tulong
                                                                      cc_default))
                                                                      ((Econst_int (Int.repr 69) tuint) ::
                                                                      nil))
                                                                    (Scall None
                                                                      (Evar _set_ns_state 
                                                                      (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                      tvoid
                                                                      cc_default))
                                                                      ((Econst_int (Int.repr 69) tuint) ::
                                                                      (Etempvar _t'32 tulong) ::
                                                                      nil)))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                      (Scall (Some _t'33)
                                                                      (Evar _sysreg_read 
                                                                      (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil)
                                                                      tulong
                                                                      cc_default))
                                                                      ((Econst_int (Int.repr 70) tuint) ::
                                                                      nil))
                                                                      (Scall None
                                                                      (Evar _set_ns_state 
                                                                      (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                      tvoid
                                                                      cc_default))
                                                                      ((Econst_int (Int.repr 70) tuint) ::
                                                                      (Etempvar _t'33 tulong) ::
                                                                      nil)))
                                                                    (Ssequence
                                                                      (Ssequence
                                                                      (Scall (Some _t'34)
                                                                      (Evar _sysreg_read 
                                                                      (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil)
                                                                      tulong
                                                                      cc_default))
                                                                      ((Econst_int (Int.repr 32) tuint) ::
                                                                      nil))
                                                                      (Scall None
                                                                      (Evar _set_ns_state 
                                                                      (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                      tvoid
                                                                      cc_default))
                                                                      ((Econst_int (Int.repr 32) tuint) ::
                                                                      (Etempvar _t'34 tulong) ::
                                                                      nil)))
                                                                      (Ssequence
                                                                      (Ssequence
                                                                      (Scall (Some _t'35)
                                                                      (Evar _sysreg_read 
                                                                      (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil)
                                                                      tulong
                                                                      cc_default))
                                                                      ((Econst_int (Int.repr 33) tuint) ::
                                                                      nil))
                                                                      (Scall None
                                                                      (Evar _set_ns_state 
                                                                      (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                      tvoid
                                                                      cc_default))
                                                                      ((Econst_int (Int.repr 33) tuint) ::
                                                                      (Etempvar _t'35 tulong) ::
                                                                      nil)))
                                                                      (Ssequence
                                                                      (Ssequence
                                                                      (Scall (Some _t'36)
                                                                      (Evar _sysreg_read 
                                                                      (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil)
                                                                      tulong
                                                                      cc_default))
                                                                      ((Econst_int (Int.repr 35) tuint) ::
                                                                      nil))
                                                                      (Scall None
                                                                      (Evar _set_ns_state 
                                                                      (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                      tvoid
                                                                      cc_default))
                                                                      ((Econst_int (Int.repr 35) tuint) ::
                                                                      (Etempvar _t'36 tulong) ::
                                                                      nil)))
                                                                      (Ssequence
                                                                      (Scall (Some _t'37)
                                                                      (Evar _sysreg_read 
                                                                      (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil)
                                                                      tulong
                                                                      cc_default))
                                                                      ((Econst_int (Int.repr 36) tuint) ::
                                                                      nil))
                                                                      (Scall None
                                                                      (Evar _set_ns_state 
                                                                      (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                      tvoid
                                                                      cc_default))
                                                                      ((Econst_int (Int.repr 36) tuint) ::
                                                                      (Etempvar _t'37 tulong) ::
                                                                      nil)))))))))))))))))))))))))))))))))))))))
.

Definition f_save_ns_state_sysreg_state := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'37, tulong) :: (_t'36, tulong) :: (_t'35, tulong) ::
               (_t'34, tulong) :: (_t'33, tulong) :: (_t'32, tulong) ::
               (_t'31, tulong) :: (_t'30, tulong) :: (_t'29, tulong) ::
               (_t'28, tulong) :: (_t'27, tulong) :: (_t'26, tulong) ::
               (_t'25, tulong) :: (_t'24, tulong) :: (_t'23, tulong) ::
               (_t'22, tulong) :: (_t'21, tulong) :: (_t'20, tulong) ::
               (_t'19, tulong) :: (_t'18, tulong) :: (_t'17, tulong) ::
               (_t'16, tulong) :: (_t'15, tulong) :: (_t'14, tulong) ::
               (_t'13, tulong) :: (_t'12, tulong) :: (_t'11, tulong) ::
               (_t'10, tulong) :: (_t'9, tulong) :: (_t'8, tulong) ::
               (_t'7, tulong) :: (_t'6, tulong) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := save_ns_state_sysreg_state_body
|}.
