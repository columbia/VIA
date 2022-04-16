Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _algo := 1%positive.
Definition _base := 2%positive.
Definition _g := 3%positive.
Definition _g_rd := 4%positive.
Definition _g_rec := 5%positive.
Definition _g_rec_list := 6%positive.
Definition _g_rtt := 7%positive.
Definition _granule := 8%positive.
Definition _i := 9%positive.
Definition _lock := 10%positive.
Definition _par_base := 11%positive.
Definition _par_end := 12%positive.
Definition _rd := 13%positive.
Definition _rd__1 := 14%positive.
Definition _rec := 15%positive.
Definition _rec_list := 16%positive.
Definition _ret := 17%positive.
Definition _rt := 18%positive.
Definition _size := 19%positive.
Definition _state := 20%positive.
Definition _t'1 := 21%positive.
Definition _t'2 := 22%positive.
Definition _t'3 := 23%positive.
Definition _t'4 := 24%positive.
Definition _t'5 := 25%positive.
Definition _t'6 := 26%positive.
Definition _t'7 := 27%positive.

Definition realm_create_ops_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_locked_granule (Tfunction (Tcons tuint Tnil)
                                    (tptr Tvoid)
                                    cc_default))
        ((Econst_int (Int.repr 0) tuint) :: nil))
      (Sset _g_rd (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_locked_granule (Tfunction (Tcons tuint Tnil)
                                      (tptr Tvoid)
                                      cc_default))
          ((Econst_int (Int.repr 1) tuint) :: nil))
        (Sset _g_rtt (Etempvar _t'2 (tptr Tvoid))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _get_locked_granule (Tfunction (Tcons tuint Tnil)
                                        (tptr Tvoid)
                                        cc_default))
            ((Econst_int (Int.repr 2) tuint) :: nil))
          (Sset _g_rec_list (Etempvar _t'3 (tptr Tvoid))))
        (Ssequence
          (Scall None
            (Evar _set_g_rtt_rd (Tfunction
                                  (Tcons (tptr Tvoid)
                                    (Tcons (tptr Tvoid)
                                      Tnil)) tvoid cc_default))
            ((Etempvar _g_rtt (tptr Tvoid)) ::
             (Etempvar _g_rd (tptr Tvoid)) :: nil))
          (Ssequence
            (Scall None
              (Evar _granule_set_state (Tfunction
                                         (Tcons
                                           (tptr Tvoid)
                                           (Tcons tuint Tnil)) tvoid
                                         cc_default))
              ((Etempvar _g_rtt (tptr Tvoid)) ::
               (Econst_int (Int.repr 5) tuint) :: nil))
            (Ssequence
              (Scall None
                (Evar _granule_unlock (Tfunction
                                        (Tcons (tptr Tvoid)
                                          Tnil) tvoid cc_default))
                ((Etempvar _g_rtt (tptr Tvoid)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _granule_set_state (Tfunction
                                             (Tcons
                                               (tptr Tvoid)
                                               (Tcons tuint Tnil)) tvoid
                                             cc_default))
                  ((Etempvar _g_rec_list (tptr Tvoid)) ::
                   (Econst_int (Int.repr 6) tuint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _granule_unlock (Tfunction
                                            (Tcons
                                              (tptr Tvoid)
                                              Tnil) tvoid cc_default))
                    ((Etempvar _g_rec_list (tptr Tvoid)) ::
                     nil))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _granule_map (Tfunction
                                             (Tcons
                                               (tptr Tvoid)
                                               (Tcons tuint Tnil)) (tptr Tvoid)
                                             cc_default))
                        ((Etempvar _g_rd (tptr Tvoid)) ::
                         (Econst_int (Int.repr 2) tuint) :: nil))
                      (Sset _rd (Etempvar _t'4 (tptr Tvoid))))
                    (Ssequence
                      (Scall None
                        (Evar _granule_set_state (Tfunction
                                                   (Tcons
                                                     (tptr Tvoid)
                                                     (Tcons tuint Tnil)) tvoid
                                                   cc_default))
                        ((Etempvar _g_rd (tptr Tvoid)) ::
                         (Econst_int (Int.repr 2) tuint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _set_rd_state (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  (Tcons tuint Tnil)) tvoid
                                                cc_default))
                          ((Etempvar _rd (tptr Tvoid)) ::
                           (Econst_int (Int.repr 0) tuint) :: nil))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'5)
                              (Evar _get_realm_params_par_base (Tfunction Tnil
                                                                 tulong
                                                                 cc_default))
                              nil)
                            (Sset _base (Etempvar _t'5 tulong)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'6)
                                (Evar _get_realm_params_par_size (Tfunction
                                                                   Tnil tulong
                                                                   cc_default))
                                nil)
                              (Sset _size (Etempvar _t'6 tulong)))
                            (Ssequence
                              (Scall None
                                (Evar _set_rd_par_base (Tfunction
                                                         (Tcons
                                                           (tptr Tvoid)
                                                           (Tcons tulong Tnil))
                                                         tvoid cc_default))
                                ((Etempvar _rd (tptr Tvoid)) ::
                                 (Etempvar _base tulong) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _set_rd_par_end (Tfunction
                                                          (Tcons
                                                            (tptr Tvoid)
                                                            (Tcons tulong Tnil))
                                                          tvoid cc_default))
                                  ((Etempvar _rd (tptr Tvoid)) ::
                                   (Ebinop Oadd (Etempvar _base tulong)
                                     (Etempvar _size tulong) tulong) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _set_rd_g_rtt (Tfunction
                                                          (Tcons
                                                            (tptr Tvoid)
                                                            (Tcons
                                                              (tptr Tvoid)
                                                              Tnil)) tvoid
                                                          cc_default))
                                    ((Etempvar _rd (tptr Tvoid)) ::
                                     (Etempvar _g_rtt (tptr Tvoid)) ::
                                     nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _set_rd_g_rec_list (Tfunction
                                                                 (Tcons
                                                                   (tptr Tvoid)
                                                                   (Tcons
                                                                     (tptr Tvoid)
                                                                     Tnil))
                                                                 tvoid
                                                                 cc_default))
                                      ((Etempvar _rd (tptr Tvoid)) ::
                                       (Etempvar _g_rec_list (tptr Tvoid)) ::
                                       nil))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'7)
                                          (Evar _get_realm_params_measurement_algo 
                                          (Tfunction Tnil tulong cc_default))
                                          nil)
                                        (Sset _algo (Etempvar _t'7 tulong)))
                                      (Ssequence
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _algo tulong)
                                                       (Econst_long (Int64.repr 1) tulong)
                                                       tint)
                                          (Scall None
                                            (Evar _set_rd_measurement_algo 
                                            (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                (Tcons tulong Tnil)) tvoid
                                              cc_default))
                                            ((Etempvar _rd (tptr Tvoid)) ::
                                             (Etempvar _algo tulong) :: nil))
                                          (Scall None
                                            (Evar _set_rd_measurement_algo 
                                            (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                (Tcons tulong Tnil)) tvoid
                                              cc_default))
                                            ((Etempvar _rd (tptr Tvoid)) ::
                                             (Econst_long (Int64.repr 0) tulong) ::
                                             nil)))
                                        (Ssequence
                                          (Scall None
                                            (Evar _measurement_start (Tfunction
                                                                      (Tcons
                                                                      (tptr Tvoid)
                                                                      Tnil)
                                                                      tvoid
                                                                      cc_default))
                                            ((Etempvar _rd (tptr Tvoid)) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _buffer_unmap (Tfunction
                                                                    (Tcons
                                                                      (tptr Tvoid)
                                                                      Tnil)
                                                                    tvoid
                                                                    cc_default))
                                              ((Etempvar _rd (tptr Tvoid)) ::
                                               nil))
                                            (Scall None
                                              (Evar _granule_unlock (Tfunction
                                                                      (Tcons
                                                                      (tptr Tvoid)
                                                                      Tnil)
                                                                      tvoid
                                                                      cc_default))
                                              ((Etempvar _g_rd (tptr Tvoid)) ::
                                               nil)))))))))))))))))))))))
.

Definition f_realm_create_ops := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_g_rd, (tptr Tvoid)) ::
               (_rd, (tptr Tvoid)) ::
               (_g_rtt, (tptr Tvoid)) ::
               (_g_rec_list, (tptr Tvoid)) ::
               (_base, tulong) :: (_size, tulong) :: (_algo, tulong) ::
               (_t'7, tulong) :: (_t'6, tulong) :: (_t'5, tulong) ::
               (_t'4, (tptr Tvoid)) ::
               (_t'3, (tptr Tvoid)) ::
               (_t'2, (tptr Tvoid)) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := realm_create_ops_body
|}.
