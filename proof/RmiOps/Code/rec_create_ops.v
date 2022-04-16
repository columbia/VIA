Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _base := 1%positive.
Definition _g := 2%positive.
Definition _g_rd := 3%positive.
Definition _g_rec := 4%positive.
Definition _g_rec_list := 5%positive.
Definition _granule := 6%positive.
Definition _i := 7%positive.
Definition _idx := 8%positive.
Definition _mpidr := 9%positive.
Definition _par_base := 10%positive.
Definition _par_end := 11%positive.
Definition _rd := 12%positive.
Definition _rd__1 := 13%positive.
Definition _rec := 14%positive.
Definition _rec__1 := 15%positive.
Definition _rec_idx := 16%positive.
Definition _rec_list := 17%positive.
Definition _rec_list__1 := 18%positive.
Definition _rec_rvic_state := 19%positive.
Definition _reg := 20%positive.
Definition _ret := 21%positive.
Definition _runnable := 22%positive.
Definition _rvic := 23%positive.
Definition _state := 24%positive.
Definition _t'1 := 25%positive.
Definition _t'2 := 26%positive.
Definition _t'3 := 27%positive.
Definition _t'4 := 28%positive.
Definition _t'5 := 29%positive.

Definition rec_create_ops_body :=
  (Ssequence
    (Scall None
      (Evar _granule_set_state (Tfunction
                                 (Tcons (tptr Tvoid)
                                   (Tcons tuint Tnil)) tvoid cc_default))
      ((Etempvar _g_rec (tptr Tvoid)) ::
       (Econst_int (Int.repr 3) tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar _realm_set_rec_entry (Tfunction
                                     (Tcons tulong
                                       (Tcons (tptr Tvoid)
                                         (Tcons
                                           (tptr Tvoid)
                                           Tnil))) tvoid cc_default))
        ((Etempvar _rec_idx tulong) ::
         (Etempvar _rec_list (tptr Tvoid)) ::
         (Etempvar _g_rec (tptr Tvoid)) :: nil))
      (Ssequence
        (Scall None
          (Evar _init_rec_read_only (Tfunction
                                      (Tcons (tptr Tvoid)
                                        (Tcons (tptr Tvoid)
                                          (Tcons tulong Tnil))) tvoid
                                      cc_default))
          ((Etempvar _rec (tptr Tvoid)) ::
           (Etempvar _g_rec (tptr Tvoid)) ::
           (Etempvar _rec_idx tulong) :: nil))
        (Ssequence
          (Scall None
            (Evar _init_rec_regs (Tfunction
                                   (Tcons (tptr Tvoid)
                                     (Tcons tulong
                                       (Tcons (tptr Tvoid) Tnil)))
                                   tvoid cc_default))
            ((Etempvar _rec (tptr Tvoid)) ::
             (Etempvar _mpidr tulong) ::
             (Etempvar _rd (tptr Tvoid)) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _get_rec_rvic (Tfunction
                                      (Tcons (tptr Tvoid) Tnil)
                                      (tptr Tvoid)
                                      cc_default))
                ((Etempvar _rec (tptr Tvoid)) :: nil))
              (Scall None
                (Evar _init_rec_rvic_state (Tfunction
                                             (Tcons
                                               (tptr Tvoid)
                                               Tnil) tvoid cc_default))
                ((Etempvar _t'1 (tptr Tvoid)) ::
                 nil)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _get_rd_par_base (Tfunction
                                           (Tcons (tptr Tvoid)
                                             Tnil) tulong cc_default))
                  ((Etempvar _rd (tptr Tvoid)) :: nil))
                (Scall None
                  (Evar _set_rec_par_base (Tfunction
                                            (Tcons (tptr Tvoid)
                                              (Tcons tulong Tnil)) tvoid
                                            cc_default))
                  ((Etempvar _rec (tptr Tvoid)) ::
                   (Etempvar _t'2 tulong) :: nil)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _get_rd_par_end (Tfunction
                                            (Tcons (tptr Tvoid)
                                              Tnil) tulong cc_default))
                    ((Etempvar _rd (tptr Tvoid)) :: nil))
                  (Scall None
                    (Evar _set_rec_par_end (Tfunction
                                             (Tcons
                                               (tptr Tvoid)
                                               (Tcons tulong Tnil)) tvoid
                                             cc_default))
                    ((Etempvar _rec (tptr Tvoid)) ::
                     (Etempvar _t'3 tulong) :: nil)))
                (Ssequence
                  (Scall None
                    (Evar _set_rec_g_rd (Tfunction
                                          (Tcons (tptr Tvoid)
                                            (Tcons
                                              (tptr Tvoid)
                                              Tnil)) tvoid cc_default))
                    ((Etempvar _rec (tptr Tvoid)) ::
                     (Etempvar _g_rd (tptr Tvoid)) :: nil))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _get_rd_g_rec_list (Tfunction
                                                   (Tcons
                                                     (tptr Tvoid)
                                                     Tnil)
                                                   (tptr Tvoid)
                                                   cc_default))
                        ((Etempvar _rd (tptr Tvoid)) :: nil))
                      (Scall None
                        (Evar _set_rec_g_rec_list (Tfunction
                                                    (Tcons
                                                      (tptr Tvoid)
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        Tnil)) tvoid
                                                    cc_default))
                        ((Etempvar _rec (tptr Tvoid)) ::
                         (Etempvar _t'4 (tptr Tvoid)) ::
                         nil)))
                    (Ssequence
                      (Scall None
                        (Evar _rec_granule_measure (Tfunction
                                                     (Tcons
                                                       (tptr Tvoid)
                                                       (Tcons
                                                         (tptr Tvoid)
                                                         (Tcons tulong Tnil)))
                                                     tvoid cc_default))
                        ((Etempvar _rd (tptr Tvoid)) ::
                         (Etempvar _rec (tptr Tvoid)) ::
                         (Econst_long (Int64.repr 4096) tulong) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _set_g_rec_rd (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    Tnil)) tvoid cc_default))
                          ((Etempvar _g_rec (tptr Tvoid)) ::
                           (Etempvar _g_rd (tptr Tvoid)) ::
                           nil))
                        (Ssequence
                          (Scall None
                            (Evar _atomic_granule_get (Tfunction
                                                        (Tcons
                                                          (tptr Tvoid)
                                                          Tnil) tvoid
                                                        cc_default))
                            ((Etempvar _g_rd (tptr Tvoid)) ::
                             nil))
                          (Ssequence
                            (Scall (Some _t'5)
                              (Evar _get_rec_params_flags (Tfunction Tnil
                                                            tulong cc_default))
                              nil)
                            (Scall None
                              (Evar _set_rec_runnable (Tfunction
                                                        (Tcons
                                                          (tptr Tvoid)
                                                          (Tcons tuint Tnil))
                                                        tvoid cc_default))
                              ((Etempvar _rec (tptr Tvoid)) ::
                               (Ebinop Oand (Etempvar _t'5 tulong)
                                 (Econst_long (Int64.repr 1) tulong) tulong) ::
                               nil)))))))))))))))
.

Definition f_rec_create_ops := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_g_rd, (tptr Tvoid)) ::
                (_g_rec, (tptr Tvoid)) ::
                (_rd, (tptr Tvoid)) ::
                (_rec_list, (tptr Tvoid)) ::
                (_rec, (tptr Tvoid)) ::
                (_mpidr, tulong) :: (_rec_idx, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tulong) :: (_t'4, (tptr Tvoid)) ::
               (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := rec_create_ops_body
|}.
