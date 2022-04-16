Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _cntp_ctl := 1%positive.
Definition _cntv_ctl := 2%positive.
Definition _emulated_timer_state := 3%positive.
Definition _g := 4%positive.
Definition _g_rec := 5%positive.
Definition _granule := 6%positive.
Definition _i := 7%positive.
Definition _lock := 8%positive.
Definition _rec := 9%positive.
Definition _rec__1 := 10%positive.
Definition _rec_rvic_state := 11%positive.
Definition _ret := 12%positive.
Definition _t'1 := 13%positive.
Definition _t'2 := 14%positive.
Definition _t'3 := 15%positive.
Definition _t'4 := 16%positive.
Definition _t'5 := 17%positive.
Definition _t'6 := 18%positive.
Definition _t'7 := 19%positive.

Definition check_pending_vtimers_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_rec_g_rec (Tfunction
                               (Tcons (tptr Tvoid) Tnil)
                               (tptr Tvoid) cc_default))
        ((Etempvar _rec (tptr Tvoid)) :: nil))
      (Sset _g_rec (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong cc_default))
          ((Econst_int (Int.repr 35) tuint) :: nil))
        (Sset _cntv_ctl (Etempvar _t'2 tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'6)
            (Evar _get_rec_vtimer (Tfunction
                                    (Tcons (tptr Tvoid) Tnil)
                                    (tptr Tvoid)
                                    cc_default))
            ((Etempvar _rec (tptr Tvoid)) :: nil))
          (Scall (Some _t'7)
            (Evar _check_timer_became_asserted (Tfunction
                                                 (Tcons
                                                   (tptr Tvoid)
                                                   (Tcons tulong Tnil)) tuint
                                                 cc_default))
            ((Etempvar _t'6 (tptr Tvoid)) ::
             (Etempvar _cntv_ctl tulong) :: nil)))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tuint)
                       (Econst_int (Int.repr 1) tuint) tint)
          (Ssequence
            (Scall None
              (Evar _granule_lock (Tfunction
                                    (Tcons (tptr Tvoid)
                                      Tnil) tvoid cc_default))
              ((Etempvar _g_rec (tptr Tvoid)) :: nil))
            (Ssequence
              (Sset _cntv_ctl
                (Ebinop Oor (Etempvar _cntv_ctl tulong)
                  (Econst_long (Int64.repr 2) tulong) tulong))
              (Ssequence
                (Scall None
                  (Evar _sysreg_write (Tfunction
                                        (Tcons tuint (Tcons tulong Tnil)) tvoid
                                        cc_default))
                  ((Econst_int (Int.repr 35) tuint) ::
                   (Etempvar _cntv_ctl tulong) :: nil))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _get_rec_sysregs (Tfunction
                                               (Tcons
                                                 (tptr Tvoid)
                                                 (Tcons tuint Tnil)) tulong
                                               cc_default))
                      ((Etempvar _rec (tptr Tvoid)) ::
                       (Econst_int (Int.repr 69) tuint) :: nil))
                    (Scall None
                      (Evar _set_rec_sysregs (Tfunction
                                               (Tcons
                                                 (tptr Tvoid)
                                                 (Tcons tuint
                                                   (Tcons tulong Tnil))) tvoid
                                               cc_default))
                      ((Etempvar _rec (tptr Tvoid)) ::
                       (Econst_int (Int.repr 69) tuint) ::
                       (Ebinop Oor (Etempvar _t'3 tulong)
                         (Econst_long (Int64.repr 8192) tulong) tulong) :: nil)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _get_rec_sysregs (Tfunction
                                                 (Tcons
                                                   (tptr Tvoid)
                                                   (Tcons tuint Tnil)) tulong
                                                 cc_default))
                        ((Etempvar _rec (tptr Tvoid)) ::
                         (Econst_int (Int.repr 69) tuint) :: nil))
                      (Scall None
                        (Evar _sysreg_write (Tfunction
                                              (Tcons tuint (Tcons tulong Tnil))
                                              tvoid cc_default))
                        ((Econst_int (Int.repr 69) tuint) ::
                         (Etempvar _t'4 tulong) :: nil)))
                    (Ssequence
                      (Scall None
                        (Evar _set_rec_vtimer_asserted (Tfunction
                                                         (Tcons
                                                           (tptr Tvoid)
                                                           (Tcons tuint Tnil))
                                                         tvoid cc_default))
                        ((Etempvar _rec (tptr Tvoid)) ::
                         (Econst_int (Int.repr 1) tuint) :: nil))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'5)
                            (Evar _get_rec_rvic (Tfunction
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    Tnil)
                                                  (tptr Tvoid)
                                                  cc_default))
                            ((Etempvar _rec (tptr Tvoid)) ::
                             nil))
                          (Scall None
                            (Evar _rvic_set_pending (Tfunction
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        (Tcons tulong Tnil))
                                                      tvoid cc_default))
                            ((Etempvar _t'5 (tptr Tvoid)) ::
                             (Econst_long (Int64.repr 27) tulong) :: nil)))
                        (Scall None
                          (Evar _granule_unlock (Tfunction
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    Tnil) tvoid cc_default))
                          ((Etempvar _g_rec (tptr Tvoid)) ::
                           nil)))))))))
          Sskip))))
.

Definition f_check_pending_vtimers := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_cntv_ctl, tulong) :: (_cntp_ctl, tulong) ::
               (_g_rec, (tptr Tvoid)) :: (_t'7, tuint) ::
               (_t'6, (tptr Tvoid)) ::
               (_t'5, (tptr Tvoid)) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := check_pending_vtimers_body
|}.
