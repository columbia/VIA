Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _cntv_ctl := 1%positive.
Definition _ec := 2%positive.
Definition _esr := 3%positive.
Definition _g := 4%positive.
Definition _i := 5%positive.
Definition _mask := 6%positive.
Definition _masked := 7%positive.
Definition _rec := 8%positive.
Definition _rec__1 := 9%positive.
Definition _reg := 10%positive.
Definition _ret := 11%positive.
Definition _rt := 12%positive.
Definition _timer := 13%positive.
Definition _val := 14%positive.
Definition _t'1 := 15%positive.
Definition _t'2 := 16%positive.
Definition _t'3 := 17%positive.
Definition _t'4 := 18%positive.
Definition _t'5 := 19%positive.
Definition _t'6 := 20%positive.
Definition _t'7 := 21%positive.
Definition _t'8 := 22%positive.

Definition handle_vtimer_sysreg_write_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _ESR_EL2_SYSREG_ISS_RT (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
        ((Etempvar _esr tulong) :: nil))
      (Sset _rt (Etempvar _t'1 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_rec_regs (Tfunction
                                (Tcons (tptr Tvoid)
                                  (Tcons tuint Tnil)) tulong cc_default))
          ((Etempvar _rec (tptr Tvoid)) ::
           (Etempvar _rt tuint) :: nil))
        (Sset _val (Etempvar _t'2 tulong)))
      (Ssequence
        (Sset _ec
          (Ecast
            (Ebinop Oand (Etempvar _esr tulong)
              (Econst_long (Int64.repr 4193310) tulong) tulong) tuint))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _ec tuint)
                         (Econst_long (Int64.repr 3209222) tulong) tint)
            (Scall None
              (Evar _sysreg_write (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                    tvoid cc_default))
              ((Econst_int (Int.repr 37) tuint) :: (Etempvar _val tulong) ::
               nil))
            (Sifthenelse (Ebinop Oeq (Etempvar _ec tuint)
                           (Econst_long (Int64.repr 3340294) tulong) tint)
              (Ssequence
                (Scall None
                  (Evar _set_rec_vtimer_masked (Tfunction
                                                 (Tcons
                                                   (tptr Tvoid)
                                                   (Tcons tuint Tnil)) tvoid
                                                 cc_default))
                  ((Etempvar _rec (tptr Tvoid)) ::
                   (Ebinop Oand (Etempvar _val tulong)
                     (Econst_long (Int64.repr 2) tulong) tulong) :: nil))
                (Scall None
                  (Evar _sysreg_write (Tfunction
                                        (Tcons tuint (Tcons tulong Tnil)) tvoid
                                        cc_default))
                  ((Econst_int (Int.repr 35) tuint) ::
                   (Ebinop Oor (Etempvar _val tulong)
                     (Econst_long (Int64.repr 2) tulong) tulong) :: nil)))
              (Sifthenelse (Ebinop Oeq (Etempvar _ec tuint)
                             (Econst_long (Int64.repr 3471366) tulong) tint)
                (Scall None
                  (Evar _sysreg_write (Tfunction
                                        (Tcons tuint (Tcons tulong Tnil)) tvoid
                                        cc_default))
                  ((Econst_int (Int.repr 36) tuint) ::
                   (Etempvar _val tulong) :: nil))
                Sskip)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                     cc_default))
                ((Econst_int (Int.repr 35) tuint) :: nil))
              (Sset _cntv_ctl (Etempvar _t'3 tulong)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _get_rec_vtimer_masked (Tfunction
                                                 (Tcons
                                                   (tptr Tvoid)
                                                   Tnil) tuint cc_default))
                  ((Etempvar _rec (tptr Tvoid)) :: nil))
                (Sifthenelse (Ebinop One (Etempvar _t'6 tuint)
                               (Econst_int (Int.repr 0) tuint) tint)
                  (Sset _t'7 (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Scall (Some _t'8)
                      (Evar _timer_condition_met (Tfunction (Tcons tulong Tnil)
                                                   tuint cc_default))
                      ((Etempvar _cntv_ctl tulong) :: nil))
                    (Sset _t'7
                      (Ecast
                        (Ebinop Oeq (Etempvar _t'8 tuint)
                          (Econst_int (Int.repr 0) tuint) tint) tbool)))))
              (Sifthenelse (Etempvar _t'7 tint)
                (Ssequence
                  (Scall None
                    (Evar _set_rec_vtimer_asserted (Tfunction
                                                     (Tcons
                                                       (tptr Tvoid)
                                                       (Tcons tuint Tnil))
                                                     tvoid cc_default))
                    ((Etempvar _rec (tptr Tvoid)) ::
                     (Econst_int (Int.repr 0) tuint) :: nil))
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
                        (Evar _set_rec_sysregs (Tfunction
                                                 (Tcons
                                                   (tptr Tvoid)
                                                   (Tcons tuint
                                                     (Tcons tulong Tnil)))
                                                 tvoid cc_default))
                        ((Etempvar _rec (tptr Tvoid)) ::
                         (Econst_int (Int.repr 69) tuint) ::
                         (Ebinop Oand (Etempvar _t'4 tulong)
                           (Econst_long (Int64.repr (18446744073709543423)) tulong) tulong) ::
                         nil)))
                    (Ssequence
                      (Scall (Some _t'5)
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
                         (Etempvar _t'5 tulong) :: nil)))))
                Sskip)))))))
.

Definition f_handle_vtimer_sysreg_write := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: (_esr, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_rt, tuint) :: (_val, tulong) :: (_cntv_ctl, tulong) ::
               (_ec, tuint) :: (_t'8, tuint) :: (_t'7, tint) ::
               (_t'6, tuint) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tuint) :: nil);
  fn_body := handle_vtimer_sysreg_write_body
|}.
