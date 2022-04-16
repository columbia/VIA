Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _cntv_ctl := 1%positive.
Definition _ec := 2%positive.
Definition _emulated_timer_state := 3%positive.
Definition _esr := 4%positive.
Definition _g := 5%positive.
Definition _i := 6%positive.
Definition _rec := 7%positive.
Definition _rec__1 := 8%positive.
Definition _reg := 9%positive.
Definition _ret := 10%positive.
Definition _rt := 11%positive.
Definition _timer := 12%positive.
Definition _t'1 := 13%positive.
Definition _t'2 := 14%positive.
Definition _t'3 := 15%positive.
Definition _t'4 := 16%positive.
Definition _t'5 := 17%positive.
Definition _t'6 := 18%positive.

Definition handle_ptimer_sysreg_read_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _ESR_EL2_SYSREG_ISS_RT (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
        ((Etempvar _esr tulong) :: nil))
      (Sset _rt (Etempvar _t'1 tuint)))
    (Ssequence
      (Sset _ec
        (Ecast
          (Ebinop Oand (Etempvar _esr tulong)
            (Econst_long (Int64.repr 4193310) tulong) tulong) tuint))
      (Sifthenelse (Ebinop Oeq (Etempvar _ec tuint)
                     (Econst_long (Int64.repr 3209220) tulong) tint)
        (Ssequence
          (Scall (Some _t'2)
            (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong cc_default))
            ((Econst_int (Int.repr 34) tuint) :: nil))
          (Scall None
            (Evar _set_rec_regs (Tfunction
                                  (Tcons (tptr Tvoid)
                                    (Tcons tuint (Tcons tulong Tnil))) tvoid
                                  cc_default))
            ((Etempvar _rec (tptr Tvoid)) ::
             (Etempvar _rt tuint) :: (Etempvar _t'2 tulong) :: nil)))
        (Sifthenelse (Ebinop Oeq (Etempvar _ec tuint)
                       (Econst_long (Int64.repr 3340292) tulong) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                     cc_default))
                ((Econst_int (Int.repr 32) tuint) :: nil))
              (Sset _cntv_ctl (Etempvar _t'3 tulong)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _get_rec_ptimer (Tfunction
                                          (Tcons (tptr Tvoid)
                                            Tnil)
                                          (tptr Tvoid)
                                          cc_default))
                  ((Etempvar _rec (tptr Tvoid)) :: nil))
                (Scall (Some _t'5)
                  (Evar _emulate_timer_ctl_read (Tfunction
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    (Tcons tulong Tnil)) tulong
                                                  cc_default))
                  ((Etempvar _t'4 (tptr Tvoid)) ::
                   (Etempvar _cntv_ctl tulong) :: nil)))
              (Scall None
                (Evar _set_rec_regs (Tfunction
                                      (Tcons (tptr Tvoid)
                                        (Tcons tuint (Tcons tulong Tnil)))
                                      tvoid cc_default))
                ((Etempvar _rec (tptr Tvoid)) ::
                 (Etempvar _rt tuint) :: (Etempvar _t'5 tulong) :: nil))))
          (Sifthenelse (Ebinop Oeq (Etempvar _ec tuint)
                         (Econst_long (Int64.repr 3471364) tulong) tint)
            (Ssequence
              (Scall (Some _t'6)
                (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                     cc_default))
                ((Econst_int (Int.repr 33) tuint) :: nil))
              (Scall None
                (Evar _set_rec_regs (Tfunction
                                      (Tcons (tptr Tvoid)
                                        (Tcons tuint (Tcons tulong Tnil)))
                                      tvoid cc_default))
                ((Etempvar _rec (tptr Tvoid)) ::
                 (Etempvar _rt tuint) :: (Etempvar _t'6 tulong) :: nil)))
            Sskip)))))
.

Definition f_handle_ptimer_sysreg_read := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: (_esr, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_rt, tuint) :: (_ec, tuint) :: (_cntv_ctl, tulong) ::
               (_t'6, tulong) :: (_t'5, tulong) ::
               (_t'4, (tptr Tvoid)) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tuint) :: nil);
  fn_body := handle_ptimer_sysreg_read_body
|}.
