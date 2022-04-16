Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _ec := 1%positive.
Definition _esr := 2%positive.
Definition _i := 3%positive.
Definition _rec := 4%positive.
Definition _rec__1 := 5%positive.
Definition _ret := 6%positive.
Definition _timer := 7%positive.
Definition _t'1 := 8%positive.
Definition _t'2 := 9%positive.
Definition _t'3 := 10%positive.
Definition _t'4 := 11%positive.
Definition _t'5 := 12%positive.
Definition _t'6 := 13%positive.

Definition handle_timer_sysreg_trap_body :=
  (Ssequence
    (Sset _ec
      (Ecast
        (Ebinop Oand (Etempvar _esr tulong)
          (Econst_long (Int64.repr 4193310) tulong) tulong) tuint))
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _ec tuint)
                       (Econst_long (Int64.repr 3209222) tulong) tint)
          (Sset _t'5 (Econst_int (Int.repr 1) tint))
          (Sset _t'5
            (Ecast
              (Ebinop Oeq (Etempvar _ec tuint)
                (Econst_long (Int64.repr 3340294) tulong) tint) tbool)))
        (Sifthenelse (Etempvar _t'5 tint)
          (Sset _t'6 (Econst_int (Int.repr 1) tint))
          (Sset _t'6
            (Ecast
              (Ebinop Oeq (Etempvar _ec tuint)
                (Econst_long (Int64.repr 3471366) tulong) tint) tbool))))
      (Sifthenelse (Etempvar _t'6 tint)
        (Ssequence
          (Scall (Some _t'1)
            (Evar _ESR_EL2_SYSREG_IS_WRITE (Tfunction (Tcons tulong Tnil) tuint
                                             cc_default))
            ((Etempvar _esr tulong) :: nil))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tuint)
                         (Econst_int (Int.repr 1) tuint) tint)
            (Scall None
              (Evar _handle_vtimer_sysreg_write (Tfunction
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    (Tcons tulong Tnil)) tvoid
                                                  cc_default))
              ((Etempvar _rec (tptr Tvoid)) ::
               (Etempvar _esr tulong) :: nil))
            (Scall None
              (Evar _handle_vtimer_sysreg_read (Tfunction
                                                 (Tcons
                                                   (tptr Tvoid)
                                                   (Tcons tulong Tnil)) tvoid
                                                 cc_default))
              ((Etempvar _rec (tptr Tvoid)) ::
               (Etempvar _esr tulong) :: nil))))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _ec tuint)
                           (Econst_long (Int64.repr 3209220) tulong) tint)
              (Sset _t'3 (Econst_int (Int.repr 1) tint))
              (Sset _t'3
                (Ecast
                  (Ebinop Oeq (Etempvar _ec tuint)
                    (Econst_long (Int64.repr 3340292) tulong) tint) tbool)))
            (Sifthenelse (Etempvar _t'3 tint)
              (Sset _t'4 (Econst_int (Int.repr 1) tint))
              (Sset _t'4
                (Ecast
                  (Ebinop Oeq (Etempvar _ec tuint)
                    (Econst_long (Int64.repr 3471364) tulong) tint) tbool))))
          (Sifthenelse (Etempvar _t'4 tint)
            (Ssequence
              (Scall (Some _t'2)
                (Evar _ESR_EL2_SYSREG_IS_WRITE (Tfunction (Tcons tulong Tnil)
                                                 tuint cc_default))
                ((Etempvar _esr tulong) :: nil))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tuint)
                             (Econst_int (Int.repr 1) tuint) tint)
                (Scall None
                  (Evar _handle_ptimer_sysreg_write (Tfunction
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        (Tcons tulong Tnil))
                                                      tvoid cc_default))
                  ((Etempvar _rec (tptr Tvoid)) ::
                   (Etempvar _esr tulong) :: nil))
                (Scall None
                  (Evar _handle_ptimer_sysreg_read (Tfunction
                                                     (Tcons
                                                       (tptr Tvoid)
                                                       (Tcons tulong Tnil))
                                                     tvoid cc_default))
                  ((Etempvar _rec (tptr Tvoid)) ::
                   (Etempvar _esr tulong) :: nil))))
            Sskip)))))
.

Definition f_handle_timer_sysreg_trap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: (_esr, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_ec, tuint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body := handle_timer_sysreg_trap_body
|}.
