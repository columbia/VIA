Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _esr := 1%positive.
Definition _i := 2%positive.
Definition _idreg := 3%positive.
Definition _mask := 4%positive.
Definition _rec := 5%positive.
Definition _rec__1 := 6%positive.
Definition _reg := 7%positive.
Definition _ret := 8%positive.
Definition _t'1 := 9%positive.
Definition _t'2 := 10%positive.
Definition _t'3 := 11%positive.

Definition handle_id_sysreg_trap_body :=
  (Ssequence
    (Sset _idreg
      (Ecast
        (Ebinop Oand (Etempvar _esr tulong)
          (Econst_long (Int64.repr 4193310) tulong) tulong) tuint))
    (Ssequence
      (Sset _mask (Ecast (Econst_int (Int.repr 0) tuint) tulong))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _ESR_EL2_SYSREG_IS_WRITE (Tfunction (Tcons tulong Tnil) tuint
                                             cc_default))
            ((Etempvar _esr tulong) :: nil))
          (Scall None
            (Evar _assert_cond (Tfunction (Tcons tuint Tnil) tvoid cc_default))
            ((Ebinop Osub (Econst_int (Int.repr 1) tuint) (Etempvar _t'1 tuint)
               tuint) :: nil)))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _idreg tuint)
                         (Econst_long (Int64.repr 3276812) tulong) tint)
            (Sset _mask (Econst_long (Int64.repr 255) tulong))
            Sskip)
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _ESR_EL2_SYSREG_ISS_RT (Tfunction (Tcons tulong Tnil)
                                               tuint cc_default))
                ((Etempvar _esr tulong) :: nil))
              (Scall (Some _t'3)
                (Evar _read_idreg (Tfunction (Tcons tuint Tnil) tulong
                                    cc_default))
                ((Etempvar _idreg tuint) :: nil)))
            (Scall None
              (Evar _set_rec_regs (Tfunction
                                    (Tcons (tptr Tvoid)
                                      (Tcons tuint (Tcons tulong Tnil))) tvoid
                                    cc_default))
              ((Etempvar _rec (tptr Tvoid)) ::
               (Etempvar _t'2 tuint) ::
               (Ebinop Oand (Etempvar _t'3 tulong)
                 (Ebinop Osub (Econst_long (Int64.repr (18446744073709551615)) tulong)
                   (Etempvar _mask tulong) tulong) tulong) :: nil)))))))
.

Definition f_handle_id_sysreg_trap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: (_esr, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_idreg, tuint) :: (_mask, tulong) :: (_t'3, tulong) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := handle_id_sysreg_trap_body
|}.
