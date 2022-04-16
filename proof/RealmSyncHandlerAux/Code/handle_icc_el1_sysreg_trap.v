Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _esr := 1%positive.
Definition _i := 2%positive.
Definition _icc := 3%positive.
Definition _rec := 4%positive.
Definition _rec__1 := 5%positive.
Definition _reg := 6%positive.
Definition _ret := 7%positive.
Definition _rt := 8%positive.
Definition _t'1 := 9%positive.
Definition _t'2 := 10%positive.

Definition handle_icc_el1_sysreg_trap_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _ESR_EL2_SYSREG_ISS_RT (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
        ((Etempvar _esr tulong) :: nil))
      (Sset _rt (Etempvar _t'1 tuint)))
    (Ssequence
      (Scall (Some _t'2)
        (Evar _ESR_EL2_SYSREG_IS_WRITE (Tfunction (Tcons tulong Tnil) tuint
                                         cc_default))
        ((Etempvar _esr tulong) :: nil))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tuint)
                     (Econst_int (Int.repr 0) tuint) tint)
        (Scall None
          (Evar _set_rec_regs (Tfunction
                                (Tcons (tptr Tvoid)
                                  (Tcons tuint (Tcons tulong Tnil))) tvoid
                                cc_default))
          ((Etempvar _rec (tptr Tvoid)) ::
           (Etempvar _rt tuint) :: (Econst_long (Int64.repr 0) tulong) :: nil))
        Sskip)))
.

Definition f_handle_icc_el1_sysreg_trap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: (_esr, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_rt, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := handle_icc_el1_sysreg_trap_body
|}.
