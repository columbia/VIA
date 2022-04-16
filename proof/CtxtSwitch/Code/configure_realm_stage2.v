Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _rec := 1%positive.
Definition _rec__1 := 2%positive.
Definition _ret := 3%positive.
Definition _t'1 := 4%positive.
Definition _t'2 := 5%positive.

Definition configure_realm_stage2_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_rec_common_sysregs (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons tuint Tnil)) tulong
                                        cc_default))
        ((Etempvar _rec (tptr Tvoid)) ::
         (Econst_int (Int.repr 74) tuint) :: nil))
      (Scall None
        (Evar _sysreg_write (Tfunction (Tcons tuint (Tcons tulong Tnil)) tvoid
                              cc_default))
        ((Econst_int (Int.repr 74) tuint) :: (Etempvar _t'1 tulong) :: nil)))
    (Ssequence
      (Scall (Some _t'2)
        (Evar _get_rec_common_sysregs (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons tuint Tnil)) tulong
                                        cc_default))
        ((Etempvar _rec (tptr Tvoid)) ::
         (Econst_int (Int.repr 73) tuint) :: nil))
      (Scall None
        (Evar _sysreg_write (Tfunction (Tcons tuint (Tcons tulong Tnil)) tvoid
                              cc_default))
        ((Econst_int (Int.repr 73) tuint) :: (Etempvar _t'2 tulong) :: nil))))
.

Definition f_configure_realm_stage2 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := configure_realm_stage2_body
|}.
