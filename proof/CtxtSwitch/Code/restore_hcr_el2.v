Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _rec := 1%positive.
Definition _rec__1 := 2%positive.
Definition _ret := 3%positive.
Definition _t'1 := 4%positive.

Definition restore_hcr_el2_body :=
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_rec_common_sysregs (Tfunction
                                      (Tcons (tptr Tvoid)
                                        (Tcons tuint Tnil)) tulong cc_default))
      ((Etempvar _rec (tptr Tvoid)) ::
       (Econst_int (Int.repr 75) tuint) :: nil))
    (Scall None
      (Evar _sysreg_write (Tfunction (Tcons tuint (Tcons tulong Tnil)) tvoid
                            cc_default))
      ((Econst_int (Int.repr 75) tuint) :: (Etempvar _t'1 tulong) :: nil)))
.

Definition f_restore_hcr_el2 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body := restore_hcr_el2_body
|}.
