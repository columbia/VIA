Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _rec := 1%positive.
Definition _rec__1 := 2%positive.
Definition _ret := 3%positive.

Definition psci_system_off_body :=
  (Ssequence
    (Scall None
      (Evar _system_off_reboot (Tfunction
                                 (Tcons (tptr Tvoid) Tnil)
                                 tvoid cc_default))
      ((Etempvar _rec (tptr Tvoid)) :: nil))
    (Scall None
      (Evar _set_psci_result_forward_psci_call (Tfunction (Tcons tuint Tnil)
                                                 tvoid cc_default))
      ((Econst_int (Int.repr 1) tuint) :: nil)))
.

Definition f_psci_system_off := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := psci_system_off_body
|}.
