Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _context_id := 2%positive.
Definition _entry_point_address := 3%positive.
Definition _rec := 4%positive.
Definition _rec__1 := 5%positive.
Definition _ret := 6%positive.

Definition psci_cpu_suspend_body :=
  (Ssequence
    (Scall None
      (Evar _set_psci_result_forward_psci_call (Tfunction (Tcons tuint Tnil)
                                                 tvoid cc_default))
      ((Econst_int (Int.repr 1) tuint) :: nil))
    (Scall None
      (Evar _set_psci_result_x0 (Tfunction (Tcons tulong Tnil) tvoid
                                  cc_default))
      ((Econst_long (Int64.repr 0) tulong) :: nil)))
.

Definition f_psci_cpu_suspend := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_entry_point_address, tulong) :: (_context_id, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := psci_cpu_suspend_body
|}.
