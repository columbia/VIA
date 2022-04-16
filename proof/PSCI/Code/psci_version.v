Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _rec := 1%positive.
Definition _rec__1 := 2%positive.
Definition _ret := 3%positive.
Definition _version_1_1 := 4%positive.

Definition psci_version_body :=
  (Ssequence
    (Sset _version_1_1 (Econst_long (Int64.repr 65537) tulong))
    (Scall None
      (Evar _set_psci_result_x0 (Tfunction (Tcons tulong Tnil) tvoid
                                  cc_default))
      ((Etempvar _version_1_1 tulong) :: nil)))
.

Definition f_psci_version := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_version_1_1, tulong) :: nil);
  fn_body := psci_version_body
|}.
