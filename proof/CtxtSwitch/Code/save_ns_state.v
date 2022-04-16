Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _ret := 1%positive.
Definition _t'1 := 2%positive.

Definition save_ns_state_body :=
  (Ssequence
    (Scall None
      (Evar _save_ns_state_sysreg_state (Tfunction Tnil tvoid cc_default)) nil)
    (Ssequence
      (Scall (Some _t'1)
        (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong cc_default))
        ((Econst_int (Int.repr 109) tuint) :: nil))
      (Scall None
        (Evar _set_ns_state (Tfunction (Tcons tuint (Tcons tulong Tnil)) tvoid
                              cc_default))
        ((Econst_int (Int.repr 109) tuint) :: (Etempvar _t'1 tulong) :: nil))))
.

Definition f_save_ns_state := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body := save_ns_state_body
|}.
