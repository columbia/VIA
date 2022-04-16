Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _ret := 1%positive.
Definition _t'1 := 2%positive.

Definition realm_ns_step_body :=
  (Ssequence
    (Scall (Some _t'1) (Evar _user_step (Tfunction Tnil tulong cc_default))
      nil)
    (Sreturn (Some (Etempvar _t'1 tulong))))
.

Definition f_realm_ns_step := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body := realm_ns_step_body
|}.
