Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _i := 1%positive.
Definition _rd := 2%positive.
Definition _rd__1 := 3%positive.
Definition _ret := 4%positive.
Definition _state := 5%positive.

Definition realm_activate_ops_body :=
  (Ssequence
    (Scall None
      (Evar _measurement_finish (Tfunction
                                  (Tcons (tptr Tvoid) Tnil)
                                  tvoid cc_default))
      ((Etempvar _rd (tptr Tvoid)) :: nil))
    (Scall None
      (Evar _set_rd_state (Tfunction
                            (Tcons (tptr Tvoid)
                              (Tcons tuint Tnil)) tvoid cc_default))
      ((Etempvar _rd (tptr Tvoid)) ::
       (Econst_int (Int.repr 1) tuint) :: nil)))
.

Definition f_realm_activate_ops := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rd, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := realm_activate_ops_body
|}.
