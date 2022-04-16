Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _esr := 1%positive.
Definition _i := 2%positive.
Definition _info := 3%positive.
Definition _rec := 4%positive.
Definition _rec__1 := 5%positive.
Definition _ret := 6%positive.

Definition reset_last_run_info_body :=
  (Scall None
    (Evar _set_rec_last_run_info_esr (Tfunction
                                       (Tcons (tptr Tvoid)
                                         (Tcons tulong Tnil)) tvoid cc_default))
    ((Etempvar _rec (tptr Tvoid)) ::
     (Econst_long (Int64.repr 0) tulong) :: nil))
.

Definition f_reset_last_run_info := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := reset_last_run_info_body
|}.
