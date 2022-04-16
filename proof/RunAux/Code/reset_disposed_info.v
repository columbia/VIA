Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _i := 1%positive.
Definition _info := 2%positive.
Definition _pending := 3%positive.
Definition _rec := 4%positive.
Definition _rec__1 := 5%positive.
Definition _ret := 6%positive.

Definition reset_disposed_info_body :=
  (Scall None
    (Evar _set_rec_dispose_pending (Tfunction
                                     (Tcons (tptr Tvoid)
                                       (Tcons tuint Tnil)) tvoid cc_default))
    ((Etempvar _rec (tptr Tvoid)) ::
     (Econst_int (Int.repr 0) tuint) :: nil))
.

Definition f_reset_disposed_info := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := reset_disposed_info_body
|}.
