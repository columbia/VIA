Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _bit := 1%positive.
Definition _bits := 2%positive.
Definition _g := 3%positive.
Definition _i := 4%positive.
Definition _intid := 5%positive.
Definition _pending := 6%positive.
Definition _rec := 7%positive.
Definition _rec_rvic_state := 8%positive.
Definition _ret := 9%positive.
Definition _rvic := 10%positive.
Definition _t'1 := 11%positive.

Definition rvic_set_pending_body :=
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_rvic_pending_bits (Tfunction
                                     (Tcons
                                       (tptr Tvoid)
                                       Tnil) (tptr Tvoid) cc_default))
      ((Etempvar _rvic (tptr Tvoid)) :: nil))
    (Scall None
      (Evar _rvic_set_flag (Tfunction (Tcons tulong (Tcons (tptr Tvoid) Tnil))
                             tvoid cc_default))
      ((Etempvar _intid tulong) :: (Etempvar _t'1 (tptr Tvoid)) :: nil)))
.

Definition f_rvic_set_pending := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rvic, (tptr Tvoid)) ::
                (_intid, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr Tvoid)) :: nil);
  fn_body := rvic_set_pending_body
|}.
