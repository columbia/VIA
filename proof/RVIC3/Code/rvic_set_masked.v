Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _bit := 1%positive.
Definition _bits := 2%positive.
Definition _g := 3%positive.
Definition _i := 4%positive.
Definition _intid := 5%positive.
Definition _mask := 6%positive.
Definition _masked := 7%positive.
Definition _rec := 8%positive.
Definition _rec_rvic_state := 9%positive.
Definition _ret := 10%positive.
Definition _rvic := 11%positive.
Definition _t'1 := 12%positive.

Definition rvic_set_masked_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_rvic_mask_bits (Tfunction
                                    (Tcons
                                      (tptr Tvoid)
                                      Tnil) (tptr Tvoid) cc_default))
        ((Etempvar _rvic (tptr Tvoid)) :: nil))
      (Sset _bits (Etempvar _t'1 (tptr Tvoid))))
    (Scall None
      (Evar _rvic_set_flag (Tfunction (Tcons tulong (Tcons (tptr Tvoid) Tnil))
                             tvoid cc_default))
      ((Etempvar _intid tulong) :: (Etempvar _bits (tptr Tvoid)) :: nil)))
.

Definition f_rvic_set_masked := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rvic, (tptr Tvoid)) ::
                (_intid, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_bits, (tptr Tvoid)) :: (_t'1, (tptr Tvoid)) :: nil);
  fn_body := rvic_set_masked_body
|}.
