Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _bit := 1%positive.
Definition _bits := 2%positive.
Definition _g := 3%positive.
Definition _i := 4%positive.
Definition _intid := 5%positive.
Definition _mask := 6%positive.
Definition _rec := 7%positive.
Definition _rec_rvic_state := 8%positive.
Definition _ret := 9%positive.
Definition _rvic := 10%positive.
Definition _t'1 := 11%positive.
Definition _t'2 := 12%positive.

Definition rvic_is_masked_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_rvic_mask_bits (Tfunction
                                    (Tcons
                                      (tptr Tvoid)
                                      Tnil) (tptr Tvoid) cc_default))
        ((Etempvar _rvic (tptr Tvoid)) :: nil))
      (Sset _bits (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _rvic_test_flag (Tfunction
                                  (Tcons tulong (Tcons (tptr Tvoid) Tnil))
                                  tuint cc_default))
          ((Etempvar _intid tulong) :: (Etempvar _bits (tptr Tvoid)) :: nil))
        (Sset _ret (Etempvar _t'2 tuint)))
      (Sreturn (Some (Etempvar _ret tuint)))))
.

Definition f_rvic_is_masked := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_rvic, (tptr Tvoid)) ::
                (_intid, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_bits, (tptr Tvoid)) :: (_ret, tuint) :: (_t'2, tuint) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := rvic_is_masked_body
|}.
