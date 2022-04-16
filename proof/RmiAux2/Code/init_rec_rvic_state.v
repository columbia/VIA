Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _bit := 1%positive.
Definition _bits := 2%positive.
Definition _i := 3%positive.
Definition _mask := 4%positive.
Definition _rec := 5%positive.
Definition _rec_rvic_state := 6%positive.
Definition _ret := 7%positive.
Definition _rvic := 8%positive.

Definition init_rec_rvic_state_body :=
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Swhile
      (Ebinop Olt (Etempvar _i tuint) (Econst_long (Int64.repr 8) tulong) tint)
      (Ssequence
        (Scall None
          (Evar _set_rvic_mask_bits (Tfunction
                                      (Tcons
                                        (tptr Tvoid)
                                        (Tcons tuint (Tcons tulong Tnil)))
                                      tvoid cc_default))
          ((Etempvar _rvic (tptr Tvoid)) ::
           (Etempvar _i tuint) :: (Econst_long (Int64.repr (18446744073709551615)) tulong) ::
           nil))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint)))))
.

Definition f_init_rec_rvic_state := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rvic, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: nil);
  fn_body := init_rec_rvic_state_body
|}.
