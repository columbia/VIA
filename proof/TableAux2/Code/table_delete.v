Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _g := 1%positive.
Definition _g_llt := 2%positive.
Definition _granule := 3%positive.
Definition _i := 4%positive.
Definition _ipa_state := 5%positive.
Definition _new_pgte := 6%positive.
Definition _pa := 7%positive.
Definition _pgte := 8%positive.
Definition _ret := 9%positive.
Definition _state := 10%positive.
Definition _table := 11%positive.
Definition _t'1 := 12%positive.

Definition table_delete_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _table_has_destroyed (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                                     cc_default))
        ((Etempvar _table (tptr Tvoid)) :: nil))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tuint)
                     (Econst_int (Int.repr 1) tuint) tint)
        (Sset _ipa_state (Ecast (Econst_int (Int.repr 3) tuint) tulong))
        (Sset _ipa_state (Ecast (Econst_int (Int.repr 0) tuint) tulong))))
    (Ssequence
      (Sset _new_pgte
        (Ebinop Oor
          (Ebinop Omul (Etempvar _ipa_state tulong)
            (Econst_long (Int64.repr 72057594037927936) tulong) tulong)
          (Econst_long (Int64.repr 0) tulong) tulong))
      (Ssequence
        (Scall None
          (Evar _granule_put (Tfunction
                               (Tcons (tptr Tvoid) Tnil)
                               tvoid cc_default))
          ((Etempvar _g_llt (tptr Tvoid)) :: nil))
        (Sreturn (Some (Etempvar _new_pgte tulong))))))
.

Definition f_table_delete := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr Tvoid)) ::
                (_g_llt, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_ipa_state, tulong) :: (_new_pgte, tulong) ::
               (_t'1, tuint) :: nil);
  fn_body := table_delete_body
|}.
