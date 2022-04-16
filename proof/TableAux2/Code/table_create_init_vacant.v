Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _g := 1%positive.
Definition _g_llt := 2%positive.
Definition _granule := 3%positive.
Definition _i := 4%positive.
Definition _ipa_state := 5%positive.
Definition _pa := 6%positive.
Definition _pte := 7%positive.
Definition _ret := 8%positive.
Definition _state := 9%positive.
Definition _table := 10%positive.

Definition table_create_init_vacant_body :=
  (Ssequence
    (Scall None
      (Evar _granule_fill_table (Tfunction
                                  (Tcons (tptr Tvoid)
                                    (Tcons tulong (Tcons tulong Tnil))) tvoid
                                  cc_default))
      ((Etempvar _pte (tptr Tvoid)) ::
       (Ebinop Oor
         (Ebinop Omul (Etempvar _ipa_state tulong)
           (Econst_long (Int64.repr 72057594037927936) tulong) tulong)
         (Econst_long (Int64.repr 0) tulong) tulong) ::
       (Econst_int (Int.repr 0) tint) :: nil))
    (Scall None
      (Evar _granule_get (Tfunction
                           (Tcons (tptr Tvoid) Tnil) tvoid
                           cc_default))
      ((Etempvar _g_llt (tptr Tvoid)) :: nil)))
.

Definition f_table_create_init_vacant := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ipa_state, tulong) :: (_pte, (tptr Tvoid)) ::
                (_g_llt, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := table_create_init_vacant_body
|}.
