Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _g := 1%positive.
Definition _granule := 2%positive.
Definition _i := 3%positive.
Definition _pgte := 4%positive.
Definition _pte := 5%positive.
Definition _pte_inc := 6%positive.
Definition _pte_val := 7%positive.
Definition _ret := 8%positive.
Definition _table := 9%positive.
Definition _val := 10%positive.

Definition granule_fill_table_body :=
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Swhile
        (Ebinop Olt (Etempvar _i tuint) (Econst_long (Int64.repr 512) tulong)
          tint)
        (Ssequence
          (Scall None
            (Evar _pgte_write (Tfunction
                                (Tcons (tptr Tvoid)
                                  (Tcons tulong (Tcons tulong Tnil))) tvoid
                                cc_default))
            ((Etempvar _pte (tptr Tvoid)) :: (Etempvar _i tuint) ::
             (Etempvar _pte_val tulong) :: nil))
          (Ssequence
            (Sset _pte_val
              (Ebinop Oadd (Etempvar _pte_val tulong)
                (Etempvar _pte_inc tulong) tulong))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                tuint)))))
      (Scall None (Evar _barrier (Tfunction Tnil tvoid cc_default)) nil)))
.

Definition f_granule_fill_table := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_pte, (tptr Tvoid)) :: (_pte_val, tulong) ::
                (_pte_inc, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: nil);
  fn_body := granule_fill_table_body
|}.
