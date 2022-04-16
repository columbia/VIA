Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _i := 1%positive.
Definition _pgte := 2%positive.
Definition _ret := 3%positive.
Definition _table := 4%positive.
Definition _t'1 := 5%positive.

Definition table_has_destroyed_body :=
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Sset _ret (Econst_int (Int.repr 0) tuint))
      (Ssequence
        (Swhile
          (Ebinop Olt (Etempvar _i tulong)
            (Econst_long (Int64.repr 512) tulong) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _pgte_read (Tfunction
                                   (Tcons (tptr Tvoid) (Tcons tulong Tnil))
                                   tulong cc_default))
                ((Etempvar _table (tptr Tvoid)) :: (Etempvar _i tulong) ::
                 nil))
              (Sset _pgte (Etempvar _t'1 tulong)))
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Ebinop Odiv
                               (Ebinop Oand (Etempvar _pgte tulong)
                                 (Econst_long (Int64.repr 504403158265495552) tulong)
                                 tulong)
                               (Econst_long (Int64.repr 72057594037927936) tulong)
                               tulong) (Econst_int (Int.repr 3) tuint) tint)
                (Sset _ret (Econst_int (Int.repr 1) tuint))
                Sskip)
              (Sset _i
                (Ebinop Oadd (Etempvar _i tulong)
                  (Econst_int (Int.repr 1) tint) tulong)))))
        (Sreturn (Some (Etempvar _ret tuint))))))
.

Definition f_table_has_destroyed := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_ret, tuint) :: (_pgte, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := table_has_destroyed_body
|}.
