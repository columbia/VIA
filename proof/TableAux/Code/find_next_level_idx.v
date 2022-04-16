Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _entry := 1%positive.
Definition _g := 2%positive.
Definition _g_tbl := 3%positive.
Definition _granule := 4%positive.
Definition _i := 5%positive.
Definition _idx := 6%positive.
Definition _level := 7%positive.
Definition _next := 8%positive.
Definition _pgte := 9%positive.
Definition _ret := 10%positive.
Definition _table := 11%positive.
Definition _t'1 := 12%positive.
Definition _t'2 := 13%positive.
Definition _t'3 := 14%positive.
Definition _t'4 := 15%positive.
Definition _t'5 := 16%positive.
Definition _t'6 := 17%positive.

Definition find_next_level_idx_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _granule_map (Tfunction
                             (Tcons (tptr Tvoid)
                               (Tcons tuint Tnil)) (tptr Tvoid) cc_default))
        ((Etempvar _g_tbl (tptr Tvoid)) ::
         (Econst_int (Int.repr 5) tuint) :: nil))
      (Sset _table (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _pgte_read (Tfunction (Tcons (tptr Tvoid) (Tcons tulong Tnil))
                             tulong cc_default))
          ((Etempvar _table (tptr Tvoid)) :: (Etempvar _idx tulong) :: nil))
        (Sset _entry (Etempvar _t'2 tulong)))
      (Ssequence
        (Scall None
          (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil) tvoid
                                cc_default))
          ((Etempvar _table (tptr Tvoid)) :: nil))
        (Ssequence
          (Ssequence
            (Scall (Some _t'6)
              (Evar _entry_is_table (Tfunction (Tcons tulong Tnil) tuint
                                      cc_default))
              ((Etempvar _entry tulong) :: nil))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint)
                           (Econst_int (Int.repr 0) tuint) tint)
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _null_ptr (Tfunction Tnil (tptr Tvoid) cc_default))
                  nil)
                (Sset _next (Etempvar _t'3 (tptr Tvoid))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _entry_to_phys (Tfunction
                                           (Tcons tulong (Tcons tulong Tnil))
                                           tulong cc_default))
                    ((Etempvar _entry tulong) ::
                     (Econst_long (Int64.repr 3) tulong) :: nil))
                  (Scall (Some _t'5)
                    (Evar _find_granule (Tfunction (Tcons tulong Tnil)
                                          (tptr Tvoid)
                                          cc_default))
                    ((Etempvar _t'4 tulong) :: nil)))
                (Sset _next (Etempvar _t'5 (tptr Tvoid))))))
          (Sreturn (Some (Etempvar _next (tptr Tvoid))))))))
.

Definition f_find_next_level_idx := {|
  fn_return := (tptr Tvoid);
  fn_callconv := cc_default;
  fn_params := ((_g_tbl, (tptr Tvoid)) ::
                (_idx, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_table, (tptr Tvoid)) :: (_entry, tulong) ::
               (_next, (tptr Tvoid)) :: (_t'6, tuint) ::
               (_t'5, (tptr Tvoid)) :: (_t'4, tulong) ::
               (_t'3, (tptr Tvoid)) :: (_t'2, tulong) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := find_next_level_idx_body
|}.
