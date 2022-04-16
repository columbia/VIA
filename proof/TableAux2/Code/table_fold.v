Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _base := 1%positive.
Definition _base_pa := 2%positive.
Definition _entry := 3%positive.
Definition _g := 4%positive.
Definition _g_tbl := 5%positive.
Definition _granule := 6%positive.
Definition _i := 7%positive.
Definition _ipa_state := 8%positive.
Definition _level := 9%positive.
Definition _new_pgte := 10%positive.
Definition _pa := 11%positive.
Definition _pgte := 12%positive.
Definition _ret := 13%positive.
Definition _state := 14%positive.
Definition _table := 15%positive.
Definition _t'1 := 16%positive.
Definition _t'2 := 17%positive.
Definition _t'3 := 18%positive.

Definition table_fold_body :=
  (Ssequence
    (Sset _new_pgte (Econst_long (Int64.repr 0) tulong))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _pgte_read (Tfunction (Tcons (tptr Tvoid) (Tcons tulong Tnil))
                             tulong cc_default))
          ((Etempvar _table (tptr Tvoid)) ::
           (Econst_long (Int64.repr 0) tulong) :: nil))
        (Sset _pgte (Etempvar _t'1 tulong)))
      (Ssequence
        (Sset _ipa_state
          (Ebinop Odiv
            (Ebinop Oand (Etempvar _pgte tulong)
              (Econst_long (Int64.repr 504403158265495552) tulong) tulong)
            (Econst_long (Int64.repr 72057594037927936) tulong) tulong))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _entry_to_phys (Tfunction
                                     (Tcons tulong (Tcons tulong Tnil)) tulong
                                     cc_default))
              ((Etempvar _pgte tulong) ::
               (Ebinop Osub (Etempvar _level tulong)
                 (Econst_int (Int.repr 1) tint) tulong) :: nil))
            (Sset _base_pa (Etempvar _t'2 tulong)))
          (Ssequence
            (Sifthenelse (Ebinop One (Etempvar _level tulong)
                           (Econst_long (Int64.repr 3) tulong) tint)
              (Scall None
                (Evar _assert_cond (Tfunction (Tcons tuint Tnil) tvoid
                                     cc_default))
                ((Econst_int (Int.repr 0) tuint) :: nil))
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _table_maps_block (Tfunction
                                            (Tcons (tptr Tvoid)
                                              (Tcons tulong
                                                (Tcons tulong Tnil))) tuint
                                            cc_default))
                  ((Etempvar _table (tptr Tvoid)) ::
                   (Etempvar _level tulong) :: (Etempvar _ipa_state tulong) ::
                   nil))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tuint)
                               (Econst_int (Int.repr 0) tuint) tint)
                  (Scall None
                    (Evar _assert_cond (Tfunction (Tcons tuint Tnil) tvoid
                                         cc_default))
                    ((Econst_int (Int.repr 0) tuint) :: nil))
                  (Ssequence
                    (Sset _new_pgte
                      (Ebinop Oor
                        (Ebinop Omul (Etempvar _ipa_state tulong)
                          (Econst_long (Int64.repr 72057594037927936) tulong)
                          tulong) (Etempvar _base_pa tulong) tulong))
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _ipa_state tulong)
                                     (Econst_int (Int.repr 2) tuint) tint)
                        (Sset _new_pgte
                          (Ebinop Oor (Etempvar _new_pgte tulong)
                            (Econst_long (Int64.repr 2009) tulong) tulong))
                        (Sset _new_pgte
                          (Ebinop Oor (Etempvar _new_pgte tulong)
                            (Econst_long (Int64.repr 0) tulong) tulong)))
                      (Scall None
                        (Evar _granule_refcount_dec (Tfunction
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        (Tcons tulong Tnil))
                                                      tvoid cc_default))
                        ((Etempvar _g_tbl (tptr Tvoid)) ::
                         (Econst_long (Int64.repr 512) tulong) :: nil)))))))
            (Sreturn (Some (Etempvar _new_pgte tulong))))))))
.

Definition f_table_fold := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr Tvoid)) :: (_level, tulong) ::
                (_g_tbl, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_pgte, tulong) :: (_ipa_state, tulong) ::
               (_base_pa, tulong) :: (_new_pgte, tulong) :: (_t'3, tuint) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := table_fold_body
|}.
