Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _base := 2%positive.
Definition _base_pa := 3%positive.
Definition _entry := 4%positive.
Definition _expected_pa := 5%positive.
Definition _i := 6%positive.
Definition _i__1 := 7%positive.
Definition _ipa_state := 8%positive.
Definition _level := 9%positive.
Definition _pgte := 10%positive.
Definition _ret := 11%positive.
Definition _state := 12%positive.
Definition _table := 13%positive.
Definition _t'1 := 14%positive.
Definition _t'2 := 15%positive.
Definition _t'3 := 16%positive.
Definition _t'4 := 17%positive.
Definition _t'5 := 18%positive.

Definition table_maps_block_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _pgte_read (Tfunction (Tcons (tptr Tvoid) (Tcons tulong Tnil))
                           tulong cc_default))
        ((Etempvar _table (tptr Tvoid)) :: (Econst_int (Int.repr 0) tint) ::
         nil))
      (Sset _pgte (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _entry_to_phys (Tfunction (Tcons tulong (Tcons tulong Tnil))
                                 tulong cc_default))
          ((Etempvar _pgte tulong) :: (Etempvar _level tulong) :: nil))
        (Sset _base_pa (Etempvar _t'2 tulong)))
      (Ssequence
        (Scall (Some _t'5)
          (Evar _addr_is_level_aligned (Tfunction
                                         (Tcons tulong (Tcons tulong Tnil))
                                         tuint cc_default))
          ((Etempvar _base_pa tulong) ::
           (Ebinop Osub (Etempvar _level tulong) (Econst_int (Int.repr 1) tint)
             tulong) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tuint)
                       (Econst_int (Int.repr 0) tuint) tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
          (Ssequence
            (Sset _ret (Econst_int (Int.repr 1) tuint))
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tuint))
              (Ssequence
                (Swhile
                  (Ebinop Olt (Etempvar _i tuint)
                    (Econst_long (Int64.repr 512) tulong) tint)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _pgte_read (Tfunction
                                           (Tcons (tptr Tvoid)
                                             (Tcons tulong Tnil)) tulong
                                           cc_default))
                        ((Etempvar _table (tptr Tvoid)) ::
                         (Etempvar _i tuint) :: nil))
                      (Sset _pgte (Etempvar _t'3 tulong)))
                    (Ssequence
                      (Sset _expected_pa
                        (Ebinop Oadd (Etempvar _base_pa tulong)
                          (Ebinop Omul (Etempvar _i tuint)
                            (Econst_long (Int64.repr 4096) tulong) tulong)
                          tulong))
                      (Ssequence
                        (Sifthenelse (Ebinop One
                                       (Ebinop Odiv
                                         (Ebinop Oand (Etempvar _pgte tulong)
                                           (Econst_long (Int64.repr 504403158265495552) tulong)
                                           tulong)
                                         (Econst_long (Int64.repr 72057594037927936) tulong)
                                         tulong) (Etempvar _ipa_state tulong)
                                       tint)
                          (Sset _ret (Econst_int (Int.repr 0) tuint))
                          (Ssequence
                            (Scall (Some _t'4)
                              (Evar _entry_to_phys (Tfunction
                                                     (Tcons tulong
                                                       (Tcons tulong Tnil))
                                                     tulong cc_default))
                              ((Etempvar _pgte tulong) ::
                               (Etempvar _level tulong) :: nil))
                            (Sifthenelse (Ebinop One (Etempvar _t'4 tulong)
                                           (Etempvar _expected_pa tulong) tint)
                              (Sset _ret (Econst_int (Int.repr 0) tuint))
                              Sskip)))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tuint)
                            (Econst_int (Int.repr 1) tint) tuint))))))
                (Sreturn (Some (Etempvar _ret tuint))))))))))
.

Definition f_table_maps_block := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr Tvoid)) :: (_level, tulong) ::
                (_ipa_state, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_base_pa, tulong) :: (_i, tulong) :: (_pgte, tulong) ::
               (_ret, tuint) :: (_i, tuint) :: (_expected_pa, tulong) ::
               (_t'5, tuint) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := table_maps_block_body
|}.
