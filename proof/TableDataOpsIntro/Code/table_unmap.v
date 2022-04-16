Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _data := 2%positive.
Definition _data_addr := 3%positive.
Definition _entry := 4%positive.
Definition _g := 5%positive.
Definition _g_llt := 6%positive.
Definition _g_rd := 7%positive.
Definition _granule := 8%positive.
Definition _i := 9%positive.
Definition _index := 10%positive.
Definition _ipa_state := 11%positive.
Definition _level := 12%positive.
Definition _ll_table := 13%positive.
Definition _llt_pgte := 14%positive.
Definition _lock := 15%positive.
Definition _map_addr := 16%positive.
Definition _new_pgte := 17%positive.
Definition _pa := 18%positive.
Definition _pgte := 19%positive.
Definition _rd := 20%positive.
Definition _ret := 21%positive.
Definition _state := 22%positive.
Definition _table := 23%positive.
Definition _t'1 := 24%positive.
Definition _t'2 := 25%positive.
Definition _t'3 := 26%positive.
Definition _t'4 := 27%positive.
Definition _t'5 := 28%positive.
Definition _t'6 := 29%positive.
Definition _t'7 := 30%positive.

Definition table_unmap_body :=
  (Ssequence
    (Scall None
      (Evar _table_walk_lock_unlock (Tfunction
                                      (Tcons (tptr Tvoid)
                                        (Tcons tulong (Tcons tulong Tnil)))
                                      tvoid cc_default))
      ((Etempvar _g_rd (tptr Tvoid)) ::
       (Etempvar _map_addr tulong) ::
       (Ebinop Osub (Etempvar _level tulong) (Econst_int (Int.repr 1) tuint)
         tulong) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_wi_g_llt (Tfunction Tnil (tptr Tvoid)
                                cc_default)) nil)
        (Sset _g_llt (Etempvar _t'1 (tptr Tvoid))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _get_wi_index (Tfunction Tnil tulong cc_default)) nil)
          (Sset _index (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'7)
              (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                               cc_default))
              ((Etempvar _g_llt (tptr Tvoid)) :: nil))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tuint)
                           (Econst_int (Int.repr 1) tuint) tint)
              (Sset _ret (Econst_long (Int64.repr 1) tulong))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _granule_map (Tfunction
                                         (Tcons
                                           (tptr Tvoid)
                                           (Tcons tuint Tnil)) (tptr Tvoid)
                                         cc_default))
                    ((Etempvar _g_llt (tptr Tvoid)) ::
                     (Econst_int (Int.repr 5) tuint) :: nil))
                  (Sset _ll_table (Etempvar _t'3 (tptr Tvoid))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _pgte_read (Tfunction
                                         (Tcons (tptr Tvoid)
                                           (Tcons tulong Tnil)) tulong
                                         cc_default))
                      ((Etempvar _ll_table (tptr Tvoid)) ::
                       (Etempvar _index tulong) :: nil))
                    (Sset _llt_pgte (Etempvar _t'4 tulong)))
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _level tulong)
                                     (Econst_long (Int64.repr 3) tulong) tint)
                        (Ssequence
                          (Scall (Some _t'6)
                            (Evar _entry_is_table (Tfunction
                                                    (Tcons tulong Tnil) tuint
                                                    cc_default))
                            ((Etempvar _llt_pgte tulong) :: nil))
                          (Sset _t'5
                            (Ecast
                              (Ebinop Oeq (Etempvar _t'6 tuint)
                                (Econst_int (Int.repr 1) tuint) tint) tbool)))
                        (Sset _t'5 (Econst_int (Int.repr 0) tint)))
                      (Sifthenelse (Etempvar _t'5 tint)
                        (Sset _ret
                          (Ecast (Econst_int (Int.repr 1) tuint) tulong))
                        (Ssequence
                          (Sset _data_addr
                            (Ebinop Oand (Etempvar _llt_pgte tulong)
                              (Econst_long (Int64.repr 281474976706560) tulong)
                              tulong))
                          (Ssequence
                            (Sset _ipa_state
                              (Ebinop Odiv
                                (Ebinop Oand (Etempvar _llt_pgte tulong)
                                  (Econst_long (Int64.repr 504403158265495552) tulong)
                                  tulong)
                                (Econst_long (Int64.repr 72057594037927936) tulong)
                                tulong))
                            (Sifthenelse (Ebinop Oeq
                                           (Etempvar _ipa_state tulong)
                                           (Econst_int (Int.repr 2) tuint)
                                           tint)
                              (Ssequence
                                (Sset _new_pgte
                                  (Ebinop Oor
                                    (Ebinop Omul
                                      (Econst_int (Int.repr 1) tuint)
                                      (Econst_long (Int64.repr 72057594037927936) tulong)
                                      tulong) (Etempvar _data_addr tulong)
                                    tulong))
                                (Ssequence
                                  (Scall None
                                    (Evar _pgte_write (Tfunction
                                                        (Tcons (tptr Tvoid)
                                                          (Tcons tulong
                                                            (Tcons tulong Tnil)))
                                                        tvoid cc_default))
                                    ((Etempvar _ll_table (tptr Tvoid)) ::
                                     (Etempvar _index tulong) ::
                                     (Etempvar _new_pgte tulong) :: nil))
                                  (Ssequence
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _level tulong)
                                                   (Econst_long (Int64.repr 3) tulong)
                                                   tint)
                                      (Scall None
                                        (Evar _invalidate_page (Tfunction
                                                                 (Tcons tulong
                                                                   Tnil) tvoid
                                                                 cc_default))
                                        ((Etempvar _map_addr tulong) :: nil))
                                      (Scall None
                                        (Evar _invalidate_block (Tfunction
                                                                  (Tcons tulong
                                                                    Tnil) tvoid
                                                                  cc_default))
                                        ((Etempvar _map_addr tulong) :: nil)))
                                    (Sset _ret
                                      (Ecast (Econst_int (Int.repr 0) tuint)
                                        tulong)))))
                              (Sset _ret
                                (Ecast (Econst_int (Int.repr 1) tuint) tulong)))))))
                    (Ssequence
                      (Scall None
                        (Evar _buffer_unmap (Tfunction
                                              (Tcons (tptr Tvoid) Tnil) tvoid
                                              cc_default))
                        ((Etempvar _ll_table (tptr Tvoid)) :: nil))
                      (Scall None
                        (Evar _granule_unlock (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  Tnil) tvoid cc_default))
                        ((Etempvar _g_llt (tptr Tvoid)) ::
                         nil))))))))
          (Sreturn (Some (Etempvar _ret tulong)))))))
.

Definition f_table_unmap := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_g_rd, (tptr Tvoid)) ::
                (_map_addr, tulong) :: (_level, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ll_table, (tptr Tvoid)) :: (_llt_pgte, tulong) ::
               (_new_pgte, tulong) :: (_data_addr, tulong) ::
               (_ipa_state, tulong) :: (_ret, tulong) :: (_index, tulong) ::
               (_g_llt, (tptr Tvoid)) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tint) :: (_t'4, tulong) ::
               (_t'3, (tptr Tvoid)) :: (_t'2, tulong) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := table_unmap_body
|}.
