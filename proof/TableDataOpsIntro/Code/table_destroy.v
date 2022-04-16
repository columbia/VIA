Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _base := 2%positive.
Definition _base_pa := 3%positive.
Definition _entry := 4%positive.
Definition _g := 5%positive.
Definition _g_llt := 6%positive.
Definition _g_rd := 7%positive.
Definition _g_table_root := 8%positive.
Definition _g_tbl := 9%positive.
Definition _gcnt := 10%positive.
Definition _granule := 11%positive.
Definition _i := 12%positive.
Definition _index := 13%positive.
Definition _ipa_state := 14%positive.
Definition _level := 15%positive.
Definition _ll_table := 16%positive.
Definition _llt_pte := 17%positive.
Definition _lock := 18%positive.
Definition _map_addr := 19%positive.
Definition _new_pgte := 20%positive.
Definition _pa := 21%positive.
Definition _pgte := 22%positive.
Definition _pte := 23%positive.
Definition _rd := 24%positive.
Definition _rd__1 := 25%positive.
Definition _ret := 26%positive.
Definition _rt := 27%positive.
Definition _rtt_addr := 28%positive.
Definition _state := 29%positive.
Definition _table := 30%positive.
Definition _t'1 := 31%positive.
Definition _t'2 := 32%positive.
Definition _t'3 := 33%positive.
Definition _t'4 := 34%positive.
Definition _t'5 := 35%positive.
Definition _t'6 := 36%positive.
Definition _t'7 := 37%positive.
Definition _t'8 := 38%positive.
Definition _t'9 := 39%positive.

Definition table_destroy_body :=
  (Ssequence
    (Sset _ret (Ecast (Econst_int (Int.repr 0) tuint) tulong))
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
            (Evar _get_wi_g_llt (Tfunction Tnil
                                  (tptr Tvoid) cc_default))
            nil)
          (Sset _g_llt (Etempvar _t'1 (tptr Tvoid))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _get_wi_index (Tfunction Tnil tulong cc_default)) nil)
            (Sset _index (Etempvar _t'2 tulong)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'9)
                (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                                 cc_default))
                ((Etempvar _g_llt (tptr Tvoid)) :: nil))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'9 tuint)
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
                      (Sset _llt_pte (Etempvar _t'4 tulong)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'8)
                          (Evar _entry_is_table (Tfunction (Tcons tulong Tnil)
                                                  tuint cc_default))
                          ((Etempvar _llt_pte tulong) :: nil))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tuint)
                                       (Econst_int (Int.repr 0) tuint) tint)
                          (Sset _ret
                            (Ecast (Econst_int (Int.repr 1) tuint) tulong))
                          (Sifthenelse (Ebinop One (Etempvar _rtt_addr tulong)
                                         (Ebinop Oand
                                           (Etempvar _llt_pte tulong)
                                           (Econst_long (Int64.repr 281474976706560) tulong)
                                           tulong) tint)
                            (Sset _ret
                              (Ecast (Econst_int (Int.repr 1) tuint) tulong))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'5)
                                  (Evar _find_lock_granule (Tfunction
                                                             (Tcons tulong
                                                               (Tcons tulong
                                                                 Tnil))
                                                             (tptr Tvoid)
                                                             cc_default))
                                  ((Etempvar _rtt_addr tulong) ::
                                   (Econst_int (Int.repr 5) tuint) :: nil))
                                (Sset _g_tbl
                                  (Etempvar _t'5 (tptr Tvoid))))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'7)
                                    (Evar _is_null (Tfunction
                                                     (Tcons (tptr Tvoid) Tnil)
                                                     tuint cc_default))
                                    ((Etempvar _g_tbl (tptr Tvoid)) ::
                                     nil))
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _t'7 tuint)
                                                 (Econst_int (Int.repr 1) tuint)
                                                 tint)
                                    (Scall None
                                      (Evar _assert_cond (Tfunction
                                                           (Tcons tuint Tnil)
                                                           tvoid cc_default))
                                      ((Econst_int (Int.repr 0) tuint) :: nil))
                                    (Ssequence
                                      (Scall (Some _t'6)
                                        (Evar _table_destroy_aux (Tfunction
                                                                   (Tcons
                                                                     (tptr Tvoid)
                                                                     (Tcons
                                                                      (tptr Tvoid)
                                                                      (Tcons
                                                                      (tptr Tvoid)
                                                                      (Tcons
                                                                      tulong
                                                                      (Tcons
                                                                      tulong
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))))))
                                                                   tulong
                                                                   cc_default))
                                        ((Etempvar _g_llt (tptr Tvoid)) ::
                                         (Etempvar _g_tbl (tptr Tvoid)) ::
                                         (Etempvar _ll_table (tptr Tvoid)) ::
                                         (Etempvar _level tulong) ::
                                         (Etempvar _index tulong) ::
                                         (Etempvar _map_addr tulong) :: nil))
                                      (Sset _ret (Etempvar _t'6 tulong)))))
                                (Scall None
                                  (Evar _granule_unlock (Tfunction
                                                          (Tcons
                                                            (tptr Tvoid)
                                                            Tnil) tvoid
                                                          cc_default))
                                  ((Etempvar _g_tbl (tptr Tvoid)) ::
                                   nil)))))))
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
            (Sreturn (Some (Etempvar _ret tulong))))))))
.

Definition f_table_destroy := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_g_rd, (tptr Tvoid)) ::
                (_map_addr, tulong) :: (_rtt_addr, tulong) ::
                (_level, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_tbl, (tptr Tvoid)) ::
               (_g_llt, (tptr Tvoid)) ::
               (_rd, (tptr Tvoid)) ::
               (_g_table_root, (tptr Tvoid)) ::
               (_table, (tptr Tvoid)) :: (_ll_table, (tptr Tvoid)) ::
               (_new_pgte, tulong) :: (_llt_pte, tulong) ::
               (_index, tulong) :: (_ipa_state, tulong) :: (_gcnt, tulong) ::
               (_pgte, tulong) :: (_base_pa, tulong) :: (_ret, tulong) ::
               (_t'9, tuint) :: (_t'8, tuint) :: (_t'7, tuint) ::
               (_t'6, tulong) :: (_t'5, (tptr Tvoid)) ::
               (_t'4, tulong) :: (_t'3, (tptr Tvoid)) :: (_t'2, tulong) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := table_destroy_body
|}.
