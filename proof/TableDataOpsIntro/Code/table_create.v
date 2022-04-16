Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _entry := 2%positive.
Definition _g := 3%positive.
Definition _g_llt := 4%positive.
Definition _g_rd := 5%positive.
Definition _g_rtt := 6%positive.
Definition _granule := 7%positive.
Definition _i := 8%positive.
Definition _index := 9%positive.
Definition _ipa_state := 10%positive.
Definition _level := 11%positive.
Definition _ll_table := 12%positive.
Definition _llt_pte := 13%positive.
Definition _lock := 14%positive.
Definition _map_addr := 15%positive.
Definition _pa := 16%positive.
Definition _pgte := 17%positive.
Definition _pte := 18%positive.
Definition _rd := 19%positive.
Definition _ret := 20%positive.
Definition _rt := 21%positive.
Definition _rtt_addr := 22%positive.
Definition _state := 23%positive.
Definition _table := 24%positive.
Definition _t'1 := 25%positive.
Definition _t'2 := 26%positive.
Definition _t'3 := 27%positive.
Definition _t'4 := 28%positive.
Definition _t'5 := 29%positive.
Definition _t'6 := 30%positive.

Definition table_create_body :=
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
              (Scall (Some _t'6)
                (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                                 cc_default))
                ((Etempvar _g_llt (tptr Tvoid)) :: nil))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint)
                             (Econst_int (Int.repr 1) tint) tint)
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
                        (Scall (Some _t'5)
                          (Evar _entry_is_table (Tfunction (Tcons tulong Tnil)
                                                  tuint cc_default))
                          ((Etempvar _llt_pte tulong) :: nil))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tuint)
                                       (Econst_int (Int.repr 1) tuint) tint)
                          (Sset _ret (Econst_long (Int64.repr 1) tulong))
                          (Scall None
                            (Evar _table_create_aux (Tfunction
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        (Tcons
                                                          (tptr Tvoid)
                                                          (Tcons
                                                            (tptr Tvoid)
                                                            (Tcons tulong
                                                              (Tcons
                                                                (tptr Tvoid)
                                                                (Tcons tulong
                                                                  (Tcons tulong
                                                                    (Tcons
                                                                      tulong
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil)))))))))
                                                      tvoid cc_default))
                            ((Etempvar _g_rd (tptr Tvoid)) ::
                             (Etempvar _g_llt (tptr Tvoid)) ::
                             (Etempvar _g_rtt (tptr Tvoid)) ::
                             (Etempvar _llt_pte tulong) ::
                             (Etempvar _ll_table (tptr Tvoid)) ::
                             (Etempvar _level tulong) ::
                             (Etempvar _index tulong) ::
                             (Etempvar _map_addr tulong) ::
                             (Etempvar _rtt_addr tulong) :: nil))))
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

Definition f_table_create := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_g_rd, (tptr Tvoid)) ::
                (_map_addr, tulong) :: (_level, tulong) ::
                (_g_rtt, (tptr Tvoid)) ::
                (_rtt_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_llt, (tptr Tvoid)) ::
               (_ret, tulong) :: (_index, tulong) :: (_pte, (tptr Tvoid)) ::
               (_ll_table, (tptr Tvoid)) :: (_llt_pte, tulong) ::
               (_pa, tulong) :: (_ipa_state, tulong) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tulong) :: (_t'3, (tptr Tvoid)) ::
               (_t'2, tulong) :: (_t'1, (tptr Tvoid)) ::
               nil);
  fn_body := table_create_body
|}.
