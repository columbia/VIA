Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _a := 1%positive.
Definition _addr := 2%positive.
Definition _b := 3%positive.
Definition _data := 4%positive.
Definition _data_addr := 5%positive.
Definition _g := 6%positive.
Definition _g_data := 7%positive.
Definition _g_llt := 8%positive.
Definition _g_rd := 9%positive.
Definition _g_src := 10%positive.
Definition _g_table_root := 11%positive.
Definition _granule := 12%positive.
Definition _i := 13%positive.
Definition _index := 14%positive.
Definition _last_level := 15%positive.
Definition _level := 16%positive.
Definition _ll_table := 17%positive.
Definition _lock := 18%positive.
Definition _map_addr := 19%positive.
Definition _new_data_state := 20%positive.
Definition _pa := 21%positive.
Definition _pte := 22%positive.
Definition _pte_val := 23%positive.
Definition _rd := 24%positive.
Definition _rd__1 := 25%positive.
Definition _rd_addr := 26%positive.
Definition _ret := 27%positive.
Definition _s := 28%positive.
Definition _state := 29%positive.
Definition _table := 30%positive.
Definition _val := 31%positive.
Definition _t'1 := 32%positive.
Definition _t'2 := 33%positive.
Definition _t'3 := 34%positive.
Definition _t'4 := 35%positive.
Definition _t'5 := 36%positive.
Definition _t'6 := 37%positive.

Definition smc_data_create_unknown_body :=
  (Ssequence
    (Sset _new_data_state (Ecast (Econst_int (Int.repr 1) tuint) tulong))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _find_lock_granule (Tfunction
                                     (Tcons tulong (Tcons tulong Tnil))
                                     (tptr Tvoid)
                                     cc_default))
          ((Etempvar _data_addr tulong) :: (Econst_int (Int.repr 1) tuint) ::
           nil))
        (Sset _g_data (Etempvar _t'1 (tptr Tvoid))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'6)
            (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                             cc_default))
            ((Etempvar _g_data (tptr Tvoid)) :: nil))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint)
                         (Econst_int (Int.repr 1) tuint) tint)
            (Sset _ret (Econst_long (Int64.repr 1) tulong))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _find_lock_granule (Tfunction
                                             (Tcons tulong (Tcons tulong Tnil))
                                             (tptr Tvoid)
                                             cc_default))
                  ((Etempvar _rd_addr tulong) ::
                   (Econst_int (Int.repr 2) tuint) :: nil))
                (Sset _g_rd (Etempvar _t'2 (tptr Tvoid))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                                     cc_default))
                    ((Etempvar _g_rd (tptr Tvoid)) :: nil))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tuint)
                                 (Econst_int (Int.repr 1) tuint) tint)
                    (Sset _ret (Econst_long (Int64.repr 1) tulong))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'3)
                          (Evar _granule_map (Tfunction
                                               (Tcons
                                                 (tptr Tvoid)
                                                 (Tcons tuint Tnil))
                                               (tptr Tvoid) cc_default))
                          ((Etempvar _g_rd (tptr Tvoid)) ::
                           (Econst_int (Int.repr 2) tuint) :: nil))
                        (Sset _rd (Etempvar _t'3 (tptr Tvoid))))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'4)
                            (Evar _data_create_unknown3 (Tfunction
                                                          (Tcons
                                                            (tptr Tvoid)
                                                            (Tcons tulong
                                                              (Tcons tulong
                                                                (Tcons
                                                                  (tptr Tvoid)
                                                                  Tnil))))
                                                          tulong cc_default))
                            ((Etempvar _g_rd (tptr Tvoid)) ::
                             (Etempvar _data_addr tulong) ::
                             (Etempvar _map_addr tulong) ::
                             (Etempvar _g_data (tptr Tvoid)) ::
                             nil))
                          (Sset _ret (Etempvar _t'4 tulong)))
                        (Ssequence
                          (Sifthenelse (Ebinop Oeq (Etempvar _ret tulong)
                                         (Econst_int (Int.repr 0) tuint) tint)
                            (Scall None
                              (Evar _granule_set_state (Tfunction
                                                         (Tcons
                                                           (tptr Tvoid)
                                                           (Tcons tuint Tnil))
                                                         tvoid cc_default))
                              ((Etempvar _g_data (tptr Tvoid)) ::
                               (Econst_int (Int.repr 4) tuint) :: nil))
                            Sskip)
                          (Ssequence
                            (Scall None
                              (Evar _buffer_unmap (Tfunction
                                                    (Tcons (tptr Tvoid) Tnil)
                                                    tvoid cc_default))
                              ((Etempvar _rd (tptr Tvoid)) ::
                               nil))
                            (Scall None
                              (Evar _granule_unlock (Tfunction
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        Tnil) tvoid cc_default))
                              ((Etempvar _g_rd (tptr Tvoid)) ::
                               nil))))))))
                (Scall None
                  (Evar _granule_unlock (Tfunction
                                          (Tcons
                                            (tptr Tvoid)
                                            Tnil) tvoid cc_default))
                  ((Etempvar _g_data (tptr Tvoid)) :: nil))))))
        (Sreturn (Some (Etempvar _ret tulong))))))
.

Definition f_smc_data_create_unknown := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_data_addr, tulong) :: (_rd_addr, tulong) ::
                (_map_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_data, (tptr Tvoid)) ::
               (_g_rd, (tptr Tvoid)) ::
               (_g_src, (tptr Tvoid)) ::
               (_g_table_root, (tptr Tvoid)) ::
               (_g_llt, (tptr Tvoid)) ::
               (_rd, (tptr Tvoid)) :: (_index, tulong) ::
               (_last_level, tulong) :: (_pte_val, tulong) ::
               (_ll_table, (tptr Tvoid)) :: (_new_data_state, tulong) ::
               (_ret, tulong) :: (_t'6, tuint) :: (_t'5, tuint) ::
               (_t'4, tulong) :: (_t'3, (tptr Tvoid)) ::
               (_t'2, (tptr Tvoid)) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := smc_data_create_unknown_body
|}.
