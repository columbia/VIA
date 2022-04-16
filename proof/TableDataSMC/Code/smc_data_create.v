Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _data := 2%positive.
Definition _data_addr := 3%positive.
Definition _g := 4%positive.
Definition _g_data := 5%positive.
Definition _g_llt := 6%positive.
Definition _g_rd := 7%positive.
Definition _g_src := 8%positive.
Definition _g_table_root := 9%positive.
Definition _granule := 10%positive.
Definition _i := 11%positive.
Definition _index := 12%positive.
Definition _last_level := 13%positive.
Definition _level := 14%positive.
Definition _ll_table := 15%positive.
Definition _lock := 16%positive.
Definition _map_addr := 17%positive.
Definition _new_data_state := 18%positive.
Definition _pa := 19%positive.
Definition _pte := 20%positive.
Definition _pte_val := 21%positive.
Definition _rd := 22%positive.
Definition _rd__1 := 23%positive.
Definition _rd_addr := 24%positive.
Definition _ret := 25%positive.
Definition _src_addr := 26%positive.
Definition _state := 27%positive.
Definition _table := 28%positive.
Definition _val := 29%positive.
Definition _t'1 := 30%positive.
Definition _t'2 := 31%positive.
Definition _t'3 := 32%positive.
Definition _t'4 := 33%positive.
Definition _t'5 := 34%positive.
Definition _t'6 := 35%positive.
Definition _t'7 := 36%positive.
Definition _t'8 := 37%positive.
Definition _t'9 := 38%positive.

Definition smc_data_create_body :=
  (Ssequence
    (Sset _new_data_state (Ecast (Econst_int (Int.repr 1) tuint) tulong))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _find_granule (Tfunction (Tcons tulong Tnil)
                                (tptr Tvoid) cc_default))
          ((Etempvar _src_addr tulong) :: nil))
        (Sset _g_src (Etempvar _t'1 (tptr Tvoid))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'9)
            (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                             cc_default))
            ((Etempvar _g_src (tptr Tvoid)) :: nil))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'9 tuint)
                         (Econst_int (Int.repr 1) tuint) tint)
            (Sset _ret (Econst_long (Int64.repr 1) tulong))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _find_lock_granule (Tfunction
                                             (Tcons tulong (Tcons tulong Tnil))
                                             (tptr Tvoid)
                                             cc_default))
                  ((Etempvar _data_addr tulong) ::
                   (Econst_int (Int.repr 1) tuint) :: nil))
                (Sset _g_data (Etempvar _t'2 (tptr Tvoid))))
              (Ssequence
                (Scall (Some _t'8)
                  (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                                   cc_default))
                  ((Etempvar _g_data (tptr Tvoid)) :: nil))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tuint)
                               (Econst_int (Int.repr 1) tuint) tint)
                  (Sset _ret (Econst_long (Int64.repr 1) tulong))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _find_lock_granule (Tfunction
                                                   (Tcons tulong
                                                     (Tcons tulong Tnil))
                                                   (tptr Tvoid)
                                                   cc_default))
                        ((Etempvar _rd_addr tulong) ::
                         (Econst_int (Int.repr 2) tuint) :: nil))
                      (Sset _g_rd
                        (Etempvar _t'3 (tptr Tvoid))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'7)
                          (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil)
                                           tuint cc_default))
                          ((Etempvar _g_rd (tptr Tvoid)) ::
                           nil))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tuint)
                                       (Econst_int (Int.repr 1) tuint) tint)
                          (Sset _ret (Econst_long (Int64.repr 1) tulong))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'4)
                                (Evar _granule_map (Tfunction
                                                     (Tcons
                                                       (tptr Tvoid)
                                                       (Tcons tuint Tnil))
                                                     (tptr Tvoid) cc_default))
                                ((Etempvar _g_rd (tptr Tvoid)) ::
                                 (Econst_int (Int.repr 2) tuint) :: nil))
                              (Sset _rd (Etempvar _t'4 (tptr Tvoid))))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'6)
                                  (Evar _get_rd_state (Tfunction
                                                        (Tcons
                                                          (tptr Tvoid)
                                                          Tnil) tuint
                                                        cc_default))
                                  ((Etempvar _rd (tptr Tvoid)) ::
                                   nil))
                                (Sifthenelse (Ebinop One (Etempvar _t'6 tuint)
                                               (Econst_int (Int.repr 0) tuint)
                                               tint)
                                  (Sset _ret
                                    (Econst_long (Int64.repr 1) tulong))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'5)
                                        (Evar _data_create3 (Tfunction
                                                              (Tcons
                                                                (tptr Tvoid)
                                                                (Tcons tulong
                                                                  (Tcons tulong
                                                                    (Tcons
                                                                      (tptr Tvoid)
                                                                      (Tcons
                                                                      (tptr Tvoid)
                                                                      Tnil)))))
                                                              tulong
                                                              cc_default))
                                        ((Etempvar _g_rd (tptr Tvoid)) ::
                                         (Etempvar _data_addr tulong) ::
                                         (Etempvar _map_addr tulong) ::
                                         (Etempvar _g_data (tptr Tvoid)) ::
                                         (Etempvar _g_src (tptr Tvoid)) ::
                                         nil))
                                      (Sset _ret (Etempvar _t'5 tulong)))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _ret tulong)
                                                   (Econst_int (Int.repr 0) tuint)
                                                   tint)
                                      (Scall None
                                        (Evar _granule_set_state (Tfunction
                                                                   (Tcons
                                                                     (tptr Tvoid)
                                                                     (Tcons
                                                                      tuint
                                                                      Tnil))
                                                                   tvoid
                                                                   cc_default))
                                        ((Etempvar _g_data (tptr Tvoid)) ::
                                         (Econst_int (Int.repr 4) tuint) ::
                                         nil))
                                      Sskip))))
                              (Ssequence
                                (Scall None
                                  (Evar _buffer_unmap (Tfunction
                                                        (Tcons (tptr Tvoid)
                                                          Tnil) tvoid
                                                        cc_default))
                                  ((Etempvar _rd (tptr Tvoid)) ::
                                   nil))
                                (Scall None
                                  (Evar _granule_unlock (Tfunction
                                                          (Tcons
                                                            (tptr Tvoid)
                                                            Tnil) tvoid
                                                          cc_default))
                                  ((Etempvar _g_rd (tptr Tvoid)) ::
                                   nil)))))))
                      (Scall None
                        (Evar _granule_unlock (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  Tnil) tvoid cc_default))
                        ((Etempvar _g_data (tptr Tvoid)) ::
                         nil)))))))))
        (Sreturn (Some (Etempvar _ret tulong))))))
.

Definition f_smc_data_create := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_data_addr, tulong) :: (_rd_addr, tulong) ::
                (_map_addr, tulong) :: (_src_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_data, (tptr Tvoid)) ::
               (_g_rd, (tptr Tvoid)) ::
               (_g_src, (tptr Tvoid)) ::
               (_g_table_root, (tptr Tvoid)) ::
               (_g_llt, (tptr Tvoid)) ::
               (_rd, (tptr Tvoid)) :: (_index, tulong) ::
               (_last_level, tulong) :: (_pte_val, tulong) ::
               (_ll_table, (tptr Tvoid)) :: (_new_data_state, tulong) ::
               (_ret, tulong) :: (_t'9, tuint) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tulong) ::
               (_t'4, (tptr Tvoid)) ::
               (_t'3, (tptr Tvoid)) ::
               (_t'2, (tptr Tvoid)) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := smc_data_create_body
|}.
