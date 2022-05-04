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
Definition _granule := 10%positive.
Definition _i := 11%positive.
Definition _index := 12%positive.
Definition _ipa_state := 13%positive.
Definition _ll_table := 14%positive.
Definition _llt_pgte := 15%positive.
Definition _lock := 16%positive.
Definition _map_addr := 17%positive.
Definition _pa := 18%positive.
Definition _pgte := 19%positive.
Definition _pte := 20%positive.
Definition _pte_val := 21%positive.
Definition _rd := 22%positive.
Definition _ret := 23%positive.
Definition _s := 24%positive.
Definition _state := 25%positive.
Definition _table := 26%positive.
Definition _val := 27%positive.
Definition _wi_g_llt := 28%positive.
Definition _wi_index := 29%positive.
Definition _t'1 := 30%positive.
Definition _t'2 := 31%positive.
Definition _t'3 := 32%positive.
Definition _t'4 := 33%positive.
Definition _t'5 := 34%positive.

Definition data_create_unknown_body :=
  (Ssequence
    (Scall None
      (Evar _table_walk_lock_unlock (Tfunction
                                      (Tcons (tptr Tvoid)
                                        (Tcons tulong (Tcons tulong Tnil)))
                                      tvoid cc_default))
      ((Etempvar _g_rd (tptr Tvoid)) ::
       (Etempvar _map_addr tulong) ::
       (Ebinop Osub (Econst_int (Int.repr 4) tuint)
         (Econst_int (Int.repr 1) tuint) tuint) :: nil))
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
            (Scall (Some _t'5)
              (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                               cc_default))
              ((Etempvar _g_llt (tptr Tvoid)) :: nil))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tuint)
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
                    (Sset _pte_val (Etempvar _t'4 tulong)))
                  (Ssequence
                    (Sifthenelse (Ebinop One
                                   (Ebinop Odiv
                                     (Ebinop Oand (Etempvar _pte_val tulong)
                                       (Econst_long (Int64.repr 504403158265495552) tulong)
                                       tulong)
                                     (Econst_long (Int64.repr 72057594037927936) tulong)
                                     tulong) (Econst_int (Int.repr 0) tuint)
                                   tint)
                      (Sset _ret (Econst_long (Int64.repr 1) tulong))
                      (Ssequence
                        (Sset _pte_val
                          (Ebinop Oor
                            (Ebinop Omul (Econst_int (Int.repr 1) tuint)
                              (Econst_long (Int64.repr 72057594037927936) tulong)
                              tulong) (Etempvar _data_addr tulong) tulong))
                        (Ssequence
                          (Scall None
                            (Evar _pgte_write (Tfunction
                                                (Tcons (tptr Tvoid)
                                                  (Tcons tulong
                                                    (Tcons tulong Tnil))) tvoid
                                                cc_default))
                            ((Etempvar _ll_table (tptr Tvoid)) ::
                             (Etempvar _index tulong) ::
                             (Etempvar _pte_val tulong) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _set_mapping (Tfunction
                                                   (Tcons tulong
                                                     (Tcons tulong Tnil)) tvoid
                                                   cc_default))
                              ((Etempvar _map_addr tulong) ::
                               (Etempvar _data_addr tulong) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _granule_get (Tfunction
                                                     (Tcons
                                                       (tptr Tvoid)
                                                       Tnil) tvoid cc_default))
                                ((Etempvar _g_llt (tptr Tvoid)) ::
                                 nil))
                              (Sset _ret (Econst_long (Int64.repr 0) tulong)))))))
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

Definition f_data_create_unknown := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_g_rd, (tptr Tvoid)) ::
                (_data_addr, tulong) :: (_map_addr, tulong) ::
                (_g_data, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_ll_table, (tptr Tvoid)) :: (_llt_pgte, tulong) ::
               (_pte_val, tulong) :: (_ipa_state, tulong) ::
               (_ret, tulong) :: (_index, tulong) ::
               (_g_llt, (tptr Tvoid)) :: (_t'5, tuint) ::
               (_t'4, tulong) :: (_t'3, (tptr Tvoid)) :: (_t'2, tulong) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := data_create_unknown_body
|}.
