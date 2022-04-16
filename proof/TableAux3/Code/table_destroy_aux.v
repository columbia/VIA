Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_llt := 3%positive.
Definition _g_rtt := 4%positive.
Definition _g_tbl := 5%positive.
Definition _gcnt := 6%positive.
Definition _granule := 7%positive.
Definition _i := 8%positive.
Definition _index := 9%positive.
Definition _level := 10%positive.
Definition _ll_table := 11%positive.
Definition _map_addr := 12%positive.
Definition _new_pgte := 13%positive.
Definition _pa := 14%positive.
Definition _pgte := 15%positive.
Definition _rd := 16%positive.
Definition _ret := 17%positive.
Definition _rt := 18%positive.
Definition _state := 19%positive.
Definition _table := 20%positive.
Definition _t'1 := 21%positive.
Definition _t'2 := 22%positive.
Definition _t'3 := 23%positive.
Definition _t'4 := 24%positive.
Definition _t'5 := 25%positive.
Definition _t'6 := 26%positive.

Definition table_destroy_aux_body :=
  (Ssequence
    (Sset _ret (Econst_long (Int64.repr 0) tulong))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _granule_map (Tfunction
                               (Tcons (tptr Tvoid)
                                 (Tcons tuint Tnil)) (tptr Tvoid) cc_default))
          ((Etempvar _g_tbl (tptr Tvoid)) ::
           (Econst_int (Int.repr 7) tuint) :: nil))
        (Sset _table (Etempvar _t'1 (tptr Tvoid))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _get_g_rtt_refcount (Tfunction
                                        (Tcons (tptr Tvoid)
                                          Tnil) tulong cc_default))
            ((Etempvar _g_tbl (tptr Tvoid)) :: nil))
          (Sset _gcnt (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _gcnt tulong)
                           (Econst_int (Int.repr 1) tuint) tint)
              (Sset _t'6 (Econst_int (Int.repr 1) tint))
              (Sset _t'6
                (Ecast
                  (Ebinop Oeq (Etempvar _gcnt tulong)
                    (Ebinop Oadd (Econst_long (Int64.repr 512) tulong)
                      (Econst_int (Int.repr 1) tint) tulong) tint) tbool)))
            (Sifthenelse (Etempvar _t'6 tint)
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _gcnt tulong)
                               (Econst_int (Int.repr 1) tuint) tint)
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _table_delete (Tfunction
                                            (Tcons (tptr Tvoid)
                                              (Tcons
                                                (tptr Tvoid)
                                                Tnil)) tulong cc_default))
                      ((Etempvar _table (tptr Tvoid)) ::
                       (Etempvar _g_llt (tptr Tvoid)) ::
                       nil))
                    (Sset _new_pgte (Etempvar _t'3 tulong)))
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _table_fold (Tfunction
                                          (Tcons (tptr Tvoid)
                                            (Tcons tulong
                                              (Tcons
                                                (tptr Tvoid)
                                                Tnil))) tulong cc_default))
                      ((Etempvar _table (tptr Tvoid)) ::
                       (Etempvar _level tulong) ::
                       (Etempvar _g_tbl (tptr Tvoid)) ::
                       nil))
                    (Sset _new_pgte (Etempvar _t'4 tulong))))
                (Ssequence
                  (Scall None
                    (Evar _pgte_write (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons tulong (Tcons tulong Tnil)))
                                        tvoid cc_default))
                    ((Etempvar _ll_table (tptr Tvoid)) ::
                     (Etempvar _index tulong) ::
                     (Econst_long (Int64.repr 0) tulong) :: nil))
                  (Ssequence
                    (Sifthenelse (Ebinop Oeq
                                   (Ebinop Odiv
                                     (Ebinop Oand (Etempvar _new_pgte tulong)
                                       (Econst_long (Int64.repr 504403158265495552) tulong)
                                       tulong)
                                     (Econst_long (Int64.repr 72057594037927936) tulong)
                                     tulong) (Econst_int (Int.repr 2) tuint)
                                   tint)
                      (Scall None
                        (Evar _invalidate_pages_in_block (Tfunction
                                                           (Tcons tulong Tnil)
                                                           tvoid cc_default))
                        ((Etempvar _map_addr tulong) :: nil))
                      (Scall None
                        (Evar _invalidate_block (Tfunction (Tcons tulong Tnil)
                                                  tvoid cc_default))
                        ((Etempvar _map_addr tulong) :: nil)))
                    (Ssequence
                      (Scall None
                        (Evar _pgte_write (Tfunction
                                            (Tcons (tptr Tvoid)
                                              (Tcons tulong
                                                (Tcons tulong Tnil))) tvoid
                                            cc_default))
                        ((Etempvar _ll_table (tptr Tvoid)) ::
                         (Etempvar _index tulong) ::
                         (Etempvar _new_pgte tulong) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _granule_put (Tfunction
                                               (Tcons
                                                 (tptr Tvoid)
                                                 Tnil) tvoid cc_default))
                          ((Etempvar _g_tbl (tptr Tvoid)) ::
                           nil))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'5)
                              (Evar _null_ptr (Tfunction Tnil (tptr Tvoid)
                                                cc_default)) nil)
                            (Scall None
                              (Evar _set_g_rtt_rd (Tfunction
                                                    (Tcons
                                                      (tptr Tvoid)
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        Tnil)) tvoid
                                                    cc_default))
                              ((Etempvar _g_tbl (tptr Tvoid)) ::
                               (Etempvar _t'5 (tptr Tvoid)) :: nil)))
                          (Ssequence
                            (Scall None
                              (Evar _granule_memzero_mapped (Tfunction
                                                              (Tcons
                                                                (tptr Tvoid)
                                                                Tnil) tvoid
                                                              cc_default))
                              ((Etempvar _table (tptr Tvoid)) :: nil))
                            (Scall None
                              (Evar _granule_set_state (Tfunction
                                                         (Tcons
                                                           (tptr Tvoid)
                                                           (Tcons tuint Tnil))
                                                         tvoid cc_default))
                              ((Etempvar _g_tbl (tptr Tvoid)) ::
                               (Econst_int (Int.repr 1) tuint) :: nil)))))))))
              (Sset _ret (Econst_long (Int64.repr 1) tulong))))
          (Ssequence
            (Scall None
              (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil) tvoid
                                    cc_default))
              ((Etempvar _table (tptr Tvoid)) :: nil))
            (Sreturn (Some (Etempvar _ret tulong))))))))
.

Definition f_table_destroy_aux := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_g_llt, (tptr Tvoid)) ::
                (_g_tbl, (tptr Tvoid)) ::
                (_ll_table, (tptr Tvoid)) :: (_level, tulong) ::
                (_index, tulong) :: (_map_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_table, (tptr Tvoid)) :: (_gcnt, tulong) ::
               (_new_pgte, tulong) :: (_ret, tulong) :: (_t'6, tint) ::
               (_t'5, (tptr Tvoid)) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, (tptr Tvoid)) :: nil);
  fn_body := table_destroy_aux_body
|}.
