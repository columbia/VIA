Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _entry := 2%positive.
Definition _g := 3%positive.
Definition _g_llt := 4%positive.
Definition _g_rd := 5%positive.
Definition _g_root := 6%positive.
Definition _g_rtt := 7%positive.
Definition _granule := 8%positive.
Definition _i := 9%positive.
Definition _idx := 10%positive.
Definition _index := 11%positive.
Definition _l := 12%positive.
Definition _last_level := 13%positive.
Definition _last_tbl := 14%positive.
Definition _level := 15%positive.
Definition _lock := 16%positive.
Definition _map_addr := 17%positive.
Definition _next := 18%positive.
Definition _pa := 19%positive.
Definition _rd := 20%positive.
Definition _rd__1 := 21%positive.
Definition _ret := 22%positive.
Definition _rt := 23%positive.
Definition _table := 24%positive.
Definition _tbl := 25%positive.
Definition _t'1 := 26%positive.
Definition _t'2 := 27%positive.
Definition _t'3 := 28%positive.
Definition _t'4 := 29%positive.
Definition _t'5 := 30%positive.
Definition _t'6 := 31%positive.
Definition _t'7 := 32%positive.
Definition _t'8 := 33%positive.

Definition table_walk_lock_unlock_body :=
  (Ssequence
    (Sset _l (Econst_long (Int64.repr 0) tulong))
    (Ssequence
      (Sset _last_level (Econst_long (Int64.repr 0) tulong))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _granule_map (Tfunction
                                 (Tcons (tptr Tvoid)
                                   (Tcons tuint Tnil)) (tptr Tvoid) cc_default))
            ((Etempvar _g_rd (tptr Tvoid)) ::
             (Econst_int (Int.repr 2) tuint) :: nil))
          (Sset _rd (Etempvar _t'1 (tptr Tvoid))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _get_rd_g_rtt (Tfunction
                                    (Tcons (tptr Tvoid) Tnil)
                                    (tptr Tvoid)
                                    cc_default))
              ((Etempvar _rd (tptr Tvoid)) :: nil))
            (Sset _g_root (Etempvar _t'2 (tptr Tvoid))))
          (Ssequence
            (Scall None
              (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil) tvoid
                                    cc_default))
              ((Etempvar _rd (tptr Tvoid)) :: nil))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Ecast (Etempvar _g_root (tptr Tvoid))
                      (tptr Tvoid)))
                  (Sset _tbl (Etempvar _t'3 (tptr Tvoid))))
                (Sset _last_tbl
                  (Etempvar _t'3 (tptr Tvoid))))
              (Ssequence
                (Scall None
                  (Evar _granule_lock (Tfunction
                                        (Tcons (tptr Tvoid)
                                          Tnil) tvoid cc_default))
                  ((Etempvar _g_root (tptr Tvoid)) :: nil))
                (Ssequence
                  (Swhile
                    (Ebinop Olt (Etempvar _l tulong) (Etempvar _level tulong)
                      tint)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'7)
                          (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil)
                                           tuint cc_default))
                          ((Etempvar _tbl (tptr Tvoid)) ::
                           nil))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tuint)
                                       (Econst_int (Int.repr 0) tuint) tint)
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'4)
                                (Evar _addr_to_idx (Tfunction
                                                     (Tcons tulong
                                                       (Tcons tulong Tnil))
                                                     tulong cc_default))
                                ((Etempvar _map_addr tulong) ::
                                 (Etempvar _l tulong) :: nil))
                              (Sset _idx (Etempvar _t'4 tulong)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'5)
                                  (Evar _find_next_level_idx (Tfunction
                                                               (Tcons
                                                                 (tptr Tvoid)
                                                                 (Tcons tulong
                                                                   Tnil))
                                                               (tptr Tvoid)
                                                               cc_default))
                                  ((Etempvar _tbl (tptr Tvoid)) ::
                                   (Etempvar _idx tulong) :: nil))
                                (Sset _tbl
                                  (Etempvar _t'5 (tptr Tvoid))))
                              (Ssequence
                                (Scall (Some _t'6)
                                  (Evar _is_null (Tfunction
                                                   (Tcons (tptr Tvoid) Tnil)
                                                   tuint cc_default))
                                  ((Etempvar _tbl (tptr Tvoid)) ::
                                   nil))
                                (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint)
                                               (Econst_int (Int.repr 0) tuint)
                                               tint)
                                  (Ssequence
                                    (Scall None
                                      (Evar _granule_lock (Tfunction
                                                            (Tcons
                                                              (tptr Tvoid)
                                                              Tnil) tvoid
                                                            cc_default))
                                      ((Etempvar _tbl (tptr Tvoid)) ::
                                       nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _granule_unlock (Tfunction
                                                                (Tcons
                                                                  (tptr Tvoid)
                                                                  Tnil) tvoid
                                                                cc_default))
                                        ((Etempvar _last_tbl (tptr Tvoid)) ::
                                         nil))
                                      (Sset _last_tbl
                                        (Etempvar _tbl (tptr Tvoid)))))
                                  (Scall None
                                    (Evar _granule_unlock (Tfunction
                                                            (Tcons
                                                              (tptr Tvoid)
                                                              Tnil) tvoid
                                                            cc_default))
                                    ((Etempvar _last_tbl (tptr Tvoid)) ::
                                     nil))))))
                          Sskip))
                      (Sset _l
                        (Ebinop Oadd (Etempvar _l tulong)
                          (Econst_int (Int.repr 1) tint) tulong))))
                  (Ssequence
                    (Scall None
                      (Evar _set_wi_g_llt (Tfunction
                                            (Tcons
                                              (tptr Tvoid)
                                              Tnil) tvoid cc_default))
                      ((Etempvar _tbl (tptr Tvoid)) :: nil))
                    (Ssequence
                      (Scall (Some _t'8)
                        (Evar _addr_to_idx (Tfunction
                                             (Tcons tulong (Tcons tulong Tnil))
                                             tulong cc_default))
                        ((Etempvar _map_addr tulong) ::
                         (Etempvar _level tulong) :: nil))
                      (Scall None
                        (Evar _set_wi_index (Tfunction (Tcons tulong Tnil)
                                              tvoid cc_default))
                        ((Etempvar _t'8 tulong) :: nil))))))))))))
.

Definition f_table_walk_lock_unlock := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_g_rd, (tptr Tvoid)) ::
                (_map_addr, tulong) :: (_level, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, tulong) :: (_idx, tulong) :: (_entry, tulong) ::
               (_last_level, tulong) ::
               (_g_root, (tptr Tvoid)) ::
               (_tbl, (tptr Tvoid)) ::
               (_last_tbl, (tptr Tvoid)) ::
               (_rd, (tptr Tvoid)) :: (_t'8, tulong) ::
               (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, (tptr Tvoid)) :: (_t'4, tulong) ::
               (_t'3, (tptr Tvoid)) ::
               (_t'2, (tptr Tvoid)) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := table_walk_lock_unlock_body
|}.
