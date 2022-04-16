Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_llt := 3%positive.
Definition _g_rd := 4%positive.
Definition _g_rtt := 5%positive.
Definition _g_table_root := 6%positive.
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
Definition _pte := 17%positive.
Definition _rd := 18%positive.
Definition _rd__1 := 19%positive.
Definition _rd_addr := 20%positive.
Definition _ret := 21%positive.
Definition _rt := 22%positive.
Definition _rtt_addr := 23%positive.
Definition _state := 24%positive.
Definition _table := 25%positive.
Definition _val := 26%positive.
Definition _valid := 27%positive.
Definition _t'1 := 28%positive.
Definition _t'2 := 29%positive.
Definition _t'3 := 30%positive.
Definition _t'4 := 31%positive.
Definition _t'5 := 32%positive.
Definition _t'6 := 33%positive.

Definition smc_rtt_create_body :=
  (Ssequence
    (Sset _ret (Ecast (Econst_int (Int.repr 0) tuint) tulong))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _validate_table_commands (Tfunction
                                           (Tcons tulong
                                             (Tcons tulong
                                               (Tcons tulong
                                                 (Tcons tulong
                                                   (Tcons tulong Tnil)))))
                                           tuint cc_default))
          ((Etempvar _map_addr tulong) :: (Etempvar _level tulong) ::
           (Econst_int (Int.repr 1) tint) ::
           (Econst_long (Int64.repr 3) tulong) ::
           (Econst_int (Int.repr 3) tint) :: nil))
        (Sset _ret (Ecast (Etempvar _t'1 tuint) tulong)))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _ret tulong)
                       (Econst_int (Int.repr 0) tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _find_lock_granule (Tfunction
                                           (Tcons tulong (Tcons tulong Tnil))
                                           (tptr Tvoid)
                                           cc_default))
                ((Etempvar _rtt_addr tulong) ::
                 (Econst_int (Int.repr 1) tuint) :: nil))
              (Sset _g_rtt (Etempvar _t'2 (tptr Tvoid))))
            (Ssequence
              (Scall (Some _t'6)
                (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                                 cc_default))
                ((Etempvar _g_rtt (tptr Tvoid)) :: nil))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint)
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
                      (Scall (Some _t'5)
                        (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil)
                                         tuint cc_default))
                        ((Etempvar _g_rd (tptr Tvoid)) ::
                         nil))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tuint)
                                     (Econst_int (Int.repr 1) tuint) tint)
                        (Sset _ret (Econst_long (Int64.repr 1) tulong))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'4)
                              (Evar _table_create3 (Tfunction
                                                     (Tcons
                                                       (tptr Tvoid)
                                                       (Tcons tulong
                                                         (Tcons tulong
                                                           (Tcons
                                                             (tptr Tvoid)
                                                             (Tcons tulong
                                                               Tnil))))) tulong
                                                     cc_default))
                              ((Etempvar _g_rd (tptr Tvoid)) ::
                               (Etempvar _map_addr tulong) ::
                               (Etempvar _level tulong) ::
                               (Etempvar _g_rtt (tptr Tvoid)) ::
                               (Etempvar _rtt_addr tulong) :: nil))
                            (Sset _ret (Etempvar _t'4 tulong)))
                          (Scall None
                            (Evar _granule_unlock (Tfunction
                                                    (Tcons
                                                      (tptr Tvoid)
                                                      Tnil) tvoid cc_default))
                            ((Etempvar _g_rd (tptr Tvoid)) ::
                             nil)))))
                    (Scall None
                      (Evar _granule_unlock (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                Tnil) tvoid cc_default))
                      ((Etempvar _g_rtt (tptr Tvoid)) ::
                       nil)))))))
          Sskip)
        (Sreturn (Some (Etempvar _ret tulong))))))
.

Definition f_smc_rtt_create := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_rtt_addr, tulong) :: (_rd_addr, tulong) ::
                (_map_addr, tulong) :: (_level, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_rd, (tptr Tvoid)) ::
               (_g_rtt, (tptr Tvoid)) ::
               (_g_llt, (tptr Tvoid)) ::
               (_rd, (tptr Tvoid)) ::
               (_g_table_root, (tptr Tvoid)) ::
               (_pte, (tptr Tvoid)) :: (_ll_table, (tptr Tvoid)) ::
               (_llt_pte, tulong) :: (_pa, tulong) :: (_index, tulong) ::
               (_ipa_state, tulong) :: (_ret, tulong) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tulong) ::
               (_t'3, (tptr Tvoid)) ::
               (_t'2, (tptr Tvoid)) :: (_t'1, tuint) ::
               nil);
  fn_body := smc_rtt_create_body
|}.
