Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_llt := 3%positive.
Definition _g_rd := 4%positive.
Definition _g_rtt := 5%positive.
Definition _granule := 6%positive.
Definition _i := 7%positive.
Definition _index := 8%positive.
Definition _ipa_state := 9%positive.
Definition _level := 10%positive.
Definition _ll_table := 11%positive.
Definition _llt_pte := 12%positive.
Definition _map_addr := 13%positive.
Definition _pa := 14%positive.
Definition _pgte := 15%positive.
Definition _pte := 16%positive.
Definition _rd := 17%positive.
Definition _ret := 18%positive.
Definition _rt := 19%positive.
Definition _rtt_addr := 20%positive.
Definition _state := 21%positive.
Definition _table := 22%positive.
Definition _t'1 := 23%positive.
Definition _t'2 := 24%positive.

Definition table_create_aux_body :=
  (Ssequence
    (Sset _ipa_state
      (Ebinop Odiv
        (Ebinop Oand (Etempvar _llt_pte tulong)
          (Econst_long (Int64.repr 504403158265495552) tulong) tulong)
        (Econst_long (Int64.repr 72057594037927936) tulong) tulong))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _granule_map (Tfunction
                               (Tcons (tptr Tvoid)
                                 (Tcons tuint Tnil)) (tptr Tvoid) cc_default))
          ((Etempvar _g_rtt (tptr Tvoid)) ::
           (Econst_int (Int.repr 1) tuint) :: nil))
        (Sset _pte (Etempvar _t'1 (tptr Tvoid))))
      (Ssequence
        (Scall None
          (Evar _granule_set_state (Tfunction
                                     (Tcons (tptr Tvoid)
                                       (Tcons tuint Tnil)) tvoid cc_default))
          ((Etempvar _g_rtt (tptr Tvoid)) ::
           (Econst_int (Int.repr 5) tuint) :: nil))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _ipa_state tulong)
                           (Econst_int (Int.repr 0) tuint) tint)
              (Sset _t'2 (Econst_int (Int.repr 1) tint))
              (Sset _t'2
                (Ecast
                  (Ebinop Oeq (Etempvar _ipa_state tulong)
                    (Econst_int (Int.repr 3) tuint) tint) tbool)))
            (Sifthenelse (Etempvar _t'2 tint)
              (Scall None
                (Evar _table_create_init_vacant (Tfunction
                                                  (Tcons tulong
                                                    (Tcons (tptr Tvoid)
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        Tnil))) tvoid
                                                  cc_default))
                ((Etempvar _ipa_state tulong) ::
                 (Etempvar _pte (tptr Tvoid)) ::
                 (Etempvar _g_llt (tptr Tvoid)) :: nil))
              (Sifthenelse (Ebinop Oeq (Etempvar _ipa_state tulong)
                             (Econst_int (Int.repr 1) tuint) tint)
                (Scall None
                  (Evar _table_create_init_absent (Tfunction
                                                    (Tcons tulong
                                                      (Tcons tulong
                                                        (Tcons (tptr Tvoid)
                                                          (Tcons
                                                            (tptr Tvoid)
                                                            Tnil)))) tvoid
                                                    cc_default))
                  ((Etempvar _level tulong) :: (Etempvar _llt_pte tulong) ::
                   (Etempvar _pte (tptr Tvoid)) ::
                   (Etempvar _g_rtt (tptr Tvoid)) :: nil))
                (Sifthenelse (Ebinop Oeq (Etempvar _ipa_state tulong)
                               (Econst_int (Int.repr 2) tuint) tint)
                  (Scall None
                    (Evar _table_create_init_present (Tfunction
                                                       (Tcons tulong
                                                         (Tcons (tptr Tvoid)
                                                           (Tcons tulong
                                                             (Tcons tulong
                                                               (Tcons tulong
                                                                 (Tcons
                                                                   (tptr Tvoid)
                                                                   (Tcons
                                                                     (tptr Tvoid)
                                                                     Tnil)))))))
                                                       tvoid cc_default))
                    ((Etempvar _level tulong) ::
                     (Etempvar _ll_table (tptr Tvoid)) ::
                     (Etempvar _index tulong) :: (Etempvar _map_addr tulong) ::
                     (Etempvar _llt_pte tulong) ::
                     (Etempvar _pte (tptr Tvoid)) ::
                     (Etempvar _g_rtt (tptr Tvoid)) :: nil))
                  (Scall None
                    (Evar _assert_cond (Tfunction (Tcons tuint Tnil) tvoid
                                         cc_default))
                    ((Econst_int (Int.repr 0) tuint) :: nil))))))
          (Ssequence
            (Scall None
              (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil) tvoid
                                    cc_default))
              ((Etempvar _pte (tptr Tvoid)) :: nil))
            (Ssequence
              (Scall None
                (Evar _granule_get (Tfunction
                                     (Tcons (tptr Tvoid)
                                       Tnil) tvoid cc_default))
                ((Etempvar _g_rtt (tptr Tvoid)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _set_g_rtt_rd (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons
                                            (tptr Tvoid)
                                            Tnil)) tvoid cc_default))
                  ((Etempvar _g_rtt (tptr Tvoid)) ::
                   (Etempvar _g_rd (tptr Tvoid)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _pgte_write (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons tulong (Tcons tulong Tnil)))
                                        tvoid cc_default))
                    ((Etempvar _ll_table (tptr Tvoid)) ::
                     (Etempvar _index tulong) ::
                     (Ebinop Oor (Etempvar _rtt_addr tulong)
                       (Econst_long (Int64.repr 3) tulong) tulong) :: nil))
                  (Scall None
                    (Evar _link_table (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons
                                            (tptr Tvoid)
                                            (Tcons tulong (Tcons tulong Tnil))))
                                        tvoid cc_default))
                    ((Etempvar _g_llt (tptr Tvoid)) ::
                     (Etempvar _g_rtt (tptr Tvoid)) ::
                     (Etempvar _level tulong) :: (Etempvar _index tulong) ::
                     nil))))))))))
.

Definition f_table_create_aux := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_g_rd, (tptr Tvoid)) ::
                (_g_llt, (tptr Tvoid)) ::
                (_g_rtt, (tptr Tvoid)) ::
                (_llt_pte, tulong) :: (_ll_table, (tptr Tvoid)) ::
                (_level, tulong) :: (_index, tulong) ::
                (_map_addr, tulong) :: (_rtt_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ipa_state, tulong) :: (_pte, (tptr Tvoid)) ::
               (_t'2, tint) :: (_t'1, (tptr Tvoid)) :: nil);
  fn_body := table_create_aux_body
|}.
