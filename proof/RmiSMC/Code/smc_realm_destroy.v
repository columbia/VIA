Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_rd := 3%positive.
Definition _g_rec := 4%positive.
Definition _g_rec_list := 5%positive.
Definition _g_rtt := 6%positive.
Definition _granule := 7%positive.
Definition _i := 8%positive.
Definition _lock := 9%positive.
Definition _rd := 10%positive.
Definition _rd__1 := 11%positive.
Definition _rd_addr := 12%positive.
Definition _rec := 13%positive.
Definition _rec_list := 14%positive.
Definition _ret := 15%positive.
Definition _rt := 16%positive.
Definition _t'1 := 17%positive.
Definition _t'2 := 18%positive.
Definition _t'3 := 19%positive.
Definition _t'4 := 20%positive.
Definition _t'5 := 21%positive.
Definition _t'6 := 22%positive.

Definition smc_realm_destroy_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _find_lock_unused_granule (Tfunction
                                          (Tcons tulong (Tcons tulong Tnil))
                                          (tptr Tvoid)
                                          cc_default))
        ((Etempvar _rd_addr tulong) :: (Econst_int (Int.repr 2) tuint) :: nil))
      (Sset _g_rd (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'6)
          (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint cc_default))
          ((Etempvar _g_rd (tptr Tvoid)) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint)
                       (Econst_int (Int.repr 0) tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _granule_map (Tfunction
                                     (Tcons (tptr Tvoid)
                                       (Tcons tuint Tnil)) (tptr Tvoid)
                                     cc_default))
                ((Etempvar _g_rd (tptr Tvoid)) ::
                 (Econst_int (Int.repr 2) tuint) :: nil))
              (Sset _rd (Etempvar _t'2 (tptr Tvoid))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _get_rd_g_rtt (Tfunction
                                        (Tcons (tptr Tvoid)
                                          Tnil)
                                        (tptr Tvoid)
                                        cc_default))
                  ((Etempvar _rd (tptr Tvoid)) :: nil))
                (Sset _g_rtt (Etempvar _t'3 (tptr Tvoid))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _get_rd_g_rec_list (Tfunction
                                               (Tcons
                                                 (tptr Tvoid)
                                                 Tnil)
                                               (tptr Tvoid)
                                               cc_default))
                    ((Etempvar _rd (tptr Tvoid)) :: nil))
                  (Sset _g_rec_list
                    (Etempvar _t'4 (tptr Tvoid))))
                (Ssequence
                  (Scall None
                    (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil)
                                          tvoid cc_default))
                    ((Etempvar _rd (tptr Tvoid)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _granule_lock (Tfunction
                                            (Tcons
                                              (tptr Tvoid)
                                              Tnil) tvoid cc_default))
                      ((Etempvar _g_rtt (tptr Tvoid)) ::
                       nil))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'5)
                          (Evar _get_g_rtt_refcount (Tfunction
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        Tnil) tulong
                                                      cc_default))
                          ((Etempvar _g_rtt (tptr Tvoid)) ::
                           nil))
                        (Sifthenelse (Ebinop One (Etempvar _t'5 tulong)
                                       (Econst_long (Int64.repr 0) tulong)
                                       tint)
                          (Ssequence
                            (Scall None
                              (Evar _granule_unlock (Tfunction
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        Tnil) tvoid cc_default))
                              ((Etempvar _g_rtt (tptr Tvoid)) ::
                               nil))
                            (Sset _ret (Econst_long (Int64.repr 1) tulong)))
                          (Ssequence
                            (Scall None
                              (Evar _realm_destroy_ops (Tfunction
                                                         (Tcons
                                                           (tptr Tvoid)
                                                           (Tcons
                                                             (tptr Tvoid)
                                                             (Tcons
                                                               (tptr Tvoid)
                                                               Tnil))) tvoid
                                                         cc_default))
                              ((Etempvar _g_rtt (tptr Tvoid)) ::
                               (Etempvar _g_rec_list (tptr Tvoid)) ::
                               (Etempvar _g_rd (tptr Tvoid)) ::
                               nil))
                            (Sset _ret (Econst_long (Int64.repr 0) tulong)))))
                      (Scall None
                        (Evar _granule_unlock (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  Tnil) tvoid cc_default))
                        ((Etempvar _g_rd (tptr Tvoid)) ::
                         nil))))))))
          (Sset _ret (Econst_long (Int64.repr 1) tulong))))
      (Sreturn (Some (Etempvar _ret tulong)))))
.

Definition f_smc_realm_destroy := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_rd_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_rd, (tptr Tvoid)) ::
               (_g_rtt, (tptr Tvoid)) ::
               (_g_rec_list, (tptr Tvoid)) ::
               (_rd, (tptr Tvoid)) :: (_ret, tulong) ::
               (_t'6, tuint) :: (_t'5, tulong) ::
               (_t'4, (tptr Tvoid)) ::
               (_t'3, (tptr Tvoid)) ::
               (_t'2, (tptr Tvoid)) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := smc_realm_destroy_body
|}.
