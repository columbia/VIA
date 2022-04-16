Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_rd := 3%positive.
Definition _g_rec := 4%positive.
Definition _g_rec_list := 5%positive.
Definition _g_rec_params := 6%positive.
Definition _granule := 7%positive.
Definition _i := 8%positive.
Definition _idx := 9%positive.
Definition _lock := 10%positive.
Definition _mpidr := 11%positive.
Definition _ns_access_ok := 12%positive.
Definition _rd := 13%positive.
Definition _rd__1 := 14%positive.
Definition _rd_addr := 15%positive.
Definition _rec := 16%positive.
Definition _rec__1 := 17%positive.
Definition _rec_addr := 18%positive.
Definition _rec_idx := 19%positive.
Definition _rec_list := 20%positive.
Definition _rec_list__1 := 21%positive.
Definition _rec_params_addr := 22%positive.
Definition _ret := 23%positive.
Definition _state := 24%positive.
Definition _val := 25%positive.
Definition _valid := 26%positive.
Definition _t'1 := 27%positive.
Definition _t'10 := 28%positive.
Definition _t'11 := 29%positive.
Definition _t'12 := 30%positive.
Definition _t'13 := 31%positive.
Definition _t'14 := 32%positive.
Definition _t'15 := 33%positive.
Definition _t'2 := 34%positive.
Definition _t'3 := 35%positive.
Definition _t'4 := 36%positive.
Definition _t'5 := 37%positive.
Definition _t'6 := 38%positive.
Definition _t'7 := 39%positive.
Definition _t'8 := 40%positive.
Definition _t'9 := 41%positive.

Definition smc_rec_create_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _find_granule (Tfunction (Tcons tulong Tnil)
                              (tptr Tvoid) cc_default))
        ((Etempvar _rec_params_addr tulong) :: nil))
      (Sset _g_rec_params (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'15)
          (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint cc_default))
          ((Etempvar _g_rec_params (tptr Tvoid)) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'15 tuint)
                       (Econst_int (Int.repr 0) tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _find_lock_granule (Tfunction
                                           (Tcons tulong (Tcons tulong Tnil))
                                           (tptr Tvoid)
                                           cc_default))
                ((Etempvar _rec_addr tulong) ::
                 (Econst_int (Int.repr 1) tuint) :: nil))
              (Sset _g_rec (Etempvar _t'2 (tptr Tvoid))))
            (Ssequence
              (Scall (Some _t'14)
                (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                                 cc_default))
                ((Etempvar _g_rec (tptr Tvoid)) :: nil))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'14 tuint)
                             (Econst_int (Int.repr 0) tuint) tint)
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
                      (Scall (Some _t'13)
                        (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil)
                                         tuint cc_default))
                        ((Etempvar _g_rd (tptr Tvoid)) ::
                         nil))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'13 tuint)
                                     (Econst_int (Int.repr 0) tuint) tint)
                        (Ssequence
                          (Scall None
                            (Evar _ns_granule_map (Tfunction
                                                    (Tcons tuint
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        Tnil)) tvoid
                                                    cc_default))
                            ((Econst_int (Int.repr 0) tuint) ::
                             (Etempvar _g_rec_params (tptr Tvoid)) ::
                             nil))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'4)
                                (Evar _ns_buffer_read_rec_params (Tfunction
                                                                   (Tcons tuint
                                                                     Tnil)
                                                                   tuint
                                                                   cc_default))
                                ((Econst_int (Int.repr 0) tuint) :: nil))
                              (Sset _ns_access_ok (Etempvar _t'4 tuint)))
                            (Ssequence
                              (Scall None
                                (Evar _ns_buffer_unmap (Tfunction
                                                         (Tcons tuint Tnil)
                                                         tvoid cc_default))
                                ((Econst_int (Int.repr 0) tuint) :: nil))
                              (Ssequence
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _ns_access_ok tuint)
                                               (Econst_int (Int.repr 0) tuint)
                                               tint)
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'5)
                                        (Evar _granule_map (Tfunction
                                                             (Tcons
                                                               (tptr Tvoid)
                                                               (Tcons tuint
                                                                 Tnil))
                                                             (tptr Tvoid)
                                                             cc_default))
                                        ((Etempvar _g_rec (tptr Tvoid)) ::
                                         (Econst_int (Int.repr 3) tuint) ::
                                         nil))
                                      (Sset _rec
                                        (Etempvar _t'5 (tptr Tvoid))))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'6)
                                          (Evar _granule_map (Tfunction
                                                               (Tcons
                                                                 (tptr Tvoid)
                                                                 (Tcons tuint
                                                                   Tnil))
                                                               (tptr Tvoid)
                                                               cc_default))
                                          ((Etempvar _g_rd (tptr Tvoid)) ::
                                           (Econst_int (Int.repr 2) tuint) ::
                                           nil))
                                        (Sset _rd
                                          (Etempvar _t'6 (tptr Tvoid))))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'7)
                                              (Evar _get_rd_g_rec_list 
                                              (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  Tnil)
                                                (tptr Tvoid)
                                                cc_default))
                                              ((Etempvar _rd (tptr Tvoid)) ::
                                               nil))
                                            (Scall (Some _t'8)
                                              (Evar _granule_map (Tfunction
                                                                   (Tcons
                                                                     (tptr Tvoid)
                                                                     (Tcons
                                                                      tuint
                                                                      Tnil))
                                                                   (tptr Tvoid)
                                                                   cc_default))
                                              ((Etempvar _t'7 (tptr Tvoid)) ::
                                               (Econst_int (Int.repr 6) tuint) ::
                                               nil)))
                                          (Sset _rec_list
                                            (Etempvar _t'8 (tptr Tvoid))))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'12)
                                              (Evar _get_rd_state (Tfunction
                                                                    (Tcons
                                                                      (tptr Tvoid)
                                                                      Tnil)
                                                                    tuint
                                                                    cc_default))
                                              ((Etempvar _rd (tptr Tvoid)) ::
                                               nil))
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _t'12 tuint)
                                                           (Econst_int (Int.repr 0) tuint)
                                                           tint)
                                              (Ssequence
                                                (Scall (Some _t'11)
                                                  (Evar _mpidr_is_valid 
                                                  (Tfunction
                                                    (Tcons tulong Tnil) tuint
                                                    cc_default))
                                                  ((Etempvar _mpidr tulong) ::
                                                   nil))
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _t'11 tuint)
                                                               (Econst_int (Int.repr 1) tuint)
                                                               tint)
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _t'9)
                                                        (Evar _mpidr_to_rec_idx 
                                                        (Tfunction
                                                          (Tcons tulong Tnil)
                                                          tulong cc_default))
                                                        ((Etempvar _mpidr tulong) ::
                                                         nil))
                                                      (Sset _rec_idx
                                                        (Etempvar _t'9 tulong)))
                                                    (Ssequence
                                                      (Scall (Some _t'10)
                                                        (Evar _is_rec_valid 
                                                        (Tfunction
                                                          (Tcons tulong
                                                            (Tcons
                                                              (tptr Tvoid)
                                                              Tnil)) tuint
                                                          cc_default))
                                                        ((Etempvar _rec_idx tulong) ::
                                                         (Etempvar _rec_list (tptr Tvoid)) ::
                                                         nil))
                                                      (Sifthenelse (Ebinop Oeq
                                                                     (Etempvar _t'10 tuint)
                                                                     (Econst_int (Int.repr 1) tuint)
                                                                     tint)
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _rec_create_ops 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr Tvoid)
                                                                (Tcons
                                                                  (tptr Tvoid)
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
                                                                      Tnil)))))))
                                                              tvoid cc_default))
                                                            ((Etempvar _g_rd (tptr Tvoid)) ::
                                                             (Etempvar _g_rec (tptr Tvoid)) ::
                                                             (Etempvar _rd (tptr Tvoid)) ::
                                                             (Etempvar _rec_list (tptr Tvoid)) ::
                                                             (Etempvar _rec (tptr Tvoid)) ::
                                                             (Etempvar _mpidr tulong) ::
                                                             (Etempvar _rec_idx tulong) ::
                                                             nil))
                                                          (Sset _ret
                                                            (Econst_long (Int64.repr 0) tulong)))
                                                        (Sset _ret
                                                          (Econst_long (Int64.repr 1) tulong)))))
                                                  (Sset _ret
                                                    (Econst_long (Int64.repr 1) tulong))))
                                              (Sset _ret
                                                (Econst_long (Int64.repr 1) tulong))))
                                          (Ssequence
                                            (Scall None
                                              (Evar _buffer_unmap (Tfunction
                                                                    (Tcons
                                                                      (tptr Tvoid)
                                                                      Tnil)
                                                                    tvoid
                                                                    cc_default))
                                              ((Etempvar _rec_list (tptr Tvoid)) ::
                                               nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _buffer_unmap (Tfunction
                                                                      (Tcons
                                                                      (tptr Tvoid)
                                                                      Tnil)
                                                                      tvoid
                                                                      cc_default))
                                                ((Etempvar _rd (tptr Tvoid)) ::
                                                 nil))
                                              (Scall None
                                                (Evar _buffer_unmap (Tfunction
                                                                      (Tcons
                                                                      (tptr Tvoid)
                                                                      Tnil)
                                                                      tvoid
                                                                      cc_default))
                                                ((Etempvar _rec (tptr Tvoid)) ::
                                                 nil))))))))
                                  (Sset _ret
                                    (Econst_long (Int64.repr 1) tulong)))
                                (Scall None
                                  (Evar _granule_unlock (Tfunction
                                                          (Tcons
                                                            (tptr Tvoid)
                                                            Tnil) tvoid
                                                          cc_default))
                                  ((Etempvar _g_rd (tptr Tvoid)) ::
                                   nil))))))
                        (Sset _ret (Econst_long (Int64.repr 1) tulong))))
                    (Scall None
                      (Evar _granule_unlock (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                Tnil) tvoid cc_default))
                      ((Etempvar _g_rec (tptr Tvoid)) ::
                       nil))))
                (Sset _ret (Econst_long (Int64.repr 1) tulong)))))
          (Sset _ret (Econst_long (Int64.repr 1) tulong))))
      (Sreturn (Some (Etempvar _ret tulong)))))
.

Definition f_smc_rec_create := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_rec_addr, tulong) :: (_rd_addr, tulong) ::
                (_mpidr, tulong) :: (_rec_params_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_rd, (tptr Tvoid)) ::
               (_g_rec, (tptr Tvoid)) ::
               (_g_rec_params, (tptr Tvoid)) ::
               (_rec, (tptr Tvoid)) ::
               (_rd, (tptr Tvoid)) ::
               (_rec_list, (tptr Tvoid)) ::
               (_rec_idx, tulong) :: (_ns_access_ok, tuint) ::
               (_ret, tulong) :: (_t'15, tuint) :: (_t'14, tuint) ::
               (_t'13, tuint) :: (_t'12, tuint) :: (_t'11, tuint) ::
               (_t'10, tuint) :: (_t'9, tulong) :: (_t'8, (tptr Tvoid)) ::
               (_t'7, (tptr Tvoid)) ::
               (_t'6, (tptr Tvoid)) :: (_t'5, (tptr Tvoid)) ::
               (_t'4, tuint) :: (_t'3, (tptr Tvoid)) ::
               (_t'2, (tptr Tvoid)) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := smc_rec_create_body
|}.
