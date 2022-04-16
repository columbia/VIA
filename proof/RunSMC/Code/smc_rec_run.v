Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_rec := 3%positive.
Definition _g_rec_run := 4%positive.
Definition _granule := 5%positive.
Definition _i := 6%positive.
Definition _info := 7%positive.
Definition _lock := 8%positive.
Definition _rec := 9%positive.
Definition _rec__1 := 10%positive.
Definition _rec_addr := 11%positive.
Definition _rec_run_addr := 12%positive.
Definition _ret := 13%positive.
Definition _runnable := 14%positive.
Definition _t'1 := 15%positive.
Definition _t'2 := 16%positive.
Definition _t'3 := 17%positive.
Definition _t'4 := 18%positive.
Definition _t'5 := 19%positive.
Definition _t'6 := 20%positive.
Definition _t'7 := 21%positive.
Definition _t'8 := 22%positive.

Definition smc_rec_run_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _find_granule (Tfunction (Tcons tulong Tnil)
                              (tptr Tvoid) cc_default))
        ((Etempvar _rec_run_addr tulong) :: nil))
      (Sset _g_rec_run (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Scall (Some _t'8)
        (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint cc_default))
        ((Etempvar _g_rec_run (tptr Tvoid)) :: nil))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tuint)
                     (Econst_int (Int.repr 1) tuint) tint)
        (Sreturn (Some (Econst_long (Int64.repr 1) tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _find_lock_unused_granule (Tfunction
                                                (Tcons tulong
                                                  (Tcons tulong Tnil))
                                                (tptr Tvoid)
                                                cc_default))
              ((Etempvar _rec_addr tulong) ::
               (Econst_int (Int.repr 3) tuint) :: nil))
            (Sset _g_rec (Etempvar _t'2 (tptr Tvoid))))
          (Ssequence
            (Scall (Some _t'7)
              (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                               cc_default))
              ((Etempvar _g_rec (tptr Tvoid)) :: nil))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tuint)
                           (Econst_int (Int.repr 1) tuint) tint)
              (Sreturn (Some (Econst_long (Int64.repr 1) tulong)))
              (Ssequence
                (Scall None
                  (Evar _atomic_granule_get (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                Tnil) tvoid cc_default))
                  ((Etempvar _g_rec (tptr Tvoid)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _granule_unlock (Tfunction
                                            (Tcons
                                              (tptr Tvoid)
                                              Tnil) tvoid cc_default))
                    ((Etempvar _g_rec (tptr Tvoid)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _ns_granule_map (Tfunction
                                              (Tcons tuint
                                                (Tcons
                                                  (tptr Tvoid)
                                                  Tnil)) tvoid cc_default))
                      ((Econst_int (Int.repr 0) tuint) ::
                       (Etempvar _g_rec_run (tptr Tvoid)) ::
                       nil))
                    (Ssequence
                      (Scall (Some _t'6)
                        (Evar _ns_buffer_read_rec_run (Tfunction
                                                        (Tcons tuint Tnil)
                                                        tuint cc_default))
                        ((Econst_int (Int.repr 0) tuint) :: nil))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint)
                                     (Econst_int (Int.repr 0) tuint) tint)
                        (Ssequence
                          (Scall None
                            (Evar _ns_buffer_unmap (Tfunction
                                                     (Tcons tuint Tnil) tvoid
                                                     cc_default))
                            ((Econst_int (Int.repr 0) tuint) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _atomic_granule_put_release (Tfunction
                                                                  (Tcons
                                                                    (tptr Tvoid)
                                                                    Tnil) tvoid
                                                                  cc_default))
                              ((Etempvar _g_rec (tptr Tvoid)) ::
                               nil))
                            (Sreturn (Some (Econst_long (Int64.repr 1) tulong)))))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'3)
                              (Evar _granule_map (Tfunction
                                                   (Tcons
                                                     (tptr Tvoid)
                                                     (Tcons tuint Tnil))
                                                   (tptr Tvoid) cc_default))
                              ((Etempvar _g_rec (tptr Tvoid)) ::
                               (Econst_int (Int.repr 3) tuint) :: nil))
                            (Sset _rec (Etempvar _t'3 (tptr Tvoid))))
                          (Ssequence
                            (Scall None
                              (Evar _granule_lock (Tfunction
                                                    (Tcons
                                                      (tptr Tvoid)
                                                      Tnil) tvoid cc_default))
                              ((Etempvar _g_rec (tptr Tvoid)) ::
                               nil))
                            (Ssequence
                              (Scall (Some _t'5)
                                (Evar _get_rec_runnable (Tfunction
                                                          (Tcons
                                                            (tptr Tvoid)
                                                            Tnil) tuint
                                                          cc_default))
                                ((Etempvar _rec (tptr Tvoid)) ::
                                 nil))
                              (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tuint)
                                             (Econst_int (Int.repr 0) tuint)
                                             tint)
                                (Ssequence
                                  (Scall None
                                    (Evar _granule_unlock (Tfunction
                                                            (Tcons
                                                              (tptr Tvoid)
                                                              Tnil) tvoid
                                                            cc_default))
                                    ((Etempvar _g_rec (tptr Tvoid)) ::
                                     nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _buffer_unmap (Tfunction
                                                            (Tcons (tptr Tvoid)
                                                              Tnil) tvoid
                                                            cc_default))
                                      ((Etempvar _rec (tptr Tvoid)) ::
                                       nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _ns_buffer_unmap (Tfunction
                                                                 (Tcons tuint
                                                                   Tnil) tvoid
                                                                 cc_default))
                                        ((Econst_int (Int.repr 0) tuint) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _atomic_granule_put_release 
                                          (Tfunction
                                            (Tcons
                                              (tptr Tvoid)
                                              Tnil) tvoid cc_default))
                                          ((Etempvar _g_rec (tptr Tvoid)) ::
                                           nil))
                                        (Sreturn (Some (Econst_long (Int64.repr 1) tulong)))))))
                                (Ssequence
                                  (Scall (Some _t'4)
                                    (Evar _complete_mmio_emulation (Tfunction
                                                                     (Tcons
                                                                      (tptr Tvoid)
                                                                      Tnil)
                                                                     tuint
                                                                     cc_default))
                                    ((Etempvar _rec (tptr Tvoid)) ::
                                     nil))
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _t'4 tuint)
                                                 (Econst_int (Int.repr 0) tuint)
                                                 tint)
                                    (Ssequence
                                      (Scall None
                                        (Evar _granule_unlock (Tfunction
                                                                (Tcons
                                                                  (tptr Tvoid)
                                                                  Tnil) tvoid
                                                                cc_default))
                                        ((Etempvar _g_rec (tptr Tvoid)) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _buffer_unmap (Tfunction
                                                                (Tcons
                                                                  (tptr Tvoid)
                                                                  Tnil) tvoid
                                                                cc_default))
                                          ((Etempvar _rec (tptr Tvoid)) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _ns_buffer_unmap (Tfunction
                                                                     (Tcons
                                                                      tuint
                                                                      Tnil)
                                                                     tvoid
                                                                     cc_default))
                                            ((Econst_int (Int.repr 0) tuint) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _atomic_granule_put_release 
                                              (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  Tnil) tvoid cc_default))
                                              ((Etempvar _g_rec (tptr Tvoid)) ::
                                               nil))
                                            (Sreturn (Some (Econst_long (Int64.repr 1) tulong)))))))
                                    (Ssequence
                                      (Scall None
                                        (Evar _complete_hvc_exit (Tfunction
                                                                   (Tcons
                                                                     (tptr Tvoid)
                                                                     Tnil)
                                                                   tvoid
                                                                   cc_default))
                                        ((Etempvar _rec (tptr Tvoid)) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _reset_last_run_info (Tfunction
                                                                      (Tcons
                                                                      (tptr Tvoid)
                                                                      Tnil)
                                                                      tvoid
                                                                      cc_default))
                                          ((Etempvar _rec (tptr Tvoid)) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _reset_disposed_info 
                                            (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                Tnil) tvoid cc_default))
                                            ((Etempvar _rec (tptr Tvoid)) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _granule_unlock (Tfunction
                                                                      (Tcons
                                                                      (tptr Tvoid)
                                                                      Tnil)
                                                                      tvoid
                                                                      cc_default))
                                              ((Etempvar _g_rec (tptr Tvoid)) ::
                                               nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _rec_run_loop (Tfunction
                                                                      (Tcons
                                                                      (tptr Tvoid)
                                                                      Tnil)
                                                                      tvoid
                                                                      cc_default))
                                                ((Etempvar _rec (tptr Tvoid)) ::
                                                 nil))
                                              (Sreturn (Some (Econst_long (Int64.repr 2) tulong)))))))))))))))))))))))))
.

Definition f_smc_rec_run := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_rec_addr, tulong) :: (_rec_run_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_rec, (tptr Tvoid)) ::
               (_g_rec_run, (tptr Tvoid)) ::
               (_rec, (tptr Tvoid)) :: (_ret, tulong) ::
               (_t'8, tuint) :: (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tuint) :: (_t'3, (tptr Tvoid)) ::
               (_t'2, (tptr Tvoid)) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := smc_rec_run_body
|}.
