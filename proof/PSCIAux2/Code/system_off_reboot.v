Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _g := 1%positive.
Definition _g_rd := 2%positive.
Definition _g_rec := 3%positive.
Definition _g_rec_list := 4%positive.
Definition _g_target_rec := 5%positive.
Definition _granule := 6%positive.
Definition _i := 7%positive.
Definition _idx := 8%positive.
Definition _lock := 9%positive.
Definition _rec := 10%positive.
Definition _rec__1 := 11%positive.
Definition _rec_idx := 12%positive.
Definition _rec_list := 13%positive.
Definition _rec_list__1 := 14%positive.
Definition _ret := 15%positive.
Definition _runnable := 16%positive.
Definition _t_rec := 17%positive.
Definition _target := 18%positive.
Definition _target_rec := 19%positive.
Definition _t'1 := 20%positive.
Definition _t'2 := 21%positive.
Definition _t'3 := 22%positive.
Definition _t'4 := 23%positive.
Definition _t'5 := 24%positive.
Definition _t'6 := 25%positive.
Definition _t'7 := 26%positive.
Definition _t'8 := 27%positive.

Definition system_off_reboot_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_rec_g_rec (Tfunction
                               (Tcons (tptr Tvoid) Tnil)
                               (tptr Tvoid) cc_default))
        ((Etempvar _rec (tptr Tvoid)) :: nil))
      (Sset _g_rec (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_rec_g_rd (Tfunction
                                (Tcons (tptr Tvoid) Tnil)
                                (tptr Tvoid) cc_default))
          ((Etempvar _rec (tptr Tvoid)) :: nil))
        (Sset _g_rd (Etempvar _t'2 (tptr Tvoid))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _get_rec_rec_idx (Tfunction
                                     (Tcons (tptr Tvoid) Tnil)
                                     tulong cc_default))
            ((Etempvar _rec (tptr Tvoid)) :: nil))
          (Sset _idx (Etempvar _t'3 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _get_rec_g_rec_list (Tfunction
                                          (Tcons (tptr Tvoid)
                                            Tnil)
                                          (tptr Tvoid)
                                          cc_default))
              ((Etempvar _rec (tptr Tvoid)) :: nil))
            (Sset _g (Etempvar _t'4 (tptr Tvoid))))
          (Ssequence
            (Scall None
              (Evar _granule_lock (Tfunction
                                    (Tcons (tptr Tvoid)
                                      Tnil) tvoid cc_default))
              ((Etempvar _g_rec (tptr Tvoid)) :: nil))
            (Ssequence
              (Scall None
                (Evar _set_rec_runnable (Tfunction
                                          (Tcons (tptr Tvoid)
                                            (Tcons tuint Tnil)) tvoid
                                          cc_default))
                ((Etempvar _rec (tptr Tvoid)) ::
                 (Econst_int (Int.repr 0) tuint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _granule_unlock (Tfunction
                                          (Tcons
                                            (tptr Tvoid)
                                            Tnil) tvoid cc_default))
                  ((Etempvar _g_rec (tptr Tvoid)) :: nil))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _granule_map (Tfunction
                                           (Tcons
                                             (tptr Tvoid)
                                             (Tcons tuint Tnil)) (tptr Tvoid)
                                           cc_default))
                      ((Etempvar _g (tptr Tvoid)) ::
                       (Econst_int (Int.repr 6) tuint) :: nil))
                    (Sset _rec_list (Etempvar _t'5 (tptr Tvoid))))
                  (Ssequence
                    (Sset _i (Econst_long (Int64.repr 0) tulong))
                    (Ssequence
                      (Swhile
                        (Ebinop Olt (Etempvar _i tulong)
                          (Econst_int (Int.repr 512) tuint) tint)
                        (Ssequence
                          (Sifthenelse (Ebinop One (Etempvar _i tulong)
                                         (Etempvar _idx tulong) tint)
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'6)
                                  (Evar _find_lock_rec (Tfunction
                                                         (Tcons
                                                           (tptr Tvoid)
                                                           (Tcons
                                                             (tptr Tvoid)
                                                             (Tcons tulong
                                                               Tnil)))
                                                         (tptr Tvoid)
                                                         cc_default))
                                  ((Etempvar _g_rd (tptr Tvoid)) ::
                                   (Etempvar _rec_list (tptr Tvoid)) ::
                                   (Etempvar _i tulong) :: nil))
                                (Sset _g_target_rec
                                  (Etempvar _t'6 (tptr Tvoid))))
                              (Ssequence
                                (Scall (Some _t'8)
                                  (Evar _is_null (Tfunction
                                                   (Tcons (tptr Tvoid) Tnil)
                                                   tuint cc_default))
                                  ((Etempvar _g_target_rec (tptr Tvoid)) ::
                                   nil))
                                (Sifthenelse (Ebinop Oeq (Etempvar _t'8 tuint)
                                               (Econst_int (Int.repr 0) tuint)
                                               tint)
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'7)
                                        (Evar _granule_map (Tfunction
                                                             (Tcons
                                                               (tptr Tvoid)
                                                               (Tcons tuint
                                                                 Tnil))
                                                             (tptr Tvoid)
                                                             cc_default))
                                        ((Etempvar _g_target_rec (tptr Tvoid)) ::
                                         (Econst_int (Int.repr 4) tuint) ::
                                         nil))
                                      (Sset _t_rec
                                        (Etempvar _t'7 (tptr Tvoid))))
                                    (Ssequence
                                      (Scall None
                                        (Evar _set_rec_runnable (Tfunction
                                                                  (Tcons
                                                                    (tptr Tvoid)
                                                                    (Tcons
                                                                      tuint
                                                                      Tnil))
                                                                  tvoid
                                                                  cc_default))
                                        ((Etempvar _t_rec (tptr Tvoid)) ::
                                         (Econst_int (Int.repr 0) tuint) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _buffer_unmap (Tfunction
                                                                (Tcons
                                                                  (tptr Tvoid)
                                                                  Tnil) tvoid
                                                                cc_default))
                                          ((Etempvar _t_rec (tptr Tvoid)) ::
                                           nil))
                                        (Scall None
                                          (Evar _granule_unlock (Tfunction
                                                                  (Tcons
                                                                    (tptr Tvoid)
                                                                    Tnil) tvoid
                                                                  cc_default))
                                          ((Etempvar _g_target_rec (tptr Tvoid)) ::
                                           nil)))))
                                  Sskip)))
                            Sskip)
                          (Sset _i
                            (Ebinop Oadd (Etempvar _i tulong)
                              (Econst_int (Int.repr 1) tint) tulong))))
                      (Scall None
                        (Evar _buffer_unmap (Tfunction
                                              (Tcons (tptr Tvoid) Tnil) tvoid
                                              cc_default))
                        ((Etempvar _rec_list (tptr Tvoid)) ::
                         nil))))))))))))
.

Definition f_system_off_reboot := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_rec_list, (tptr Tvoid)) ::
               (_g, (tptr Tvoid)) :: (_i, tulong) ::
               (_g_rec, (tptr Tvoid)) ::
               (_g_rd, (tptr Tvoid)) :: (_idx, tulong) ::
               (_g_target_rec, (tptr Tvoid)) ::
               (_t_rec, (tptr Tvoid)) :: (_t'8, tuint) ::
               (_t'7, (tptr Tvoid)) ::
               (_t'6, (tptr Tvoid)) ::
               (_t'5, (tptr Tvoid)) ::
               (_t'4, (tptr Tvoid)) :: (_t'3, tulong) ::
               (_t'2, (tptr Tvoid)) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := system_off_reboot_body
|}.
