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
Definition _idx1 := 9%positive.
Definition _idx2 := 10%positive.
Definition _lock := 11%positive.
Definition _rec := 12%positive.
Definition _rec__1 := 13%positive.
Definition _rec_idx := 14%positive.
Definition _rec_list := 15%positive.
Definition _rec_list__1 := 16%positive.
Definition _ret := 17%positive.
Definition _target := 18%positive.
Definition _target_rec := 19%positive.
Definition _t'1 := 20%positive.
Definition _t'10 := 21%positive.
Definition _t'11 := 22%positive.
Definition _t'12 := 23%positive.
Definition _t'2 := 24%positive.
Definition _t'3 := 25%positive.
Definition _t'4 := 26%positive.
Definition _t'5 := 27%positive.
Definition _t'6 := 28%positive.
Definition _t'7 := 29%positive.
Definition _t'8 := 30%positive.
Definition _t'9 := 31%positive.

Definition find_lock_map_target_rec_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _mpidr_to_rec_idx (Tfunction (Tcons tulong Tnil) tulong
                                  cc_default))
        ((Etempvar _target tulong) :: nil))
      (Sset _idx1 (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_rec_rec_idx (Tfunction
                                   (Tcons (tptr Tvoid) Tnil)
                                   tulong cc_default))
          ((Etempvar _rec (tptr Tvoid)) :: nil))
        (Sset _idx2 (Etempvar _t'2 tulong)))
      (Sifthenelse (Ebinop Oeq (Etempvar _idx1 tulong) (Etempvar _idx2 tulong)
                     tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _get_rec_g_rec (Tfunction
                                     (Tcons (tptr Tvoid) Tnil)
                                     (tptr Tvoid)
                                     cc_default))
              ((Etempvar _rec (tptr Tvoid)) :: nil))
            (Sset _g (Etempvar _t'3 (tptr Tvoid))))
          (Ssequence
            (Scall None
              (Evar _granule_lock (Tfunction
                                    (Tcons (tptr Tvoid)
                                      Tnil) tvoid cc_default))
              ((Etempvar _g (tptr Tvoid)) :: nil))
            (Ssequence
              (Scall (Some _t'4)
                (Evar _granule_map (Tfunction
                                     (Tcons (tptr Tvoid)
                                       (Tcons tuint Tnil)) (tptr Tvoid)
                                     cc_default))
                ((Etempvar _g (tptr Tvoid)) ::
                 (Econst_int (Int.repr 4) tuint) :: nil))
              (Scall None
                (Evar _set_target_rec (Tfunction
                                        (Tcons (tptr Tvoid)
                                          Tnil) tvoid cc_default))
                ((Etempvar _t'4 (tptr Tvoid)) :: nil)))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _get_rec_g_rd (Tfunction
                                    (Tcons (tptr Tvoid) Tnil)
                                    (tptr Tvoid)
                                    cc_default))
              ((Etempvar _rec (tptr Tvoid)) :: nil))
            (Sset _g_rd (Etempvar _t'5 (tptr Tvoid))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _get_rec_g_rec_list (Tfunction
                                            (Tcons (tptr Tvoid)
                                              Tnil)
                                            (tptr Tvoid)
                                            cc_default))
                ((Etempvar _rec (tptr Tvoid)) :: nil))
              (Sset _g_rec_list
                (Etempvar _t'6 (tptr Tvoid))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'7)
                  (Evar _granule_map (Tfunction
                                       (Tcons (tptr Tvoid)
                                         (Tcons tuint Tnil)) (tptr Tvoid)
                                       cc_default))
                  ((Etempvar _g_rec_list (tptr Tvoid)) ::
                   (Econst_int (Int.repr 6) tuint) :: nil))
                (Sset _rec_list (Etempvar _t'7 (tptr Tvoid))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'8)
                      (Evar _mpidr_to_rec_idx (Tfunction (Tcons tulong Tnil)
                                                tulong cc_default))
                      ((Etempvar _target tulong) :: nil))
                    (Scall (Some _t'9)
                      (Evar _find_lock_rec (Tfunction
                                             (Tcons
                                               (tptr Tvoid)
                                               (Tcons
                                                 (tptr Tvoid)
                                                 (Tcons tulong Tnil)))
                                             (tptr Tvoid)
                                             cc_default))
                      ((Etempvar _g_rd (tptr Tvoid)) ::
                       (Etempvar _rec_list (tptr Tvoid)) ::
                       (Etempvar _t'8 tulong) :: nil)))
                  (Sset _g_target_rec
                    (Etempvar _t'9 (tptr Tvoid))))
                (Ssequence
                  (Scall None
                    (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil)
                                          tvoid cc_default))
                    ((Etempvar _rec_list (tptr Tvoid)) ::
                     nil))
                  (Ssequence
                    (Scall (Some _t'12)
                      (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                                       cc_default))
                      ((Etempvar _g_target_rec (tptr Tvoid)) ::
                       nil))
                    (Sifthenelse (Ebinop Oeq (Etempvar _t'12 tuint)
                                   (Econst_int (Int.repr 1) tint) tint)
                      (Ssequence
                        (Scall (Some _t'10)
                          (Evar _null_ptr (Tfunction Tnil (tptr Tvoid)
                                            cc_default)) nil)
                        (Scall None
                          (Evar _set_target_rec (Tfunction
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    Tnil) tvoid cc_default))
                          ((Etempvar _t'10 (tptr Tvoid)) :: nil)))
                      (Ssequence
                        (Scall (Some _t'11)
                          (Evar _granule_map (Tfunction
                                               (Tcons
                                                 (tptr Tvoid)
                                                 (Tcons tuint Tnil))
                                               (tptr Tvoid) cc_default))
                          ((Etempvar _g_target_rec (tptr Tvoid)) ::
                           (Econst_int (Int.repr 4) tuint) :: nil))
                        (Scall None
                          (Evar _set_target_rec (Tfunction
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    Tnil) tvoid cc_default))
                          ((Etempvar _t'11 (tptr Tvoid)) :: nil)))))))))))))
.

Definition f_find_lock_map_target_rec := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_target, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_target_rec, (tptr Tvoid)) ::
               (_idx1, tulong) :: (_idx2, tulong) ::
               (_ret, (tptr Tvoid)) ::
               (_g, (tptr Tvoid)) ::
               (_g_rd, (tptr Tvoid)) ::
               (_g_rec_list, (tptr Tvoid)) ::
               (_rec_list, (tptr Tvoid)) ::
               (_t'12, tuint) :: (_t'11, (tptr Tvoid)) ::
               (_t'10, (tptr Tvoid)) ::
               (_t'9, (tptr Tvoid)) :: (_t'8, tulong) ::
               (_t'7, (tptr Tvoid)) ::
               (_t'6, (tptr Tvoid)) ::
               (_t'5, (tptr Tvoid)) ::
               (_t'4, (tptr Tvoid)) ::
               (_t'3, (tptr Tvoid)) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := find_lock_map_target_rec_body
|}.
