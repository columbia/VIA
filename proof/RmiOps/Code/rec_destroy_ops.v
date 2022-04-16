Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _g := 1%positive.
Definition _g_rd := 2%positive.
Definition _g_rec := 3%positive.
Definition _g_rec_list := 4%positive.
Definition _granule := 5%positive.
Definition _i := 6%positive.
Definition _idx := 7%positive.
Definition _rd := 8%positive.
Definition _rec := 9%positive.
Definition _rec__1 := 10%positive.
Definition _rec_idx := 11%positive.
Definition _rec_list := 12%positive.
Definition _rec_list__1 := 13%positive.
Definition _ret := 14%positive.
Definition _state := 15%positive.
Definition _t'1 := 16%positive.
Definition _t'2 := 17%positive.
Definition _t'3 := 18%positive.
Definition _t'4 := 19%positive.
Definition _t'5 := 20%positive.
Definition _t'6 := 21%positive.
Definition _t'7 := 22%positive.

Definition rec_destroy_ops_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_g_rec_rd (Tfunction
                              (Tcons (tptr Tvoid) Tnil)
                              (tptr Tvoid) cc_default))
        ((Etempvar _g_rec (tptr Tvoid)) :: nil))
      (Sset _g_rd (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _granule_map (Tfunction
                               (Tcons (tptr Tvoid)
                                 (Tcons tuint Tnil)) (tptr Tvoid) cc_default))
          ((Etempvar _g_rec (tptr Tvoid)) ::
           (Econst_int (Int.repr 3) tuint) :: nil))
        (Sset _rec (Etempvar _t'2 (tptr Tvoid))))
      (Ssequence
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _get_rec_g_rec_list (Tfunction
                                          (Tcons (tptr Tvoid)
                                            Tnil)
                                          (tptr Tvoid)
                                          cc_default))
              ((Etempvar _rec (tptr Tvoid)) :: nil))
            (Scall (Some _t'4)
              (Evar _granule_map (Tfunction
                                   (Tcons (tptr Tvoid)
                                     (Tcons tuint Tnil)) (tptr Tvoid)
                                   cc_default))
              ((Etempvar _t'3 (tptr Tvoid)) ::
               (Econst_int (Int.repr 6) tuint) :: nil)))
          (Sset _rec_list (Etempvar _t'4 (tptr Tvoid))))
        (Ssequence
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _get_rec_rec_idx (Tfunction
                                         (Tcons (tptr Tvoid)
                                           Tnil) tulong cc_default))
                ((Etempvar _rec (tptr Tvoid)) :: nil))
              (Scall (Some _t'6)
                (Evar _null_ptr (Tfunction Tnil (tptr Tvoid) cc_default)) nil))
            (Scall None
              (Evar _realm_set_rec_entry (Tfunction
                                           (Tcons tulong
                                             (Tcons
                                               (tptr Tvoid)
                                               (Tcons
                                                 (tptr Tvoid)
                                                 Tnil))) tvoid cc_default))
              ((Etempvar _t'5 tulong) ::
               (Etempvar _rec_list (tptr Tvoid)) ::
               (Etempvar _t'6 (tptr Tvoid)) :: nil)))
          (Ssequence
            (Scall None
              (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil) tvoid
                                    cc_default))
              ((Etempvar _rec_list (tptr Tvoid)) ::
               nil))
            (Ssequence
              (Scall None
                (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil) tvoid
                                      cc_default))
                ((Etempvar _rec (tptr Tvoid)) :: nil))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _null_ptr (Tfunction Tnil (tptr Tvoid) cc_default))
                    nil)
                  (Scall None
                    (Evar _set_g_rec_rd (Tfunction
                                          (Tcons
                                            (tptr Tvoid)
                                            (Tcons
                                              (tptr Tvoid)
                                              Tnil)) tvoid cc_default))
                    ((Etempvar _g_rec (tptr Tvoid)) ::
                     (Etempvar _t'7 (tptr Tvoid)) :: nil)))
                (Ssequence
                  (Scall None
                    (Evar _granule_memzero (Tfunction
                                             (Tcons
                                               (tptr Tvoid)
                                               (Tcons tuint Tnil)) tvoid
                                             cc_default))
                    ((Etempvar _g_rec (tptr Tvoid)) ::
                     (Econst_int (Int.repr 3) tuint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _granule_set_state (Tfunction
                                                 (Tcons
                                                   (tptr Tvoid)
                                                   (Tcons tuint Tnil)) tvoid
                                                 cc_default))
                      ((Etempvar _g_rec (tptr Tvoid)) ::
                       (Econst_int (Int.repr 1) tuint) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _granule_unlock (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  Tnil) tvoid cc_default))
                        ((Etempvar _g_rec (tptr Tvoid)) ::
                         nil))
                      (Scall None
                        (Evar _atomic_granule_put_release (Tfunction
                                                            (Tcons
                                                              (tptr Tvoid)
                                                              Tnil) tvoid
                                                            cc_default))
                        ((Etempvar _g_rd (tptr Tvoid)) ::
                         nil))))))))))))
.

Definition f_rec_destroy_ops := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_g_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_rd, (tptr Tvoid)) ::
               (_rec, (tptr Tvoid)) ::
               (_rec_list, (tptr Tvoid)) ::
               (_t'7, (tptr Tvoid)) :: (_t'6, (tptr Tvoid)) ::
               (_t'5, tulong) :: (_t'4, (tptr Tvoid)) ::
               (_t'3, (tptr Tvoid)) ::
               (_t'2, (tptr Tvoid)) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := rec_destroy_ops_body
|}.
