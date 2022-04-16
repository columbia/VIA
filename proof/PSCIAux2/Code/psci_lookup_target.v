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
Definition _lock := 8%positive.
Definition _rec := 9%positive.
Definition _rec__1 := 10%positive.
Definition _rec_idx := 11%positive.
Definition _rec_list := 12%positive.
Definition _rec_list__1 := 13%positive.
Definition _ret := 14%positive.
Definition _target := 15%positive.
Definition _valid := 16%positive.
Definition _t'1 := 17%positive.
Definition _t'2 := 18%positive.
Definition _t'3 := 19%positive.
Definition _t'4 := 20%positive.
Definition _t'5 := 21%positive.
Definition _t'6 := 22%positive.
Definition _t'7 := 23%positive.

Definition psci_lookup_target_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _mpidr_is_valid (Tfunction (Tcons tulong Tnil) tuint cc_default))
        ((Etempvar _target tulong) :: nil))
      (Sset _valid (Etempvar _t'1 tuint)))
    (Sifthenelse (Ebinop Oeq (Etempvar _valid tint)
                   (Econst_int (Int.repr 0) tuint) tint)
      (Ssequence
        (Scall (Some _t'2)
          (Evar _null_ptr (Tfunction Tnil (tptr Tvoid) cc_default)) nil)
        (Sreturn (Some (Etempvar _t'2 (tptr Tvoid)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _get_rec_g_rd (Tfunction
                                  (Tcons (tptr Tvoid) Tnil)
                                  (tptr Tvoid) cc_default))
            ((Etempvar _rec (tptr Tvoid)) :: nil))
          (Sset _g_rd (Etempvar _t'3 (tptr Tvoid))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _get_rec_g_rec_list (Tfunction
                                          (Tcons (tptr Tvoid)
                                            Tnil)
                                          (tptr Tvoid)
                                          cc_default))
              ((Etempvar _rec (tptr Tvoid)) :: nil))
            (Sset _g_rec_list (Etempvar _t'4 (tptr Tvoid))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _granule_map (Tfunction
                                     (Tcons (tptr Tvoid)
                                       (Tcons tuint Tnil)) (tptr Tvoid)
                                     cc_default))
                ((Etempvar _g_rec_list (tptr Tvoid)) ::
                 (Econst_int (Int.repr 6) tuint) :: nil))
              (Sset _rec_list (Etempvar _t'5 (tptr Tvoid))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Scall (Some _t'6)
                    (Evar _mpidr_to_rec_idx (Tfunction (Tcons tulong Tnil)
                                              tulong cc_default))
                    ((Etempvar _target tulong) :: nil))
                  (Scall (Some _t'7)
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
                     (Etempvar _t'6 tulong) :: nil)))
                (Sset _g_rec (Etempvar _t'7 (tptr Tvoid))))
              (Ssequence
                (Scall None
                  (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil)
                                        tvoid cc_default))
                  ((Etempvar _rec_list (tptr Tvoid)) ::
                   nil))
                (Sreturn (Some (Etempvar _g_rec (tptr Tvoid)))))))))))
.

Definition f_psci_lookup_target := {|
  fn_return := (tptr Tvoid);
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_target, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_valid, tint) :: (_g_rd, (tptr Tvoid)) ::
               (_g_rec_list, (tptr Tvoid)) ::
               (_g_rec, (tptr Tvoid)) ::
               (_rec_list, (tptr Tvoid)) ::
               (_t'7, (tptr Tvoid)) :: (_t'6, tulong) ::
               (_t'5, (tptr Tvoid)) ::
               (_t'4, (tptr Tvoid)) ::
               (_t'3, (tptr Tvoid)) ::
               (_t'2, (tptr Tvoid)) :: (_t'1, tuint) :: nil);
  fn_body := psci_lookup_target_body
|}.
