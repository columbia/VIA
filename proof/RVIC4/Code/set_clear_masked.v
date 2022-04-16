Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _g := 1%positive.
Definition _g_rec := 2%positive.
Definition _granule := 3%positive.
Definition _i := 4%positive.
Definition _intid := 5%positive.
Definition _mask := 6%positive.
Definition _masked := 7%positive.
Definition _need_notify := 8%positive.
Definition _rec := 9%positive.
Definition _rec__1 := 10%positive.
Definition _rec_rvic_state := 11%positive.
Definition _ret := 12%positive.
Definition _rvic := 13%positive.
Definition _target := 14%positive.
Definition _target_rec := 15%positive.
Definition _valid := 16%positive.
Definition _was_masked := 17%positive.
Definition _x0 := 18%positive.
Definition _t'1 := 19%positive.
Definition _t'2 := 20%positive.
Definition _t'3 := 21%positive.
Definition _t'4 := 22%positive.
Definition _t'5 := 23%positive.
Definition _t'6 := 24%positive.
Definition _t'7 := 25%positive.

Definition set_clear_masked_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _validate_and_lookup_target (Tfunction
                                            (Tcons (tptr Tvoid)
                                              (Tcons tulong
                                                (Tcons tulong Tnil))) tulong
                                            cc_default))
        ((Etempvar _rec (tptr Tvoid)) ::
         (Etempvar _target tulong) :: (Etempvar _intid tulong) :: nil))
      (Sset _x0 (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_target_rec (Tfunction Tnil (tptr Tvoid)
                                  cc_default)) nil)
        (Sset _target_rec (Etempvar _t'2 (tptr Tvoid))))
      (Ssequence
        (Scall None
          (Evar _set_rvic_result_x0 (Tfunction (Tcons tulong Tnil) tvoid
                                      cc_default))
          ((Etempvar _x0 tulong) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar _x0 tulong)
                       (Econst_int (Int.repr 0) tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _get_rec_rvic (Tfunction
                                      (Tcons (tptr Tvoid) Tnil)
                                      (tptr Tvoid)
                                      cc_default))
                ((Etempvar _target_rec (tptr Tvoid)) :: nil))
              (Sset _rvic
                (Etempvar _t'3 (tptr Tvoid))))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _masked tuint)
                             (Econst_int (Int.repr 1) tuint) tint)
                (Scall None
                  (Evar _rvic_set_masked (Tfunction
                                           (Tcons
                                             (tptr Tvoid)
                                             (Tcons tulong Tnil)) tvoid
                                           cc_default))
                  ((Etempvar _rvic (tptr Tvoid)) ::
                   (Etempvar _intid tulong) :: nil))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _rvic_is_masked (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                (Tcons tulong Tnil)) tuint
                                              cc_default))
                      ((Etempvar _rvic (tptr Tvoid)) ::
                       (Etempvar _intid tulong) :: nil))
                    (Sset _was_masked (Etempvar _t'4 tuint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'5)
                        (Evar _need_ns_notify (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    (Tcons tulong Tnil))) tuint
                                                cc_default))
                        ((Etempvar _rec (tptr Tvoid)) ::
                         (Etempvar _target_rec (tptr Tvoid)) ::
                         (Etempvar _intid tulong) :: nil))
                      (Sset _need_notify (Etempvar _t'5 tuint)))
                    (Ssequence
                      (Sifthenelse (Ebinop One (Etempvar _was_masked tuint)
                                     (Econst_int (Int.repr 0) tint) tint)
                        (Sset _t'6
                          (Ecast
                            (Ebinop One (Etempvar _need_notify tuint)
                              (Econst_int (Int.repr 0) tint) tint) tbool))
                        (Sset _t'6 (Econst_int (Int.repr 0) tint)))
                      (Sifthenelse (Etempvar _t'6 tint)
                        (Ssequence
                          (Scall None
                            (Evar _set_rvic_result_ns_notify (Tfunction
                                                               (Tcons tuint
                                                                 Tnil) tvoid
                                                               cc_default))
                            ((Econst_int (Int.repr 1) tuint) :: nil))
                          (Scall None
                            (Evar _set_rvic_result_target (Tfunction
                                                            (Tcons tulong Tnil)
                                                            tvoid cc_default))
                            ((Etempvar _target tulong) :: nil)))
                        (Scall None
                          (Evar _rvic_clear_masked (Tfunction
                                                     (Tcons
                                                       (tptr Tvoid)
                                                       (Tcons tulong Tnil))
                                                     tvoid cc_default))
                          ((Etempvar _rvic (tptr Tvoid)) ::
                           (Etempvar _intid tulong) :: nil)))))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _get_rec_g_rec (Tfunction
                                           (Tcons (tptr Tvoid)
                                             Tnil)
                                           (tptr Tvoid)
                                           cc_default))
                    ((Etempvar _target_rec (tptr Tvoid)) ::
                     nil))
                  (Sset _g_rec
                    (Etempvar _t'7 (tptr Tvoid))))
                (Ssequence
                  (Scall None
                    (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil)
                                          tvoid cc_default))
                    ((Etempvar _target_rec (tptr Tvoid)) ::
                     nil))
                  (Scall None
                    (Evar _granule_unlock (Tfunction
                                            (Tcons
                                              (tptr Tvoid)
                                              Tnil) tvoid cc_default))
                    ((Etempvar _g_rec (tptr Tvoid)) :: nil))))))
          Sskip))))
.

Definition f_set_clear_masked := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_target, tulong) :: (_intid, tulong) :: (_masked, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_target_rec, (tptr Tvoid)) ::
               (_g_rec, (tptr Tvoid)) :: (_x0, tulong) ::
               (_rvic, (tptr Tvoid)) ::
               (_was_masked, tuint) :: (_need_notify, tuint) ::
               (_t'7, (tptr Tvoid)) :: (_t'6, tint) ::
               (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, (tptr Tvoid)) ::
               (_t'2, (tptr Tvoid)) :: (_t'1, tulong) :: nil);
  fn_body := set_clear_masked_body
|}.
