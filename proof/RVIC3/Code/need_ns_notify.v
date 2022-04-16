Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _enabled := 1%positive.
Definition _g := 2%positive.
Definition _i := 3%positive.
Definition _idx := 4%positive.
Definition _idx1 := 5%positive.
Definition _idx2 := 6%positive.
Definition _intid := 7%positive.
Definition _mask := 8%positive.
Definition _masked := 9%positive.
Definition _pending := 10%positive.
Definition _rec := 11%positive.
Definition _rec__1 := 12%positive.
Definition _rec_idx := 13%positive.
Definition _rec_rvic_state := 14%positive.
Definition _ret := 15%positive.
Definition _rvic := 16%positive.
Definition _target := 17%positive.
Definition _target_rec := 18%positive.
Definition _t'1 := 19%positive.
Definition _t'2 := 20%positive.
Definition _t'3 := 21%positive.
Definition _t'4 := 22%positive.
Definition _t'5 := 23%positive.
Definition _t'6 := 24%positive.

Definition need_ns_notify_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_rec_rec_idx (Tfunction
                                 (Tcons (tptr Tvoid) Tnil)
                                 tulong cc_default))
        ((Etempvar _target_rec (tptr Tvoid)) :: nil))
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
        (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _get_rec_rvic_enabled (Tfunction
                                            (Tcons (tptr Tvoid)
                                              Tnil) tuint cc_default))
              ((Etempvar _target_rec (tptr Tvoid)) :: nil))
            (Sset _enabled (Etempvar _t'3 tuint)))
          (Sifthenelse (Ebinop Oeq (Etempvar _enabled tuint)
                         (Econst_int (Int.repr 0) tuint) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _get_rec_rvic (Tfunction
                                        (Tcons (tptr Tvoid)
                                          Tnil)
                                        (tptr Tvoid)
                                        cc_default))
                  ((Etempvar _target_rec (tptr Tvoid)) :: nil))
                (Sset _rvic
                  (Etempvar _t'4 (tptr Tvoid))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _rvic_is_pending (Tfunction
                                             (Tcons
                                               (tptr Tvoid)
                                               (Tcons tulong Tnil)) tuint
                                             cc_default))
                    ((Etempvar _rvic (tptr Tvoid)) ::
                     (Etempvar _intid tulong) :: nil))
                  (Sset _pending (Etempvar _t'5 tuint)))
                (Sifthenelse (Ebinop Oeq (Etempvar _pending tuint)
                               (Econst_int (Int.repr 0) tuint) tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'6)
                        (Evar _rvic_is_masked (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  (Tcons tulong Tnil)) tuint
                                                cc_default))
                        ((Etempvar _rvic (tptr Tvoid)) ::
                         (Etempvar _intid tulong) :: nil))
                      (Sset _masked (Etempvar _t'6 tuint)))
                    (Sifthenelse (Ebinop Oeq (Etempvar _masked tuint)
                                   (Econst_int (Int.repr 1) tuint) tint)
                      (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
                      (Sreturn (Some (Econst_int (Int.repr 1) tuint)))))))))))))
.

Definition f_need_ns_notify := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_target_rec, (tptr Tvoid)) ::
                (_intid, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_idx1, tulong) :: (_idx2, tulong) :: (_enabled, tuint) ::
               (_rvic, (tptr Tvoid)) ::
               (_pending, tuint) :: (_masked, tuint) :: (_t'6, tuint) ::
               (_t'5, tuint) ::
               (_t'4, (tptr Tvoid)) ::
               (_t'3, tuint) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := need_ns_notify_body
|}.
