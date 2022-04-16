Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _g_target_rec := 1%positive.
Definition _granule := 2%positive.
Definition _lowest_affinity_level := 3%positive.
Definition _rec := 4%positive.
Definition _rec__1 := 5%positive.
Definition _ret := 6%positive.
Definition _runnable := 7%positive.
Definition _target_affinity := 8%positive.
Definition _target_rec := 9%positive.
Definition _t'1 := 10%positive.
Definition _t'2 := 11%positive.
Definition _t'3 := 12%positive.
Definition _t'4 := 13%positive.

Definition psci_affinity_info_body :=
  (Sifthenelse (Ebinop One (Etempvar _lowest_affinity_level tulong)
                 (Econst_int (Int.repr 0) tint) tint)
    (Scall None
      (Evar _set_psci_result_x0 (Tfunction (Tcons tulong Tnil) tvoid
                                  cc_default))
      ((Econst_long (Int64.repr 4294967294) tulong) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _psci_lookup_target (Tfunction
                                      (Tcons (tptr Tvoid)
                                        (Tcons tulong Tnil))
                                      (tptr Tvoid)
                                      cc_default))
          ((Etempvar _rec (tptr Tvoid)) ::
           (Etempvar _target_affinity tulong) :: nil))
        (Sset _g_target_rec (Etempvar _t'1 (tptr Tvoid))))
      (Ssequence
        (Scall (Some _t'4)
          (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint cc_default))
          ((Etempvar _g_target_rec (tptr Tvoid)) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tuint)
                       (Econst_int (Int.repr 1) tint) tint)
          (Scall None
            (Evar _set_psci_result_x0 (Tfunction (Tcons tulong Tnil) tvoid
                                        cc_default))
            ((Econst_long (Int64.repr 4294967294) tulong) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _granule_map (Tfunction
                                     (Tcons (tptr Tvoid)
                                       (Tcons tuint Tnil)) (tptr Tvoid)
                                     cc_default))
                ((Etempvar _g_target_rec (tptr Tvoid)) ::
                 (Econst_int (Int.repr 4) tuint) :: nil))
              (Sset _target_rec (Etempvar _t'2 (tptr Tvoid))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _get_rec_runnable (Tfunction
                                            (Tcons (tptr Tvoid)
                                              Tnil) tuint cc_default))
                  ((Etempvar _target_rec (tptr Tvoid)) :: nil))
                (Sset _runnable (Etempvar _t'3 tuint)))
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _runnable tuint)
                               (Econst_int (Int.repr 1) tuint) tint)
                  (Sset _ret (Econst_long (Int64.repr 0) tulong))
                  (Sset _ret (Econst_long (Int64.repr 1) tulong)))
                (Ssequence
                  (Scall None
                    (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil)
                                          tvoid cc_default))
                    ((Etempvar _target_rec (tptr Tvoid)) ::
                     nil))
                  (Ssequence
                    (Scall None
                      (Evar _granule_unlock (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                Tnil) tvoid cc_default))
                      ((Etempvar _g_target_rec (tptr Tvoid)) ::
                       nil))
                    (Scall None
                      (Evar _set_psci_result_x0 (Tfunction (Tcons tulong Tnil)
                                                  tvoid cc_default))
                      ((Etempvar _ret tulong) :: nil)))))))))))
.

Definition f_psci_affinity_info := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_target_affinity, tulong) ::
                (_lowest_affinity_level, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_target_rec, (tptr Tvoid)) ::
               (_target_rec, (tptr Tvoid)) ::
               (_runnable, tuint) :: (_ret, tulong) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, (tptr Tvoid)) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := psci_affinity_info_body
|}.
