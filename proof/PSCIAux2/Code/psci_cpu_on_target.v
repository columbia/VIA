Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _entry_point_address := 2%positive.
Definition _g := 3%positive.
Definition _g_target_rec := 4%positive.
Definition _granule := 5%positive.
Definition _i := 6%positive.
Definition _rec := 7%positive.
Definition _rec__1 := 8%positive.
Definition _ret := 9%positive.
Definition _runnable := 10%positive.
Definition _target := 11%positive.
Definition _target_cpu := 12%positive.
Definition _target_rec := 13%positive.
Definition _t'1 := 14%positive.

Definition psci_cpu_on_target_body :=
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_rec_runnable (Tfunction
                                (Tcons (tptr Tvoid) Tnil) tuint
                                cc_default))
      ((Etempvar _target_rec (tptr Tvoid)) :: nil))
    (Sifthenelse (Ebinop One (Etempvar _t'1 tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall None
          (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil) tvoid
                                cc_default))
          ((Etempvar _target_rec (tptr Tvoid)) :: nil))
        (Ssequence
          (Scall None
            (Evar _granule_unlock (Tfunction
                                    (Tcons (tptr Tvoid)
                                      Tnil) tvoid cc_default))
            ((Etempvar _g_target_rec (tptr Tvoid)) :: nil))
          (Scall None
            (Evar _set_psci_result_x0 (Tfunction (Tcons tulong Tnil) tvoid
                                        cc_default))
            ((Econst_long (Int64.repr 4294967292) tulong) :: nil))))
      (Ssequence
        (Scall None
          (Evar _psci_reset_rec (Tfunction
                                  (Tcons (tptr Tvoid)
                                    (Tcons (tptr Tvoid) Tnil))
                                  tvoid cc_default))
          ((Etempvar _rec (tptr Tvoid)) ::
           (Etempvar _target_rec (tptr Tvoid)) :: nil))
        (Ssequence
          (Scall None
            (Evar _set_rec_pc (Tfunction
                                (Tcons (tptr Tvoid)
                                  (Tcons tulong Tnil)) tvoid cc_default))
            ((Etempvar _target_rec (tptr Tvoid)) ::
             (Etempvar _entry_point_address tulong) :: nil))
          (Ssequence
            (Scall None
              (Evar _set_rec_runnable (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons tuint Tnil)) tvoid cc_default))
              ((Etempvar _target_rec (tptr Tvoid)) ::
               (Econst_int (Int.repr 1) tuint) :: nil))
            (Ssequence
              (Scall None
                (Evar _set_psci_result_forward_psci_call (Tfunction
                                                           (Tcons tuint Tnil)
                                                           tvoid cc_default))
                ((Econst_int (Int.repr 1) tuint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _set_psci_result_forward_x1 (Tfunction
                                                      (Tcons tulong Tnil) tvoid
                                                      cc_default))
                  ((Etempvar _target_cpu tulong) :: nil))
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
                      ((Econst_long (Int64.repr 0) tulong) :: nil)))))))))))
.

Definition f_psci_cpu_on_target := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_g_target_rec, (tptr Tvoid)) ::
                (_target_rec, (tptr Tvoid)) ::
                (_rec, (tptr Tvoid)) ::
                (_entry_point_address, tulong) :: (_target_cpu, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body := psci_cpu_on_target_body
|}.
