Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _g := 1%positive.
Definition _g_rd := 2%positive.
Definition _g_rec := 3%positive.
Definition _g_rec_list := 4%positive.
Definition _g_rtt := 5%positive.
Definition _granule := 6%positive.
Definition _i := 7%positive.
Definition _lock := 8%positive.
Definition _rd := 9%positive.
Definition _rec := 10%positive.
Definition _rec_list := 11%positive.
Definition _ret := 12%positive.
Definition _rt := 13%positive.
Definition _state := 14%positive.
Definition _t'1 := 15%positive.

Definition realm_destroy_ops_body :=
  (Ssequence
    (Scall None
      (Evar _granule_lock (Tfunction
                            (Tcons (tptr Tvoid) Tnil) tvoid
                            cc_default))
      ((Etempvar _g_rec_list (tptr Tvoid)) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _null_ptr (Tfunction Tnil (tptr Tvoid) cc_default)) nil)
        (Scall None
          (Evar _set_g_rtt_rd (Tfunction
                                (Tcons (tptr Tvoid)
                                  (Tcons (tptr Tvoid) Tnil))
                                tvoid cc_default))
          ((Etempvar _g_rtt (tptr Tvoid)) ::
           (Etempvar _t'1 (tptr Tvoid)) :: nil)))
      (Ssequence
        (Scall None
          (Evar _granule_memzero (Tfunction
                                   (Tcons (tptr Tvoid)
                                     (Tcons tuint Tnil)) tvoid cc_default))
          ((Etempvar _g_rtt (tptr Tvoid)) ::
           (Econst_int (Int.repr 5) tuint) :: nil))
        (Ssequence
          (Scall None
            (Evar _granule_set_state (Tfunction
                                       (Tcons (tptr Tvoid)
                                         (Tcons tuint Tnil)) tvoid cc_default))
            ((Etempvar _g_rtt (tptr Tvoid)) ::
             (Econst_int (Int.repr 1) tuint) :: nil))
          (Ssequence
            (Scall None
              (Evar _granule_unlock (Tfunction
                                      (Tcons (tptr Tvoid)
                                        Tnil) tvoid cc_default))
              ((Etempvar _g_rtt (tptr Tvoid)) :: nil))
            (Ssequence
              (Scall None
                (Evar _granule_memzero (Tfunction
                                         (Tcons
                                           (tptr Tvoid)
                                           (Tcons tuint Tnil)) tvoid
                                         cc_default))
                ((Etempvar _g_rec_list (tptr Tvoid)) ::
                 (Econst_int (Int.repr 6) tuint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _granule_set_state (Tfunction
                                             (Tcons
                                               (tptr Tvoid)
                                               (Tcons tuint Tnil)) tvoid
                                             cc_default))
                  ((Etempvar _g_rec_list (tptr Tvoid)) ::
                   (Econst_int (Int.repr 1) tuint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _granule_memzero (Tfunction
                                             (Tcons
                                               (tptr Tvoid)
                                               (Tcons tuint Tnil)) tvoid
                                             cc_default))
                    ((Etempvar _g_rd (tptr Tvoid)) ::
                     (Econst_int (Int.repr 2) tuint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _granule_set_state (Tfunction
                                                 (Tcons
                                                   (tptr Tvoid)
                                                   (Tcons tuint Tnil)) tvoid
                                                 cc_default))
                      ((Etempvar _g_rd (tptr Tvoid)) ::
                       (Econst_int (Int.repr 1) tuint) :: nil))
                    (Scall None
                      (Evar _granule_unlock (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                Tnil) tvoid cc_default))
                      ((Etempvar _g_rec_list (tptr Tvoid)) ::
                       nil)))))))))))
.

Definition f_realm_destroy_ops := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_g_rtt, (tptr Tvoid)) ::
                (_g_rec_list, (tptr Tvoid)) ::
                (_g_rd, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr Tvoid)) :: nil);
  fn_body := realm_destroy_ops_body
|}.
