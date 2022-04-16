Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_rd := 3%positive.
Definition _granule := 4%positive.
Definition _i := 5%positive.
Definition _lock := 6%positive.
Definition _rd := 7%positive.
Definition _rd__1 := 8%positive.
Definition _rd_addr := 9%positive.
Definition _ret := 10%positive.
Definition _state := 11%positive.
Definition _t'1 := 12%positive.
Definition _t'2 := 13%positive.
Definition _t'3 := 14%positive.
Definition _t'4 := 15%positive.

Definition smc_realm_activate_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _find_lock_granule (Tfunction (Tcons tulong (Tcons tulong Tnil))
                                   (tptr Tvoid) cc_default))
        ((Etempvar _rd_addr tulong) :: (Econst_int (Int.repr 2) tuint) :: nil))
      (Sset _g_rd (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'4)
          (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint cc_default))
          ((Etempvar _g_rd (tptr Tvoid)) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tuint)
                       (Econst_int (Int.repr 0) tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _granule_map (Tfunction
                                     (Tcons (tptr Tvoid)
                                       (Tcons tuint Tnil)) (tptr Tvoid)
                                     cc_default))
                ((Etempvar _g_rd (tptr Tvoid)) ::
                 (Econst_int (Int.repr 2) tuint) :: nil))
              (Sset _rd (Etempvar _t'2 (tptr Tvoid))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _get_rd_state (Tfunction
                                        (Tcons (tptr Tvoid)
                                          Tnil) tuint cc_default))
                  ((Etempvar _rd (tptr Tvoid)) :: nil))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tuint)
                               (Econst_int (Int.repr 0) tuint) tint)
                  (Ssequence
                    (Scall None
                      (Evar _realm_activate_ops (Tfunction
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    Tnil) tvoid cc_default))
                      ((Etempvar _rd (tptr Tvoid)) :: nil))
                    (Sset _ret (Econst_long (Int64.repr 0) tulong)))
                  (Sset _ret (Econst_long (Int64.repr 1) tulong))))
              (Ssequence
                (Scall None
                  (Evar _buffer_unmap (Tfunction (Tcons (tptr Tvoid) Tnil)
                                        tvoid cc_default))
                  ((Etempvar _rd (tptr Tvoid)) :: nil))
                (Scall None
                  (Evar _granule_unlock (Tfunction
                                          (Tcons
                                            (tptr Tvoid)
                                            Tnil) tvoid cc_default))
                  ((Etempvar _g_rd (tptr Tvoid)) :: nil)))))
          (Sset _ret (Econst_long (Int64.repr 1) tulong))))
      (Sreturn (Some (Etempvar _ret tulong)))))
.

Definition f_smc_realm_activate := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_rd_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_rd, (tptr Tvoid)) ::
               (_g_rd, (tptr Tvoid)) :: (_ret, tulong) ::
               (_t'4, tuint) :: (_t'3, tuint) :: (_t'2, (tptr Tvoid)) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := smc_realm_activate_body
|}.
