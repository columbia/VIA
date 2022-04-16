Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _idx := 2%positive.
Definition _lock := 3%positive.
Definition _pas := 4%positive.
Definition _ret := 5%positive.
Definition _t'1 := 6%positive.
Definition _t'2 := 7%positive.
Definition _t'3 := 8%positive.
Definition _t'4 := 9%positive.

Definition asc_mark_realm_body :=
  (Ssequence
    (Sset _ret (Econst_long (Int64.repr 0) tulong))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _addr_to_gidx (Tfunction (Tcons tulong Tnil) tulong cc_default))
          ((Etempvar _addr tulong) :: nil))
        (Sset _idx (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _check_granule_idx (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
            ((Etempvar _idx tulong) :: nil))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tuint)
                         (Econst_int (Int.repr 0) tuint) tint)
            (Sset _ret (Econst_long (Int64.repr 1) tulong))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _find_spinlock (Tfunction (Tcons tulong Tnil)
                                         (tptr Tvoid) cc_default))
                  ((Etempvar _addr tulong) :: nil))
                (Sset _lock (Etempvar _t'2 (tptr Tvoid))))
              (Ssequence
                (Scall None
                  (Evar _spinlock_acquire (Tfunction (Tcons (tptr Tvoid) Tnil)
                                            tvoid cc_default))
                  ((Etempvar _lock (tptr Tvoid)) :: nil))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _get_pas (Tfunction (Tcons tulong Tnil) tulong
                                       cc_default))
                      ((Etempvar _idx tulong) :: nil))
                    (Sset _pas (Ecast (Etempvar _t'3 tulong) tuint)))
                  (Ssequence
                    (Sifthenelse (Ebinop One (Etempvar _pas tuint)
                                   (Econst_int (Int.repr 9) tuint) tint)
                      (Sset _ret (Econst_long (Int64.repr 1) tulong))
                      (Ssequence
                        (Scall None
                          (Evar _set_pas (Tfunction
                                           (Tcons tulong (Tcons tulong Tnil))
                                           tvoid cc_default))
                          ((Etempvar _idx tulong) ::
                           (Econst_int (Int.repr 11) tuint) :: nil))
                        (Scall None
                          (Evar _tlbi_by_pa (Tfunction (Tcons tulong Tnil)
                                              tvoid cc_default))
                          ((Etempvar _addr tulong) :: nil))))
                    (Scall None
                      (Evar _spinlock_release (Tfunction
                                                (Tcons (tptr Tvoid) Tnil) tvoid
                                                cc_default))
                      ((Etempvar _lock (tptr Tvoid)) :: nil))))))))
        (Sreturn (Some (Etempvar _ret tulong))))))
.

Definition f_asc_mark_realm := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tulong) :: (_idx, tulong) :: (_lock, (tptr Tvoid)) ::
               (_pas, tuint) :: (_t'4, tuint) :: (_t'3, tulong) ::
               (_t'2, (tptr Tvoid)) :: (_t'1, tulong) :: nil);
  fn_body := asc_mark_realm_body
|}.
