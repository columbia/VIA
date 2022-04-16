Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _icc := 1%positive.
Definition _rec := 2%positive.
Definition _rec__1 := 3%positive.
Definition _ret := 4%positive.
Definition _t'1 := 5%positive.
Definition _t'2 := 6%positive.
Definition _t'3 := 7%positive.

Definition restore_realm_state_body :=
  (Ssequence
    (Scall None
      (Evar _restore_sysreg_state (Tfunction
                                    (Tcons (tptr Tvoid) Tnil)
                                    tvoid cc_default))
      ((Etempvar _rec (tptr Tvoid)) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_rec_pc (Tfunction
                              (Tcons (tptr Tvoid) Tnil) tulong
                              cc_default))
          ((Etempvar _rec (tptr Tvoid)) :: nil))
        (Scall None
          (Evar _sysreg_write (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                tvoid cc_default))
          ((Econst_int (Int.repr 81) tuint) :: (Etempvar _t'1 tulong) :: nil)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _get_rec_pstate (Tfunction
                                    (Tcons (tptr Tvoid) Tnil)
                                    tulong cc_default))
            ((Etempvar _rec (tptr Tvoid)) :: nil))
          (Scall None
            (Evar _sysreg_write (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                  tvoid cc_default))
            ((Econst_int (Int.repr 94) tuint) :: (Etempvar _t'2 tulong) :: nil)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                   cc_default))
              ((Econst_int (Int.repr 109) tuint) :: nil))
            (Sset _icc (Etempvar _t'3 tulong)))
          (Scall None
            (Evar _sysreg_write (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                  tvoid cc_default))
            ((Econst_int (Int.repr 109) tuint) ::
             (Ebinop Oand (Etempvar _icc tulong)
               (Econst_long (Int64.repr (18446744073709551607)) tulong) tulong) :: nil))))))
.

Definition f_restore_realm_state := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_icc, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := restore_realm_state_body
|}.
