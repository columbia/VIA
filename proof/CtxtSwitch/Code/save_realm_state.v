Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _rec := 1%positive.
Definition _rec__1 := 2%positive.
Definition _ret := 3%positive.
Definition _t'1 := 4%positive.
Definition _t'2 := 5%positive.

Definition save_realm_state_body :=
  (Ssequence
    (Scall None
      (Evar _save_sysreg_state (Tfunction
                                 (Tcons (tptr Tvoid) Tnil)
                                 tvoid cc_default))
      ((Etempvar _rec (tptr Tvoid)) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong cc_default))
          ((Econst_int (Int.repr 81) tuint) :: nil))
        (Scall None
          (Evar _set_rec_pc (Tfunction
                              (Tcons (tptr Tvoid)
                                (Tcons tulong Tnil)) tvoid cc_default))
          ((Etempvar _rec (tptr Tvoid)) ::
           (Etempvar _t'1 tulong) :: nil)))
      (Ssequence
        (Scall (Some _t'2)
          (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong cc_default))
          ((Econst_int (Int.repr 94) tuint) :: nil))
        (Scall None
          (Evar _set_rec_pstate (Tfunction
                                  (Tcons (tptr Tvoid)
                                    (Tcons tulong Tnil)) tvoid cc_default))
          ((Etempvar _rec (tptr Tvoid)) ::
           (Etempvar _t'2 tulong) :: nil)))))
.

Definition f_save_realm_state := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := save_realm_state_body
|}.
