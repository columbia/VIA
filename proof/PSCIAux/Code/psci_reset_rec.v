Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _rec := 1%positive.
Definition _rec__1 := 2%positive.
Definition _reg := 3%positive.
Definition _ret := 4%positive.
Definition _target_rec := 5%positive.
Definition _t'1 := 6%positive.

Definition psci_reset_rec_body :=
  (Ssequence
    (Scall None
      (Evar _set_rec_pstate (Tfunction
                              (Tcons (tptr Tvoid)
                                (Tcons tulong Tnil)) tvoid cc_default))
      ((Etempvar _target_rec (tptr Tvoid)) ::
       (Econst_int (Int.repr 965) tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar _set_rec_sysregs (Tfunction
                                 (Tcons (tptr Tvoid)
                                   (Tcons tuint (Tcons tulong Tnil))) tvoid
                                 cc_default))
        ((Etempvar _target_rec (tptr Tvoid)) ::
         (Econst_int (Int.repr 47) tuint) ::
         (Econst_long (Int64.repr 12912760) tulong) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _get_rec_sysregs (Tfunction
                                     (Tcons (tptr Tvoid)
                                       (Tcons tuint Tnil)) tulong cc_default))
            ((Etempvar _rec (tptr Tvoid)) ::
             (Econst_int (Int.repr 47) tuint) :: nil))
          (Sset _reg (Etempvar _t'1 tulong)))
        (Scall None
          (Evar _set_rec_sysregs (Tfunction
                                   (Tcons (tptr Tvoid)
                                     (Tcons tuint (Tcons tulong Tnil))) tvoid
                                   cc_default))
          ((Etempvar _target_rec (tptr Tvoid)) ::
           (Econst_int (Int.repr 47) tuint) ::
           (Ebinop Oor (Econst_long (Int64.repr 12912760) tulong)
             (Ebinop Oand (Etempvar _reg tulong)
               (Econst_long (Int64.repr 33554432) tulong) tulong) tulong) ::
           nil)))))
.

Definition f_psci_reset_rec := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_target_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_reg, tulong) :: (_t'1, tulong) :: nil);
  fn_body := psci_reset_rec_body
|}.
