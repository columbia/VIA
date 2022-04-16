Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _i := 1%positive.
Definition _mpidr := 2%positive.
Definition _rec := 3%positive.
Definition _rec__1 := 4%positive.
Definition _ret := 5%positive.

Definition init_rec_sysregs_body :=
  (Ssequence
    (Scall None
      (Evar _set_rec_sysregs (Tfunction
                               (Tcons (tptr Tvoid)
                                 (Tcons tuint (Tcons tulong Tnil))) tvoid
                               cc_default))
      ((Etempvar _rec (tptr Tvoid)) ::
       (Econst_int (Int.repr 39) tuint) ::
       (Econst_long (Int64.repr 64) tulong) :: nil))
    (Ssequence
      (Scall None
        (Evar _set_rec_sysregs (Tfunction
                                 (Tcons (tptr Tvoid)
                                   (Tcons tuint (Tcons tulong Tnil))) tvoid
                                 cc_default))
        ((Etempvar _rec (tptr Tvoid)) ::
         (Econst_int (Int.repr 47) tuint) ::
         (Econst_long (Int64.repr 12912760) tulong) :: nil))
      (Ssequence
        (Scall None
          (Evar _set_rec_sysregs (Tfunction
                                   (Tcons (tptr Tvoid)
                                     (Tcons tuint (Tcons tulong Tnil))) tvoid
                                   cc_default))
          ((Etempvar _rec (tptr Tvoid)) ::
           (Econst_int (Int.repr 65) tuint) ::
           (Econst_long (Int64.repr 4096) tulong) :: nil))
        (Ssequence
          (Scall None
            (Evar _set_rec_sysregs (Tfunction
                                     (Tcons (tptr Tvoid)
                                       (Tcons tuint (Tcons tulong Tnil))) tvoid
                                     cc_default))
            ((Etempvar _rec (tptr Tvoid)) ::
             (Econst_int (Int.repr 72) tuint) :: (Etempvar _mpidr tulong) ::
             nil))
          (Scall None
            (Evar _set_rec_sysregs (Tfunction
                                     (Tcons (tptr Tvoid)
                                       (Tcons tuint (Tcons tulong Tnil))) tvoid
                                     cc_default))
            ((Etempvar _rec (tptr Tvoid)) ::
             (Econst_int (Int.repr 69) tuint) ::
             (Econst_long (Int64.repr 3072) tulong) :: nil))))))
.

Definition f_init_rec_sysregs := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_mpidr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := init_rec_sysregs_body
|}.
