Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _granule := 3%positive.
Definition _i := 4%positive.
Definition _ret := 5%positive.
Definition _state := 6%positive.

Definition granule_delegate_ops_body :=
  (Ssequence
    (Scall None
      (Evar _smc_mark_realm (Tfunction (Tcons tulong Tnil) tvoid cc_default))
      ((Etempvar _addr tulong) :: nil))
    (Ssequence
      (Scall None
        (Evar _granule_set_state (Tfunction
                                   (Tcons (tptr Tvoid)
                                     (Tcons tuint Tnil)) tvoid cc_default))
        ((Etempvar _g (tptr Tvoid)) ::
         (Econst_int (Int.repr 1) tuint) :: nil))
      (Ssequence
        (Scall None
          (Evar _granule_memzero (Tfunction
                                   (Tcons (tptr Tvoid)
                                     (Tcons tuint Tnil)) tvoid cc_default))
          ((Etempvar _g (tptr Tvoid)) ::
           (Econst_int (Int.repr 1) tuint) :: nil))
        (Scall None
          (Evar _granule_unlock (Tfunction
                                  (Tcons (tptr Tvoid) Tnil)
                                  tvoid cc_default))
          ((Etempvar _g (tptr Tvoid)) :: nil)))))
.

Definition f_granule_delegate_ops := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_g, (tptr Tvoid)) :: (_addr, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := granule_delegate_ops_body
|}.
