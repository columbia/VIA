Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _exception := 1%positive.
Definition _realm_exception_code := 2%positive.
Definition _rec := 3%positive.
Definition _rec__1 := 4%positive.
Definition _ret := 5%positive.

Definition rec_run_loop_body :=
  (Ssequence
    (Scall None (Evar _save_ns_state (Tfunction Tnil tvoid cc_default)) nil)
    (Ssequence
      (Scall None
        (Evar _restore_realm_state (Tfunction
                                     (Tcons (tptr Tvoid) Tnil)
                                     tvoid cc_default))
        ((Etempvar _rec (tptr Tvoid)) :: nil))
      (Ssequence
        (Scall None
          (Evar _configure_realm_stage2 (Tfunction
                                          (Tcons (tptr Tvoid)
                                            Tnil) tvoid cc_default))
          ((Etempvar _rec (tptr Tvoid)) :: nil))
        (Ssequence
          (Scall None
            (Evar _restore_hcr_el2 (Tfunction
                                     (Tcons (tptr Tvoid) Tnil)
                                     tvoid cc_default))
            ((Etempvar _rec (tptr Tvoid)) :: nil))
          (Scall None
            (Evar _run_realm (Tfunction
                               (Tcons (tptr Tvoid) Tnil) tvoid
                               cc_default))
            ((Etempvar _rec (tptr Tvoid)) :: nil))))))
.

Definition f_rec_run_loop := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_realm_exception_code, tint) :: nil);
  fn_body := rec_run_loop_body
|}.
