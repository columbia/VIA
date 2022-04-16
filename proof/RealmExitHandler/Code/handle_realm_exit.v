Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _exception := 1%positive.
Definition _i := 2%positive.
Definition _reason := 3%positive.
Definition _rec := 4%positive.
Definition _rec__1 := 5%positive.
Definition _ret := 6%positive.
Definition _t'1 := 7%positive.
Definition _t'2 := 8%positive.

Definition handle_realm_exit_body :=
  (Sifthenelse (Ebinop Oeq (Etempvar _exception tuint)
                 (Econst_long (Int64.repr 0) tulong) tint)
    (Ssequence
      (Scall None
        (Evar _set_rec_run_exit_reason (Tfunction (Tcons tulong Tnil) tvoid
                                         cc_default))
        ((Econst_long (Int64.repr 0) tulong) :: nil))
      (Ssequence
        (Scall (Some _t'1)
          (Evar _handle_exception_sync (Tfunction
                                         (Tcons (tptr Tvoid)
                                           Tnil) tuint cc_default))
          ((Etempvar _rec (tptr Tvoid)) :: nil))
        (Sreturn (Some (Etempvar _t'1 tuint)))))
    (Sifthenelse (Ebinop Oeq (Etempvar _exception tuint)
                   (Econst_long (Int64.repr 1) tulong) tint)
      (Ssequence
        (Scall (Some _t'2)
          (Evar _handle_excpetion_irq_lel (Tfunction
                                            (Tcons (tptr Tvoid)
                                              Tnil) tuint cc_default))
          ((Etempvar _rec (tptr Tvoid)) :: nil))
        (Sreturn (Some (Etempvar _t'2 tuint))))
      (Sifthenelse (Ebinop Oeq (Etempvar _exception tuint)
                     (Econst_long (Int64.repr 2) tulong) tint)
        (Ssequence
          (Scall None
            (Evar _set_rec_run_exit_reason (Tfunction (Tcons tulong Tnil) tvoid
                                             cc_default))
            ((Econst_long (Int64.repr 2) tulong) :: nil))
          (Sreturn (Some (Econst_int (Int.repr 0) tuint))))
        (Sreturn (Some (Econst_int (Int.repr 0) tuint))))))
.

Definition f_handle_realm_exit := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_exception, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := handle_realm_exit_body
|}.
