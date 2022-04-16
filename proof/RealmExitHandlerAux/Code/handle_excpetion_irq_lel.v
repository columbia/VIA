Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _i := 1%positive.
Definition _icc := 2%positive.
Definition _icc_hppir1_el1 := 3%positive.
Definition _intid := 4%positive.
Definition _reason := 5%positive.
Definition _rec := 6%positive.
Definition _rec__1 := 7%positive.
Definition _ret := 8%positive.
Definition _t'1 := 9%positive.
Definition _t'2 := 10%positive.

Definition handle_excpetion_irq_lel_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong cc_default))
        ((Econst_int (Int.repr 110) tuint) :: nil))
      (Sset _icc_hppir1_el1 (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _intid
        (Ebinop Oand (Etempvar _icc_hppir1_el1 tulong)
          (Econst_long (Int64.repr 16777215) tulong) tulong))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _intid tulong)
                       (Econst_long (Int64.repr 27) tulong) tint)
          (Sset _t'2 (Econst_int (Int.repr 1) tint))
          (Sset _t'2
            (Ecast
              (Ebinop Oeq (Etempvar _intid tulong)
                (Econst_long (Int64.repr 30) tulong) tint) tbool)))
        (Sifthenelse (Etempvar _t'2 tint)
          (Sreturn (Some (Econst_int (Int.repr 1) tuint)))
          (Ssequence
            (Scall None
              (Evar _set_rec_run_exit_reason (Tfunction (Tcons tulong Tnil)
                                               tvoid cc_default))
              ((Econst_long (Int64.repr 1) tulong) :: nil))
            (Sreturn (Some (Econst_int (Int.repr 0) tuint))))))))
.

Definition f_handle_excpetion_irq_lel := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_icc_hppir1_el1, tulong) :: (_intid, tulong) ::
               (_t'2, tint) :: (_t'1, tulong) :: nil);
  fn_body := handle_excpetion_irq_lel_body
|}.
