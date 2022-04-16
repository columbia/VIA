Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _esr := 1%positive.
Definition _i := 2%positive.
Definition _icc := 3%positive.
Definition _rec := 4%positive.
Definition _rec__1 := 5%positive.
Definition _ret := 6%positive.
Definition _timer := 7%positive.

Definition handle_sysreg_access_trap_body :=
  (Ssequence
    (Scall None
      (Evar _assert_cond (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Ebinop Oand (Etempvar _esr tulong)
         (Econst_long (Int64.repr 4227858432) tulong) tulong) :: nil))
    (Sifthenelse (Ebinop Oeq
                   (Ebinop Oand (Etempvar _esr tulong)
                     (Econst_long (Int64.repr 3275776) tulong) tulong)
                   (Econst_long (Int64.repr 3145728) tulong) tint)
      (Scall None
        (Evar _handle_id_sysreg_trap (Tfunction
                                       (Tcons (tptr Tvoid)
                                         (Tcons tulong Tnil)) tvoid cc_default))
        ((Etempvar _rec (tptr Tvoid)) ::
         (Etempvar _esr tulong) :: nil))
      (Sifthenelse (Ebinop Oeq
                     (Ebinop Oand (Etempvar _esr tulong)
                       (Econst_long (Int64.repr 3210264) tulong) tulong)
                     (Econst_long (Int64.repr 3209216) tulong) tint)
        (Scall None
          (Evar _handle_timer_sysreg_trap (Tfunction
                                            (Tcons (tptr Tvoid)
                                              (Tcons tulong Tnil)) tvoid
                                            cc_default))
          ((Etempvar _rec (tptr Tvoid)) ::
           (Etempvar _esr tulong) :: nil))
        (Sifthenelse (Ebinop Oeq
                       (Ebinop Oand (Etempvar _esr tulong)
                         (Econst_long (Int64.repr 3210256) tulong) tulong)
                       (Econst_long (Int64.repr 3158032) tulong) tint)
          (Scall None
            (Evar _handle_icc_el1_sysreg_trap (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  (Tcons tulong Tnil)) tvoid
                                                cc_default))
            ((Etempvar _rec (tptr Tvoid)) ::
             (Etempvar _esr tulong) :: nil))
          Sskip))))
.

Definition f_handle_sysreg_access_trap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: (_esr, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := handle_sysreg_access_trap_body
|}.
