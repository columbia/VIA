Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _esr := 1%positive.
Definition _g := 2%positive.
Definition _i := 3%positive.
Definition _info := 4%positive.
Definition _rec := 5%positive.
Definition _rec__1 := 6%positive.
Definition _reg := 7%positive.
Definition _ret := 8%positive.
Definition _t'1 := 9%positive.
Definition _t'2 := 10%positive.

Definition complete_hvc_exit_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_rec_last_run_info_esr (Tfunction
                                           (Tcons (tptr Tvoid)
                                             Tnil) tulong cc_default))
        ((Etempvar _rec (tptr Tvoid)) :: nil))
      (Sset _esr (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sifthenelse (Ebinop Oeq
                     (Ebinop Oand (Etempvar _esr tulong)
                       (Econst_long (Int64.repr 4227858432) tulong) tulong)
                     (Econst_long (Int64.repr 1476395008) tulong) tint)
        (Ssequence
          (Swhile
            (Ebinop Olt (Etempvar _i tuint) (Econst_long (Int64.repr 7) tulong)
              tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _get_rec_run_gprs (Tfunction (Tcons tuint Tnil) tulong
                                            cc_default))
                  ((Etempvar _i tuint) :: nil))
                (Scall None
                  (Evar _set_rec_regs (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons tuint (Tcons tulong Tnil)))
                                        tvoid cc_default))
                  ((Etempvar _rec (tptr Tvoid)) ::
                   (Etempvar _i tuint) :: (Etempvar _t'2 tulong) :: nil)))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                  tuint))))
          (Scall None
            (Evar _reset_last_run_info (Tfunction
                                         (Tcons (tptr Tvoid)
                                           Tnil) tvoid cc_default))
            ((Etempvar _rec (tptr Tvoid)) :: nil)))
        Sskip)))
.

Definition f_complete_hvc_exit := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_esr, tulong) :: (_i, tuint) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := complete_hvc_exit_body
|}.
