Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _cntx_ctl := 1%positive.
Definition _emulated_timer_state := 2%positive.
Definition _g := 3%positive.
Definition _i := 4%positive.
Definition _ret := 5%positive.
Definition _timer := 6%positive.
Definition _t'1 := 7%positive.
Definition _t'2 := 8%positive.
Definition _t'3 := 9%positive.
Definition _t'4 := 10%positive.
Definition _t'5 := 11%positive.

Definition check_timer_became_asserted_body :=
  (Ssequence
    (Scall (Some _t'5)
      (Evar _get_timer_asserted (Tfunction
                                  (Tcons
                                    (tptr Tvoid)
                                    Tnil) tuint cc_default))
      ((Etempvar _timer (tptr Tvoid)) :: nil))
    (Sifthenelse (Ebinop One (Etempvar _t'5 tuint)
                   (Econst_int (Int.repr 0) tuint) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _timer_is_masked (Tfunction (Tcons tulong Tnil) tuint
                                     cc_default))
            ((Etempvar _cntx_ctl tulong) :: nil))
          (Scall None
            (Evar _set_timer_masked (Tfunction
                                      (Tcons
                                        (tptr Tvoid)
                                        (Tcons tuint Tnil)) tvoid cc_default))
            ((Etempvar _timer (tptr Tvoid)) ::
             (Etempvar _t'1 tuint) :: nil)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _get_timer_masked (Tfunction
                                        (Tcons
                                          (tptr Tvoid)
                                          Tnil) tuint cc_default))
              ((Etempvar _timer (tptr Tvoid)) ::
               nil))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tuint)
                           (Econst_int (Int.repr 0) tuint) tint)
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _timer_condition_met (Tfunction (Tcons tulong Tnil)
                                               tuint cc_default))
                  ((Etempvar _cntx_ctl tulong) :: nil))
                (Sset _t'3
                  (Ecast
                    (Ebinop Oeq (Etempvar _t'4 tuint)
                      (Econst_int (Int.repr 1) tuint) tint) tbool)))
              (Sset _t'3 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'3 tint)
            (Sreturn (Some (Econst_int (Int.repr 1) tuint)))
            (Sreturn (Some (Econst_int (Int.repr 0) tuint))))))))
.

Definition f_check_timer_became_asserted := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_timer, (tptr Tvoid)) ::
                (_cntx_ctl, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tuint) :: (_t'4, tuint) :: (_t'3, tint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body := check_timer_became_asserted_body
|}.
