Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _arg1 := 1%positive.
Definition _arg2 := 2%positive.
Definition _arg3 := 3%positive.
Definition _function_id := 4%positive.
Definition _g := 5%positive.
Definition _i := 6%positive.
Definition _reason := 7%positive.
Definition _rec := 8%positive.
Definition _rec__1 := 9%positive.
Definition _reg := 10%positive.
Definition _ret := 11%positive.
Definition _x0 := 12%positive.
Definition _t'1 := 13%positive.
Definition _t'10 := 14%positive.
Definition _t'11 := 15%positive.
Definition _t'12 := 16%positive.
Definition _t'13 := 17%positive.
Definition _t'14 := 18%positive.
Definition _t'2 := 19%positive.
Definition _t'3 := 20%positive.
Definition _t'4 := 21%positive.
Definition _t'5 := 22%positive.
Definition _t'6 := 23%positive.
Definition _t'7 := 24%positive.
Definition _t'8 := 25%positive.
Definition _t'9 := 26%positive.

Definition handle_realm_rsi_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_rec_regs (Tfunction
                              (Tcons (tptr Tvoid)
                                (Tcons tuint Tnil)) tulong cc_default))
        ((Etempvar _rec (tptr Tvoid)) ::
         (Econst_int (Int.repr 0) tuint) :: nil))
      (Sset _function_id (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_rec_regs (Tfunction
                                (Tcons (tptr Tvoid)
                                  (Tcons tuint Tnil)) tulong cc_default))
          ((Etempvar _rec (tptr Tvoid)) ::
           (Econst_int (Int.repr 1) tuint) :: nil))
        (Sset _arg1 (Etempvar _t'2 tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _get_rec_regs (Tfunction
                                  (Tcons (tptr Tvoid)
                                    (Tcons tuint Tnil)) tulong cc_default))
            ((Etempvar _rec (tptr Tvoid)) ::
             (Econst_int (Int.repr 2) tuint) :: nil))
          (Sset _arg2 (Etempvar _t'3 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _get_rec_regs (Tfunction
                                    (Tcons (tptr Tvoid)
                                      (Tcons tuint Tnil)) tulong cc_default))
              ((Etempvar _rec (tptr Tvoid)) ::
               (Econst_int (Int.repr 3) tuint) :: nil))
            (Sset _arg3 (Etempvar _t'4 tulong)))
          (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                         (Econst_long (Int64.repr 3355443200) tulong) tint)
            (Ssequence
              (Scall None
                (Evar _set_rec_regs (Tfunction
                                      (Tcons (tptr Tvoid)
                                        (Tcons tuint (Tcons tulong Tnil)))
                                      tvoid cc_default))
                ((Etempvar _rec (tptr Tvoid)) ::
                 (Econst_int (Int.repr 1) tuint) ::
                 (Econst_long (Int64.repr 196608) tulong) :: nil))
              (Ssequence
                (Scall None
                  (Evar _set_rec_regs (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons tuint (Tcons tulong Tnil)))
                                        tvoid cc_default))
                  ((Etempvar _rec (tptr Tvoid)) ::
                   (Econst_int (Int.repr 0) tuint) ::
                   (Econst_int (Int.repr 0) tuint) :: nil))
                (Sreturn (Some (Econst_int (Int.repr 1) tuint)))))
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop Oge (Etempvar _function_id tulong)
                               (Econst_long (Int64.repr 2214592512) tulong)
                               tint)
                  (Sset _t'13
                    (Ecast
                      (Ebinop Ole (Etempvar _function_id tulong)
                        (Econst_long (Int64.repr 2214592543) tulong) tint)
                      tbool))
                  (Sset _t'13 (Econst_int (Int.repr 0) tint)))
                (Sifthenelse (Etempvar _t'13 tint)
                  (Sset _t'14 (Econst_int (Int.repr 1) tint))
                  (Sifthenelse (Ebinop Oge (Etempvar _function_id tulong)
                                 (Econst_long (Int64.repr 3288334336) tulong)
                                 tint)
                    (Ssequence
                      (Sset _t'14
                        (Ecast
                          (Ebinop Ole (Etempvar _function_id tulong)
                            (Econst_long (Int64.repr 3288334367) tulong) tint)
                          tbool))
                      (Sset _t'14 (Ecast (Etempvar _t'14 tint) tbool)))
                    (Sset _t'14 (Ecast (Econst_int (Int.repr 0) tint) tbool)))))
              (Sifthenelse (Etempvar _t'14 tint)
                (Ssequence
                  (Scall None
                    (Evar _psci_rsi (Tfunction
                                      (Tcons (tptr Tvoid)
                                        (Tcons tuint
                                          (Tcons tulong
                                            (Tcons tulong (Tcons tulong Tnil)))))
                                      tvoid cc_default))
                    ((Etempvar _rec (tptr Tvoid)) ::
                     (Etempvar _function_id tulong) ::
                     (Etempvar _arg1 tulong) :: (Etempvar _arg2 tulong) ::
                     (Etempvar _arg3 tulong) :: nil))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'5)
                        (Evar _get_psci_result_x0 (Tfunction Tnil tulong
                                                    cc_default)) nil)
                      (Scall None
                        (Evar _set_rec_regs (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                (Tcons tuint
                                                  (Tcons tulong Tnil))) tvoid
                                              cc_default))
                        ((Etempvar _rec (tptr Tvoid)) ::
                         (Econst_int (Int.repr 0) tuint) ::
                         (Etempvar _t'5 tulong) :: nil)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'6)
                          (Evar _get_psci_result_x1 (Tfunction Tnil tulong
                                                      cc_default)) nil)
                        (Scall None
                          (Evar _set_rec_regs (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  (Tcons tuint
                                                    (Tcons tulong Tnil))) tvoid
                                                cc_default))
                          ((Etempvar _rec (tptr Tvoid)) ::
                           (Econst_int (Int.repr 1) tuint) ::
                           (Etempvar _t'6 tulong) :: nil)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'7)
                            (Evar _get_psci_result_x2 (Tfunction Tnil tulong
                                                        cc_default)) nil)
                          (Scall None
                            (Evar _set_rec_regs (Tfunction
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    (Tcons tuint
                                                      (Tcons tulong Tnil)))
                                                  tvoid cc_default))
                            ((Etempvar _rec (tptr Tvoid)) ::
                             (Econst_int (Int.repr 2) tuint) ::
                             (Etempvar _t'7 tulong) :: nil)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'8)
                              (Evar _get_psci_result_x3 (Tfunction Tnil tulong
                                                          cc_default)) nil)
                            (Scall None
                              (Evar _set_rec_regs (Tfunction
                                                    (Tcons
                                                      (tptr Tvoid)
                                                      (Tcons tuint
                                                        (Tcons tulong Tnil)))
                                                    tvoid cc_default))
                              ((Etempvar _rec (tptr Tvoid)) ::
                               (Econst_int (Int.repr 3) tuint) ::
                               (Etempvar _t'8 tulong) :: nil)))
                          (Ssequence
                            (Scall (Some _t'12)
                              (Evar _get_psci_result_forward_psci_call 
                              (Tfunction Tnil tuint cc_default)) nil)
                            (Sifthenelse (Ebinop Oeq (Etempvar _t'12 tuint)
                                           (Econst_int (Int.repr 1) tuint)
                                           tint)
                              (Ssequence
                                (Scall None
                                  (Evar _set_rec_run_exit_reason (Tfunction
                                                                   (Tcons
                                                                     tulong
                                                                     Tnil)
                                                                   tvoid
                                                                   cc_default))
                                  ((Econst_long (Int64.repr 3) tulong) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _set_rec_run_gprs (Tfunction
                                                              (Tcons tuint
                                                                (Tcons tulong
                                                                  Tnil)) tvoid
                                                              cc_default))
                                    ((Econst_int (Int.repr 0) tuint) ::
                                     (Etempvar _function_id tulong) :: nil))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'9)
                                        (Evar _get_psci_result_forward_x1 
                                        (Tfunction Tnil tulong cc_default))
                                        nil)
                                      (Scall None
                                        (Evar _set_rec_run_gprs (Tfunction
                                                                  (Tcons tuint
                                                                    (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                  tvoid
                                                                  cc_default))
                                        ((Econst_int (Int.repr 1) tuint) ::
                                         (Etempvar _t'9 tulong) :: nil)))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'10)
                                          (Evar _get_psci_result_forward_x2 
                                          (Tfunction Tnil tulong cc_default))
                                          nil)
                                        (Scall None
                                          (Evar _set_rec_run_gprs (Tfunction
                                                                    (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                    tvoid
                                                                    cc_default))
                                          ((Econst_int (Int.repr 2) tuint) ::
                                           (Etempvar _t'10 tulong) :: nil)))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'11)
                                            (Evar _get_psci_result_forward_x3 
                                            (Tfunction Tnil tulong cc_default))
                                            nil)
                                          (Scall None
                                            (Evar _set_rec_run_gprs (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      (Tcons
                                                                      tulong
                                                                      Tnil))
                                                                      tvoid
                                                                      cc_default))
                                            ((Econst_int (Int.repr 3) tuint) ::
                                             (Etempvar _t'11 tulong) :: nil)))
                                        (Ssequence
                                          (Sset _i
                                            (Econst_int (Int.repr 4) tint))
                                          (Ssequence
                                            (Swhile
                                              (Ebinop Olt (Etempvar _i tuint)
                                                (Econst_long (Int64.repr 7) tulong)
                                                tint)
                                              (Ssequence
                                                (Scall None
                                                  (Evar _set_rec_run_gprs 
                                                  (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tulong Tnil))
                                                    tvoid cc_default))
                                                  ((Etempvar _i tuint) ::
                                                   (Econst_long (Int64.repr 0) tulong) ::
                                                   nil))
                                                (Sset _i
                                                  (Ebinop Oadd
                                                    (Etempvar _i tuint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tuint))))
                                            (Sreturn (Some (Econst_int (Int.repr 0) tuint))))))))))
                              (Sreturn (Some (Econst_int (Int.repr 1) tuint))))))))))
                (Ssequence
                  (Scall None
                    (Evar _set_rec_regs (Tfunction
                                          (Tcons (tptr Tvoid)
                                            (Tcons tuint (Tcons tulong Tnil)))
                                          tvoid cc_default))
                    ((Etempvar _rec (tptr Tvoid)) ::
                     (Econst_int (Int.repr 0) tuint) ::
                     (Econst_long (Int64.repr 4294967295) tulong) :: nil))
                  (Sreturn (Some (Econst_int (Int.repr 1) tuint)))))))))))
.

Definition f_handle_realm_rsi := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_function_id, tulong) :: (_arg1, tulong) ::
               (_arg2, tulong) :: (_arg3, tulong) :: (_i, tuint) ::
               (_t'14, tint) :: (_t'13, tint) :: (_t'12, tuint) ::
               (_t'11, tulong) :: (_t'10, tulong) :: (_t'9, tulong) ::
               (_t'8, tulong) :: (_t'7, tulong) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := handle_realm_rsi_body
|}.
