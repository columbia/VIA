Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _ec := 1%positive.
Definition _esr := 2%positive.
Definition _exception := 3%positive.
Definition _g := 4%positive.
Definition _i := 5%positive.
Definition _info := 6%positive.
Definition _pc := 7%positive.
Definition _pc__1 := 8%positive.
Definition _rec := 9%positive.
Definition _rec__1 := 10%positive.
Definition _reg := 11%positive.
Definition _ret := 12%positive.
Definition _t'1 := 13%positive.
Definition _t'2 := 14%positive.
Definition _t'3 := 15%positive.
Definition _t'4 := 16%positive.
Definition _t'5 := 17%positive.
Definition _t'6 := 18%positive.

Definition handle_exception_sync_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong cc_default))
        ((Econst_int (Int.repr 82) tuint) :: nil))
      (Sset _esr (Etempvar _t'1 tulong)))
    (Ssequence
      (Sset _ec
        (Ebinop Oand (Etempvar _esr tulong)
          (Econst_long (Int64.repr 4227858432) tulong) tulong))
      (Sifthenelse (Ebinop Oeq (Etempvar _ec tulong)
                     (Econst_long (Int64.repr 67108864) tulong) tint)
        (Ssequence
          (Scall None
            (Evar _set_rec_run_esr (Tfunction (Tcons tulong Tnil) tvoid
                                     cc_default))
            ((Ebinop Oand (Etempvar _esr tulong)
               (Ebinop Oor (Econst_long (Int64.repr 4227858432) tulong)
                 (Econst_long (Int64.repr 1) tulong) tulong) tulong) :: nil))
          (Sreturn (Some (Econst_int (Int.repr 0) tuint))))
        (Sifthenelse (Ebinop Oeq (Etempvar _ec tulong)
                       (Econst_long (Int64.repr 1476395008) tulong) tint)
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tuint))
            (Ssequence
              (Sset _info
                (Ebinop Oand (Etempvar _esr tulong)
                  (Ebinop Oor (Econst_long (Int64.repr 4227858432) tulong)
                    (Econst_long (Int64.repr 65535) tulong) tulong) tulong))
              (Ssequence
                (Scall None
                  (Evar _set_rec_last_run_info_esr (Tfunction
                                                     (Tcons
                                                       (tptr Tvoid)
                                                       (Tcons tulong Tnil))
                                                     tvoid cc_default))
                  ((Etempvar _rec (tptr Tvoid)) ::
                   (Etempvar _info tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _set_rec_run_esr (Tfunction (Tcons tulong Tnil) tvoid
                                             cc_default))
                    ((Etempvar _info tulong) :: nil))
                  (Ssequence
                    (Swhile
                      (Ebinop Olt (Etempvar _i tuint)
                        (Econst_long (Int64.repr 7) tulong) tint)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'2)
                            (Evar _get_rec_regs (Tfunction
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    (Tcons tuint Tnil)) tulong
                                                  cc_default))
                            ((Etempvar _rec (tptr Tvoid)) ::
                             (Etempvar _i tuint) :: nil))
                          (Scall None
                            (Evar _set_rec_run_gprs (Tfunction
                                                      (Tcons tuint
                                                        (Tcons tulong Tnil))
                                                      tvoid cc_default))
                            ((Etempvar _i tuint) :: (Etempvar _t'2 tulong) ::
                             nil)))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tuint)
                            (Econst_int (Int.repr 1) tint) tuint))))
                    (Sreturn (Some (Econst_int (Int.repr 0) tuint))))))))
          (Sifthenelse (Ebinop Oeq (Etempvar _ec tulong)
                         (Econst_long (Int64.repr 1543503872) tulong) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                       cc_default))
                  ((Econst_int (Int.repr 81) tuint) :: nil))
                (Sset _pc (Etempvar _t'3 tulong)))
              (Ssequence
                (Scall None
                  (Evar _sysreg_write (Tfunction
                                        (Tcons tuint (Tcons tulong Tnil)) tvoid
                                        cc_default))
                  ((Econst_int (Int.repr 81) tuint) ::
                   (Ebinop Oadd (Etempvar _pc tulong)
                     (Econst_long (Int64.repr 4) tulong) tulong) :: nil))
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _handle_realm_rsi (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                Tnil) tuint cc_default))
                    ((Etempvar _rec (tptr Tvoid)) :: nil))
                  (Sreturn (Some (Etempvar _t'4 tuint))))))
            (Sifthenelse (Ebinop Oeq (Etempvar _ec tulong)
                           (Econst_long (Int64.repr 1610612736) tulong) tint)
              (Ssequence
                (Scall None
                  (Evar _handle_sysreg_access_trap (Tfunction
                                                     (Tcons
                                                       (tptr Tvoid)
                                                       (Tcons tulong Tnil))
                                                     tvoid cc_default))
                  ((Etempvar _rec (tptr Tvoid)) ::
                   (Etempvar _esr tulong) :: nil))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                           cc_default))
                      ((Econst_int (Int.repr 81) tuint) :: nil))
                    (Sset _pc (Etempvar _t'5 tulong)))
                  (Ssequence
                    (Scall None
                      (Evar _sysreg_write (Tfunction
                                            (Tcons tuint (Tcons tulong Tnil))
                                            tvoid cc_default))
                      ((Econst_int (Int.repr 81) tuint) ::
                       (Ebinop Oadd (Etempvar _pc tulong)
                         (Econst_long (Int64.repr 4) tulong) tulong) :: nil))
                    (Sreturn (Some (Econst_int (Int.repr 1) tuint))))))
              (Sifthenelse (Ebinop Oeq (Etempvar _ec tulong)
                             (Econst_long (Int64.repr 2147483648) tulong) tint)
                (Ssequence
                  (Scall (Some _t'6)
                    (Evar _handle_instruction_abort (Tfunction
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        (Tcons tulong Tnil))
                                                      tuint cc_default))
                    ((Etempvar _rec (tptr Tvoid)) ::
                     (Etempvar _esr tulong) :: nil))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tuint)
                                 (Econst_int (Int.repr 1) tuint) tint)
                    (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
                    (Ssequence
                      (Scall None
                        (Evar _set_rec_run_esr (Tfunction (Tcons tulong Tnil)
                                                 tvoid cc_default))
                        ((Econst_long (Int64.repr 0) tulong) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _set_rec_run_far (Tfunction (Tcons tulong Tnil)
                                                   tvoid cc_default))
                          ((Econst_long (Int64.repr 0) tulong) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _set_rec_run_hpfar (Tfunction
                                                       (Tcons tulong Tnil)
                                                       tvoid cc_default))
                            ((Econst_long (Int64.repr 0) tulong) :: nil))
                          (Sreturn (Some (Econst_int (Int.repr 0) tuint))))))))
                (Sifthenelse (Ebinop Oeq (Etempvar _ec tulong)
                               (Econst_long (Int64.repr 2415919104) tulong)
                               tint)
                  (Ssequence
                    (Scall None
                      (Evar _handle_data_abort (Tfunction
                                                 (Tcons
                                                   (tptr Tvoid)
                                                   (Tcons tulong Tnil)) tvoid
                                                 cc_default))
                      ((Etempvar _rec (tptr Tvoid)) ::
                       (Etempvar _esr tulong) :: nil))
                    (Sreturn (Some (Econst_int (Int.repr 0) tuint))))
                  (Ssequence
                    (Scall None
                      (Evar _set_rec_run_esr (Tfunction (Tcons tulong Tnil)
                                               tvoid cc_default))
                      ((Econst_long (Int64.repr 0) tulong) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _set_rec_run_far (Tfunction (Tcons tulong Tnil)
                                                 tvoid cc_default))
                        ((Econst_long (Int64.repr 0) tulong) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _set_rec_run_hpfar (Tfunction
                                                     (Tcons tulong Tnil) tvoid
                                                     cc_default))
                          ((Econst_long (Int64.repr 0) tulong) :: nil))
                        (Sreturn (Some (Econst_int (Int.repr 0) tuint))))))))))))))
.

Definition f_handle_exception_sync := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_esr, tulong) :: (_ec, tulong) :: (_i, tuint) ::
               (_info, tulong) :: (_pc, tulong) :: (_pc, tulong) ::
               (_t'6, tuint) :: (_t'5, tulong) :: (_t'4, tuint) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := handle_exception_sync_body
|}.
