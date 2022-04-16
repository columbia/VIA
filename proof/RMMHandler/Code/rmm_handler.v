Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _arg0 := 1%positive.
Definition _arg1 := 2%positive.
Definition _arg2 := 3%positive.
Definition _arg3 := 4%positive.
Definition _function_id := 5%positive.
Definition _i := 6%positive.
Definition _reg := 7%positive.
Definition _ret := 8%positive.
Definition _t'1 := 9%positive.
Definition _t'2 := 10%positive.
Definition _t'3 := 11%positive.
Definition _t'4 := 12%positive.
Definition _t'5 := 13%positive.
Definition _t'6 := 14%positive.

Definition rmm_handler_body :=
  (Ssequence
    (Scall None (Evar _el3_sync_lel (Tfunction Tnil tvoid cc_default)) nil)
    (Ssequence
      (Scall None (Evar _enter_rmm (Tfunction Tnil tvoid cc_default)) nil)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _read_reg (Tfunction (Tcons tuint Tnil) tulong cc_default))
            ((Econst_int (Int.repr 0) tuint) :: nil))
          (Sset _function_id (Etempvar _t'1 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _read_reg (Tfunction (Tcons tuint Tnil) tulong cc_default))
              ((Econst_int (Int.repr 1) tuint) :: nil))
            (Sset _arg0 (Etempvar _t'2 tulong)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _read_reg (Tfunction (Tcons tuint Tnil) tulong
                                  cc_default))
                ((Econst_int (Int.repr 2) tuint) :: nil))
              (Sset _arg1 (Etempvar _t'3 tulong)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _read_reg (Tfunction (Tcons tuint Tnil) tulong
                                    cc_default))
                  ((Econst_int (Int.repr 3) tuint) :: nil))
                (Sset _arg2 (Etempvar _t'4 tulong)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _read_reg (Tfunction (Tcons tuint Tnil) tulong
                                      cc_default))
                    ((Econst_int (Int.repr 4) tuint) :: nil))
                  (Sset _arg3 (Etempvar _t'5 tulong)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'6)
                      (Evar _handle_ns_smc (Tfunction
                                             (Tcons tulong
                                               (Tcons tulong
                                                 (Tcons tulong
                                                   (Tcons tulong
                                                     (Tcons tulong Tnil)))))
                                             tulong cc_default))
                      ((Etempvar _function_id tulong) ::
                       (Etempvar _arg0 tulong) :: (Etempvar _arg1 tulong) ::
                       (Etempvar _arg2 tulong) :: (Etempvar _arg3 tulong) ::
                       nil))
                    (Sset _ret (Etempvar _t'6 tulong)))
                  (Sifthenelse (Ebinop One (Etempvar _ret tulong)
                                 (Econst_long (Int64.repr 2) tulong) tint)
                    (Ssequence
                      (Scall None
                        (Evar _exit_rmm (Tfunction (Tcons tulong Tnil) tvoid
                                          cc_default))
                        ((Etempvar _ret tulong) :: nil))
                      (Scall None
                        (Evar _el3_sync_lel (Tfunction Tnil tvoid cc_default))
                        nil))
                    Sskip)))))))))
.

Definition f_rmm_handler := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_function_id, tulong) :: (_arg0, tulong) ::
               (_arg1, tulong) :: (_arg2, tulong) :: (_arg3, tulong) ::
               (_ret, tulong) :: (_t'6, tulong) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := rmm_handler_body
|}.
