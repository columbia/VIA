Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _ret := 2%positive.
Definition _t'1 := 3%positive.

Definition smc_mark_realm_body :=
  (Ssequence
    (Scall None
      (Evar _set_monitor_call (Tfunction (Tcons tuint (Tcons tulong Tnil))
                                tvoid cc_default))
      ((Ebinop Oadd (Econst_int (Int.repr (3288334336)) tuint)
         (Econst_long (Int64.repr 256) tulong) tulong) ::
       (Etempvar _addr tulong) :: nil))
    (Ssequence
      (Scall None (Evar _el3_sync_lel (Tfunction Tnil tvoid cc_default)) nil)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _get_monitor_call_ret (Tfunction Tnil tulong cc_default))
            nil)
          (Sset _ret (Ecast (Etempvar _t'1 tulong) tuint)))
        (Scall None
          (Evar _assert_cond (Tfunction (Tcons tuint Tnil) tvoid cc_default))
          ((Ebinop Osub (Econst_int (Int.repr 1) tuint) (Etempvar _ret tuint)
             tuint) :: nil)))))
.

Definition f_smc_mark_realm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tuint) :: (_t'1, tulong) :: nil);
  fn_body := smc_mark_realm_body
|}.
