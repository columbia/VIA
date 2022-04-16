Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _addr__1 := 2%positive.
Definition _reason := 3%positive.
Definition _ret := 4%positive.
Definition _ret__1 := 5%positive.
Definition _t'1 := 6%positive.
Definition _t'2 := 7%positive.
Definition _t'3 := 8%positive.
Definition _t'4 := 9%positive.
Definition _t'5 := 10%positive.

Definition el3_sync_lel_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _baremore_enter (Tfunction Tnil tuint cc_default)) nil)
      (Sset _reason (Etempvar _t'1 tuint)))
    (Sifthenelse (Ebinop Oeq (Etempvar _reason tuint)
                   (Econst_long (Int64.repr 256) tulong) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _get_monitor_call_arg (Tfunction Tnil tulong cc_default))
            nil)
          (Sset _addr (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _asc_mark_realm (Tfunction (Tcons tulong Tnil) tulong
                                      cc_default))
              ((Etempvar _addr tulong) :: nil))
            (Sset _ret (Etempvar _t'3 tulong)))
          (Scall None
            (Evar _baremore_return_rmm (Tfunction (Tcons tulong Tnil) tvoid
                                         cc_default))
            ((Etempvar _ret tulong) :: nil))))
      (Sifthenelse (Ebinop Oeq (Etempvar _reason tuint)
                     (Econst_long (Int64.repr 257) tulong) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _get_monitor_call_arg (Tfunction Tnil tulong cc_default))
              nil)
            (Sset _addr (Etempvar _t'4 tulong)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _asc_mark_nonsecure (Tfunction (Tcons tulong Tnil) tulong
                                            cc_default))
                ((Etempvar _addr tulong) :: nil))
              (Sset _ret (Ecast (Etempvar _t'5 tulong) tuint)))
            (Scall None
              (Evar _baremore_return_rmm (Tfunction (Tcons tulong Tnil) tvoid
                                           cc_default))
              ((Etempvar _ret tuint) :: nil))))
        (Sifthenelse (Ebinop Oeq (Etempvar _reason tuint)
                       (Econst_int (Int.repr 3) tuint) tint)
          (Scall None (Evar _baremore_to_ns (Tfunction Tnil tvoid cc_default))
            nil)
          (Sifthenelse (Ebinop Oeq (Etempvar _reason tuint)
                         (Econst_int (Int.repr 4) tuint) tint)
            (Scall None
              (Evar _baremore_to_rmm (Tfunction Tnil tvoid cc_default)) nil)
            (Scall None
              (Evar _assert_cond (Tfunction (Tcons tuint Tnil) tvoid
                                   cc_default))
              ((Econst_int (Int.repr 0) tint) :: nil)))))))
.

Definition f_el3_sync_lel := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_reason, tuint) :: (_addr, tulong) :: (_ret, tulong) ::
               (_addr, tulong) :: (_ret, tuint) :: (_t'5, tulong) ::
               (_t'4, tulong) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tuint) :: nil);
  fn_body := el3_sync_lel_body
|}.
