Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_rd := 3%positive.
Definition _g_rec := 4%positive.
Definition _g_rec_list := 5%positive.
Definition _g_rtt := 6%positive.
Definition _granule := 7%positive.
Definition _i := 8%positive.
Definition _lock := 9%positive.
Definition _rd := 10%positive.
Definition _rd__1 := 11%positive.
Definition _rd_addr := 12%positive.
Definition _realm_params_addr := 13%positive.
Definition _rec := 14%positive.
Definition _rec_list := 15%positive.
Definition _rec_list_addr := 16%positive.
Definition _ret := 17%positive.
Definition _rt := 18%positive.
Definition _rtt_addr := 19%positive.
Definition _val := 20%positive.
Definition _valid := 21%positive.
Definition _t'1 := 22%positive.
Definition _t'2 := 23%positive.
Definition _t'3 := 24%positive.
Definition _t'4 := 25%positive.
Definition _t'5 := 26%positive.

Definition smc_realm_create_body :=
  (Ssequence
    (Scall (Some _t'5)
      (Evar _get_realm_params (Tfunction (Tcons tulong Tnil) tuint cc_default))
      ((Etempvar _realm_params_addr tulong) :: nil))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tuint)
                   (Econst_int (Int.repr 0) tuint) tint)
      (Ssequence
        (Scall (Some _t'4)
          (Evar _validate_realm_params (Tfunction Tnil tulong cc_default)) nil)
        (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tulong)
                       (Econst_long (Int64.repr 0) tulong) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _get_realm_params_rtt_addr (Tfunction Tnil tulong
                                                   cc_default)) nil)
              (Sset _rtt_addr (Etempvar _t'1 tulong)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _get_realm_params_rec_list_addr (Tfunction Tnil tulong
                                                          cc_default)) nil)
                (Sset _rec_list_addr (Etempvar _t'2 tulong)))
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _find_lock_three_delegated_granules (Tfunction
                                                              (Tcons tulong
                                                                (Tcons tulong
                                                                  (Tcons tulong
                                                                    Tnil)))
                                                              tuint cc_default))
                  ((Etempvar _rd_addr tulong) :: (Etempvar _rtt_addr tulong) ::
                   (Etempvar _rec_list_addr tulong) :: nil))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tuint)
                               (Econst_int (Int.repr 0) tuint) tint)
                  (Ssequence
                    (Scall None
                      (Evar _realm_create_ops (Tfunction Tnil tvoid cc_default))
                      nil)
                    (Sreturn (Some (Econst_long (Int64.repr 0) tulong))))
                  (Sreturn (Some (Econst_long (Int64.repr 1) tulong)))))))
          (Sreturn (Some (Econst_long (Int64.repr 1) tulong)))))
      (Sreturn (Some (Econst_long (Int64.repr 1) tulong)))))
.

Definition f_smc_realm_create := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_rd_addr, tulong) :: (_realm_params_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_rd, (tptr Tvoid)) ::
               (_rd, (tptr Tvoid)) ::
               (_g_rtt, (tptr Tvoid)) ::
               (_g_rec_list, (tptr Tvoid)) ::
               (_rtt_addr, tulong) :: (_rec_list_addr, tulong) ::
               (_t'5, tuint) :: (_t'4, tulong) :: (_t'3, tuint) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := smc_realm_create_body
|}.
