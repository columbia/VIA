Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _data := 2%positive.
Definition _data_addr := 3%positive.
Definition _g := 4%positive.
Definition _g_rd := 5%positive.
Definition _granule := 6%positive.
Definition _i := 7%positive.
Definition _index := 8%positive.
Definition _ipa_state := 9%positive.
Definition _last_level := 10%positive.
Definition _level := 11%positive.
Definition _ll_table := 12%positive.
Definition _lock := 13%positive.
Definition _map_addr := 14%positive.
Definition _pa := 15%positive.
Definition _pte := 16%positive.
Definition _pte_val := 17%positive.
Definition _rd := 18%positive.
Definition _rd__1 := 19%positive.
Definition _rd_addr := 20%positive.
Definition _ret := 21%positive.
Definition _state := 22%positive.
Definition _table := 23%positive.
Definition _val := 24%positive.
Definition _t'1 := 25%positive.
Definition _t'2 := 26%positive.
Definition _t'3 := 27%positive.

Definition smc_data_destroy_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _find_lock_granule (Tfunction (Tcons tulong (Tcons tulong Tnil))
                                   (tptr Tvoid) cc_default))
        ((Etempvar _rd_addr tulong) :: (Econst_int (Int.repr 2) tuint) :: nil))
      (Sset _g_rd (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint cc_default))
          ((Etempvar _g_rd (tptr Tvoid)) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tuint)
                       (Econst_int (Int.repr 1) tuint) tint)
          (Sset _ret (Econst_long (Int64.repr 1) tulong))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _data_destroy3 (Tfunction
                                       (Tcons (tptr Tvoid)
                                         (Tcons tulong Tnil)) tulong
                                       cc_default))
                ((Etempvar _g_rd (tptr Tvoid)) ::
                 (Etempvar _map_addr tulong) :: nil))
              (Sset _ret (Etempvar _t'2 tulong)))
            (Scall None
              (Evar _granule_unlock (Tfunction
                                      (Tcons (tptr Tvoid)
                                        Tnil) tvoid cc_default))
              ((Etempvar _g_rd (tptr Tvoid)) :: nil)))))
      (Sreturn (Some (Etempvar _ret tulong)))))
.

Definition f_smc_data_destroy := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_rd_addr, tulong) :: (_map_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_rd, (tptr Tvoid)) ::
               (_last_level, tulong) :: (_index, tulong) ::
               (_data_addr, tulong) :: (_pte_val, tulong) ::
               (_ll_table, (tptr Tvoid)) ::
               (_rd, (tptr Tvoid)) :: (_ret, tulong) ::
               (_ipa_state, tuint) :: (_t'3, tuint) :: (_t'2, tulong) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := smc_data_destroy_body
|}.
