Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_rd := 3%positive.
Definition _granule := 4%positive.
Definition _i := 5%positive.
Definition _level := 6%positive.
Definition _lock := 7%positive.
Definition _map_addr := 8%positive.
Definition _pa := 9%positive.
Definition _rd := 10%positive.
Definition _rd_addr := 11%positive.
Definition _ret := 12%positive.
Definition _rt := 13%positive.
Definition _table := 14%positive.
Definition _val := 15%positive.
Definition _valid := 16%positive.
Definition _t'1 := 17%positive.
Definition _t'2 := 18%positive.
Definition _t'3 := 19%positive.
Definition _t'4 := 20%positive.

Definition smc_rtt_map_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _validate_table_commands (Tfunction
                                         (Tcons tulong
                                           (Tcons tulong
                                             (Tcons tulong
                                               (Tcons tulong
                                                 (Tcons tulong Tnil))))) tuint
                                         cc_default))
        ((Etempvar _map_addr tulong) :: (Etempvar _level tulong) ::
         (Econst_int (Int.repr 2) tint) ::
         (Econst_long (Int64.repr 3) tulong) ::
         (Econst_int (Int.repr 2) tint) :: nil))
      (Sset _ret (Ecast (Etempvar _t'1 tuint) tulong)))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _ret tulong)
                     (Econst_int (Int.repr 0) tuint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _find_lock_granule (Tfunction
                                         (Tcons tulong (Tcons tulong Tnil))
                                         (tptr Tvoid)
                                         cc_default))
              ((Etempvar _rd_addr tulong) :: (Econst_int (Int.repr 2) tuint) ::
               nil))
            (Sset _g_rd (Etempvar _t'2 (tptr Tvoid))))
          (Ssequence
            (Scall (Some _t'4)
              (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                               cc_default))
              ((Etempvar _g_rd (tptr Tvoid)) :: nil))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tuint)
                           (Econst_int (Int.repr 1) tuint) tint)
              (Sset _ret (Econst_long (Int64.repr 1) tulong))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _table_map3 (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons tulong (Tcons tulong Tnil)))
                                        tulong cc_default))
                    ((Etempvar _g_rd (tptr Tvoid)) ::
                     (Etempvar _map_addr tulong) :: (Etempvar _level tulong) ::
                     nil))
                  (Sset _ret (Etempvar _t'3 tulong)))
                (Scall None
                  (Evar _granule_unlock (Tfunction
                                          (Tcons
                                            (tptr Tvoid)
                                            Tnil) tvoid cc_default))
                  ((Etempvar _g_rd (tptr Tvoid)) :: nil))))))
        Sskip)
      (Sreturn (Some (Etempvar _ret tulong)))))
.

Definition f_smc_rtt_map := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_rd_addr, tulong) :: (_map_addr, tulong) ::
                (_level, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_rd, (tptr Tvoid)) :: (_ret, tulong) ::
               (_t'4, tuint) :: (_t'3, tulong) ::
               (_t'2, (tptr Tvoid)) :: (_t'1, tuint) ::
               nil);
  fn_body := smc_rtt_map_body
|}.
