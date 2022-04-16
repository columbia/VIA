Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_rd := 3%positive.
Definition _g_rec := 4%positive.
Definition _granule := 5%positive.
Definition _i := 6%positive.
Definition _lock := 7%positive.
Definition _rd := 8%positive.
Definition _rec := 9%positive.
Definition _rec__1 := 10%positive.
Definition _rec_addr := 11%positive.
Definition _rec_list := 12%positive.
Definition _rec_list__1 := 13%positive.
Definition _ret := 14%positive.
Definition _t'1 := 15%positive.
Definition _t'2 := 16%positive.

Definition smc_rec_destroy_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _find_lock_unused_granule (Tfunction
                                          (Tcons tulong (Tcons tulong Tnil))
                                          (tptr Tvoid)
                                          cc_default))
        ((Etempvar _rec_addr tulong) :: (Econst_int (Int.repr 3) tuint) :: nil))
      (Sset _g_rec (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint cc_default))
          ((Etempvar _g_rec (tptr Tvoid)) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tuint)
                       (Econst_int (Int.repr 0) tuint) tint)
          (Ssequence
            (Scall None
              (Evar _rec_destroy_ops (Tfunction
                                       (Tcons (tptr Tvoid)
                                         Tnil) tvoid cc_default))
              ((Etempvar _g_rec (tptr Tvoid)) :: nil))
            (Sset _ret (Econst_long (Int64.repr 0) tulong)))
          (Sset _ret (Econst_long (Int64.repr 1) tulong))))
      (Sreturn (Some (Etempvar _ret tulong)))))
.

Definition f_smc_rec_destroy := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_rec_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_rec, (tptr Tvoid)) ::
               (_g_rd, (tptr Tvoid)) ::
               (_rec, (tptr Tvoid)) ::
               (_rec_list, (tptr Tvoid)) ::
               (_ret, tulong) :: (_t'2, tuint) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := smc_rec_destroy_body
|}.
