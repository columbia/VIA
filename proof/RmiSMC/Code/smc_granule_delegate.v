Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _granule := 3%positive.
Definition _i := 4%positive.
Definition _lock := 5%positive.
Definition _ret := 6%positive.
Definition _t'1 := 7%positive.
Definition _t'2 := 8%positive.

Definition smc_granule_delegate_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _find_lock_granule (Tfunction (Tcons tulong (Tcons tulong Tnil))
                                   (tptr Tvoid) cc_default))
        ((Etempvar _addr tulong) :: (Econst_int (Int.repr 0) tuint) :: nil))
      (Sset _g (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint cc_default))
          ((Etempvar _g (tptr Tvoid)) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tuint)
                       (Econst_long (Int64.repr 0) tulong) tint)
          (Ssequence
            (Scall None
              (Evar _granule_delegate_ops (Tfunction
                                            (Tcons
                                              (tptr Tvoid)
                                              (Tcons tulong Tnil)) tvoid
                                            cc_default))
              ((Etempvar _g (tptr Tvoid)) ::
               (Etempvar _addr tulong) :: nil))
            (Sset _ret (Econst_long (Int64.repr 0) tulong)))
          (Sset _ret (Econst_long (Int64.repr 1) tulong))))
      (Sreturn (Some (Etempvar _ret tulong)))))
.

Definition f_smc_granule_delegate := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g, (tptr Tvoid)) :: (_ret, tulong) ::
               (_t'2, tuint) :: (_t'1, (tptr Tvoid)) ::
               nil);
  fn_body := smc_granule_delegate_body
|}.
