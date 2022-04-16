Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _granule := 3%positive.
Definition _i := 4%positive.
Definition _rd := 5%positive.
Definition _rd__1 := 6%positive.
Definition _rec := 7%positive.
Definition _rec__1 := 8%positive.
Definition _ret := 9%positive.
Definition _rt := 10%positive.
Definition _t'1 := 11%positive.
Definition _t'2 := 12%positive.

Definition init_common_sysregs_body :=
  (Ssequence
    (Scall None
      (Evar _set_rec_common_sysregs (Tfunction
                                      (Tcons (tptr Tvoid)
                                        (Tcons tuint (Tcons tulong Tnil)))
                                      tvoid cc_default))
      ((Etempvar _rec (tptr Tvoid)) ::
       (Econst_int (Int.repr 75) tuint) ::
       (Econst_long (Int64.repr 70388072318015) tulong) :: nil))
    (Ssequence
      (Scall None
        (Evar _set_rec_common_sysregs (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons tuint (Tcons tulong Tnil)))
                                        tvoid cc_default))
        ((Etempvar _rec (tptr Tvoid)) ::
         (Econst_int (Int.repr 74) tuint) ::
         (Econst_long (Int64.repr 3221370256) tulong) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _get_rd_g_rtt (Tfunction
                                  (Tcons (tptr Tvoid) Tnil)
                                  (tptr Tvoid) cc_default))
            ((Etempvar _rd (tptr Tvoid)) :: nil))
          (Scall (Some _t'2)
            (Evar _granule_addr (Tfunction
                                  (Tcons (tptr Tvoid) Tnil)
                                  tulong cc_default))
            ((Etempvar _t'1 (tptr Tvoid)) :: nil)))
        (Scall None
          (Evar _set_rec_common_sysregs (Tfunction
                                          (Tcons (tptr Tvoid)
                                            (Tcons tuint (Tcons tulong Tnil)))
                                          tvoid cc_default))
          ((Etempvar _rec (tptr Tvoid)) ::
           (Econst_int (Int.repr 73) tuint) ::
           (Ebinop Oand (Etempvar _t'2 tulong)
             (Econst_long (Int64.repr 281474976710654) tulong) tulong) :: nil)))))
.

Definition f_init_common_sysregs := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_rd, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tulong) :: (_t'1, (tptr Tvoid)) ::
               nil);
  fn_body := init_common_sysregs_body
|}.
