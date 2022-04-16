Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _entry := 1%positive.
Definition _g := 2%positive.
Definition _g_rtt := 3%positive.
Definition _granule := 4%positive.
Definition _i := 5%positive.
Definition _level := 6%positive.
Definition _llt_pte := 7%positive.
Definition _pa := 8%positive.
Definition _pte := 9%positive.
Definition _ret := 10%positive.
Definition _rt := 11%positive.
Definition _table := 12%positive.
Definition _t'1 := 13%positive.

Definition table_create_init_absent_body :=
  (Sifthenelse (Ebinop Oeq (Etempvar _level tulong)
                 (Econst_long (Int64.repr 3) tulong) tint)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _entry_to_phys (Tfunction (Tcons tulong (Tcons tulong Tnil))
                                 tulong cc_default))
          ((Etempvar _llt_pte tulong) ::
           (Ebinop Osub (Etempvar _level tulong) (Econst_int (Int.repr 1) tint)
             tulong) :: nil))
        (Sset _pa (Etempvar _t'1 tulong)))
      (Ssequence
        (Scall None
          (Evar _granule_fill_table (Tfunction
                                      (Tcons (tptr Tvoid)
                                        (Tcons tulong (Tcons tulong Tnil)))
                                      tvoid cc_default))
          ((Etempvar _pte (tptr Tvoid)) ::
           (Ebinop Oor
             (Ebinop Oor
               (Ebinop Omul (Econst_int (Int.repr 1) tuint)
                 (Econst_long (Int64.repr 72057594037927936) tulong) tulong)
               (Etempvar _pa tulong) tulong)
             (Econst_long (Int64.repr 0) tulong) tulong) ::
           (Econst_long (Int64.repr 4096) tulong) :: nil))
        (Scall None
          (Evar _granule_refcount_inc (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons tulong Tnil)) tvoid
                                        cc_default))
          ((Etempvar _g_rtt (tptr Tvoid)) ::
           (Econst_long (Int64.repr 512) tulong) :: nil))))
    (Scall None
      (Evar _assert_cond (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Econst_int (Int.repr 0) tuint) :: nil)))
.

Definition f_table_create_init_absent := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_level, tulong) :: (_llt_pte, tulong) ::
                (_pte, (tptr Tvoid)) ::
                (_g_rtt, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_pa, tulong) :: (_t'1, tulong) :: nil);
  fn_body := table_create_init_absent_body
|}.
