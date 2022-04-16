Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _entry := 2%positive.
Definition _g := 3%positive.
Definition _g_rtt := 4%positive.
Definition _granule := 5%positive.
Definition _i := 6%positive.
Definition _index := 7%positive.
Definition _level := 8%positive.
Definition _ll_table := 9%positive.
Definition _llt_pte := 10%positive.
Definition _map_addr := 11%positive.
Definition _pa := 12%positive.
Definition _pgte := 13%positive.
Definition _pte := 14%positive.
Definition _ret := 15%positive.
Definition _rt := 16%positive.
Definition _table := 17%positive.
Definition _t'1 := 18%positive.

Definition table_create_init_present_body :=
  (Sifthenelse (Ebinop Oeq (Etempvar _level tulong)
                 (Econst_long (Int64.repr 3) tulong) tint)
    (Ssequence
      (Scall None
        (Evar _pgte_write (Tfunction
                            (Tcons (tptr Tvoid)
                              (Tcons tulong (Tcons tulong Tnil))) tvoid
                            cc_default))
        ((Etempvar _ll_table (tptr Tvoid)) :: (Etempvar _index tulong) ::
         (Econst_long (Int64.repr 0) tulong) :: nil))
      (Ssequence
        (Scall None
          (Evar _invalidate_block (Tfunction (Tcons tulong Tnil) tvoid
                                    cc_default))
          ((Etempvar _map_addr tulong) :: nil))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _entry_to_phys (Tfunction
                                     (Tcons tulong (Tcons tulong Tnil)) tulong
                                     cc_default))
              ((Etempvar _llt_pte tulong) ::
               (Ebinop Osub (Etempvar _level tulong)
                 (Econst_int (Int.repr 1) tuint) tulong) :: nil))
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
                   (Ebinop Omul (Econst_int (Int.repr 2) tuint)
                     (Econst_long (Int64.repr 72057594037927936) tulong)
                     tulong) (Etempvar _pa tulong) tulong)
                 (Econst_long (Int64.repr 2011) tulong) tulong) ::
               (Econst_long (Int64.repr 4096) tulong) :: nil))
            (Scall None
              (Evar _granule_refcount_inc (Tfunction
                                            (Tcons
                                              (tptr Tvoid)
                                              (Tcons tulong Tnil)) tvoid
                                            cc_default))
              ((Etempvar _g_rtt (tptr Tvoid)) ::
               (Econst_long (Int64.repr 512) tulong) :: nil))))))
    (Scall None
      (Evar _assert_cond (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Econst_int (Int.repr 0) tuint) :: nil)))
.

Definition f_table_create_init_present := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_level, tulong) :: (_ll_table, (tptr Tvoid)) ::
                (_index, tulong) :: (_map_addr, tulong) ::
                (_llt_pte, tulong) :: (_pte, (tptr Tvoid)) ::
                (_g_rtt, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_pa, tulong) :: (_t'1, tulong) :: nil);
  fn_body := table_create_init_present_body
|}.
