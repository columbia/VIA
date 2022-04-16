Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _psci_func_id := 1%positive.
Definition _rec := 2%positive.
Definition _rec__1 := 3%positive.
Definition _ret := 4%positive.
Definition _t'1 := 5%positive.
Definition _t'2 := 6%positive.
Definition _t'3 := 7%positive.
Definition _t'4 := 8%positive.
Definition _t'5 := 9%positive.
Definition _t'6 := 10%positive.
Definition _t'7 := 11%positive.
Definition _t'8 := 12%positive.
Definition _t'9 := 13%positive.

Definition psci_features_body :=
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _psci_func_id tuint)
                                     (Econst_long (Int64.repr 2214592513) tulong)
                                     tint)
                        (Sset _t'1 (Econst_int (Int.repr 1) tint))
                        (Sset _t'1
                          (Ecast
                            (Ebinop Oeq (Etempvar _psci_func_id tuint)
                              (Econst_long (Int64.repr 3288334337) tulong)
                              tint) tbool)))
                      (Sifthenelse (Etempvar _t'1 tint)
                        (Sset _t'2 (Econst_int (Int.repr 1) tint))
                        (Sset _t'2
                          (Ecast
                            (Ebinop Oeq (Etempvar _psci_func_id tuint)
                              (Econst_long (Int64.repr 2214592514) tulong)
                              tint) tbool))))
                    (Sifthenelse (Etempvar _t'2 tint)
                      (Sset _t'3 (Econst_int (Int.repr 1) tint))
                      (Sset _t'3
                        (Ecast
                          (Ebinop Oeq (Etempvar _psci_func_id tuint)
                            (Econst_long (Int64.repr 2214592515) tulong) tint)
                          tbool))))
                  (Sifthenelse (Etempvar _t'3 tint)
                    (Sset _t'4 (Econst_int (Int.repr 1) tint))
                    (Sset _t'4
                      (Ecast
                        (Ebinop Oeq (Etempvar _psci_func_id tuint)
                          (Econst_long (Int64.repr 3288334339) tulong) tint)
                        tbool))))
                (Sifthenelse (Etempvar _t'4 tint)
                  (Sset _t'5 (Econst_int (Int.repr 1) tint))
                  (Sset _t'5
                    (Ecast
                      (Ebinop Oeq (Etempvar _psci_func_id tuint)
                        (Econst_long (Int64.repr 2214592516) tulong) tint)
                      tbool))))
              (Sifthenelse (Etempvar _t'5 tint)
                (Sset _t'6 (Econst_int (Int.repr 1) tint))
                (Sset _t'6
                  (Ecast
                    (Ebinop Oeq (Etempvar _psci_func_id tuint)
                      (Econst_long (Int64.repr 3288334340) tulong) tint) tbool))))
            (Sifthenelse (Etempvar _t'6 tint)
              (Sset _t'7 (Econst_int (Int.repr 1) tint))
              (Sset _t'7
                (Ecast
                  (Ebinop Oeq (Etempvar _psci_func_id tuint)
                    (Econst_long (Int64.repr 2214592520) tulong) tint) tbool))))
          (Sifthenelse (Etempvar _t'7 tint)
            (Sset _t'8 (Econst_int (Int.repr 1) tint))
            (Sset _t'8
              (Ecast
                (Ebinop Oeq (Etempvar _psci_func_id tuint)
                  (Econst_long (Int64.repr 2214592521) tulong) tint) tbool))))
        (Sifthenelse (Etempvar _t'8 tint)
          (Sset _t'9 (Econst_int (Int.repr 1) tint))
          (Sset _t'9
            (Ecast
              (Ebinop Oeq (Etempvar _psci_func_id tuint)
                (Econst_long (Int64.repr 2214592522) tulong) tint) tbool))))
      (Sifthenelse (Etempvar _t'9 tint)
        (Sset _ret (Econst_long (Int64.repr 0) tulong))
        (Sset _ret (Econst_long (Int64.repr 4294967295) tulong))))
    (Scall None
      (Evar _set_psci_result_x0 (Tfunction (Tcons tulong Tnil) tvoid
                                  cc_default)) ((Etempvar _ret tulong) :: nil)))
.

Definition f_psci_features := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_psci_func_id, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tulong) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body := psci_features_body
|}.
