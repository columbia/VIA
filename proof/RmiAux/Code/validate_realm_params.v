Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _base := 1%positive.
Definition _g := 2%positive.
Definition _i := 3%positive.
Definition _par_base := 4%positive.
Definition _ret := 5%positive.
Definition _size := 6%positive.
Definition _val := 7%positive.
Definition _valid := 8%positive.
Definition _t'1 := 9%positive.
Definition _t'2 := 10%positive.
Definition _t'3 := 11%positive.
Definition _t'4 := 12%positive.
Definition _t'5 := 13%positive.
Definition _t'6 := 14%positive.

Definition validate_realm_params_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_realm_params_par_base (Tfunction Tnil tulong cc_default))
        nil)
      (Sset _base (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_realm_params_par_size (Tfunction Tnil tulong cc_default))
          nil)
        (Sset _size (Etempvar _t'2 tulong)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Oeq
                             (Ebinop Omod (Etempvar _base tulong)
                               (Econst_long (Int64.repr 4096) tulong) tulong)
                             (Econst_long (Int64.repr 0) tulong) tint)
                (Sset _t'3
                  (Ecast
                    (Ebinop Oeq
                      (Ebinop Omod (Etempvar _size tulong)
                        (Econst_long (Int64.repr 4096) tulong) tulong)
                      (Econst_long (Int64.repr 0) tulong) tint) tbool))
                (Sset _t'3 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'3 tint)
                (Sset _t'4
                  (Ecast
                    (Ebinop Ogt
                      (Ebinop Oadd (Etempvar _base tulong)
                        (Etempvar _size tulong) tulong) (Etempvar _base tulong)
                      tint) tbool))
                (Sset _t'4 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'4 tint)
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _max_ipa_size (Tfunction Tnil tulong cc_default)) nil)
                (Sset _t'5
                  (Ecast
                    (Ebinop Olt
                      (Ebinop Oadd (Etempvar _base tulong)
                        (Etempvar _size tulong) tulong) (Etempvar _t'6 tulong)
                      tint) tbool)))
              (Sset _t'5 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'5 tint)
            (Sset _ret (Econst_long (Int64.repr 0) tulong))
            (Sset _ret (Econst_long (Int64.repr 1) tulong))))
        (Sreturn (Some (Etempvar _ret tulong))))))
.

Definition f_validate_realm_params := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_ret, tulong) :: (_base, tulong) :: (_size, tulong) ::
               (_t'6, tulong) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := validate_realm_params_body
|}.
