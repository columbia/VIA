Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _g := 1%positive.
Definition _i := 2%positive.
Definition _intid := 3%positive.
Definition _lock := 4%positive.
Definition _rec := 5%positive.
Definition _rec__1 := 6%positive.
Definition _ret := 7%positive.
Definition _rvic := 8%positive.
Definition _target := 9%positive.
Definition _target_rec := 10%positive.
Definition _target_valid := 11%positive.
Definition _valid := 12%positive.
Definition _t'1 := 13%positive.
Definition _t'2 := 14%positive.
Definition _t'3 := 15%positive.
Definition _t'4 := 16%positive.
Definition _t'5 := 17%positive.
Definition _t'6 := 18%positive.

Definition validate_and_lookup_target_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _rvic_target_is_valid (Tfunction (Tcons tulong Tnil) tuint
                                      cc_default))
        ((Etempvar _target tulong) :: nil))
      (Sset _target_valid (Etempvar _t'1 tuint)))
    (Sifthenelse (Ebinop Oeq (Etempvar _target_valid tuint)
                   (Econst_int (Int.repr 0) tuint) tint)
      (Sreturn (Some (Econst_long (Int64.repr 1) tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _is_trusted_intid (Tfunction (Tcons tulong Tnil) tuint
                                      cc_default))
            ((Etempvar _intid tulong) :: nil))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tuint)
                         (Econst_int (Int.repr 0) tuint) tint)
            (Ssequence
              (Scall (Some _t'6)
                (Evar _is_untrusted_intid (Tfunction (Tcons tulong Tnil) tuint
                                            cc_default))
                ((Etempvar _intid tulong) :: nil))
              (Sset _t'5
                (Ecast
                  (Ebinop Oeq (Etempvar _t'6 tuint)
                    (Econst_int (Int.repr 0) tuint) tint) tbool)))
            (Sset _t'5 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'5 tint)
          (Sreturn (Some (Econst_long (Int64.repr 1) tulong)))
          (Ssequence
            (Scall None
              (Evar _find_lock_map_target_rec (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  (Tcons tulong Tnil)) tvoid
                                                cc_default))
              ((Etempvar _rec (tptr Tvoid)) ::
               (Etempvar _target tulong) :: nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _get_target_rec (Tfunction Tnil
                                          (tptr Tvoid)
                                          cc_default)) nil)
                (Scall (Some _t'3)
                  (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                                   cc_default))
                  ((Etempvar _t'2 (tptr Tvoid)) :: nil)))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tuint)
                             (Econst_int (Int.repr 1) tuint) tint)
                (Sreturn (Some (Econst_long (Int64.repr 1) tulong)))
                (Sreturn (Some (Econst_long (Int64.repr 0) tulong))))))))))
.

Definition f_validate_and_lookup_target := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_target, tulong) :: (_intid, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_target_valid, tuint) :: (_t'6, tuint) :: (_t'5, tint) ::
               (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, (tptr Tvoid)) :: (_t'1, tuint) :: nil);
  fn_body := validate_and_lookup_target_body
|}.
