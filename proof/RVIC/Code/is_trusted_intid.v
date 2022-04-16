Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _i := 1%positive.
Definition _intid := 2%positive.
Definition _ret := 3%positive.
Definition _t'1 := 4%positive.

Definition is_trusted_intid_body :=
  (Ssequence
    (Sifthenelse (Ebinop Oge (Etempvar _intid tulong)
                   (Econst_long (Int64.repr 0) tulong) tint)
      (Sset _t'1
        (Ecast
          (Ebinop Ole (Etempvar _intid tulong)
            (Econst_long (Int64.repr 31) tulong) tint) tbool))
      (Sset _t'1 (Econst_int (Int.repr 0) tint)))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Econst_int (Int.repr 1) tuint)))
      (Sreturn (Some (Econst_int (Int.repr 0) tuint)))))
.

Definition f_is_trusted_intid := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_intid, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body := is_trusted_intid_body
|}.
