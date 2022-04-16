Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _i := 1%positive.
Definition _mask := 2%positive.
Definition _ret := 3%positive.
Definition _rvic := 4%positive.
Definition _target := 5%positive.
Definition _tmp := 6%positive.
Definition _valid := 7%positive.

Definition rvic_target_is_valid_body :=
  (Ssequence
    (Sset _mask (Econst_long (Int64.repr 1095233437695) tulong))
    (Ssequence
      (Sset _tmp
        (Ebinop Oand (Etempvar _target tulong)
          (Ebinop Osub (Econst_long (Int64.repr (18446744073709551615)) tulong)
            (Etempvar _mask tulong) tulong) tulong))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _tmp tulong)
                       (Econst_long (Int64.repr 0) tulong) tint)
          (Sset _ret (Econst_int (Int.repr 1) tuint))
          (Sset _ret (Econst_int (Int.repr 0) tuint)))
        (Sreturn (Some (Etempvar _ret tuint))))))
.

Definition f_rvic_target_is_valid := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_target, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_mask, tulong) :: (_tmp, tulong) :: (_ret, tuint) :: nil);
  fn_body := rvic_target_is_valid_body
|}.
