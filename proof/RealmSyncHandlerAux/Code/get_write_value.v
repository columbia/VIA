Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _esr := 1%positive.
Definition _g := 2%positive.
Definition _i := 3%positive.
Definition _mask := 4%positive.
Definition _rec := 5%positive.
Definition _rec__1 := 6%positive.
Definition _reg := 7%positive.
Definition _ret := 8%positive.
Definition _rt := 9%positive.
Definition _write_val := 10%positive.
Definition _t'1 := 11%positive.
Definition _t'2 := 12%positive.
Definition _t'3 := 13%positive.

Definition get_write_value_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _esr_srt (Tfunction (Tcons tulong Tnil) tuint cc_default))
        ((Etempvar _esr tulong) :: nil))
      (Sset _rt (Etempvar _t'1 tuint)))
    (Sifthenelse (Ebinop Oeq (Etempvar _rt tuint)
                   (Econst_int (Int.repr 31) tuint) tint)
      (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _get_rec_regs (Tfunction
                                  (Tcons (tptr Tvoid)
                                    (Tcons tuint Tnil)) tulong cc_default))
            ((Etempvar _rec (tptr Tvoid)) ::
             (Etempvar _rt tuint) :: nil))
          (Scall (Some _t'3)
            (Evar _access_mask (Tfunction (Tcons tulong Tnil) tulong
                                 cc_default)) ((Etempvar _esr tulong) :: nil)))
        (Sreturn (Some (Ebinop Oand (Etempvar _t'2 tulong)
                         (Etempvar _t'3 tulong) tulong))))))
.

Definition f_get_write_value := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: (_esr, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_rt, tuint) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tuint) :: nil);
  fn_body := get_write_value_body
|}.
