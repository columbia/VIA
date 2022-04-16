Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _bit := 1%positive.
Definition _bitmap := 2%positive.
Definition _g := 3%positive.
Definition _i := 4%positive.
Definition _idx := 5%positive.
Definition _intid := 6%positive.
Definition _ret := 7%positive.
Definition _t'1 := 8%positive.
Definition _t'2 := 9%positive.
Definition _t'3 := 10%positive.
Definition _t'4 := 11%positive.

Definition rvic_test_flag_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _interrupt_bitmap_dword (Tfunction (Tcons tulong Tnil) tulong
                                        cc_default))
        ((Etempvar _intid tulong) :: nil))
      (Sset _idx (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _interrupt_bit (Tfunction (Tcons tulong Tnil) tulong
                                 cc_default))
          ((Etempvar _intid tulong) :: nil))
        (Sset _bit (Etempvar _t'2 tulong)))
      (Ssequence
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _get_bitmap_loc (Tfunction
                                      (Tcons (tptr Tvoid) (Tcons tulong Tnil))
                                      (tptr Tvoid) cc_default))
              ((Etempvar _bitmap (tptr Tvoid)) :: (Etempvar _idx tulong) ::
               nil))
            (Scall (Some _t'4)
              (Evar _test_bit_acquire_64 (Tfunction
                                           (Tcons (tptr Tvoid)
                                             (Tcons tuint Tnil)) tuint
                                           cc_default))
              ((Etempvar _t'3 (tptr Tvoid)) :: (Etempvar _bit tulong) :: nil)))
          (Sset _ret (Etempvar _t'4 tuint)))
        (Sreturn (Some (Etempvar _ret tuint))))))
.

Definition f_rvic_test_flag := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_intid, tulong) :: (_bitmap, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_idx, tulong) :: (_bit, tulong) :: (_ret, tuint) ::
               (_t'4, tuint) :: (_t'3, (tptr Tvoid)) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := rvic_test_flag_body
|}.
