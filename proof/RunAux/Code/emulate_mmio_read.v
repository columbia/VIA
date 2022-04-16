Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _bit := 1%positive.
Definition _bit_count := 2%positive.
Definition _esr := 3%positive.
Definition _g := 4%positive.
Definition _i := 5%positive.
Definition _mask := 6%positive.
Definition _rec := 7%positive.
Definition _rec__1 := 8%positive.
Definition _reg := 9%positive.
Definition _ret := 10%positive.
Definition _rt := 11%positive.
Definition _val := 12%positive.
Definition _t'1 := 13%positive.
Definition _t'2 := 14%positive.
Definition _t'3 := 15%positive.
Definition _t'4 := 16%positive.
Definition _t'5 := 17%positive.
Definition _t'6 := 18%positive.

Definition emulate_mmio_read_body :=
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_rec_run_emulated_read_val (Tfunction Tnil tulong
                                                 cc_default)) nil)
        (Scall (Some _t'2)
          (Evar _access_mask (Tfunction (Tcons tulong Tnil) tulong cc_default))
          ((Etempvar _esr tulong) :: nil)))
      (Sset _val
        (Ebinop Oand (Etempvar _t'1 tulong) (Etempvar _t'2 tulong) tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'6)
          (Evar _esr_sign_extend (Tfunction (Tcons tulong Tnil) tuint
                                   cc_default))
          ((Etempvar _esr tulong) :: nil))
        (Sifthenelse (Ebinop One (Etempvar _t'6 tuint)
                       (Econst_int (Int.repr 0) tuint) tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _access_len (Tfunction (Tcons tulong Tnil) tuint
                                    cc_default))
                ((Etempvar _esr tulong) :: nil))
              (Sset _bit_count
                (Ebinop Omul (Etempvar _t'3 tuint)
                  (Econst_int (Int.repr 8) tuint) tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _shiftl (Tfunction (Tcons tulong (Tcons tulong Tnil))
                                  tulong cc_default))
                  ((Econst_long (Int64.repr 1) tulong) ::
                   (Ebinop Osub (Etempvar _bit_count tuint)
                     (Econst_int (Int.repr 1) tuint) tuint) :: nil))
                (Sset _mask (Etempvar _t'4 tulong)))
              (Ssequence
                (Sset _val
                  (Ebinop Osub
                    (Ebinop Oxor (Etempvar _val tulong) (Etempvar _mask tulong)
                      tulong) (Etempvar _mask tulong) tulong))
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _esr_sixty_four (Tfunction (Tcons tulong Tnil) tuint
                                            cc_default))
                    ((Etempvar _esr tulong) :: nil))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tuint)
                                 (Econst_int (Int.repr 0) tuint) tint)
                    (Sset _val
                      (Ebinop Oand (Etempvar _val tulong)
                        (Econst_int (Int.repr (4294967295)) tuint) tulong))
                    Sskip)))))
          Sskip))
      (Scall None
        (Evar _set_rec_regs (Tfunction
                              (Tcons (tptr Tvoid)
                                (Tcons tuint (Tcons tulong Tnil))) tvoid
                              cc_default))
        ((Etempvar _rec (tptr Tvoid)) ::
         (Etempvar _rt tuint) :: (Etempvar _val tulong) :: nil))))
.

Definition f_emulate_mmio_read := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_esr, tulong) :: (_rt, tuint) ::
                (_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_val, tulong) :: (_bit_count, tuint) :: (_mask, tulong) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tulong) ::
               (_t'3, tuint) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := emulate_mmio_read_body
|}.
