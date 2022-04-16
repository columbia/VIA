Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _esr := 1%positive.
Definition _g := 2%positive.
Definition _i := 3%positive.
Definition _info := 4%positive.
Definition _pc := 5%positive.
Definition _rec := 6%positive.
Definition _rec__1 := 7%positive.
Definition _ret := 8%positive.
Definition _rt := 9%positive.
Definition _val := 10%positive.
Definition _t'1 := 11%positive.
Definition _t'2 := 12%positive.
Definition _t'3 := 13%positive.
Definition _t'4 := 14%positive.
Definition _t'5 := 15%positive.
Definition _t'6 := 16%positive.
Definition _t'7 := 17%positive.

Definition complete_mmio_emulation_body :=
  (Ssequence
    (Scall (Some _t'7)
      (Evar _get_rec_run_is_emulated_mmio (Tfunction Tnil tulong cc_default))
      nil)
    (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tulong)
                   (Econst_long (Int64.repr 0) tulong) tint)
      (Sreturn (Some (Econst_int (Int.repr 1) tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _get_rec_last_run_info_esr (Tfunction
                                               (Tcons
                                                 (tptr Tvoid)
                                                 Tnil) tulong cc_default))
            ((Etempvar _rec (tptr Tvoid)) :: nil))
          (Sset _esr (Etempvar _t'1 tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _esr_srt (Tfunction (Tcons tulong Tnil) tuint cc_default))
              ((Etempvar _esr tulong) :: nil))
            (Sset _rt (Etempvar _t'2 tuint)))
          (Ssequence
            (Sifthenelse (Ebinop One
                           (Ebinop Oand (Etempvar _esr tulong)
                             (Econst_long (Int64.repr 4227858432) tulong)
                             tulong)
                           (Econst_long (Int64.repr 2415919104) tulong) tint)
              (Sset _t'6 (Econst_int (Int.repr 1) tint))
              (Sset _t'6
                (Ecast
                  (Ebinop Oeq
                    (Ebinop Oand (Etempvar _esr tulong)
                      (Econst_long (Int64.repr 16777216) tulong) tulong)
                    (Econst_long (Int64.repr 0) tulong) tint) tbool)))
            (Sifthenelse (Etempvar _t'6 tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _esr_is_write (Tfunction (Tcons tulong Tnil) tuint
                                            cc_default))
                      ((Etempvar _esr tulong) :: nil))
                    (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tuint)
                                   (Econst_int (Int.repr 0) tuint) tint)
                      (Sset _t'4
                        (Ecast
                          (Ebinop One (Etempvar _rt tuint)
                            (Econst_int (Int.repr 31) tuint) tint) tbool))
                      (Sset _t'4 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'4 tint)
                    (Scall None
                      (Evar _emulate_mmio_read (Tfunction
                                                 (Tcons tulong
                                                   (Tcons tuint
                                                     (Tcons
                                                       (tptr Tvoid)
                                                       Tnil))) tvoid
                                                 cc_default))
                      ((Etempvar _esr tulong) :: (Etempvar _rt tuint) ::
                       (Etempvar _rec (tptr Tvoid)) :: nil))
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _get_rec_pc (Tfunction
                                          (Tcons (tptr Tvoid)
                                            Tnil) tulong cc_default))
                      ((Etempvar _rec (tptr Tvoid)) :: nil))
                    (Scall None
                      (Evar _set_rec_pc (Tfunction
                                          (Tcons (tptr Tvoid)
                                            (Tcons tulong Tnil)) tvoid
                                          cc_default))
                      ((Etempvar _rec (tptr Tvoid)) ::
                       (Ebinop Oadd (Etempvar _t'5 tulong)
                         (Econst_long (Int64.repr 4) tulong) tulong) :: nil)))
                  (Sreturn (Some (Econst_int (Int.repr 1) tuint)))))))))))
.

Definition f_complete_mmio_emulation := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_rt, tuint) :: (_esr, tulong) :: (_val, tulong) ::
               (_t'7, tulong) :: (_t'6, tint) :: (_t'5, tulong) ::
               (_t'4, tint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tulong) :: nil);
  fn_body := complete_mmio_emulation_body
|}.
