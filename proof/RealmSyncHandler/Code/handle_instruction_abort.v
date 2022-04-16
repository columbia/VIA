Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _esr := 2%positive.
Definition _fipa := 3%positive.
Definition _fsc := 4%positive.
Definition _fsc_type := 5%positive.
Definition _hpfar := 6%positive.
Definition _i := 7%positive.
Definition _rec := 8%positive.
Definition _rec__1 := 9%positive.
Definition _ret := 10%positive.
Definition _t'1 := 11%positive.
Definition _t'2 := 12%positive.
Definition _t'3 := 13%positive.

Definition handle_instruction_abort_body :=
  (Ssequence
    (Sset _fsc
      (Ebinop Oand (Etempvar _esr tulong) (Econst_long (Int64.repr 63) tulong)
        tulong))
    (Ssequence
      (Sset _fsc_type
        (Ebinop Oand (Etempvar _fsc tulong)
          (Econst_long (Int64.repr (18446744073709551612)) tulong) tulong))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong cc_default))
            ((Econst_int (Int.repr 85) tuint) :: nil))
          (Sset _hpfar (Etempvar _t'1 tulong)))
        (Sifthenelse (Ebinop Oeq (Etempvar _fsc_type tulong)
                       (Econst_long (Int64.repr 12) tulong) tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
          (Sifthenelse (Ebinop One (Etempvar _fsc_type tulong)
                         (Econst_long (Int64.repr 4) tulong) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _shiftl (Tfunction (Tcons tulong (Tcons tulong Tnil))
                                  tulong cc_default))
                  ((Ebinop Oand (Etempvar _hpfar tulong)
                     (Econst_long (Int64.repr 17592186044400) tulong) tulong) ::
                   (Econst_long (Int64.repr 8) tulong) :: nil))
                (Sset _fipa (Etempvar _t'2 tulong)))
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _is_addr_in_par_rec (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                (Tcons tulong Tnil)) tuint
                                              cc_default))
                  ((Etempvar _rec (tptr Tvoid)) ::
                   (Etempvar _fipa tulong) :: nil))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tuint)
                               (Econst_int (Int.repr 0) tuint) tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tuint)))
                  (Ssequence
                    (Scall None
                      (Evar _set_rec_run_hpfar (Tfunction (Tcons tulong Tnil)
                                                 tvoid cc_default))
                      ((Etempvar _hpfar tulong) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _set_rec_run_esr (Tfunction (Tcons tulong Tnil)
                                                 tvoid cc_default))
                        ((Ebinop Oand (Etempvar _esr tulong)
                           (Ebinop Oor
                             (Econst_long (Int64.repr 4227858432) tulong)
                             (Econst_long (Int64.repr 63) tulong) tulong)
                           tulong) :: nil))
                      (Sreturn (Some (Econst_int (Int.repr 1) tuint)))))))))))))
.

Definition f_handle_instruction_abort := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: (_esr, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_fsc, tulong) :: (_fsc_type, tulong) :: (_hpfar, tulong) ::
               (_fipa, tulong) :: (_t'3, tuint) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body := handle_instruction_abort_body
|}.
