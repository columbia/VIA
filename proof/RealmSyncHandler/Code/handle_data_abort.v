Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _esr := 1%positive.
Definition _far := 2%positive.
Definition _g := 3%positive.
Definition _hpfar := 4%positive.
Definition _i := 5%positive.
Definition _info := 6%positive.
Definition _rec := 7%positive.
Definition _rec__1 := 8%positive.
Definition _ret := 9%positive.
Definition _spsr := 10%positive.
Definition _write_val := 11%positive.
Definition _t'1 := 12%positive.
Definition _t'2 := 13%positive.
Definition _t'3 := 14%positive.
Definition _t'4 := 15%positive.
Definition _t'5 := 16%positive.
Definition _t'6 := 17%positive.
Definition _t'7 := 18%positive.

Definition handle_data_abort_body :=
  (Ssequence
    (Sset _far (Econst_long (Int64.repr 0) tulong))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong cc_default))
          ((Econst_int (Int.repr 85) tuint) :: nil))
        (Sset _hpfar (Etempvar _t'1 tulong)))
      (Ssequence
        (Sset _write_val (Econst_long (Int64.repr 0) tulong))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _sysreg_read (Tfunction (Tcons tuint Tnil) tulong
                                   cc_default))
              ((Econst_int (Int.repr 94) tuint) :: nil))
            (Sset _spsr (Etempvar _t'2 tulong)))
          (Ssequence
            (Sifthenelse (Ebinop One
                           (Ebinop Oand (Etempvar _spsr tulong)
                             (Econst_long (Int64.repr 16) tulong) tulong)
                           (Econst_long (Int64.repr 0) tulong) tint)
              (Sset _esr
                (Ebinop Oand (Etempvar _esr tulong)
                  (Econst_long (Int64.repr (18446744073692774399)) tulong) tulong))
              Sskip)
            (Ssequence
              (Ssequence
                (Sifthenelse (Ebinop Oeq
                               (Ebinop Oand (Etempvar _esr tulong)
                                 (Econst_long (Int64.repr 16777216) tulong)
                                 tulong) (Econst_long (Int64.repr 0) tulong)
                               tint)
                  (Sset _t'6 (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Scall (Some _t'7)
                      (Evar _access_in_par (Tfunction
                                             (Tcons
                                               (tptr Tvoid)
                                               (Tcons tulong
                                                 (Tcons tulong Tnil))) tuint
                                             cc_default))
                      ((Etempvar _rec (tptr Tvoid)) ::
                       (Etempvar _hpfar tulong) :: (Etempvar _esr tulong) ::
                       nil))
                    (Sset _t'6
                      (Ecast
                        (Ebinop Oeq (Etempvar _t'7 tuint)
                          (Econst_int (Int.repr 0) tuint) tint) tbool))))
                (Sifthenelse (Etempvar _t'6 tint)
                  (Sset _esr
                    (Ebinop Oand (Etempvar _esr tulong)
                      (Ebinop Oor (Econst_long (Int64.repr 4227858432) tulong)
                        (Econst_long (Int64.repr 63) tulong) tulong) tulong))
                  (Ssequence
                    (Scall None
                      (Evar _set_rec_last_run_info_esr (Tfunction
                                                         (Tcons
                                                           (tptr Tvoid)
                                                           (Tcons tulong Tnil))
                                                         tvoid cc_default))
                      ((Etempvar _rec (tptr Tvoid)) ::
                       (Etempvar _esr tulong) :: nil))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'4)
                          (Evar _esr_is_write (Tfunction (Tcons tulong Tnil)
                                                tuint cc_default))
                          ((Etempvar _esr tulong) :: nil))
                        (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tuint)
                                       (Econst_int (Int.repr 1) tuint) tint)
                          (Ssequence
                            (Scall (Some _t'3)
                              (Evar _get_write_value (Tfunction
                                                       (Tcons
                                                         (tptr Tvoid)
                                                         (Tcons tulong Tnil))
                                                       tulong cc_default))
                              ((Etempvar _rec (tptr Tvoid)) ::
                               (Etempvar _esr tulong) :: nil))
                            (Sset _write_val (Etempvar _t'3 tulong)))
                          Sskip))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'5)
                            (Evar _sysreg_read (Tfunction (Tcons tuint Tnil)
                                                 tulong cc_default))
                            ((Econst_int (Int.repr 83) tuint) :: nil))
                          (Sset _far
                            (Ebinop Oand (Etempvar _t'5 tulong)
                              (Econst_int (Int.repr 4095) tint) tulong)))
                        (Sset _esr
                          (Ebinop Oand (Etempvar _esr tulong)
                            (Econst_long (Int64.repr 4095) tulong) tulong)))))))
              (Ssequence
                (Scall None
                  (Evar _set_rec_run_esr (Tfunction (Tcons tulong Tnil) tvoid
                                           cc_default))
                  ((Etempvar _esr tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _set_rec_run_far (Tfunction (Tcons tulong Tnil) tvoid
                                             cc_default))
                    ((Etempvar _far tulong) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _set_rec_run_hpfar (Tfunction (Tcons tulong Tnil)
                                                 tvoid cc_default))
                      ((Etempvar _hpfar tulong) :: nil))
                    (Scall None
                      (Evar _set_rec_run_emulated_write_val (Tfunction
                                                              (Tcons tulong
                                                                Tnil) tvoid
                                                              cc_default))
                      ((Etempvar _write_val tulong) :: nil)))))))))))
.

Definition f_handle_data_abort := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) :: (_esr, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_far, tulong) :: (_hpfar, tulong) :: (_write_val, tulong) ::
               (_spsr, tulong) :: (_t'7, tuint) :: (_t'6, tint) ::
               (_t'5, tulong) :: (_t'4, tuint) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := handle_data_abort_body
|}.
