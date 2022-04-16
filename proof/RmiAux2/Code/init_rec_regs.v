Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _g := 1%positive.
Definition _i := 2%positive.
Definition _mpidr := 3%positive.
Definition _pc := 4%positive.
Definition _rd := 5%positive.
Definition _rd__1 := 6%positive.
Definition _rec := 7%positive.
Definition _rec__1 := 8%positive.
Definition _reg := 9%positive.
Definition _ret := 10%positive.
Definition _t'1 := 11%positive.
Definition _t'2 := 12%positive.

Definition init_rec_regs_body :=
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Swhile
        (Ebinop Olt (Etempvar _i tuint) (Econst_long (Int64.repr 8) tulong)
          tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _get_rec_params_gprs (Tfunction (Tcons tuint Tnil) tulong
                                           cc_default))
              ((Etempvar _i tuint) :: nil))
            (Scall None
              (Evar _set_rec_regs (Tfunction
                                    (Tcons (tptr Tvoid)
                                      (Tcons tuint (Tcons tulong Tnil))) tvoid
                                    cc_default))
              ((Etempvar _rec (tptr Tvoid)) ::
               (Etempvar _i tuint) :: (Etempvar _t'1 tulong) :: nil)))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _get_rec_params_pc (Tfunction Tnil tulong cc_default)) nil)
          (Scall None
            (Evar _set_rec_pc (Tfunction
                                (Tcons (tptr Tvoid)
                                  (Tcons tulong Tnil)) tvoid cc_default))
            ((Etempvar _rec (tptr Tvoid)) ::
             (Etempvar _t'2 tulong) :: nil)))
        (Ssequence
          (Scall None
            (Evar _set_rec_pstate (Tfunction
                                    (Tcons (tptr Tvoid)
                                      (Tcons tulong Tnil)) tvoid cc_default))
            ((Etempvar _rec (tptr Tvoid)) ::
             (Econst_long (Int64.repr 965) tulong) :: nil))
          (Ssequence
            (Scall None
              (Evar _init_rec_sysregs (Tfunction
                                        (Tcons (tptr Tvoid)
                                          (Tcons tulong Tnil)) tvoid
                                        cc_default))
              ((Etempvar _rec (tptr Tvoid)) ::
               (Etempvar _mpidr tulong) :: nil))
            (Scall None
              (Evar _init_common_sysregs (Tfunction
                                           (Tcons (tptr Tvoid)
                                             (Tcons (tptr Tvoid)
                                               Tnil)) tvoid cc_default))
              ((Etempvar _rec (tptr Tvoid)) ::
               (Etempvar _rd (tptr Tvoid)) :: nil)))))))
.

Definition f_init_rec_regs := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_mpidr, tulong) :: (_rd, (tptr Tvoid)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := init_rec_regs_body
|}.
