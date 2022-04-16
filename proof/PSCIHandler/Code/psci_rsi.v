Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _arg0 := 1%positive.
Definition _arg1 := 2%positive.
Definition _arg2 := 3%positive.
Definition _function_id := 4%positive.
Definition _i := 5%positive.
Definition _rec := 6%positive.
Definition _rec__1 := 7%positive.
Definition _ret := 8%positive.
Definition _t'1 := 9%positive.

Definition psci_rsi_body :=
  (Sifthenelse (Ebinop Oeq (Etempvar _function_id tuint)
                 (Econst_long (Int64.repr 2214592512) tulong) tint)
    (Scall None
      (Evar _psci_version (Tfunction (Tcons (tptr Tvoid) Tnil)
                            tvoid cc_default))
      ((Etempvar _rec (tptr Tvoid)) :: nil))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _function_id tuint)
                     (Econst_long (Int64.repr 2214592513) tulong) tint)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Sset _t'1
          (Ecast
            (Ebinop Oeq (Etempvar _function_id tuint)
              (Econst_long (Int64.repr 3288334337) tulong) tint) tbool)))
      (Sifthenelse (Etempvar _t'1 tint)
        (Scall None
          (Evar _psci_cpu_suspend (Tfunction
                                    (Tcons (tptr Tvoid)
                                      (Tcons tulong (Tcons tulong Tnil))) tvoid
                                    cc_default))
          ((Etempvar _rec (tptr Tvoid)) ::
           (Etempvar _arg0 tulong) :: (Etempvar _arg1 tulong) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar _function_id tuint)
                       (Econst_long (Int64.repr 2214592514) tulong) tint)
          (Scall None
            (Evar _psci_cpu_off (Tfunction
                                  (Tcons (tptr Tvoid) Tnil)
                                  tvoid cc_default))
            ((Etempvar _rec (tptr Tvoid)) :: nil))
          (Sifthenelse (Ebinop Oeq (Etempvar _function_id tuint)
                         (Econst_long (Int64.repr 2214592515) tulong) tint)
            (Ssequence
              (Sset _arg0 (Ecast (Ecast (Etempvar _arg0 tulong) tuint) tulong))
              (Ssequence
                (Sset _arg1
                  (Ecast (Ecast (Etempvar _arg1 tulong) tuint) tulong))
                (Ssequence
                  (Sset _arg2
                    (Ecast (Ecast (Etempvar _arg2 tulong) tuint) tulong))
                  (Scall None
                    (Evar _psci_cpu_on (Tfunction
                                         (Tcons (tptr Tvoid)
                                           (Tcons tulong
                                             (Tcons tulong (Tcons tulong Tnil))))
                                         tvoid cc_default))
                    ((Etempvar _rec (tptr Tvoid)) ::
                     (Etempvar _arg0 tulong) :: (Etempvar _arg1 tulong) ::
                     (Etempvar _arg2 tulong) :: nil)))))
            (Sifthenelse (Ebinop Oeq (Etempvar _function_id tuint)
                           (Econst_long (Int64.repr 3288334339) tulong) tint)
              (Scall None
                (Evar _psci_cpu_on (Tfunction
                                     (Tcons (tptr Tvoid)
                                       (Tcons tulong
                                         (Tcons tulong (Tcons tulong Tnil))))
                                     tvoid cc_default))
                ((Etempvar _rec (tptr Tvoid)) ::
                 (Etempvar _arg0 tulong) :: (Etempvar _arg1 tulong) ::
                 (Etempvar _arg2 tulong) :: nil))
              (Sifthenelse (Ebinop Oeq (Etempvar _function_id tuint)
                             (Econst_long (Int64.repr 2214592516) tulong) tint)
                (Ssequence
                  (Sset _arg0
                    (Ecast (Ecast (Etempvar _arg0 tulong) tuint) tulong))
                  (Ssequence
                    (Sset _arg1
                      (Ecast (Ecast (Etempvar _arg1 tulong) tuint) tulong))
                    (Scall None
                      (Evar _psci_affinity_info (Tfunction
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    (Tcons tulong
                                                      (Tcons tulong Tnil)))
                                                  tvoid cc_default))
                      ((Etempvar _rec (tptr Tvoid)) ::
                       (Etempvar _arg0 tulong) :: (Etempvar _arg1 tulong) ::
                       nil))))
                (Sifthenelse (Ebinop Oeq (Etempvar _function_id tuint)
                               (Econst_long (Int64.repr 3288334340) tulong)
                               tint)
                  (Scall None
                    (Evar _psci_affinity_info (Tfunction
                                                (Tcons
                                                  (tptr Tvoid)
                                                  (Tcons tulong
                                                    (Tcons tulong Tnil))) tvoid
                                                cc_default))
                    ((Etempvar _rec (tptr Tvoid)) ::
                     (Etempvar _arg0 tulong) :: (Etempvar _arg1 tulong) :: nil))
                  (Sifthenelse (Ebinop Oeq (Etempvar _function_id tuint)
                                 (Econst_long (Int64.repr 2214592520) tulong)
                                 tint)
                    (Scall None
                      (Evar _psci_system_off (Tfunction
                                               (Tcons
                                                 (tptr Tvoid)
                                                 Tnil) tvoid cc_default))
                      ((Etempvar _rec (tptr Tvoid)) :: nil))
                    (Sifthenelse (Ebinop Oeq (Etempvar _function_id tuint)
                                   (Econst_long (Int64.repr 2214592521) tulong)
                                   tint)
                      (Scall None
                        (Evar _psci_system_reset (Tfunction
                                                   (Tcons
                                                     (tptr Tvoid)
                                                     Tnil) tvoid cc_default))
                        ((Etempvar _rec (tptr Tvoid)) ::
                         nil))
                      (Sifthenelse (Ebinop Oeq (Etempvar _function_id tuint)
                                     (Econst_long (Int64.repr 2214592522) tulong)
                                     tint)
                        (Scall None
                          (Evar _psci_features (Tfunction
                                                 (Tcons
                                                   (tptr Tvoid)
                                                   (Tcons tuint Tnil)) tvoid
                                                 cc_default))
                          ((Etempvar _rec (tptr Tvoid)) ::
                           (Etempvar _arg0 tulong) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _set_psci_result_x0 (Tfunction
                                                        (Tcons tulong Tnil)
                                                        tvoid cc_default))
                            ((Econst_long (Int64.repr 4294967295) tulong) ::
                             nil))
                          (Scall None
                            (Evar _set_psci_result_forward_psci_call (Tfunction
                                                                      (Tcons
                                                                      tuint
                                                                      Tnil)
                                                                      tvoid
                                                                      cc_default))
                            ((Econst_int (Int.repr 0) tuint) :: nil))))))))))))))
.

Definition f_psci_rsi := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_function_id, tuint) :: (_arg0, tulong) ::
                (_arg1, tulong) :: (_arg2, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body := psci_rsi_body
|}.
