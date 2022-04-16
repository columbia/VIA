Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _arg0 := 1%positive.
Definition _arg1 := 2%positive.
Definition _arg2 := 3%positive.
Definition _arg3 := 4%positive.
Definition _function_id := 5%positive.
Definition _g := 6%positive.
Definition _granule := 7%positive.
Definition _i := 8%positive.
Definition _rec := 9%positive.
Definition _ret := 10%positive.
Definition _rt := 11%positive.
Definition _t'1 := 12%positive.
Definition _t'10 := 13%positive.
Definition _t'11 := 14%positive.
Definition _t'12 := 15%positive.
Definition _t'13 := 16%positive.
Definition _t'14 := 17%positive.
Definition _t'2 := 18%positive.
Definition _t'3 := 19%positive.
Definition _t'4 := 20%positive.
Definition _t'5 := 21%positive.
Definition _t'6 := 22%positive.
Definition _t'7 := 23%positive.
Definition _t'8 := 24%positive.
Definition _t'9 := 25%positive.

Definition handle_ns_smc_body :=
  (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                 (Econst_long (Int64.repr 0) tulong) tint)
    (Sreturn (Some (Ecast (Econst_long (Int64.repr 1572864) tulong) tulong)))
    (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                   (Econst_long (Int64.repr 1) tulong) tint)
      (Ssequence
        (Scall (Some _t'1)
          (Evar _smc_granule_delegate (Tfunction (Tcons tulong Tnil) tulong
                                        cc_default))
          ((Etempvar _arg0 tulong) :: nil))
        (Sreturn (Some (Etempvar _t'1 tulong))))
      (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                     (Econst_long (Int64.repr 2) tulong) tint)
        (Ssequence
          (Scall (Some _t'2)
            (Evar _smc_granule_undelegate (Tfunction (Tcons tulong Tnil) tulong
                                            cc_default))
            ((Etempvar _arg0 tulong) :: nil))
          (Sreturn (Some (Etempvar _t'2 tulong))))
        (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                       (Econst_long (Int64.repr 3) tulong) tint)
          (Ssequence
            (Scall (Some _t'3)
              (Evar _smc_realm_create (Tfunction
                                        (Tcons tulong (Tcons tulong Tnil))
                                        tulong cc_default))
              ((Etempvar _arg0 tulong) :: (Etempvar _arg1 tulong) :: nil))
            (Sreturn (Some (Etempvar _t'3 tulong))))
          (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                         (Econst_long (Int64.repr 4) tulong) tint)
            (Ssequence
              (Scall (Some _t'4)
                (Evar _smc_realm_destroy (Tfunction (Tcons tulong Tnil) tulong
                                           cc_default))
                ((Etempvar _arg0 tulong) :: nil))
              (Sreturn (Some (Etempvar _t'4 tulong))))
            (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                           (Econst_long (Int64.repr 5) tulong) tint)
              (Ssequence
                (Scall (Some _t'5)
                  (Evar _smc_realm_activate (Tfunction (Tcons tulong Tnil)
                                              tulong cc_default))
                  ((Etempvar _arg0 tulong) :: nil))
                (Sreturn (Some (Etempvar _t'5 tulong))))
              (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                             (Econst_long (Int64.repr 6) tulong) tint)
                (Ssequence
                  (Scall (Some _t'6)
                    (Evar _smc_rec_create (Tfunction
                                            (Tcons tulong
                                              (Tcons tulong
                                                (Tcons tulong
                                                  (Tcons tulong Tnil)))) tulong
                                            cc_default))
                    ((Etempvar _arg0 tulong) :: (Etempvar _arg1 tulong) ::
                     (Etempvar _arg2 tulong) :: (Etempvar _arg3 tulong) :: nil))
                  (Sreturn (Some (Etempvar _t'6 tulong))))
                (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                               (Econst_long (Int64.repr 7) tulong) tint)
                  (Ssequence
                    (Scall (Some _t'7)
                      (Evar _smc_rec_destroy (Tfunction (Tcons tulong Tnil)
                                               tulong cc_default))
                      ((Etempvar _arg0 tulong) :: nil))
                    (Sreturn (Some (Etempvar _t'7 tulong))))
                  (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                                 (Econst_long (Int64.repr 8) tulong) tint)
                    (Ssequence
                      (Scall (Some _t'8)
                        (Evar _smc_data_create (Tfunction
                                                 (Tcons tulong
                                                   (Tcons tulong
                                                     (Tcons tulong
                                                       (Tcons tulong Tnil))))
                                                 tulong cc_default))
                        ((Etempvar _arg0 tulong) :: (Etempvar _arg1 tulong) ::
                         (Etempvar _arg2 tulong) :: (Etempvar _arg3 tulong) ::
                         nil))
                      (Sreturn (Some (Etempvar _t'8 tulong))))
                    (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                                   (Econst_long (Int64.repr 9) tulong) tint)
                      (Ssequence
                        (Scall (Some _t'9)
                          (Evar _smc_data_destroy (Tfunction
                                                    (Tcons tulong
                                                      (Tcons tulong Tnil))
                                                    tulong cc_default))
                          ((Etempvar _arg0 tulong) ::
                           (Etempvar _arg1 tulong) :: nil))
                        (Sreturn (Some (Etempvar _t'9 tulong))))
                      (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                                     (Econst_long (Int64.repr 10) tulong) tint)
                        (Ssequence
                          (Scall (Some _t'10)
                            (Evar _smc_rtt_create (Tfunction
                                                    (Tcons tulong
                                                      (Tcons tulong
                                                        (Tcons tulong
                                                          (Tcons tulong Tnil))))
                                                    tulong cc_default))
                            ((Etempvar _arg0 tulong) ::
                             (Etempvar _arg1 tulong) ::
                             (Etempvar _arg2 tulong) ::
                             (Etempvar _arg3 tulong) :: nil))
                          (Sreturn (Some (Etempvar _t'10 tulong))))
                        (Sifthenelse (Ebinop Oeq (Etempvar _function_id tulong)
                                       (Econst_long (Int64.repr 11) tulong)
                                       tint)
                          (Ssequence
                            (Scall (Some _t'11)
                              (Evar _smc_rtt_destroy (Tfunction
                                                       (Tcons tulong
                                                         (Tcons tulong
                                                           (Tcons tulong
                                                             (Tcons tulong
                                                               Tnil)))) tulong
                                                       cc_default))
                              ((Etempvar _arg0 tulong) ::
                               (Etempvar _arg1 tulong) ::
                               (Etempvar _arg2 tulong) ::
                               (Etempvar _arg3 tulong) :: nil))
                            (Sreturn (Some (Etempvar _t'11 tulong))))
                          (Sifthenelse (Ebinop Oeq
                                         (Etempvar _function_id tulong)
                                         (Econst_long (Int64.repr 12) tulong)
                                         tint)
                            (Ssequence
                              (Scall (Some _t'12)
                                (Evar _smc_rec_run (Tfunction
                                                     (Tcons tulong
                                                       (Tcons tulong Tnil))
                                                     tulong cc_default))
                                ((Etempvar _arg0 tulong) ::
                                 (Etempvar _arg1 tulong) :: nil))
                              (Sreturn (Some (Etempvar _t'12 tulong))))
                            (Sifthenelse (Ebinop Oeq
                                           (Etempvar _function_id tulong)
                                           (Econst_long (Int64.repr 13) tulong)
                                           tint)
                              (Ssequence
                                (Scall (Some _t'13)
                                  (Evar _smc_rtt_map (Tfunction
                                                       (Tcons tulong
                                                         (Tcons tulong
                                                           (Tcons tulong Tnil)))
                                                       tulong cc_default))
                                  ((Etempvar _arg0 tulong) ::
                                   (Etempvar _arg1 tulong) ::
                                   (Etempvar _arg2 tulong) :: nil))
                                (Sreturn (Some (Etempvar _t'13 tulong))))
                              (Sifthenelse (Ebinop Oeq
                                             (Etempvar _function_id tulong)
                                             (Econst_long (Int64.repr 14) tulong)
                                             tint)
                                (Ssequence
                                  (Scall (Some _t'14)
                                    (Evar _smc_rtt_unmap (Tfunction
                                                           (Tcons tulong
                                                             (Tcons tulong
                                                               (Tcons tulong
                                                                 Tnil))) tulong
                                                           cc_default))
                                    ((Etempvar _arg0 tulong) ::
                                     (Etempvar _arg1 tulong) ::
                                     (Etempvar _arg2 tulong) :: nil))
                                  (Sreturn (Some (Etempvar _t'14 tulong))))
                                (Ssequence
                                  (Scall None
                                    (Evar _assert_cond (Tfunction
                                                         (Tcons tuint Tnil)
                                                         tvoid cc_default))
                                    ((Econst_long (Int64.repr 0) tulong) ::
                                     nil))
                                  (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))))))))))))))))))
.

Definition f_handle_ns_smc := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_function_id, tulong) :: (_arg0, tulong) ::
                (_arg1, tulong) :: (_arg2, tulong) :: (_arg3, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'14, tulong) :: (_t'13, tulong) :: (_t'12, tulong) ::
               (_t'11, tulong) :: (_t'10, tulong) :: (_t'9, tulong) ::
               (_t'8, tulong) :: (_t'7, tulong) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := handle_ns_smc_body
|}.
