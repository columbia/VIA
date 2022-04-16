Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _context_id := 2%positive.
Definition _entry_point_address := 3%positive.
Definition _g_rec := 4%positive.
Definition _g_target_rec := 5%positive.
Definition _granule := 6%positive.
Definition _idx := 7%positive.
Definition _idx1 := 8%positive.
Definition _idx2 := 9%positive.
Definition _par_base := 10%positive.
Definition _par_end := 11%positive.
Definition _rec := 12%positive.
Definition _rec__1 := 13%positive.
Definition _ret := 14%positive.
Definition _target_cpu := 15%positive.
Definition _target_rec := 16%positive.
Definition _t'1 := 17%positive.
Definition _t'2 := 18%positive.
Definition _t'3 := 19%positive.
Definition _t'4 := 20%positive.
Definition _t'5 := 21%positive.
Definition _t'6 := 22%positive.
Definition _t'7 := 23%positive.
Definition _t'8 := 24%positive.

Definition psci_cpu_on_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_rec_par_base (Tfunction
                                  (Tcons (tptr Tvoid) Tnil)
                                  tulong cc_default))
        ((Etempvar _rec (tptr Tvoid)) :: nil))
      (Sset _par_base (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_rec_par_end (Tfunction
                                   (Tcons (tptr Tvoid) Tnil)
                                   tulong cc_default))
          ((Etempvar _rec (tptr Tvoid)) :: nil))
        (Sset _par_end (Etempvar _t'2 tulong)))
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _entry_point_address tulong)
                       (Etempvar _par_base tulong) tint)
          (Sset _t'8 (Econst_int (Int.repr 1) tint))
          (Sset _t'8
            (Ecast
              (Ebinop Oge (Etempvar _entry_point_address tulong)
                (Etempvar _par_end tulong) tint) tbool)))
        (Sifthenelse (Etempvar _t'8 tint)
          (Scall None
            (Evar _set_psci_result_x0 (Tfunction (Tcons tulong Tnil) tvoid
                                        cc_default))
            ((Econst_long (Int64.repr 4294967287) tulong) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _mpidr_to_rec_idx (Tfunction (Tcons tulong Tnil) tulong
                                          cc_default))
                ((Etempvar _target_cpu tulong) :: nil))
              (Sset _idx1 (Ecast (Etempvar _t'3 tulong) tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _get_rec_rec_idx (Tfunction
                                           (Tcons (tptr Tvoid)
                                             Tnil) tulong cc_default))
                  ((Etempvar _rec (tptr Tvoid)) :: nil))
                (Sset _idx2 (Ecast (Etempvar _t'4 tulong) tuint)))
              (Sifthenelse (Ebinop Oeq (Etempvar _idx1 tuint)
                             (Etempvar _idx2 tuint) tint)
                (Scall None
                  (Evar _set_psci_result_x0 (Tfunction (Tcons tulong Tnil)
                                              tvoid cc_default))
                  ((Econst_long (Int64.repr 4294967292) tulong) :: nil))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _psci_lookup_target (Tfunction
                                                  (Tcons
                                                    (tptr Tvoid)
                                                    (Tcons tulong Tnil))
                                                  (tptr Tvoid)
                                                  cc_default))
                      ((Etempvar _rec (tptr Tvoid)) ::
                       (Etempvar _target_cpu tulong) :: nil))
                    (Sset _g_target_rec
                      (Etempvar _t'5 (tptr Tvoid))))
                  (Ssequence
                    (Scall (Some _t'7)
                      (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint
                                       cc_default))
                      ((Etempvar _g_target_rec (tptr Tvoid)) ::
                       nil))
                    (Sifthenelse (Ebinop Oeq (Etempvar _t'7 tuint)
                                   (Econst_int (Int.repr 1) tuint) tint)
                      (Scall None
                        (Evar _set_psci_result_x0 (Tfunction
                                                    (Tcons tulong Tnil) tvoid
                                                    cc_default))
                        ((Econst_long (Int64.repr 4294967294) tulong) :: nil))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'6)
                            (Evar _granule_map (Tfunction
                                                 (Tcons
                                                   (tptr Tvoid)
                                                   (Tcons tuint Tnil))
                                                 (tptr Tvoid) cc_default))
                            ((Etempvar _g_target_rec (tptr Tvoid)) ::
                             (Econst_int (Int.repr 4) tuint) :: nil))
                          (Sset _target_rec (Etempvar _t'6 (tptr Tvoid))))
                        (Scall None
                          (Evar _psci_cpu_on_target (Tfunction
                                                      (Tcons
                                                        (tptr Tvoid)
                                                        (Tcons
                                                          (tptr Tvoid)
                                                          (Tcons
                                                            (tptr Tvoid)
                                                            (Tcons tulong
                                                              (Tcons tulong
                                                                Tnil))))) tvoid
                                                      cc_default))
                          ((Etempvar _g_target_rec (tptr Tvoid)) ::
                           (Etempvar _target_rec (tptr Tvoid)) ::
                           (Etempvar _rec (tptr Tvoid)) ::
                           (Etempvar _entry_point_address tulong) ::
                           (Etempvar _target_cpu tulong) :: nil)))))))))))))
.

Definition f_psci_cpu_on := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rec, (tptr Tvoid)) ::
                (_target_cpu, tulong) :: (_entry_point_address, tulong) ::
                (_context_id, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_target_rec, (tptr Tvoid)) ::
               (_target_rec, (tptr Tvoid)) ::
               (_par_base, tulong) :: (_par_end, tulong) ::
               (_g_rec, (tptr Tvoid)) ::
               (_idx1, tuint) :: (_idx2, tuint) :: (_t'8, tint) ::
               (_t'7, tuint) :: (_t'6, (tptr Tvoid)) ::
               (_t'5, (tptr Tvoid)) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body := psci_cpu_on_body
|}.
