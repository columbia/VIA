Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _g_rd := 1%positive.
Definition _g_rec := 2%positive.
Definition _granule := 3%positive.
Definition _idx := 4%positive.
Definition _lock := 5%positive.
Definition _rec := 6%positive.
Definition _rec_idx := 7%positive.
Definition _rec_list := 8%positive.
Definition _rec_list__1 := 9%positive.
Definition _ret := 10%positive.
Definition _t'1 := 11%positive.
Definition _t'10 := 12%positive.
Definition _t'2 := 13%positive.
Definition _t'3 := 14%positive.
Definition _t'4 := 15%positive.
Definition _t'5 := 16%positive.
Definition _t'6 := 17%positive.
Definition _t'7 := 18%positive.
Definition _t'8 := 19%positive.
Definition _t'9 := 20%positive.

Definition find_lock_rec_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _realm_get_rec_entry (Tfunction
                                     (Tcons tulong
                                       (Tcons (tptr Tvoid)
                                         Tnil))
                                     (tptr Tvoid)
                                     cc_default))
        ((Etempvar _rec_idx tulong) ::
         (Etempvar _rec_list (tptr Tvoid)) :: nil))
      (Sset _g_rec (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Scall (Some _t'10)
        (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint cc_default))
        ((Etempvar _g_rec (tptr Tvoid)) :: nil))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'10 tuint)
                     (Econst_int (Int.repr 1) tuint) tint)
        (Sreturn (Some (Etempvar _g_rec (tptr Tvoid))))
        (Ssequence
          (Scall None
            (Evar _granule_lock (Tfunction
                                  (Tcons (tptr Tvoid) Tnil)
                                  tvoid cc_default))
            ((Etempvar _g_rec (tptr Tvoid)) :: nil))
          (Ssequence
            (Scall (Some _t'9)
              (Evar _granule_get_state (Tfunction
                                         (Tcons
                                           (tptr Tvoid)
                                           Tnil) tuint cc_default))
              ((Etempvar _g_rec (tptr Tvoid)) :: nil))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'9 tuint)
                           (Econst_int (Int.repr 3) tuint) tint)
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _get_g_rec_rd (Tfunction
                                            (Tcons
                                              (tptr Tvoid)
                                              Tnil)
                                            (tptr Tvoid)
                                            cc_default))
                      ((Etempvar _g_rec (tptr Tvoid)) ::
                       nil))
                    (Scall (Some _t'4)
                      (Evar _ptr_eq (Tfunction
                                      (Tcons (tptr Tvoid)
                                        (Tcons (tptr Tvoid) Tnil)) tuint
                                      cc_default))
                      ((Etempvar _t'3 (tptr Tvoid)) ::
                       (Etempvar _g_rd (tptr Tvoid)) ::
                       nil)))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tuint)
                                 (Econst_int (Int.repr 1) tuint) tint)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'6)
                          (Evar _realm_get_rec_entry (Tfunction
                                                       (Tcons tulong
                                                         (Tcons
                                                           (tptr Tvoid)
                                                           Tnil))
                                                       (tptr Tvoid)
                                                       cc_default))
                          ((Etempvar _rec_idx tulong) ::
                           (Etempvar _rec_list (tptr Tvoid)) ::
                           nil))
                        (Scall (Some _t'7)
                          (Evar _ptr_eq (Tfunction
                                          (Tcons (tptr Tvoid)
                                            (Tcons (tptr Tvoid) Tnil)) tuint
                                          cc_default))
                          ((Etempvar _t'6 (tptr Tvoid)) ::
                           (Etempvar _g_rec (tptr Tvoid)) ::
                           nil)))
                      (Sset _t'5
                        (Ecast
                          (Ebinop Oeq (Etempvar _t'7 tuint)
                            (Econst_int (Int.repr 1) tuint) tint) tbool)))
                    (Sset _t'5 (Econst_int (Int.repr 0) tint))))
                (Sifthenelse (Etempvar _t'5 tint)
                  (Sreturn (Some (Etempvar _g_rec (tptr Tvoid))))
                  (Ssequence
                    (Scall None
                      (Evar _granule_unlock (Tfunction
                                              (Tcons
                                                (tptr Tvoid)
                                                Tnil) tvoid cc_default))
                      ((Etempvar _g_rec (tptr Tvoid)) ::
                       nil))
                    (Ssequence
                      (Scall (Some _t'2)
                        (Evar _null_ptr (Tfunction Tnil (tptr Tvoid)
                                          cc_default)) nil)
                      (Sreturn (Some (Etempvar _t'2 (tptr Tvoid))))))))
              (Ssequence
                (Scall None
                  (Evar _granule_unlock (Tfunction
                                          (Tcons
                                            (tptr Tvoid)
                                            Tnil) tvoid cc_default))
                  ((Etempvar _g_rec (tptr Tvoid)) :: nil))
                (Ssequence
                  (Scall (Some _t'8)
                    (Evar _null_ptr (Tfunction Tnil (tptr Tvoid) cc_default))
                    nil)
                  (Sreturn (Some (Etempvar _t'8 (tptr Tvoid))))))))))))
.

Definition f_find_lock_rec := {|
  fn_return := (tptr Tvoid);
  fn_callconv := cc_default;
  fn_params := ((_g_rd, (tptr Tvoid)) ::
                (_rec_list, (tptr Tvoid)) ::
                (_rec_idx, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_rec, (tptr Tvoid)) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, (tptr Tvoid)) ::
               (_t'7, tuint) :: (_t'6, (tptr Tvoid)) ::
               (_t'5, tint) :: (_t'4, tuint) ::
               (_t'3, (tptr Tvoid)) ::
               (_t'2, (tptr Tvoid)) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := find_lock_rec_body
|}.
