Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_realm_params := 3%positive.
Definition _granule := 4%positive.
Definition _i := 5%positive.
Definition _realm_params_addr := 6%positive.
Definition _ret := 7%positive.
Definition _t'1 := 8%positive.
Definition _t'2 := 9%positive.
Definition _t'3 := 10%positive.

Definition get_realm_params_body :=
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _find_granule (Tfunction (Tcons tulong Tnil)
                              (tptr Tvoid) cc_default))
        ((Etempvar _realm_params_addr tulong) :: nil))
      (Sset _g_realm_params (Etempvar _t'1 (tptr Tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _is_null (Tfunction (Tcons (tptr Tvoid) Tnil) tuint cc_default))
          ((Etempvar _g_realm_params (tptr Tvoid)) :: nil))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tuint)
                       (Econst_int (Int.repr 1) tuint) tint)
          (Sset _ret (Econst_int (Int.repr 1) tuint))
          (Ssequence
            (Scall None
              (Evar _ns_granule_map (Tfunction
                                      (Tcons tuint
                                        (Tcons (tptr Tvoid)
                                          Tnil)) tvoid cc_default))
              ((Econst_int (Int.repr 0) tuint) ::
               (Etempvar _g_realm_params (tptr Tvoid)) ::
               nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _ns_buffer_read_realm_params (Tfunction
                                                       (Tcons tuint Tnil) tuint
                                                       cc_default))
                  ((Econst_int (Int.repr 0) tuint) :: nil))
                (Sset _ret (Etempvar _t'2 tuint)))
              (Scall None
                (Evar _ns_buffer_unmap (Tfunction (Tcons tuint Tnil) tvoid
                                         cc_default))
                ((Econst_int (Int.repr 0) tuint) :: nil))))))
      (Sreturn (Some (Etempvar _ret tuint)))))
.

Definition f_get_realm_params := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_realm_params_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_g_realm_params, (tptr Tvoid)) ::
               (_ret, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, (tptr Tvoid)) :: nil);
  fn_body := get_realm_params_body
|}.
