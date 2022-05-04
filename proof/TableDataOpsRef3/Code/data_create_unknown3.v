Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _a := 1%positive.
Definition _addr := 2%positive.
Definition _b := 3%positive.
Definition _data := 4%positive.
Definition _data_addr := 5%positive.
Definition _g := 6%positive.
Definition _g_data := 7%positive.
Definition _g_rd := 8%positive.
Definition _granule := 9%positive.
Definition _map_addr := 10%positive.
Definition _pa := 11%positive.
Definition _rd := 12%positive.
Definition _ret := 13%positive.
Definition _t'1 := 14%positive.

Definition data_create_unknown3_body :=
  (Ssequence
    (Scall (Some _t'1)
      (Evar _data_create_unknown2 (Tfunction
                                    (Tcons (tptr Tvoid)
                                      (Tcons tulong
                                        (Tcons tulong
                                          (Tcons
                                            (tptr Tvoid)
                                            Tnil)))) tulong cc_default))
      ((Etempvar _g_rd (tptr Tvoid)) ::
       (Etempvar _data_addr tulong) :: (Etempvar _map_addr tulong) ::
       (Etempvar _g_data (tptr Tvoid)) :: nil))
    (Sreturn (Some (Etempvar _t'1 tulong))))
.

Definition f_data_create_unknown3 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_g_rd, (tptr Tvoid)) ::
                (_data_addr, tulong) :: (_map_addr, tulong) ::
                (_g_data, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body := data_create_unknown3_body
|}.
