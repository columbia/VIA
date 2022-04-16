Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _data := 2%positive.
Definition _data_addr := 3%positive.
Definition _g := 4%positive.
Definition _g_data := 5%positive.
Definition _g_rd := 6%positive.
Definition _g_src := 7%positive.
Definition _granule := 8%positive.
Definition _map_addr := 9%positive.
Definition _pa := 10%positive.
Definition _rd := 11%positive.
Definition _ret := 12%positive.
Definition _t'1 := 13%positive.

Definition data_create1_body :=
  (Ssequence
    (Scall (Some _t'1)
      (Evar _data_create (Tfunction
                           (Tcons (tptr Tvoid)
                             (Tcons tulong
                               (Tcons tulong
                                 (Tcons (tptr Tvoid)
                                   (Tcons (tptr Tvoid)
                                     Tnil))))) tulong cc_default))
      ((Etempvar _g_rd (tptr Tvoid)) ::
       (Etempvar _data_addr tulong) :: (Etempvar _map_addr tulong) ::
       (Etempvar _g_data (tptr Tvoid)) ::
       (Etempvar _g_src (tptr Tvoid)) :: nil))
    (Sreturn (Some (Etempvar _t'1 tulong))))
.

Definition f_data_create1 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_g_rd, (tptr Tvoid)) ::
                (_data_addr, tulong) :: (_map_addr, tulong) ::
                (_g_data, (tptr Tvoid)) ::
                (_g_src, (tptr Tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body := data_create1_body
|}.
