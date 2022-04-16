Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_rd := 3%positive.
Definition _granule := 4%positive.
Definition _level := 5%positive.
Definition _map_addr := 6%positive.
Definition _pa := 7%positive.
Definition _rd := 8%positive.
Definition _ret := 9%positive.
Definition _table := 10%positive.
Definition _t'1 := 11%positive.

Definition table_unmap1_body :=
  (Ssequence
    (Scall (Some _t'1)
      (Evar _table_unmap (Tfunction
                           (Tcons (tptr Tvoid)
                             (Tcons tulong (Tcons tulong Tnil))) tulong
                           cc_default))
      ((Etempvar _g_rd (tptr Tvoid)) ::
       (Etempvar _map_addr tulong) :: (Etempvar _level tulong) :: nil))
    (Sreturn (Some (Etempvar _t'1 tulong))))
.

Definition f_table_unmap1 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_g_rd, (tptr Tvoid)) ::
                (_map_addr, tulong) :: (_level, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body := table_unmap1_body
|}.
