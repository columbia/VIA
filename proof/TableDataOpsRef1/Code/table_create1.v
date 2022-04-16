Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _g := 2%positive.
Definition _g_rd := 3%positive.
Definition _g_rtt := 4%positive.
Definition _granule := 5%positive.
Definition _level := 6%positive.
Definition _map_addr := 7%positive.
Definition _pa := 8%positive.
Definition _rd := 9%positive.
Definition _ret := 10%positive.
Definition _rt := 11%positive.
Definition _rtt_addr := 12%positive.
Definition _table := 13%positive.
Definition _t'1 := 14%positive.

Definition table_create1_body :=
  (Ssequence
    (Scall (Some _t'1)
      (Evar _table_create (Tfunction
                            (Tcons (tptr Tvoid)
                              (Tcons tulong
                                (Tcons tulong
                                  (Tcons (tptr Tvoid)
                                    (Tcons tulong Tnil))))) tulong cc_default))
      ((Etempvar _g_rd (tptr Tvoid)) ::
       (Etempvar _map_addr tulong) :: (Etempvar _level tulong) ::
       (Etempvar _g_rtt (tptr Tvoid)) ::
       (Etempvar _rtt_addr tulong) :: nil))
    (Sreturn (Some (Etempvar _t'1 tulong))))
.

Definition f_table_create1 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_g_rd, (tptr Tvoid)) ::
                (_map_addr, tulong) :: (_level, tulong) ::
                (_g_rtt, (tptr Tvoid)) ::
                (_rtt_addr, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body := table_create1_body
|}.
