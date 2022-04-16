Require Import CodeDeps.
Require Import Ident.

Local Open Scope Z_scope.

Definition _addr := 1%positive.
Definition _i := 2%positive.
Definition _index := 3%positive.
Definition _level := 4%positive.
Definition _map_addr := 5%positive.
Definition _max_level := 6%positive.
Definition _min_level := 7%positive.
Definition _ret := 8%positive.
Definition _table := 9%positive.
Definition _val := 10%positive.
Definition _valid := 11%positive.
Definition _t'1 := 12%positive.
Definition _t'2 := 13%positive.
Definition _t'3 := 14%positive.

Definition validate_table_commands_body :=
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _level tulong)
                     (Etempvar _min_level tulong) tint)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Sset _t'1
          (Ecast
            (Ebinop Ogt (Etempvar _level tulong) (Etempvar _max_level tulong)
              tint) tbool)))
      (Sifthenelse (Etempvar _t'1 tint)
        (Sset _t'2 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Scall (Some _t'3)
            (Evar _addr_is_level_aligned (Tfunction
                                           (Tcons tulong (Tcons tulong Tnil))
                                           tuint cc_default))
            ((Etempvar _map_addr tulong) :: (Etempvar _level tulong) :: nil))
          (Sset _t'2
            (Ecast
              (Ebinop Oeq (Etempvar _t'3 tuint) (Econst_int (Int.repr 0) tuint)
                tint) tbool)))))
    (Sifthenelse (Etempvar _t'2 tint)
      (Sreturn (Some (Econst_int (Int.repr 1) tuint)))
      (Sreturn (Some (Econst_int (Int.repr 0) tuint)))))
.

Definition f_validate_table_commands := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_map_addr, tulong) :: (_level, tulong) ::
                (_min_level, tulong) :: (_max_level, tulong) ::
                (_index, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tuint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body := validate_table_commands_body
|}.
