Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition validate_table_commands_spec0 (map_addr: Z64) (level: Z64) (min_level: Z64) (max_level: Z64) (index: Z64) (adt: RData) : option Z :=
    match map_addr, level, min_level, max_level, index with
    | VZ64 _map_addr, VZ64 _level, VZ64 _min_level, VZ64 _max_level, VZ64 _index =>
      if (_level <? _min_level) then
        let _t'1 := 1 in
        let _t'2 := 1 in
        Some 1
      else
        let _t'1 := (_level >? _max_level) in
        if _t'1 then
          let _t'2 := 1 in
          Some 1
        else
          rely is_int64 _map_addr;
          rely is_int64 _level;
          when _t'3 == addr_is_level_aligned_spec (VZ64 _map_addr) (VZ64 _level) adt;
          rely is_int _t'3;
          let _t'2 := (_t'3 =? 0) in
          if _t'2 then
            Some 1
          else
            Some 0
     end
    .

End SpecLow.
