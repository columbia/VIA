Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition validate_table_commands_spec (map_addr: Z64) (level: Z64) (min_level: Z64) (max_level: Z64) (index: Z64) (adt: RData) : option Z :=
    match map_addr, level, min_level, max_level, index with
    | VZ64 map_addr, VZ64 level, VZ64 min_level, VZ64 max_level, VZ64 index =>
      rely is_int64 map_addr; rely is_int64 level;
      if (level >=? min_level) && (level <=? max_level) && (__addr_is_level_aligned map_addr level) then
        Some 0
      else
        Some 1
    end.

End Spec.

