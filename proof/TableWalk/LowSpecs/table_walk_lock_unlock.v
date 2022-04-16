Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Fixpoint table_walk_lock_unlock_loop0 (n: nat) (l: Z) (tbl: Pointer) (last_tbl: Pointer) (map_addr: Z) (adt: RData) :=
    match n with
    | O => Some (l, tbl, last_tbl, adt)
    | S n' =>
      match table_walk_lock_unlock_loop0 n' l tbl last_tbl map_addr adt with
      | Some (l, tbl, last_tbl, adt) =>
        rely is_int l;
        when null == is_null_spec tbl adt;
        rely is_int null;
        if null =? 0 then
          when' idx == addr_to_idx_spec (VZ64 map_addr) (VZ64 l) adt;
          rely is_int64 idx;
          when tbl, adt == find_next_level_idx_spec tbl (VZ64 idx) adt;
          when null == is_null_spec tbl adt;
          rely is_int null;
          if null =? 0 then
            when adt == granule_lock_spec tbl adt;
            when adt == granule_unlock_spec last_tbl adt;
            Some (l + 1, tbl, tbl, adt)
          else
            when adt == granule_unlock_spec last_tbl adt;
            Some (l + 1, tbl, last_tbl, adt)
        else Some (l + 1, tbl, last_tbl, adt)
      | _ => None
      end
    end.

  Definition table_walk_lock_unlock_spec0 (g_rd: Pointer) (map_addr: Z64) (level: Z64) (adt: RData) : option RData :=
    match map_addr, level with
    | VZ64 map_addr, VZ64 level =>
      when rd, adt == granule_map_spec g_rd SLOT_RD adt;
      when g_root == get_rd_g_rtt_spec rd adt;
      when adt == buffer_unmap_spec rd adt;
      when adt == granule_lock_spec g_root adt;
      match table_walk_lock_unlock_loop0 (Z.to_nat level) 0 g_root g_root map_addr adt with
      | Some (l, tbl, last_tb, adt) =>
        rely is_int l;
        when adt == set_wi_g_llt_spec tbl adt;
        when' idx == addr_to_idx_spec (VZ64 map_addr) (VZ64 level) adt;
        rely is_int64 idx;
        when adt == set_wi_index_spec (VZ64 idx) adt;
        Some adt
      | _ => None
      end
    end.

End SpecLow.
