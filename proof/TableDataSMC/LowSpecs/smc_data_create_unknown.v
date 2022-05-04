Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef3.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition smc_data_create_unknown_spec0 (data_addr: Z64) (rd_addr: Z64) (map_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match data_addr, rd_addr, map_addr with
    | VZ64 _data_addr, VZ64 _rd_addr, VZ64 _map_addr =>
      let _new_data_state := 1 in
      rely is_int64 _data_addr;
      when'' _g_data_base, _g_data_ofst, adt == find_lock_granule_spec (VZ64 _data_addr) (VZ64 1) adt;
      rely is_int _g_data_ofst;
      when _t'6 == is_null_spec (_g_data_base, _g_data_ofst) adt;
      rely is_int _t'6;
      if (_t'6 =? 1) then
        let _ret := 1 in
        Some (adt, (VZ64 _ret))
      else
        rely is_int64 _rd_addr;
        when'' _g_rd_base, _g_rd_ofst, adt == find_lock_granule_spec (VZ64 _rd_addr) (VZ64 2) adt;
        rely is_int _g_rd_ofst;
        when _t'5 == is_null_spec (_g_rd_base, _g_rd_ofst) adt;
        rely is_int _t'5;
        if (_t'5 =? 1) then
          let _ret := 1 in
          when adt == granule_unlock_spec (_g_data_base, _g_data_ofst) adt;
          Some (adt, (VZ64 _ret))
        else
          when'' _rd_base, _rd_ofst, adt == granule_map_spec (_g_rd_base, _g_rd_ofst) 2 adt;
          rely is_int _rd_ofst;
          rely is_int64 _map_addr;
          when' _ret, adt == data_create_unknown3_spec (_g_rd_base, _g_rd_ofst) (VZ64 _data_addr) (VZ64 _map_addr) (_g_data_base, _g_data_ofst) adt;
          rely is_int64 _ret;
          if (_ret =? 0) then
            when adt == granule_set_state_spec (_g_data_base, _g_data_ofst) 4 adt;
            when adt == buffer_unmap_spec (_rd_base, _rd_ofst) adt;
            when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
            when adt == granule_unlock_spec (_g_data_base, _g_data_ofst) adt;
            Some (adt, (VZ64 _ret))
          else
            when adt == buffer_unmap_spec (_rd_base, _rd_ofst) adt;
            when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
            when adt == granule_unlock_spec (_g_data_base, _g_data_ofst) adt;
            Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
