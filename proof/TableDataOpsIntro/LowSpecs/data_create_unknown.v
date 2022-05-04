Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import TableWalk.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition data_create_unknown_spec0 (g_rd: Pointer) (data_addr: Z64) (map_addr: Z64) (g_data: Pointer) (adt: RData) : option (RData * Z64) :=
    match g_rd, data_addr, map_addr, g_data with
    | (_g_rd_base, _g_rd_ofst), VZ64 _data_addr, VZ64 _map_addr, (_g_data_base, _g_data_ofst) =>
      rely is_int (4 - 1);
      rely is_int64 _map_addr;
      rely is_int64 (4 - 1);
      when adt == table_walk_lock_unlock_spec (_g_rd_base, _g_rd_ofst) (VZ64 _map_addr) (VZ64 (4 - 1)) adt;
      when'' _g_llt_base, _g_llt_ofst == get_wi_g_llt_spec  adt;
      rely is_int _g_llt_ofst;
      when' _index == get_wi_index_spec  adt;
      rely is_int64 _index;
      when _t'5 == is_null_spec (_g_llt_base, _g_llt_ofst) adt;
      rely is_int _t'5;
      if (_t'5 =? 1) then
        let _ret := 1 in
        Some (adt, (VZ64 _ret))
      else
        when'' _ll_table_base, _ll_table_ofst, adt == granule_map_spec (_g_llt_base, _g_llt_ofst) 5 adt;
        rely is_int _ll_table_ofst;
        when' _pte_val == pgte_read_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) adt;
        rely is_int64 _pte_val;
        rely is_int64 (Z.land _pte_val 504403158265495552);
        rely is_int64 ((Z.land _pte_val 504403158265495552) / 72057594037927936);
        if (negb (((Z.land _pte_val 504403158265495552) / 72057594037927936) =? 0)) then
          let _ret := 1 in
          when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
          when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
          Some (adt, (VZ64 _ret))
        else
          rely is_int64 (1 * 72057594037927936);
          rely is_int64 (Z.lor (1 * 72057594037927936) _data_addr);
          let _pte_val := (Z.lor (1 * 72057594037927936) _data_addr) in
          when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _pte_val) adt;
          rely is_int64 _data_addr;
          when adt == set_mapping_spec (VZ64 _map_addr) (VZ64 _data_addr) adt;
          when adt == granule_get_spec (_g_llt_base, _g_llt_ofst) adt;
          let _ret := 0 in
          when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
          when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
          Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
