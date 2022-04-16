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

  Definition data_destroy_spec0 (g_rd: Pointer) (map_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match g_rd, map_addr with
    | (_g_rd_base, _g_rd_ofst), VZ64 _map_addr =>
      rely is_int (4 - 1);
      rely is_int64 _map_addr;
      rely is_int64 (4 - 1);
      when adt == table_walk_lock_unlock_spec (_g_rd_base, _g_rd_ofst) (VZ64 _map_addr) (VZ64 (4 - 1)) adt;
      when'' _g_llt_base, _g_llt_ofst == get_wi_g_llt_spec  adt;
      rely is_int _g_llt_ofst;
      when' _index == get_wi_index_spec  adt;
      rely is_int64 _index;
      when _t'7 == is_null_spec (_g_llt_base, _g_llt_ofst) adt;
      rely is_int _t'7;
      if (_t'7 =? 1) then
        let _ret := 1 in
        Some (adt, (VZ64 _ret))
      else
        when'' _ll_table_base, _ll_table_ofst, adt == granule_map_spec (_g_llt_base, _g_llt_ofst) 5 adt;
        rely is_int _ll_table_ofst;
        when' _pte_val == pgte_read_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) adt;
        rely is_int64 _pte_val;
        rely is_int64 (Z.land _pte_val 504403158265495552);
        rely is_int64 ((Z.land _pte_val 504403158265495552) / 72057594037927936);
        let _ipa_state := ((Z.land _pte_val 504403158265495552) / 72057594037927936) in
        if (negb (_ipa_state =? 1)) then
          let _ret := 1 in
          when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
          when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
          Some (adt, (VZ64 _ret))
        else
          rely is_int64 (Z.land _pte_val 281474976706560);
          let _data_addr := (Z.land _pte_val 281474976706560) in
          rely is_int64 _data_addr;
          when'' _g_data_base, _g_data_ofst, adt == find_lock_granule_spec (VZ64 _data_addr) (VZ64 4) adt;
          rely is_int _g_data_ofst;
          when _t'6 == is_null_spec (_g_data_base, _g_data_ofst) adt;
          rely is_int _t'6;
          if (_t'6 =? 1) then
            let _ret := 1 in
            when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
            when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
            Some (adt, (VZ64 _ret))
          else
            rely is_int64 (3 * 72057594037927936);
            let _pte_val := (3 * 72057594037927936) in
            when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _pte_val) adt;
            when adt == granule_put_spec (_g_llt_base, _g_llt_ofst) adt;
            when adt == granule_memzero_spec (_g_data_base, _g_data_ofst) 1 adt;
            when adt == granule_set_state_spec (_g_data_base, _g_data_ofst) 1 adt;
            when adt == granule_unlock_spec (_g_data_base, _g_data_ofst) adt;
            let _ret := 0 in
            when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
            when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
            Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
