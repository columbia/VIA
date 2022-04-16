Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux2.Spec.
Require Import TableAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition table_destroy_aux_spec0 (g_llt: Pointer) (g_tbl: Pointer) (ll_table: Pointer) (level: Z64) (index: Z64) (map_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match g_llt, g_tbl, ll_table, level, index, map_addr with
    | (_g_llt_base, _g_llt_ofst), (_g_tbl_base, _g_tbl_ofst), (_ll_table_base, _ll_table_ofst), VZ64 _level, VZ64 _index, VZ64 _map_addr =>
      let _ret := 0 in
      when'' _table_base, _table_ofst, adt == granule_map_spec (_g_tbl_base, _g_tbl_ofst) 7 adt;
      rely is_int _table_ofst;
      when' _gcnt, adt == get_g_rtt_refcount_spec (_g_tbl_base, _g_tbl_ofst) adt;
      rely is_int64 _gcnt;
      if (_gcnt =? 1) then
        let _t'6 := 1 in
        if (_gcnt =? 1) then
          when' _new_pgte, adt == table_delete_spec (_table_base, _table_ofst) (_g_llt_base, _g_llt_ofst) adt;
          rely is_int64 _new_pgte;
          rely is_int64 _index;
          when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 0) adt;
          rely is_int64 (Z.land _new_pgte 504403158265495552);
          rely is_int64 ((Z.land _new_pgte 504403158265495552) / 72057594037927936);
          if (((Z.land _new_pgte 504403158265495552) / 72057594037927936) =? 2) then
            rely is_int64 _map_addr;
            when adt == invalidate_pages_in_block_spec (VZ64 _map_addr) adt;
            when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _new_pgte) adt;
            when adt == granule_put_spec (_g_tbl_base, _g_tbl_ofst) adt;
            when'' _t'5_base, _t'5_ofst == null_ptr_spec  adt;
            rely is_int _t'5_ofst;
            when adt == set_g_rtt_rd_spec (_g_tbl_base, _g_tbl_ofst) (_t'5_base, _t'5_ofst) adt;
            when adt == granule_memzero_mapped_spec (_table_base, _table_ofst) adt;
            when adt == granule_set_state_spec (_g_tbl_base, _g_tbl_ofst) 1 adt;
            when adt == buffer_unmap_spec (_table_base, _table_ofst) adt;
            Some (adt, (VZ64 _ret))
          else
            rely is_int64 _map_addr;
            when adt == invalidate_block_spec (VZ64 _map_addr) adt;
            when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _new_pgte) adt;
            when adt == granule_put_spec (_g_tbl_base, _g_tbl_ofst) adt;
            when'' _t'5_base, _t'5_ofst == null_ptr_spec  adt;
            rely is_int _t'5_ofst;
            when adt == set_g_rtt_rd_spec (_g_tbl_base, _g_tbl_ofst) (_t'5_base, _t'5_ofst) adt;
            when adt == granule_memzero_mapped_spec (_table_base, _table_ofst) adt;
            when adt == granule_set_state_spec (_g_tbl_base, _g_tbl_ofst) 1 adt;
            when adt == buffer_unmap_spec (_table_base, _table_ofst) adt;
            Some (adt, (VZ64 _ret))
        else
          rely is_int64 _level;
          when' _new_pgte, adt == table_fold_spec (_table_base, _table_ofst) (VZ64 _level) (_g_tbl_base, _g_tbl_ofst) adt;
          rely is_int64 _new_pgte;
          rely is_int64 _index;
          when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 0) adt;
          rely is_int64 (Z.land _new_pgte 504403158265495552);
          rely is_int64 ((Z.land _new_pgte 504403158265495552) / 72057594037927936);
          if (((Z.land _new_pgte 504403158265495552) / 72057594037927936) =? 2) then
            rely is_int64 _map_addr;
            when adt == invalidate_pages_in_block_spec (VZ64 _map_addr) adt;
            when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _new_pgte) adt;
            when adt == granule_put_spec (_g_tbl_base, _g_tbl_ofst) adt;
            when'' _t'5_base, _t'5_ofst == null_ptr_spec  adt;
            rely is_int _t'5_ofst;
            when adt == set_g_rtt_rd_spec (_g_tbl_base, _g_tbl_ofst) (_t'5_base, _t'5_ofst) adt;
            when adt == granule_memzero_mapped_spec (_table_base, _table_ofst) adt;
            when adt == granule_set_state_spec (_g_tbl_base, _g_tbl_ofst) 1 adt;
            when adt == buffer_unmap_spec (_table_base, _table_ofst) adt;
            Some (adt, (VZ64 _ret))
          else
            rely is_int64 _map_addr;
            when adt == invalidate_block_spec (VZ64 _map_addr) adt;
            when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _new_pgte) adt;
            when adt == granule_put_spec (_g_tbl_base, _g_tbl_ofst) adt;
            when'' _t'5_base, _t'5_ofst == null_ptr_spec  adt;
            rely is_int _t'5_ofst;
            when adt == set_g_rtt_rd_spec (_g_tbl_base, _g_tbl_ofst) (_t'5_base, _t'5_ofst) adt;
            when adt == granule_memzero_mapped_spec (_table_base, _table_ofst) adt;
            when adt == granule_set_state_spec (_g_tbl_base, _g_tbl_ofst) 1 adt;
            when adt == buffer_unmap_spec (_table_base, _table_ofst) adt;
            Some (adt, (VZ64 _ret))
      else
        rely is_int64 (512 + 1);
        let _t'6 := (_gcnt =? (512 + 1)) in
        if _t'6 then
          if (_gcnt =? 1) then
            when' _new_pgte, adt == table_delete_spec (_table_base, _table_ofst) (_g_llt_base, _g_llt_ofst) adt;
            rely is_int64 _new_pgte;
            rely is_int64 _index;
            when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 0) adt;
            rely is_int64 (Z.land _new_pgte 504403158265495552);
            rely is_int64 ((Z.land _new_pgte 504403158265495552) / 72057594037927936);
            if (((Z.land _new_pgte 504403158265495552) / 72057594037927936) =? 2) then
              rely is_int64 _map_addr;
              when adt == invalidate_pages_in_block_spec (VZ64 _map_addr) adt;
              when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _new_pgte) adt;
              when adt == granule_put_spec (_g_tbl_base, _g_tbl_ofst) adt;
              when'' _t'5_base, _t'5_ofst == null_ptr_spec  adt;
              rely is_int _t'5_ofst;
              when adt == set_g_rtt_rd_spec (_g_tbl_base, _g_tbl_ofst) (_t'5_base, _t'5_ofst) adt;
              when adt == granule_memzero_mapped_spec (_table_base, _table_ofst) adt;
              when adt == granule_set_state_spec (_g_tbl_base, _g_tbl_ofst) 1 adt;
              when adt == buffer_unmap_spec (_table_base, _table_ofst) adt;
              Some (adt, (VZ64 _ret))
            else
              rely is_int64 _map_addr;
              when adt == invalidate_block_spec (VZ64 _map_addr) adt;
              when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _new_pgte) adt;
              when adt == granule_put_spec (_g_tbl_base, _g_tbl_ofst) adt;
              when'' _t'5_base, _t'5_ofst == null_ptr_spec  adt;
              rely is_int _t'5_ofst;
              when adt == set_g_rtt_rd_spec (_g_tbl_base, _g_tbl_ofst) (_t'5_base, _t'5_ofst) adt;
              when adt == granule_memzero_mapped_spec (_table_base, _table_ofst) adt;
              when adt == granule_set_state_spec (_g_tbl_base, _g_tbl_ofst) 1 adt;
              when adt == buffer_unmap_spec (_table_base, _table_ofst) adt;
              Some (adt, (VZ64 _ret))
          else
            rely is_int64 _level;
            when' _new_pgte, adt == table_fold_spec (_table_base, _table_ofst) (VZ64 _level) (_g_tbl_base, _g_tbl_ofst) adt;
            rely is_int64 _new_pgte;
            rely is_int64 _index;
            when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 0) adt;
            rely is_int64 (Z.land _new_pgte 504403158265495552);
            rely is_int64 ((Z.land _new_pgte 504403158265495552) / 72057594037927936);
            if (((Z.land _new_pgte 504403158265495552) / 72057594037927936) =? 2) then
              rely is_int64 _map_addr;
              when adt == invalidate_pages_in_block_spec (VZ64 _map_addr) adt;
              when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _new_pgte) adt;
              when adt == granule_put_spec (_g_tbl_base, _g_tbl_ofst) adt;
              when'' _t'5_base, _t'5_ofst == null_ptr_spec  adt;
              rely is_int _t'5_ofst;
              when adt == set_g_rtt_rd_spec (_g_tbl_base, _g_tbl_ofst) (_t'5_base, _t'5_ofst) adt;
              when adt == granule_memzero_mapped_spec (_table_base, _table_ofst) adt;
              when adt == granule_set_state_spec (_g_tbl_base, _g_tbl_ofst) 1 adt;
              when adt == buffer_unmap_spec (_table_base, _table_ofst) adt;
              Some (adt, (VZ64 _ret))
            else
              rely is_int64 _map_addr;
              when adt == invalidate_block_spec (VZ64 _map_addr) adt;
              when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _new_pgte) adt;
              when adt == granule_put_spec (_g_tbl_base, _g_tbl_ofst) adt;
              when'' _t'5_base, _t'5_ofst == null_ptr_spec  adt;
              rely is_int _t'5_ofst;
              when adt == set_g_rtt_rd_spec (_g_tbl_base, _g_tbl_ofst) (_t'5_base, _t'5_ofst) adt;
              when adt == granule_memzero_mapped_spec (_table_base, _table_ofst) adt;
              when adt == granule_set_state_spec (_g_tbl_base, _g_tbl_ofst) 1 adt;
              when adt == buffer_unmap_spec (_table_base, _table_ofst) adt;
              Some (adt, (VZ64 _ret))
        else
          let _ret := 1 in
          when adt == buffer_unmap_spec (_table_base, _table_ofst) adt;
          Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
