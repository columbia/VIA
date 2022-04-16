Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import TableWalk.Spec.
Require Import AbsAccessor.Spec.
Require Import TableAux3.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition table_destroy_spec0 (g_rd: Pointer) (map_addr: Z64) (rtt_addr: Z64) (level: Z64) (adt: RData) : option (RData * Z64) :=
    match g_rd, map_addr, rtt_addr, level with
    | (_g_rd_base, _g_rd_ofst), VZ64 _map_addr, VZ64 _rtt_addr, VZ64 _level =>
      let _ret := 0 in
      rely is_int64 (_level - 1);
      rely is_int64 _map_addr;
      when adt == table_walk_lock_unlock_spec (_g_rd_base, _g_rd_ofst) (VZ64 _map_addr) (VZ64 (_level - 1)) adt;
      when'' _g_llt_base, _g_llt_ofst == get_wi_g_llt_spec  adt;
      rely is_int _g_llt_ofst;
      when' _index == get_wi_index_spec  adt;
      rely is_int64 _index;
      when _t'9 == is_null_spec (_g_llt_base, _g_llt_ofst) adt;
      rely is_int _t'9;
      if (_t'9 =? 1) then
        let _ret := 1 in
        Some (adt, (VZ64 _ret))
      else
        when'' _ll_table_base, _ll_table_ofst, adt == granule_map_spec (_g_llt_base, _g_llt_ofst) 5 adt;
        rely is_int _ll_table_ofst;
        when' _llt_pte == pgte_read_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) adt;
        rely is_int64 _llt_pte;
        when _t'8 == entry_is_table_spec (VZ64 _llt_pte) adt;
        rely is_int _t'8;
        if (_t'8 =? 0) then
          let _ret := 1 in
          when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
          when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
          Some (adt, (VZ64 _ret))
        else
          rely is_int64 (Z.land _llt_pte 281474976706560);
          if (negb (_rtt_addr =? (Z.land _llt_pte 281474976706560))) then
            let _ret := 1 in
            when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
            when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
            Some (adt, (VZ64 _ret))
          else
            rely is_int64 _rtt_addr;
            when'' _g_tbl_base, _g_tbl_ofst, adt == find_lock_granule_spec (VZ64 _rtt_addr) (VZ64 5) adt;
            rely is_int _g_tbl_ofst;
            when _t'7 == is_null_spec (_g_tbl_base, _g_tbl_ofst) adt;
            rely is_int _t'7;
            if (_t'7 =? 1) then
              when adt == assert_cond_spec 0 adt;
              when adt == granule_unlock_spec (_g_tbl_base, _g_tbl_ofst) adt;
              when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
              when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
              Some (adt, (VZ64 _ret))
            else
              rely is_int64 _level;
              when' _ret, adt == table_destroy_aux_spec (_g_llt_base, _g_llt_ofst) (_g_tbl_base, _g_tbl_ofst) (_ll_table_base, _ll_table_ofst) (VZ64 _level) (VZ64 _index) (VZ64 _map_addr) adt;
              rely is_int64 _ret;
              when adt == granule_unlock_spec (_g_tbl_base, _g_tbl_ofst) adt;
              when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
              when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
              Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
