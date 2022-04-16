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

  Definition table_create_spec0 (g_rd: Pointer) (map_addr: Z64) (level: Z64) (g_rtt: Pointer) (rtt_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match g_rd, map_addr, level, g_rtt, rtt_addr with
    | (_g_rd_base, _g_rd_ofst), VZ64 _map_addr, VZ64 _level, (_g_rtt_base, _g_rtt_ofst), VZ64 _rtt_addr =>
      let _ret := 0 in
      rely is_int64 (_level - 1);
      rely is_int64 _map_addr;
      when adt == table_walk_lock_unlock_spec (_g_rd_base, _g_rd_ofst) (VZ64 _map_addr) (VZ64 (_level - 1)) adt;
      when'' _g_llt_base, _g_llt_ofst == get_wi_g_llt_spec  adt;
      rely is_int _g_llt_ofst;
      when' _index == get_wi_index_spec  adt;
      rely is_int64 _index;
      when _t'6 == is_null_spec (_g_llt_base, _g_llt_ofst) adt;
      rely is_int _t'6;
      if (_t'6 =? 1) then
        let _ret := 1 in
        Some (adt, (VZ64 _ret))
      else
        when'' _ll_table_base, _ll_table_ofst, adt == granule_map_spec (_g_llt_base, _g_llt_ofst) 5 adt;
        rely is_int _ll_table_ofst;
        when' _llt_pte == pgte_read_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) adt;
        rely is_int64 _llt_pte;
        when _t'5 == entry_is_table_spec (VZ64 _llt_pte) adt;
        rely is_int _t'5;
        if (_t'5 =? 1) then
          let _ret := 1 in
          when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
          when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
          Some (adt, (VZ64 _ret))
        else
          rely is_int64 _level;
          rely is_int64 _rtt_addr;
          when adt == table_create_aux_spec (_g_rd_base, _g_rd_ofst) (_g_llt_base, _g_llt_ofst) (_g_rtt_base, _g_rtt_ofst) (VZ64 _llt_pte) (_ll_table_base, _ll_table_ofst) (VZ64 _level) (VZ64 _index) (VZ64 _map_addr) (VZ64 _rtt_addr) adt;
          when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
          when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
          Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
