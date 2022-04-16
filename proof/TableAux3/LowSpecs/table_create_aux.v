Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux2.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition table_create_aux_spec0 (g_rd: Pointer) (g_llt: Pointer) (g_rtt: Pointer) (llt_pte: Z64) (ll_table: Pointer) (level: Z64) (index: Z64) (map_addr: Z64) (rtt_addr: Z64) (adt: RData) : option RData :=
    match g_rd, g_llt, g_rtt, llt_pte, ll_table, level, index, map_addr, rtt_addr with
    | (_g_rd_base, _g_rd_ofst), (_g_llt_base, _g_llt_ofst), (_g_rtt_base, _g_rtt_ofst), VZ64 _llt_pte, (_ll_table_base, _ll_table_ofst), VZ64 _level, VZ64 _index, VZ64 _map_addr, VZ64 _rtt_addr =>
      rely is_int64 (Z.land _llt_pte 504403158265495552);
      rely is_int64 ((Z.land _llt_pte 504403158265495552) / 72057594037927936);
      let _ipa_state := ((Z.land _llt_pte 504403158265495552) / 72057594037927936) in
      when'' _pte_base, _pte_ofst, adt == granule_map_spec (_g_rtt_base, _g_rtt_ofst) 1 adt;
      rely is_int _pte_ofst;
      when adt == granule_set_state_spec (_g_rtt_base, _g_rtt_ofst) 5 adt;
      if (_ipa_state =? 0) then
        let _t'2 := 1 in
        rely is_int64 _ipa_state;
        when adt == table_create_init_vacant_spec (VZ64 _ipa_state) (_pte_base, _pte_ofst) (_g_llt_base, _g_llt_ofst) adt;
        when adt == buffer_unmap_spec (_pte_base, _pte_ofst) adt;
        when adt == granule_get_spec (_g_rtt_base, _g_rtt_ofst) adt;
        when adt == set_g_rtt_rd_spec (_g_rtt_base, _g_rtt_ofst) (_g_rd_base, _g_rd_ofst) adt;
        rely is_int64 (Z.lor _rtt_addr 3);
        rely is_int64 _index;
        when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 (Z.lor _rtt_addr 3)) adt;
        rely is_int64 _level;
        when adt == link_table_spec (_g_llt_base, _g_llt_ofst) (_g_rtt_base, _g_rtt_ofst) (VZ64 _level) (VZ64 _index) adt;
        Some adt
      else
        let _t'2 := (_ipa_state =? 3) in
        if _t'2 then
          rely is_int64 _ipa_state;
          when adt == table_create_init_vacant_spec (VZ64 _ipa_state) (_pte_base, _pte_ofst) (_g_llt_base, _g_llt_ofst) adt;
          when adt == buffer_unmap_spec (_pte_base, _pte_ofst) adt;
          when adt == granule_get_spec (_g_rtt_base, _g_rtt_ofst) adt;
          when adt == set_g_rtt_rd_spec (_g_rtt_base, _g_rtt_ofst) (_g_rd_base, _g_rd_ofst) adt;
          rely is_int64 (Z.lor _rtt_addr 3);
          rely is_int64 _index;
          when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 (Z.lor _rtt_addr 3)) adt;
          rely is_int64 _level;
          when adt == link_table_spec (_g_llt_base, _g_llt_ofst) (_g_rtt_base, _g_rtt_ofst) (VZ64 _level) (VZ64 _index) adt;
          Some adt
        else
          if (_ipa_state =? 1) then
            rely is_int64 _level;
            rely is_int64 _llt_pte;
            when adt == table_create_init_absent_spec (VZ64 _level) (VZ64 _llt_pte) (_pte_base, _pte_ofst) (_g_rtt_base, _g_rtt_ofst) adt;
            when adt == buffer_unmap_spec (_pte_base, _pte_ofst) adt;
            when adt == granule_get_spec (_g_rtt_base, _g_rtt_ofst) adt;
            when adt == set_g_rtt_rd_spec (_g_rtt_base, _g_rtt_ofst) (_g_rd_base, _g_rd_ofst) adt;
            rely is_int64 (Z.lor _rtt_addr 3);
            rely is_int64 _index;
            when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 (Z.lor _rtt_addr 3)) adt;
            when adt == link_table_spec (_g_llt_base, _g_llt_ofst) (_g_rtt_base, _g_rtt_ofst) (VZ64 _level) (VZ64 _index) adt;
            Some adt
          else
            if (_ipa_state =? 2) then
              rely is_int64 _level;
              rely is_int64 _index;
              rely is_int64 _map_addr;
              rely is_int64 _llt_pte;
              when adt == table_create_init_present_spec (VZ64 _level) (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _map_addr) (VZ64 _llt_pte) (_pte_base, _pte_ofst) (_g_rtt_base, _g_rtt_ofst) adt;
              when adt == buffer_unmap_spec (_pte_base, _pte_ofst) adt;
              when adt == granule_get_spec (_g_rtt_base, _g_rtt_ofst) adt;
              when adt == set_g_rtt_rd_spec (_g_rtt_base, _g_rtt_ofst) (_g_rd_base, _g_rd_ofst) adt;
              rely is_int64 (Z.lor _rtt_addr 3);
              when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 (Z.lor _rtt_addr 3)) adt;
              when adt == link_table_spec (_g_llt_base, _g_llt_ofst) (_g_rtt_base, _g_rtt_ofst) (VZ64 _level) (VZ64 _index) adt;
              Some adt
            else
              when adt == assert_cond_spec 0 adt;
              when adt == buffer_unmap_spec (_pte_base, _pte_ofst) adt;
              when adt == granule_get_spec (_g_rtt_base, _g_rtt_ofst) adt;
              when adt == set_g_rtt_rd_spec (_g_rtt_base, _g_rtt_ofst) (_g_rd_base, _g_rd_ofst) adt;
              rely is_int64 (Z.lor _rtt_addr 3);
              rely is_int64 _index;
              when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 (Z.lor _rtt_addr 3)) adt;
              rely is_int64 _level;
              when adt == link_table_spec (_g_llt_base, _g_llt_ofst) (_g_rtt_base, _g_rtt_ofst) (VZ64 _level) (VZ64 _index) adt;
              Some adt
     end
    .

End SpecLow.
