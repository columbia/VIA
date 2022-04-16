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

  Definition table_map_spec0 (g_rd: Pointer) (map_addr: Z64) (level: Z64) (adt: RData) : option (RData * Z64) :=
    match g_rd, map_addr, level with
    | (_g_rd_base, _g_rd_ofst), VZ64 _map_addr, VZ64 _level =>
      rely is_int64 (_level - 1);
      rely is_int64 _map_addr;
      when adt == table_walk_lock_unlock_spec (_g_rd_base, _g_rd_ofst) (VZ64 _map_addr) (VZ64 (_level - 1)) adt;
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
        when' _llt_pgte == pgte_read_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) adt;
        rely is_int64 _llt_pgte;
        if (_level <? 3) then
          when _t'6 == entry_is_table_spec (VZ64 _llt_pgte) adt;
          rely is_int _t'6;
          let _t'5 := (_t'6 =? 1) in
          if _t'5 then
            let _ret := 1 in
            when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
            when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
            Some (adt, (VZ64 _ret))
          else
            rely is_int64 (Z.land _llt_pgte 281474976706560);
            let _data_addr := (Z.land _llt_pgte 281474976706560) in
            rely is_int64 (Z.land _llt_pgte 504403158265495552);
            rely is_int64 ((Z.land _llt_pgte 504403158265495552) / 72057594037927936);
            let _ipa_state := ((Z.land _llt_pgte 504403158265495552) / 72057594037927936) in
            if (_ipa_state =? 1) then
              rely is_int64 (2 * 72057594037927936);
              rely is_int64 (Z.lor (2 * 72057594037927936) _data_addr);
              let _new_pgte := (Z.lor (2 * 72057594037927936) _data_addr) in
              if (_level =? 3) then
                rely is_int64 (Z.lor _new_pgte 2011);
                let _new_pgte := (Z.lor _new_pgte 2011) in
                rely is_int64 _new_pgte;
                when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _new_pgte) adt;
                let _ret := 0 in
                when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
                when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
                Some (adt, (VZ64 _ret))
              else
                rely is_int64 (Z.lor _new_pgte 2009);
                let _new_pgte := (Z.lor _new_pgte 2009) in
                rely is_int64 _new_pgte;
                when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _new_pgte) adt;
                let _ret := 0 in
                when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
                when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
                Some (adt, (VZ64 _ret))
            else
              let _ret := 1 in
              when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
              when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
              Some (adt, (VZ64 _ret))
        else
          let _t'5 := 0 in
          rely is_int64 (Z.land _llt_pgte 281474976706560);
          let _data_addr := (Z.land _llt_pgte 281474976706560) in
          rely is_int64 (Z.land _llt_pgte 504403158265495552);
          rely is_int64 ((Z.land _llt_pgte 504403158265495552) / 72057594037927936);
          let _ipa_state := ((Z.land _llt_pgte 504403158265495552) / 72057594037927936) in
          if (_ipa_state =? 1) then
            rely is_int64 (2 * 72057594037927936);
            rely is_int64 (Z.lor (2 * 72057594037927936) _data_addr);
            let _new_pgte := (Z.lor (2 * 72057594037927936) _data_addr) in
            if (_level =? 3) then
              rely is_int64 (Z.lor _new_pgte 2011);
              let _new_pgte := (Z.lor _new_pgte 2011) in
              rely is_int64 _new_pgte;
              when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _new_pgte) adt;
              let _ret := 0 in
              when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
              when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
              Some (adt, (VZ64 _ret))
            else
              rely is_int64 (Z.lor _new_pgte 2009);
              let _new_pgte := (Z.lor _new_pgte 2009) in
              rely is_int64 _new_pgte;
              when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 _new_pgte) adt;
              let _ret := 0 in
              when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
              when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
              Some (adt, (VZ64 _ret))
          else
            let _ret := 1 in
            when adt == buffer_unmap_spec (_ll_table_base, _ll_table_ofst) adt;
            when adt == granule_unlock_spec (_g_llt_base, _g_llt_ofst) adt;
            Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
