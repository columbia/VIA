Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition smc_rec_create_spec0 (rec_addr: Z64) (rd_addr: Z64) (mpidr: Z64) (rec_params_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match rec_addr, rd_addr, mpidr, rec_params_addr with
    | VZ64 _rec_addr, VZ64 _rd_addr, VZ64 _mpidr, VZ64 _rec_params_addr =>
      rely is_int64 _rec_params_addr;
      when'' _g_rec_params_base, _g_rec_params_ofst == find_granule_spec (VZ64 _rec_params_addr) adt;
      rely is_int _g_rec_params_ofst;
      when _t'15 == is_null_spec (_g_rec_params_base, _g_rec_params_ofst) adt;
      rely is_int _t'15;
      if (_t'15 =? 0) then
        rely is_int64 _rec_addr;
        when'' _g_rec_base, _g_rec_ofst, adt == find_lock_granule_spec (VZ64 _rec_addr) (VZ64 1) adt;
        when _t'14 == is_null_spec (_g_rec_base, _g_rec_ofst) adt;
        rely is_int _t'14;
        if (_t'14 =? 0) then
          rely is_int64 _rd_addr;
          when'' _g_rd_base, _g_rd_ofst, adt == find_lock_granule_spec (VZ64 _rd_addr) (VZ64 2) adt;
          when _t'13 == is_null_spec (_g_rd_base, _g_rd_ofst) adt;
          rely is_int _t'13;
          if (_t'13 =? 0) then
            when adt == ns_granule_map_spec 0 (_g_rec_params_base, _g_rec_params_ofst) adt;
            when _ns_access_ok, adt == ns_buffer_read_rec_params_spec 0 adt;
            rely is_int _ns_access_ok;
            when adt == ns_buffer_unmap_spec 0 adt;
            if (_ns_access_ok =? 0) then
              when'' _rec_base, _rec_ofst, adt == granule_map_spec (_g_rec_base, _g_rec_ofst) 3 adt;
              when'' _rd_base, _rd_ofst, adt == granule_map_spec (_g_rd_base, _g_rd_ofst) 2 adt;
              when'' _t'7_base, _t'7_ofst == get_rd_g_rec_list_spec (_rd_base, _rd_ofst) adt;
              when'' _t'8_base, _t'8_ofst, adt == granule_map_spec (_t'7_base, _t'7_ofst) 6 adt;
              when _t'12 == get_rd_state_spec (_rd_base, _rd_ofst) adt;
              rely is_int _t'12;
              if (_t'12 =? 0) then
                rely is_int64 _mpidr;
                when _t'11 == mpidr_is_valid_spec (VZ64 _mpidr) adt;
                rely is_int _t'11;
                if (_t'11 =? 1) then
                  when' _rec_idx == mpidr_to_rec_idx_spec (VZ64 _mpidr) adt;
                  rely is_int64 _rec_idx;
                  when _t'10, adt == is_rec_valid_spec (VZ64 _rec_idx) (_t'8_base, _t'8_ofst) adt;
                  rely is_int _t'10;
                  if (_t'10 =? 1) then
                    when adt == rec_create_ops_spec (_g_rd_base, _g_rd_ofst) (_g_rec_base, _g_rec_ofst) (_rd_base, _rd_ofst) (_t'8_base, _t'8_ofst) (_rec_base, _rec_ofst) (VZ64 _mpidr) (VZ64 _rec_idx) adt;
                    let _ret := 0 in
                    when adt == buffer_unmap_spec (_t'8_base, _t'8_ofst) adt;
                    when adt == buffer_unmap_spec (_rd_base, _rd_ofst) adt;
                    when adt == buffer_unmap_spec (_rec_base, _rec_ofst) adt;
                    when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
                    when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
                    Some (adt, (VZ64 _ret))
                  else
                    let _ret := 1 in
                    when adt == buffer_unmap_spec (_t'8_base, _t'8_ofst) adt;
                    when adt == buffer_unmap_spec (_rd_base, _rd_ofst) adt;
                    when adt == buffer_unmap_spec (_rec_base, _rec_ofst) adt;
                    when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
                    when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
                    Some (adt, (VZ64 _ret))
                else
                  let _ret := 1 in
                  when adt == buffer_unmap_spec (_t'8_base, _t'8_ofst) adt;
                  when adt == buffer_unmap_spec (_rd_base, _rd_ofst) adt;
                  when adt == buffer_unmap_spec (_rec_base, _rec_ofst) adt;
                  when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
                  when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
                  Some (adt, (VZ64 _ret))
              else
                let _ret := 1 in
                when adt == buffer_unmap_spec (_t'8_base, _t'8_ofst) adt;
                when adt == buffer_unmap_spec (_rd_base, _rd_ofst) adt;
                when adt == buffer_unmap_spec (_rec_base, _rec_ofst) adt;
                when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
                when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
                Some (adt, (VZ64 _ret))
            else
              let _ret := 1 in
              when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
              when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
              Some (adt, (VZ64 _ret))
          else
            let _ret := 1 in
            when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
            Some (adt, (VZ64 _ret))
        else
          let _ret := 1 in
          Some (adt, (VZ64 _ret))
      else
        let _ret := 1 in
        Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
